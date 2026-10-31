use std::cell::RefCell;
use std::path::Path;
use std::sync::Arc;

use rustc_data_structures::fx::FxHashMap;
use rustc_hir::def_id::{CrateNum, DefId, DefIndex, DefPathHash, LOCAL_CRATE, StableCrateId};
use rustc_middle::mir::interpret::{AllocDecodingSession, AllocDecodingState, AllocId};
use rustc_middle::ty::codec::TyDecoder;
use rustc_middle::ty::{Ty, TyCtxt};
use rustc_serialize::opaque::{MAGIC_END_BYTES, MemDecoder};
use rustc_serialize::{Decodable as _, Decoder};
use rustc_span::hygiene::{HygieneDecodeContext, SyntaxContextKey};
use rustc_span::source_map::SourceMap;
use rustc_span::{
    AttrId, BlobDecoder, BytePos, ByteSymbol, ExpnData, ExpnHash, ExpnId, Pos, SourceFile, Span,
    SpanDecoder, Symbol, SyntaxContext,
};

use super::{Error, Footer, Header, MAGIC, VERSION, checksum, io_error};
use crate::RecordedMir;

pub(crate) fn read(tcx: TyCtxt<'_>, path: &Path, krate: CrateNum) -> Result<RecordedCrate, Error> {
    let mut bytes: Vec<u8> = std::fs::read(path).map_err(|e| io_error(path, e))?;
    let fail = || Error::new(format!("the MIR file `{}` is truncated or corrupt", path.display()));
    if bytes.len() < MAGIC.len() + 4 + MAGIC_END_BYTES.len() + 24 {
        return Err(fail());
    }
    let trailer: usize = bytes.len() - 16;
    let length: u64 = u64::from_le_bytes(
        bytes[trailer..trailer + 8].try_into().expect("the length field is eight bytes"),
    );
    let saved_checksum: u64 = u64::from_le_bytes(
        bytes[trailer + 8..].try_into().expect("the checksum field is eight bytes"),
    );
    let data: &[u8] = &bytes[..trailer];
    if length != data.len() as u64 || checksum(data) != saved_checksum || !data.starts_with(MAGIC) {
        return Err(fail());
    }
    // Reject incompatible layouts before rustc's decoder reads any header fields.
    let version: u32 = u32::from_le_bytes(
        data[MAGIC.len()..MAGIC.len() + 4].try_into().expect("the version field is four bytes"),
    );
    if version != VERSION {
        return Err(Error::new(format!(
            "MIR file format version {version} is unsupported (expected {VERSION})"
        )));
    }
    let mut opaque: MemDecoder<'_> = MemDecoder::new(data, MAGIC.len() + 4).map_err(|()| fail())?;
    let header: Header = Header::decode(&mut opaque);
    header.validate(&Header::new(tcx, krate))?;
    let content_end: usize = opaque.len();
    if content_end < 8 {
        return Err(fail());
    }
    let footer_pos: usize = usize::try_from(u64::from_le_bytes(
        data[content_end - 8..content_end].try_into().expect("the footer field is eight bytes"),
    ))
    .map_err(|_| fail())?;
    if footer_pos >= content_end - 8 {
        return Err(fail());
    }
    let mut footer_decoder: MemDecoder<'_> =
        MemDecoder::new(data, footer_pos).map_err(|()| fail())?;
    let footer: Footer = Footer::decode(&mut footer_decoder);
    if footer.roots.values().any(|&p| p < MAGIC.len() || p >= footer_pos)
        || footer.allocations.iter().any(|&p| !usize::try_from(p).is_ok_and(|p| p < footer_pos))
        || footer.source_files.iter().any(|&p| p >= footer_pos)
        || footer.syntax_contexts.values().any(|&p| p >= footer_pos)
        || footer.expansions.values().any(|&(_, p)| p >= footer_pos)
    {
        return Err(fail());
    }
    bytes.truncate(trailer);
    let allocations: AllocDecodingState = AllocDecodingState::new(footer.allocations.clone());
    let files: RefCell<Vec<Option<Arc<SourceFile>>>> =
        RefCell::new(vec![None; footer.source_files.len()]);
    Ok(RecordedCrate {
        data: bytes,
        footer,
        allocations,
        files,
        hygiene: HygieneDecodeContext::default(),
    })
}

pub(crate) struct RecordedCrate {
    data: Vec<u8>,
    footer: Footer,
    allocations: AllocDecodingState,
    hygiene: HygieneDecodeContext,
    files: RefCell<Vec<Option<Arc<SourceFile>>>>,
}

impl RecordedCrate {
    pub(crate) fn body_set<'tcx>(
        &self,
        tcx: TyCtxt<'tcx>,
        root: DefId,
    ) -> Result<RecordedMir<'tcx>, Error> {
        let hash: DefPathHash = tcx.def_path_hash(root);
        let &position = self.footer.roots.get(&hash).ok_or_else(|| {
            Error::new(format!("recorded MIR has no body for `{}`", tcx.def_path_str(root)))
        })?;
        let mut decoder = MirDecoder {
            tcx,
            opaque: MemDecoder::new(&self.data, position).expect("validated MIR container"),
            types: FxHashMap::default(),
            footer: &self.footer,
            allocations: self.allocations.new_decoding_session(),
            hygiene: &self.hygiene,
            files: &self.files,
        };
        let set: RecordedMir<'tcx> = RecordedMir::decode(&mut decoder);
        if set.root != root {
            return Err(Error::new("recorded MIR root does not match its index"));
        }
        Ok(set)
    }
}

struct MirDecoder<'a, 'tcx> {
    tcx: TyCtxt<'tcx>,
    opaque: MemDecoder<'a>,
    types: FxHashMap<usize, Ty<'tcx>>,
    footer: &'a Footer,
    allocations: AllocDecodingSession<'a>,
    hygiene: &'a HygieneDecodeContext,
    files: &'a RefCell<Vec<Option<Arc<SourceFile>>>>,
}

rustc_middle::implement_ty_decoder!(MirDecoder<'a, 'tcx>);

impl MirDecoder<'_, '_> {
    fn source_file(&mut self, index: usize) -> Arc<SourceFile> {
        if let Some(file) = &self.files.borrow()[index] {
            return Arc::clone(file);
        }
        let file: SourceFile =
            self.with_position(self.footer.source_files[index], SourceFile::decode);
        let source_map: &SourceMap = self.tcx.sess.source_map();
        let existing: Option<Arc<SourceFile>> = source_map.source_file_by_stable_id(file.stable_id);
        let file: Arc<SourceFile> = existing.unwrap_or_else(|| {
            source_map.new_imported_source_file(
                file.name,
                file.src_hash,
                file.checksum_hash,
                file.stable_id,
                file.normalized_source_len.to_u32(),
                file.unnormalized_source_len,
                file.cnum,
                file.lines,
                file.multibyte_chars,
                file.normalized_pos,
                0,
            )
        });
        self.files.borrow_mut()[index] = Some(Arc::clone(&file));
        file
    }
}

impl BlobDecoder for MirDecoder<'_, '_> {
    fn decode_symbol(&mut self) -> Symbol {
        Symbol::intern(self.read_str())
    }
    fn decode_byte_symbol(&mut self) -> ByteSymbol {
        ByteSymbol::intern(self.read_byte_str())
    }
    fn decode_def_index(&mut self) -> DefIndex {
        panic!("recorded MIR contains a DefIndex without a definition");
    }
}

impl SpanDecoder for MirDecoder<'_, '_> {
    fn decode_span(&mut self) -> Span {
        let context: SyntaxContext = SyntaxContext::decode(self);
        match self.read_u8() {
            0 => Span::new(BytePos(0), BytePos(0), context, None),
            1 => {
                let index: usize = usize::decode(self);
                let offset: BytePos = BytePos::decode(self);
                let length: BytePos = BytePos::decode(self);
                let file: Arc<SourceFile> = self.source_file(index);
                let lo: BytePos = file.start_pos + offset;
                Span::new(lo, lo + length, context, None)
            }
            tag => panic!("invalid recorded MIR span tag {tag}"),
        }
    }
    fn decode_expn_id(&mut self) -> ExpnId {
        let hash: ExpnHash = ExpnHash::decode(self);
        if hash.is_root() {
            return ExpnId::root();
        }
        if let Some(expansion) = ExpnId::from_hash(hash) {
            return expansion;
        }
        let krate: CrateNum = self.tcx.stable_crate_id_to_crate_num(hash.stable_crate_id());
        let (index, pos) = self.footer.expansions[&hash];
        if krate == LOCAL_CRATE {
            let data: ExpnData = self.with_position(pos, ExpnData::decode);
            rustc_span::hygiene::register_local_expn_id(data, hash)
        } else {
            rustc_span::hygiene::decode_expn_id(krate, index, |_| {
                let data: ExpnData = self.with_position(pos, ExpnData::decode);
                (data, hash)
            })
        }
    }
    fn decode_syntax_context(&mut self) -> SyntaxContext {
        let hygiene: &HygieneDecodeContext = self.hygiene;
        rustc_span::hygiene::decode_syntax_context(self, hygiene, |decoder, index| {
            decoder.with_position(decoder.footer.syntax_contexts[&index], SyntaxContextKey::decode)
        })
    }
    fn decode_crate_num(&mut self) -> CrateNum {
        let stable: StableCrateId = StableCrateId::decode(self);
        self.tcx.stable_crate_id_to_crate_num(stable)
    }
    fn decode_def_id(&mut self) -> DefId {
        let hash: DefPathHash = DefPathHash::decode(self);
        self.tcx
            .def_path_hash_to_def_id(hash)
            .expect("a definition in the recorded MIR is absent from the metadata")
    }
    fn decode_attr_id(&mut self) -> AttrId {
        panic!("recorded MIR contains a compiler-local AttrId");
    }
}

impl<'tcx> TyDecoder<'tcx> for MirDecoder<'_, 'tcx> {
    const CLEAR_CROSS_CRATE: bool = false;
    fn interner(&self) -> TyCtxt<'tcx> {
        self.tcx
    }
    fn cached_ty_for_shorthand<F>(&mut self, shorthand: usize, make: F) -> Ty<'tcx>
    where
        F: FnOnce(&mut Self) -> Ty<'tcx>,
    {
        if let Some(ty) = self.types.get(&shorthand) {
            return *ty;
        }
        let ty: Ty<'tcx> = make(self);
        self.types.insert(shorthand, ty);
        ty
    }
    fn with_position<F, R>(&mut self, position: usize, f: F) -> R
    where
        F: FnOnce(&mut Self) -> R,
    {
        let next: MemDecoder<'_> = self.opaque.split_at(position);
        let original: MemDecoder<'_> = std::mem::replace(&mut self.opaque, next);
        let value: R = f(self);
        self.opaque = original;
        value
    }
    fn decode_alloc_id(&mut self) -> AllocId {
        let session: AllocDecodingSession<'_> = self.allocations;
        session.decode_alloc_id(self)
    }
}
