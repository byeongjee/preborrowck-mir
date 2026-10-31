use std::io::Write;
use std::path::Path;
use std::sync::Arc;

use rustc_data_structures::fx::{FxHashMap, FxIndexSet};
use rustc_hir::def_id::{CrateNum, DefId, DefIndex, DefPathHash, LOCAL_CRATE};
use rustc_middle::mir::interpret::{self, AllocId};
use rustc_middle::ty::codec::TyEncoder;
use rustc_middle::ty::{self, Ty, TyCtxt};
use rustc_serialize::opaque::FileEncoder;
use rustc_serialize::{Encodable as _, Encoder};
use rustc_span::hygiene::HygieneEncodeContext;
use rustc_span::{
    ByteSymbol, ExpnHash, ExpnId, SourceFile, Span, SpanData, SpanEncoder, StableSourceFileId,
    Symbol, SyntaxContext,
};

use super::{Error, Footer, Header, MAGIC, VERSION, checksum, io_error};
use crate::CrateBodies;

pub(crate) fn write<'tcx>(
    tcx: TyCtxt<'tcx>,
    path: &Path,
    inputs: &CrateBodies<'tcx>,
) -> Result<(), Error> {
    let hygiene: HygieneEncodeContext = HygieneEncodeContext::default();
    let mut encoder = MirEncoder {
        tcx,
        out: FileEncoder::new(path).map_err(|e| io_error(path, e))?,
        types: FxHashMap::default(),
        predicates: FxHashMap::default(),
        allocations: FxIndexSet::default(),
        hygiene: &hygiene,
        files: Vec::new(),
        file_indices: FxHashMap::default(),
    };
    encoder.emit_raw_bytes(MAGIC);
    encoder.emit_raw_bytes(&VERSION.to_le_bytes());
    Header::new(tcx, LOCAL_CRATE).encode(&mut encoder);
    let mut roots: FxHashMap<DefPathHash, usize> = FxHashMap::default();
    for (&def, input) in &inputs.sets {
        roots.insert(tcx.def_path_hash(def), encoder.position());
        input.encode(&mut encoder);
    }

    // Serializing an allocation can discover more allocations. Continue until
    // every pointer in the transitive allocation graph has a table entry.
    let mut allocations: Vec<u64> = Vec::new();
    while allocations.len() != encoder.allocations.len() {
        let index: usize = allocations.len();
        let alloc: AllocId = encoder.allocations[index];
        allocations.push(encoder.position() as u64);
        interpret::specialized_encode_alloc_id(&mut encoder, tcx, alloc);
    }

    let mut syntax_contexts: FxHashMap<u32, usize> = FxHashMap::default();
    let mut expansions: FxHashMap<ExpnHash, (u32, usize)> = FxHashMap::default();
    hygiene.encode(
        &mut encoder,
        |encoder, index, data| {
            syntax_contexts.insert(index, encoder.position());
            data.encode(encoder);
        },
        |encoder, expansion, data, hash| {
            expansions.insert(hash, (expansion.local_id.as_u32(), encoder.position()));
            data.encode(encoder);
        },
    );

    // Hygiene data can add spans, so source files must follow hygiene encoding.
    let mut source_files: Vec<usize> = Vec::with_capacity(encoder.files.len());
    for file in encoder.files.clone() {
        source_files.push(encoder.position());
        let mut exported: SourceFile = (*file).clone();
        let _ = exported.lines();
        if exported.cnum == LOCAL_CRATE {
            exported.stable_id = StableSourceFileId::from_filename_for_export(
                &exported.name,
                tcx.stable_crate_id(LOCAL_CRATE),
            );
        }
        exported.encode(&mut encoder);
    }
    let footer_pos: u64 = encoder.position() as u64;
    Footer { roots, allocations, syntax_contexts, expansions, source_files }.encode(&mut encoder);
    encoder.out.write_array(footer_pos.to_le_bytes());
    encoder.out.finish().map_err(|(_, e)| io_error(path, e))?;
    drop(encoder);

    // rustc's decoder is infallible; reject damaged streams before invoking it.
    let bytes: Vec<u8> = std::fs::read(path).map_err(|e| io_error(path, e))?;
    let mut file =
        std::fs::OpenOptions::new().append(true).open(path).map_err(|e| io_error(path, e))?;
    file.write_all(&(bytes.len() as u64).to_le_bytes()).map_err(|e| io_error(path, e))?;
    file.write_all(&checksum(&bytes).to_le_bytes()).map_err(|e| io_error(path, e))?;
    file.sync_all().map_err(|e| io_error(path, e))
}

struct MirEncoder<'a, 'tcx> {
    tcx: TyCtxt<'tcx>,
    out: FileEncoder,
    types: FxHashMap<Ty<'tcx>, usize>,
    predicates: FxHashMap<ty::PredicateKind<'tcx>, usize>,
    allocations: FxIndexSet<AllocId>,
    hygiene: &'a HygieneEncodeContext,
    files: Vec<Arc<SourceFile>>,
    file_indices: FxHashMap<*const SourceFile, usize>,
}

macro_rules! emit {
    ($($method:ident:$ty:ty),* $(,)?) => { $(fn $method(&mut self, value:$ty) { self.out.$method(value); })* };
}
impl Encoder for MirEncoder<'_, '_> {
    emit!(emit_usize:usize, emit_u128:u128, emit_u64:u64, emit_u32:u32, emit_u16:u16, emit_u8:u8,
        emit_isize:isize, emit_i128:i128, emit_i64:i64, emit_i32:i32, emit_i16:i16, emit_raw_bytes:&[u8]);
}

impl SpanEncoder for MirEncoder<'_, '_> {
    fn encode_span(&mut self, span: Span) {
        let span: SpanData = span.data_untracked();
        span.ctxt.encode(self);
        if span.is_dummy() {
            self.emit_u8(0);
            return;
        }
        self.emit_u8(1);
        let file: Arc<SourceFile> = self.tcx.sess.source_map().lookup_source_file(span.lo);
        let pointer: *const SourceFile = Arc::as_ptr(&file);
        let index: usize = *self.file_indices.entry(pointer).or_insert_with(|| {
            let index: usize = self.files.len();
            self.files.push(Arc::clone(&file));
            index
        });
        index.encode(self);
        (span.lo - file.start_pos).encode(self);
        (span.hi - span.lo).encode(self);
        // Span.parent is a local incremental-dependency hint, not source or
        // hygiene information; an external span cannot carry a LocalDefId.
    }
    fn encode_symbol(&mut self, symbol: Symbol) {
        self.emit_str(symbol.as_str());
    }
    fn encode_byte_symbol(&mut self, symbol: ByteSymbol) {
        self.emit_byte_str(symbol.as_byte_str());
    }
    fn encode_expn_id(&mut self, expansion: ExpnId) {
        self.hygiene.schedule_expn_data_for_encoding(expansion);
        expansion.expn_hash().encode(self);
    }
    fn encode_syntax_context(&mut self, context: SyntaxContext) {
        rustc_span::hygiene::raw_encode_syntax_context(context, self.hygiene, self);
    }
    fn encode_crate_num(&mut self, krate: CrateNum) {
        self.tcx.stable_crate_id(krate).encode(self);
    }
    fn encode_def_index(&mut self, _: DefIndex) {
        panic!("recorded MIR contains a DefIndex without a definition");
    }
    fn encode_def_id(&mut self, def: DefId) {
        self.tcx.def_path_hash(def).encode(self);
    }
}

impl<'tcx> TyEncoder<'tcx> for MirEncoder<'_, 'tcx> {
    // DerefTemp and guard references affect borrow checking; clearing all local
    // information would discard them along with diagnostic-only HIR IDs.
    const CLEAR_CROSS_CRATE: bool = false;
    fn position(&self) -> usize {
        self.out.position()
    }
    fn type_shorthands(&mut self) -> &mut FxHashMap<Ty<'tcx>, usize> {
        &mut self.types
    }
    fn predicate_shorthands(&mut self) -> &mut FxHashMap<ty::PredicateKind<'tcx>, usize> {
        &mut self.predicates
    }
    fn encode_alloc_id(&mut self, allocation: &AllocId) {
        let (index, _) = self.allocations.insert_full(*allocation);
        u32::try_from(index).expect("too many MIR constant allocations").encode(self);
    }
}
