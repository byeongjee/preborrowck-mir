mod decode;
mod encode;

use std::collections::hash_map::DefaultHasher;
use std::hash::Hasher;
use std::path::Path;

pub(crate) use decode::{RecordedCrate, read};
pub(crate) use encode::write;
use rustc_data_structures::fx::FxHashMap;
use rustc_hir::def_id::{CrateNum, DefPathHash};
use rustc_macros::{Decodable, Encodable};
use rustc_middle::ty::TyCtxt;
use rustc_span::ExpnHash;

use crate::Error;

const MAGIC: &[u8] = b"PREBORROWCK-MIR\0";
const VERSION: u32 = 5;

#[derive(Encodable, Decodable)]
struct Header {
    compiler: String,
    target: String,
    stable_crate: String,
    crate_hash: String,
}

impl Header {
    fn new(tcx: TyCtxt<'_>, krate: CrateNum) -> Self {
        Self {
            compiler: rustc_interface::util::rustc_version_str().unwrap_or("unknown").to_owned(),
            target: tcx.sess.opts.target_triple.to_string(),
            stable_crate: format!("{:?}", tcx.stable_crate_id(krate)),
            crate_hash: tcx.crate_hash(krate).to_hex(),
        }
    }

    fn validate(&self, expected: &Self) -> Result<(), Error> {
        for (name, actual, expected) in [
            ("compiler", &self.compiler, &expected.compiler),
            ("target", &self.target, &expected.target),
            ("crate identity", &self.stable_crate, &expected.stable_crate),
            ("crate hash", &self.crate_hash, &expected.crate_hash),
        ] {
            if actual != expected {
                return Err(Error::new(format!(
                    "recorded MIR {name} mismatch: found `{actual}`, expected `{expected}`"
                )));
            }
        }
        Ok(())
    }
}

#[derive(Encodable, Decodable)]
struct Footer {
    roots: FxHashMap<DefPathHash, usize>,
    allocations: Vec<u64>,
    syntax_contexts: FxHashMap<u32, usize>,
    expansions: FxHashMap<ExpnHash, (u32, usize)>,
    source_files: Vec<usize>,
}

fn io_error(path: &Path, error: impl std::fmt::Display) -> Error {
    Error::new(format!("cannot access the MIR file `{}`: {error}", path.display()))
}

fn checksum(bytes: &[u8]) -> u64 {
    let mut hasher: DefaultHasher = DefaultHasher::new();
    hasher.write(bytes);
    hasher.finish()
}

pub(crate) fn prepare_body(body: &mut rustc_middle::mir::Body<'_>) {
    use rustc_middle::mir::{ClearCrossCrate, FakeReadCause, LocalInfo, StatementKind};
    for scope in &mut body.source_scopes {
        scope.local_data = ClearCrossCrate::Clear;
    }
    for block in body.basic_blocks.as_mut_preserves_cfg() {
        for statement in &mut block.statements {
            if let StatementKind::FakeRead(read) = &mut statement.kind {
                match &mut read.0 {
                    FakeReadCause::ForMatchedPlace(owner) | FakeReadCause::ForLet(owner) => {
                        *owner = None;
                    }
                    _ => {}
                }
            }
        }
    }
    if let Some(coroutine) = body.coroutine.as_mut() {
        for nested in [
            &mut coroutine.coroutine_drop,
            &mut coroutine.coroutine_drop_async,
            &mut coroutine.coroutine_drop_proxy_async,
        ]
        .into_iter()
        .flatten()
        {
            prepare_body(nested);
        }
    }
    for local in &mut body.local_decls {
        if matches!(&local.local_info, ClearCrossCrate::Set(info) if matches!(info.as_ref(), LocalInfo::IfThenRescopeTemp { .. }))
        {
            local.local_info = ClearCrossCrate::Set(Box::new(LocalInfo::Boring));
        }
    }
}

#[cfg(test)]
mod tests {
    use std::path::PathBuf;

    use rustc_hir::def_id::LOCAL_CRATE;
    use rustc_serialize::opaque::MAGIC_END_BYTES;

    use super::*;

    #[test]
    fn unsupported_version_is_rejected_before_decoding_the_header() {
        let mut bytes: Vec<u8> = MAGIC.to_vec();
        bytes.extend_from_slice(&(VERSION + 1).to_le_bytes());
        bytes.extend_from_slice(&[0xff; 32]);
        bytes.extend_from_slice(MAGIC_END_BYTES);
        let length: u64 = bytes.len() as u64;
        let digest: u64 = checksum(&bytes);
        bytes.extend_from_slice(&length.to_le_bytes());
        bytes.extend_from_slice(&digest.to_le_bytes());
        let path: PathBuf = std::env::temp_dir().join(format!(
            "preborrowck-mir-unsupported-version-{}-{}.preborrowck-mir",
            std::process::id(),
            std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .expect("the clock is after the epoch")
                .as_nanos()
        ));
        std::fs::write(&path, bytes).expect("the temporary directory is writable");
        crate::test_utils::Compile::source("pub fn fixture() {}").run(move |tcx| {
            let result: Result<RecordedCrate, Error> = read(tcx, &path, LOCAL_CRATE);
            std::fs::remove_file(&path).expect("the temporary file is removable");
            let error: Error = result.err().expect("an incompatible version must be rejected");
            assert!(!error.is_unavailable());
            assert!(error.reason.contains("format version"), "{error}");
            assert!(error.reason.contains("unsupported"), "{error}");
        });
    }
}
