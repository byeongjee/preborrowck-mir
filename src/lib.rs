#![feature(rustc_private)]

extern crate rustc_borrowck;
extern crate rustc_data_structures;
#[cfg(feature = "test")]
extern crate rustc_driver;
extern crate rustc_hir;
extern crate rustc_index;
extern crate rustc_interface;
extern crate rustc_macros;
extern crate rustc_middle;
extern crate rustc_serialize;
extern crate rustc_session;
extern crate rustc_span;

mod codec;
pub mod driver;
mod error;
mod facts;
mod record;
#[cfg(feature = "test")]
pub mod test_utils;

use std::cell::RefCell;
use std::mem::transmute;
use std::path::{Path, PathBuf};
use std::sync::Arc;

pub use error::{Error, ErrorKind};
pub use facts::borrowck_facts;
use record::mir_file_path;
use rustc_data_structures::fx::FxHashMap;
use rustc_hir::def::DefKind;
use rustc_hir::def_id::{CrateNum, DefId};
use rustc_index::IndexVec;
use rustc_macros::{TyDecodable, TyEncodable};
use rustc_middle::mir::{Body, Promoted};
use rustc_middle::ty::{
    self, EarlyBinder, GenericArgsRef, Instance, ParamEnv, Ty, TyCtxt, TypingEnv, TypingMode,
};
use rustc_session::cstore::CrateSource;
use rustc_span::{Span, Symbol};
use rustc_utils::cache::Cache;

// What rustc knows about a body besides its MIR and needs to type check it again.
#[derive(Clone, TyEncodable, TyDecodable)]
pub struct TypeckData<'tcx> {
    // The late-bound vars of a function.
    pub bound_vars: Vec<ty::BoundVariableKind<'tcx>>,
    // The signature the user wrote for a closure.
    pub closure_sig: Option<ty::CanonicalPolyFnSig<'tcx>>,
    // The types an associated item assumes well-formed.
    pub assumed_wf_types: Vec<(Ty<'tcx>, Span)>,
    // The type of an inline const.
    pub inline_const_ty: Option<Ty<'tcx>>,
}

// The MIR of a function and of every closure, coroutine, and inline const within it,
// recorded as rustc borrow checks it: generic, with its regions in place. rustc borrow
// checks that whole group at once, so it is recorded and read as one.
#[derive(Clone, TyEncodable, TyDecodable)]
pub struct RecordedMir<'tcx> {
    // The function: the typeck root of every body in the group.
    pub root: DefId,
    // rustc rejects an operation that needs `unsafe` outside an `unsafe fn` or an `unsafe` block.
    pub uses_unsafe: bool,
    pub bodies: FxHashMap<DefId, (Body<'tcx>, IndexVec<Promoted, Body<'tcx>>)>,
    pub typeck: FxHashMap<DefId, TypeckData<'tcx>>,
    // The bodies in the order rustc borrow checks them: a nested body before its parent.
    pub order: Vec<DefId>,
}

impl<'tcx> RecordedMir<'tcx> {
    // The args of a body of this set given the args of the root: a closure and an inline
    // const add the values of the params that rustc gives them after the root's params.
    pub fn args_of_body(
        &self,
        tcx: TyCtxt<'tcx>,
        def: DefId,
        args: GenericArgsRef<'tcx>,
    ) -> Result<GenericArgsRef<'tcx>, Error> {
        if def == self.root {
            return Ok(args);
        }
        if tcx.def_kind(def) == DefKind::InlineConst {
            let ty: Ty<'tcx> = self.typeck[&def]
                .inline_const_ty
                .ok_or_else(|| Error::new("inline const defining type is unavailable"))?;
            let ty: Ty<'tcx> = tcx.instantiate_and_normalize_erasing_regions(
                args,
                typing_env(def),
                EarlyBinder::bind(ty),
            );
            return Ok(ty::InlineConstArgs::new(
                tcx,
                ty::InlineConstArgsParts { parent_args: args, ty },
            )
            .args);
        }
        let ty: Ty<'tcx> =
            tcx.normalize_erasing_regions(typing_env(def), tcx.type_of(def).instantiate(tcx, args));
        match *ty.kind() {
            ty::Closure(_, args) | ty::Coroutine(_, args) | ty::CoroutineClosure(_, args) => {
                Ok(args)
            }
            _ => Err(Error::new("a recorded nested body has an unsupported defining type")),
        }
    }
}

// The typing env in which a body of `def` and its types are normalized: the opaque types
// of other bodies stay opaque in a local body, as rustc analyzes it, while an external
// body is analyzed with everything revealed.
pub fn typing_env<'tcx>(def: DefId) -> TypingEnv<'tcx> {
    if def.is_local() {
        TypingEnv::new(ParamEnv::empty(), TypingMode::non_body_analysis())
    } else {
        TypingEnv::fully_monomorphized()
    }
}

#[derive(TyEncodable, TyDecodable)]
pub(crate) struct CrateBodies<'tcx> {
    pub sets: FxHashMap<DefId, RecordedMir<'tcx>>,
}

thread_local! {
    static RECORDED: RefCell<FxHashMap<DefId, Box<RecordedMir<'static>>>> = RefCell::default();
    static LOADED: Cache<CrateNum, Result<codec::RecordedCrate, Error>> = Cache::default();
    static DECODED: Cache<DefId, Result<RecordedMir<'static>, Error>> = Cache::default();
}

fn require_rust_body(tcx: TyCtxt<'_>, def: DefId) -> Result<(), Error> {
    if tcx.is_foreign_item(def) {
        return Err(Error::unavailable(format!(
            "no body for `{}`: extern declaration has no Rust function body",
            tcx.def_path_str(def)
        )));
    }
    if tcx.is_constructor(def) || tcx.is_synthetic_mir(def) {
        return Err(Error::unavailable(format!(
            "no region constraints for `{}`: rustc builds its MIR without a borrow check",
            tcx.def_path_str(def)
        )));
    }
    Ok(())
}

pub(crate) fn track_file(tcx: TyCtxt<'_>, path: &Path) {
    let path: PathBuf = std::fs::canonicalize(path).unwrap_or_else(|_| path.to_owned());
    if let Some(path) = path.to_str() {
        tcx.sess.file_depinfo.lock().insert(Symbol::intern(path));
    }
}

// The instances of the function-like bodies recorded with the function of `instance`:
// the function and its closures with the args of `instance`, not its inline consts.
pub fn instances_within<'tcx>(
    tcx: TyCtxt<'tcx>,
    instance: Instance<'tcx>,
) -> Result<Vec<Instance<'tcx>>, Error> {
    let set: &RecordedMir<'tcx> = recorded_mir(tcx, instance.def_id())?;
    let args: GenericArgsRef<'tcx> = instance.args.truncate_to(tcx, tcx.generics_of(set.root));
    set.order
        .iter()
        .copied()
        .filter(|&def| tcx.def_kind(def).is_fn_like())
        .map(|def| Ok(Instance::new_raw(def, set.args_of_body(tcx, def, args)?)))
        .collect()
}

// The recorded MIR of the function that contains `def`.
pub fn recorded_mir<'tcx>(tcx: TyCtxt<'tcx>, def: DefId) -> Result<&'tcx RecordedMir<'tcx>, Error> {
    require_rust_body(tcx, def)?;
    let root: DefId = tcx.typeck_root_def_id(def);
    if let Some(local) = root.as_local() {
        let _ = tcx.mir_borrowck(local);
        return RECORDED.with(|sets| {
            let sets = sets.borrow();
            let set: &RecordedMir<'static> = sets.get(&root).ok_or_else(|| {
                Error::new(format!("the MIR of `{}` was not recorded", tcx.def_path_str(root)))
            })?;
            // SAFETY: the box is never replaced once recorded, and HashMap growth
            // cannot move it. Its arena references belong to this session.
            Ok(unsafe { transmute::<&RecordedMir<'static>, &'tcx RecordedMir<'tcx>>(set) })
        });
    }
    DECODED.with(|cache| {
        let set: &Result<RecordedMir<'static>, Error> = cache.get(&root, |_| {
            let input: RecordedMir<'tcx> = crate_inputs(tcx, root.krate)?.body_set(tcx, root)?;
            // SAFETY: the thread-local cache cannot be reused by another session.
            Ok(unsafe { transmute::<RecordedMir<'tcx>, RecordedMir<'static>>(input) })
        });
        match set {
            Ok(set) => {
                // SAFETY: Cache pins its entries; both the cache and its arena
                // references remain valid throughout this compiler session.
                Ok(unsafe { transmute::<&RecordedMir<'static>, &'tcx RecordedMir<'tcx>>(set) })
            }
            Err(error) => Err(error.clone()),
        }
    })
}

pub(crate) fn candidates(tcx: TyCtxt<'_>, krate: CrateNum) -> Vec<PathBuf> {
    let source: &Arc<CrateSource> = tcx.used_crate_source(krate);
    let mut paths: Vec<PathBuf> = Vec::new();
    for artifact in [&source.rmeta, &source.rlib, &source.dylib].into_iter().flatten() {
        let path: PathBuf = mir_file_path(artifact);
        if !paths.contains(&path) {
            paths.push(path);
        }
    }
    paths
}

fn prebuilt_sysroot_artifact(tcx: TyCtxt<'_>, krate: CrateNum) -> Option<PathBuf> {
    let sysroot: PathBuf = tcx.sess.opts.sysroot.path().canonicalize().ok()?;
    let source: &Arc<CrateSource> = tcx.used_crate_source(krate);
    [&source.rmeta, &source.rlib, &source.dylib]
        .into_iter()
        .flatten()
        .filter_map(|artifact| artifact.canonicalize().ok())
        .find(|artifact| artifact.starts_with(&sysroot))
}

fn crate_inputs<'tcx>(
    tcx: TyCtxt<'tcx>,
    krate: CrateNum,
) -> Result<&'tcx codec::RecordedCrate, Error> {
    let loaded: &'tcx Result<codec::RecordedCrate, Error> = LOADED.with(|cache| {
        let result: &Result<codec::RecordedCrate, Error> = cache.get(&krate, |_| {
            let candidates: Vec<PathBuf> = candidates(tcx, krate);
            let path: &PathBuf =
                candidates.iter().find(|path| path.is_file()).ok_or_else(|| {
                    if let Some(artifact) = prebuilt_sysroot_artifact(tcx, krate) {
                        return Error::unavailable(format!(
                            "the MIR of prebuilt sysroot library `{}` is not recorded ({})",
                            tcx.crate_name(krate),
                            artifact.display()
                        ));
                    }
                    Error::new(format!(
                        "the MIR of crate `{}` was not recorded (expected {})",
                        tcx.crate_name(krate),
                        candidates
                            .iter()
                            .map(|p| p.display().to_string())
                            .collect::<Vec<_>>()
                            .join(" or ")
                    ))
                })?;
            track_file(tcx, path);
            codec::read(tcx, path, krate)
        });
        // SAFETY: Cache pins its entries, and rustc's fresh compiler threads
        // prevent this reference from escaping into a later session.
        unsafe {
            transmute::<
                &Result<codec::RecordedCrate, Error>,
                &'tcx Result<codec::RecordedCrate, Error>,
            >(result)
        }
    });
    loaded.as_ref().map_err(Clone::clone)
}
