use std::mem::transmute;
use std::path::{Path, PathBuf};

use rustc_data_structures::fx::FxHashMap;
use rustc_hir::def::DefKind;
use rustc_hir::def_id::LocalDefId;
use rustc_hir::intravisit::{self, Visitor};
use rustc_hir::{Block, BlockCheckMode};
use rustc_middle::mir::Body;
use rustc_middle::ty::{BoundVariableKind, CanonicalPolyFnSig, Ty, TyCtxt};
use rustc_session::config::{OutFileName, OutputType};
use rustc_span::Span;

use crate::dead_drops::remove_dead_drops;
use crate::{CrateBodies, Error, RECORDED, RecordedMir, TypeckData, codec};

pub(crate) fn record<'tcx>(tcx: TyCtxt<'tcx>, root: LocalDefId) {
    if RECORDED.with(|sets| sets.borrow().contains_key(&root.to_def_id())) {
        return;
    }
    let order: Vec<LocalDefId> =
        tcx.nested_bodies_within(root).iter().chain(std::iter::once(root)).collect();
    let mut bodies = FxHashMap::default();
    let mut typeck = FxHashMap::default();
    for &def in &order {
        let kind: DefKind = tcx.def_kind(def);
        let (body, promoted) = tcx.mir_promoted(def);
        let mut body: Body<'tcx> = body.borrow().clone();
        remove_dead_drops(tcx, &mut body);
        bodies.insert(def.to_def_id(), (body, promoted.borrow().clone()));
        let bound_vars: Vec<BoundVariableKind> = match kind {
            DefKind::Fn | DefKind::AssocFn => {
                tcx.late_bound_vars(tcx.local_def_id_to_hir_id(def)).to_vec()
            }
            _ => Vec::new(),
        };
        let closure_sig: Option<CanonicalPolyFnSig<'tcx>> =
            (kind == DefKind::Closure).then(|| tcx.closure_user_provided_sig(def));
        let assumed_wf_types: Vec<(Ty<'tcx>, Span)> =
            if matches!(kind, DefKind::AssocFn | DefKind::AssocConst { .. }) {
                tcx.assumed_wf_types(tcx.local_parent(def)).to_vec()
            } else {
                Vec::new()
            };
        let inline_const_ty: Option<Ty<'tcx>> = if kind == DefKind::InlineConst {
            Some(tcx.typeck(def).node_type(tcx.local_def_id_to_hir_id(def)))
        } else {
            None
        };
        typeck.insert(
            def.to_def_id(),
            TypeckData { bound_vars, closure_sig, assumed_wf_types, inline_const_ty },
        );
    }
    let set: RecordedMir<'tcx> = RecordedMir {
        root: root.to_def_id(),
        uses_unsafe: uses_unsafe(tcx, root, &order),
        bodies,
        typeck,
        order: order.into_iter().map(LocalDefId::to_def_id).collect(),
    };
    // SAFETY: rustc creates fresh compiler threads for each session. The erased
    // arena lifetime is restored only on that session's compiler thread.
    let set: RecordedMir<'static> =
        unsafe { transmute::<RecordedMir<'tcx>, RecordedMir<'static>>(set) };
    RECORDED.with(|sets| {
        sets.borrow_mut().insert(root.to_def_id(), Box::new(set));
    });
}

fn uses_unsafe(tcx: TyCtxt<'_>, root: LocalDefId, bodies: &[LocalDefId]) -> bool {
    let is_unsafe_fn: bool = matches!(tcx.def_kind(root), DefKind::Fn | DefKind::AssocFn)
        && tcx.fn_sig(root).skip_binder().safety().is_unsafe();
    is_unsafe_fn
        || bodies.iter().any(|&def| {
            let mut finder: UnsafeBlockFinder = UnsafeBlockFinder { found: false };
            finder.visit_body(tcx.hir_body_owned_by(def));
            finder.found
        })
}

struct UnsafeBlockFinder {
    found: bool,
}

impl<'v> Visitor<'v> for UnsafeBlockFinder {
    fn visit_block(&mut self, block: &'v Block<'v>) {
        if matches!(block.rules, BlockCheckMode::UnsafeBlock(_)) {
            self.found = true;
        }
        intravisit::walk_block(self, block);
    }
}

// The MIR file next to a crate artifact (rmeta, rlib, or dylib).
pub fn mir_file_path(artifact: &Path) -> PathBuf {
    artifact.with_extension("preborrowck-mir")
}

pub(crate) fn write_mir_file<'tcx>(tcx: TyCtxt<'tcx>) -> Result<(), Error> {
    // Only Rust-linkable library artifacts can be dependencies. Nonincremental
    // executables deliberately have no HIR/crate hash to put in this header.
    if !tcx.needs_metadata() {
        return Ok(());
    }
    let OutFileName::Real(output) = tcx.output_filenames(()).path(OutputType::Metadata) else {
        return Ok(());
    };
    let path: PathBuf = mir_file_path(&output);
    let parent: &Path = path.parent().unwrap_or_else(|| Path::new("."));
    std::fs::create_dir_all(parent)
        .map_err(|e| Error::new(format!("cannot create the directory of the MIR file: {e}")))?;
    let temporary: PathBuf =
        path.with_extension(format!("preborrowck-mir.{}.tmp", std::process::id()));
    let inputs: CrateBodies<'tcx> = RECORDED.with(|sets| {
        let sets = sets.borrow();
        let inputs: CrateBodies<'static> = CrateBodies {
            sets: sets
                .iter()
                .map(|(&def, set)| {
                    let mut set: RecordedMir<'static> = (**set).clone();
                    for (body, promoted) in set.bodies.values_mut() {
                        codec::prepare_body(body);
                        for body in promoted.iter_mut() {
                            codec::prepare_body(body);
                        }
                    }
                    (def, set)
                })
                .collect(),
        };
        // SAFETY: RECORDED belongs to this compiler thread's current session.
        unsafe { transmute::<CrateBodies<'static>, CrateBodies<'tcx>>(inputs) }
    });
    // Encoding can trigger compiler queries. Do not retain a RECORDED borrow
    // while those queries may record another body.
    if let Err(error) = codec::write(tcx, &temporary, &inputs) {
        let _ = std::fs::remove_file(&temporary);
        return Err(error);
    }
    std::fs::rename(&temporary, &path).map_err(|e| {
        let _ = std::fs::remove_file(&temporary);
        Error::new(format!("cannot write the MIR file `{}`: {e}", path.display()))
    })?;
    Ok(())
}
