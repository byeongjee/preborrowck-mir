// What a driver calls: install the hooks that record the MIR, then handle the MIR files.
use std::cell::Cell;
use std::path::PathBuf;

use rustc_hir::def_id::LocalDefId;
use rustc_interface::DEFAULT_QUERY_PROVIDERS;
use rustc_middle::queries::mir_borrowck::ProvidedValue;
use rustc_middle::ty::TyCtxt;
use rustc_middle::util::Providers;

use crate::{Error, candidates, facts, record, track_file};

#[derive(Clone, Copy, Default)]
struct Record {
    mir: bool,
    borrowck_facts: bool,
}

thread_local! {
    // rustc installs the providers and runs the queries on one compiler thread per session.
    static RECORD: Cell<Record> = Cell::default();
}

// Records the MIR of every body of this crate as it is before rustc borrow checks it.
pub fn record_mir(providers: &mut Providers) {
    RECORD.with(|record| record.set(Record { mir: true, ..record.get() }));
    providers.queries.mir_borrowck = record_then_borrowck;
}

// Records the facts the borrow checker of rustc computes for every body of this crate.
pub fn record_borrowck_facts(providers: &mut Providers) {
    RECORD.with(|record| record.set(Record { borrowck_facts: true, ..record.get() }));
    providers.queries.mir_borrowck = record_then_borrowck;
}

// `mir_drops_elaborated_and_const_checked` steals the MIR right after borrow checking it,
// so the MIR is recorded inside the `mir_borrowck` override.
fn record_then_borrowck(tcx: TyCtxt<'_>, root: LocalDefId) -> ProvidedValue<'_> {
    let record: Record = RECORD.with(Cell::get);
    if record.mir {
        record::record(tcx, root);
    }
    if record.borrowck_facts {
        facts::record(tcx, root);
    }
    (DEFAULT_QUERY_PROVIDERS.queries.mir_borrowck)(tcx, root)
}

// Registers the MIR files of the dependencies as inputs of this compilation, so Cargo
// rebuilds this crate when one changes. Call after expansion: rustc writes the dep-info
// before analysis. The MIR file of this crate itself is an output, never an input.
pub fn register_dependency_mir_files(tcx: TyCtxt<'_>) {
    for &krate in tcx.crates(()) {
        for path in candidates(tcx, krate).into_iter().filter(|path: &PathBuf| path.is_file()) {
            track_file(tcx, &path);
        }
    }
}

// Writes the MIR file of this crate next to its metadata. Call after analysis.
pub fn write_mir_file(tcx: TyCtxt<'_>) -> Result<(), Error> {
    record::write_mir_file(tcx)
}
