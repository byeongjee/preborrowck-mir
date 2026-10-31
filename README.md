# preborrowck-mir

This crate makes the MIR of a function available to other crates with its regions intact.

## Motivation

rustc erases the regions of a function's MIR right after it borrow checks the function, and the
MIR it ships in crate metadata has no regions left, so an analysis that needs the regions of a
function defined in another crate has no input. This crate records the MIR of every function at
the moment rustc borrow checks it, so that a dependent crate can read it with its regions intact.

## Usage

Compile every dependency with a driver that installs these hooks:

```rust
// Config::override_queries: record the MIR as rustc borrow checks it
preborrowck_mir::driver::record_mir(providers);
// after expansion: let Cargo rebuild when a dependency's MIR changes
preborrowck_mir::driver::register_dependency_mir_files(tcx);
// after analysis: write the records next to the crate's metadata
preborrowck_mir::driver::write_mir_file(tcx)?;
```

Then `recorded_mir` reads the MIR of a function of this crate or of a dependency:

```rust
let mir = preborrowck_mir::recorded_mir(tcx, def)?;
let (body, promoted) = &mir.bodies[&def];
```
