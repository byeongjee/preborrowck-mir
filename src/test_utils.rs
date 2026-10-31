use std::path::PathBuf;
use std::process::Command;
use std::sync::LazyLock;

use rustc_driver::{Callbacks, Compilation, catch_fatal_errors, run_compiler};
use rustc_interface::interface::{Compiler, Config};
use rustc_middle::ty::TyCtxt;
use rustc_middle::util::Providers;
use rustc_session::Session;
use rustc_utils::test_utils::{DUMMY_FILE_NAME, StringLoader};

use crate::driver;
pub use crate::record::mir_file_path;

static SYSROOT: LazyLock<String> = LazyLock::new(|| {
    let output: Vec<u8> = Command::new("rustc")
        .args(["--print", "sysroot"])
        .output()
        .expect("rustc prints its sysroot")
        .stdout;
    String::from_utf8(output).expect("the sysroot is UTF-8").trim().to_owned()
});

// The crate root a compilation reads.
pub enum Input {
    // A source text compiled in place of a file.
    Source(String),
    // The path of the root file.
    File(PathBuf),
}

// A compilation of one crate.
pub struct Compile {
    // The crate root.
    pub input: Input,
    // The rustc arguments added to the default ones.
    pub args: Vec<String>,
    // The query overrides installed in the session.
    pub overrides: fn(&Session, &mut Providers),
}

impl Compile {
    // Compiles `source` as the whole crate.
    pub fn source(source: impl Into<String>) -> Self {
        Self { input: Input::Source(source.into()), args: Vec::new(), overrides: record_all }
    }

    // Compiles the crate whose root file is at `path`.
    pub fn file(path: impl Into<PathBuf>) -> Self {
        Self { input: Input::File(path.into()), args: Vec::new(), overrides: record_all }
    }

    // Compiles as a lib crate with the sysroot of `rustc` and calls back with the `TyCtxt`
    // after the analysis.
    pub fn run(self, callback: impl for<'tcx> FnOnce(TyCtxt<'tcx>) + Send) {
        let Compile { input, args: extra_args, overrides } = self;
        let (root, source): (String, Option<String>) = match input {
            Input::Source(source) => (DUMMY_FILE_NAME.to_owned(), Some(source)),
            Input::File(path) => {
                (path.into_os_string().into_string().expect("the crate root path is UTF-8"), None)
            }
        };
        let mut args: Vec<String> = [
            "rustc",
            &root,
            "--crate-type",
            "lib",
            "-Clink-dead-code",
            "-Zidentify-regions",
            "-Zmir-opt-level=0",
            "-Zmaximal-hir-to-mir-coverage",
            // The registry crates deny lints of their own, which `--allow` does not override.
            "--cap-lints",
            "allow",
            "--sysroot",
            &SYSROOT,
        ]
        .into_iter()
        .map(str::to_owned)
        .collect();
        if !extra_args.iter().any(|arg| arg == "--edition" || arg.starts_with("--edition=")) {
            args.push("--edition=2024".to_owned());
        }
        args.extend(extra_args);
        let mut callbacks: CompileCallbacks<_> =
            CompileCallbacks { source, overrides, callback: Some(callback) };
        catch_fatal_errors(|| run_compiler(&args, &mut callbacks))
            .expect("the compilation succeeds");
    }
}

fn record_all(_: &Session, providers: &mut Providers) {
    driver::record_mir(providers);
    driver::record_borrowck_facts(providers);
}

struct CompileCallbacks<Callback> {
    source: Option<String>,
    overrides: fn(&Session, &mut Providers),
    callback: Option<Callback>,
}

impl<Callback> Callbacks for CompileCallbacks<Callback>
where
    Callback: for<'tcx> FnOnce(TyCtxt<'tcx>),
{
    fn config(&mut self, config: &mut Config) {
        config.override_queries = Some(self.overrides);
        if let Some(source) = &self.source {
            config.file_loader = Some(Box::new(StringLoader(source.clone())));
        }
    }

    fn after_analysis(&mut self, _compiler: &Compiler, tcx: TyCtxt<'_>) -> Compilation {
        let callback: Callback = self.callback.take().expect("the analysis finishes once");
        callback(tcx);
        Compilation::Stop
    }
}
