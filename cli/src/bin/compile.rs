use argh::FromArgs;
use compiler::compile;
use io::Write;
use std::{fs, io, path::Path};
use walox::{
    compiler,
    scanner::Scanner,
    vm::{Heap, VM},
};

#[derive(FromArgs, Debug)]
/// Compile lox code in a single pass
struct Args {
    /// script path
    #[argh(positional)]
    file_path: String,

    /// output nicely formatted chunks
    #[argh(switch, short = 'd')]
    dump: bool,

    /// interpret the compiled bytecode
    #[argh(switch, short = 'r')]
    intepret: bool,
}

fn main() {
    tracing_subscriber::fmt::init();
    let args: Args = argh::from_env();

    tracing::debug!(?args, "Running 'compile' command...");
    if run(&args.file_path, args.dump, args.intepret) {
        panic!(
            "Encounter errors while running [{}].",
            <String as AsRef<Path>>::as_ref(&args.file_path).display()
        )
    }
    tracing::debug!(?args, "Ran 'compile' command.");
}

fn run(file_path: impl AsRef<Path>, should_dump: bool, should_interpret: bool) -> bool {
    let file_path = file_path.as_ref();
    assert!(
        file_path.exists(),
        "File '{}' does not exist!",
        file_path.display()
    );
    assert!(
        file_path.is_file(),
        "'{}' is not a file!",
        file_path.display()
    );

    let file_contents = fs::read_to_string(file_path).expect("Failed to read file");
    let scanner = Scanner::new(file_contents.as_str());
    let mut heap = Heap::new();
    let script = match compile(scanner, &heap) {
        Ok(c) => c,
        Err(e) => {
            for err in e {
                tracing::error!(%err);
            }
            return true;
        },
    };

    if should_dump {
        let mut stdout = io::stdout();

        let chunk_name = file_path
            .file_stem()
            .expect("unable to extract file stem")
            .to_string_lossy();

        script
            .chunk
            .write_disassembled(&mut stdout, Some(chunk_name.as_ref()))
            .expect("unable to output chunk");
    }

    if should_interpret {
        let mut stdout = io::stdout();
        let mut vm = VM::new(&mut stdout, script, &mut heap);
        let interp_result = vm.interpret();
        stdout.flush().expect("Unable to flush stdout");

        match interp_result {
            Ok(()) => {},
            Err(err) => {
                tracing::error!(%err);
                return true;
            },
        }
    }

    false
}
