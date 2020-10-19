use anyhow::Context;
use globwalk::FileType;
use io::Write;
use std::{
    env, fs, io,
    path::{Component, Path, PathBuf},
};
use walox::{analysis::AstValidator, interpreter::Interpreter, parser::parse, scanner::Scanner};
use walox_test_util::{
    anyhow, filecheck, filecheck::CheckerBuilder, get_workspace_root, globwalk, num_cpus, regex,
    threadpool::ThreadPool, tracing_subscriber, Test, TestOutput,
};

fn main() -> anyhow::Result<()> {
    tracing_subscriber::fmt::init();

    tracing::debug!("Starting interpreter filecheck tests.");
    let test_data_dir = if let Some(val) = env::var_os("TEST_DATA_DIR") {
        PathBuf::from(val)
    } else {
        let mut workspace_root = get_workspace_root()?;
        workspace_root.push("test_data");
        workspace_root
    };

    tracing::debug!("Checking for test name pattern.");
    let test_name_pattern = env::args()
        .nth(1)
        .map(|reg_src| regex::Regex::new(&reg_src).expect("Passed regex was not valid!"));

    assert!(
        test_data_dir.is_dir(),
        "The test data directory should be a directory."
    );

    tracing::debug!(test_data = %test_data_dir.display(), ?test_name_pattern, "Gathering files from test data directory");

    let pool = ThreadPool::with_name("test-runner".into(), num_cpus::get());
    let (tx, rx) = std::sync::mpsc::channel();
    let mut test_count = 0;

    let test_dispatch_span = tracing::debug_span!("test_dispatch");
    for entry in collect_test_files(&test_data_dir)? {
        let _guard = test_dispatch_span.enter();

        let entry = entry.context("error retrieving test file entry")?;
        let path = entry.path();

        let test_name_components: Vec<_> = path
            .strip_prefix(&test_data_dir)
            .context("unable to strip test data dir prefix")?
            .components()
            .map(|c| match c {
                Component::Normal(c) => c
                    .to_str()
                    .ok_or_else(|| anyhow::anyhow!("Unable to convert file component to unicode")),
                x => Err(anyhow::anyhow!("Non-normal path component: [{:?}]", x)),
            })
            .collect::<Result<_, _>>()?;

        let test_name_prefix: String = test_name_components
            .split_last()
            .map(|(_, cs)| cs.join("::"))
            .unwrap_or_default();

        let test_name_suffix: String = path
            .file_stem()
            .ok_or_else(|| anyhow::anyhow!("File lacks name stem"))?
            .to_str()
            .ok_or_else(|| anyhow::anyhow!("Unable to convert file stem to unicode"))?
            .into();

        let mut test_name = String::new();
        if !test_name_prefix.is_empty() {
            test_name.push_str(&test_name_prefix);
            test_name.push_str("::");
        }
        test_name.push_str(&test_name_suffix);

        if let Some(ref test_name_pattern) = test_name_pattern {
            if !test_name_pattern.is_match(&test_name) {
                continue;
            }
        }

        let file_content = fs::read_to_string(path)?;

        tracing::trace!(%test_name, "Dispatching test case for execution");

        pool.execute({
            let tx = tx.clone();
            let test_span =
                tracing::trace_span!("test_execution", id = test_count, name = %test_name);

            move || {
                test_span.in_scope(|| {
                    tracing::trace!("Starting test execution");

                    let result = Test::execute(
                        &(execute_interpreter_filecheck as fn(String) -> Result<(), anyhow::Error>),
                        file_content,
                    );

                    tracing::trace!(?result, "Test case finished. Sending result.");

                    tx.send(TestOutput {
                        name: test_name,
                        result,
                    })
                    .expect("Failed to send test result");
                });
            }
        });

        test_count += 1;
    }

    tracing::debug!(parent: &test_dispatch_span, %test_count, "Sent all test cases to threadpool, now waiting for tests to complete.");

    pool.join();

    tracing::debug!(parent: &test_dispatch_span, %test_count, "All tests complete. Receiving results.");

    let outputs: Vec<_> = rx.into_iter().take(test_count).collect();

    walox_test_util::display_test_outputs(&mut io::stdout(), outputs)?;

    Ok(())
}

fn execute_interpreter_filecheck(file_content: String) -> anyhow::Result<()> {
    let stdout_backing = Vec::new();
    let mut checker_builder = CheckerBuilder::new();
    let mut stderr_checker_builder = CheckerBuilder::new();

    // Perform textual analysis of the source code
    let mut scanner = Scanner::new(&file_content);
    let parse_result = parse(scanner.by_ref()).map_err(|errs| {
        errs.into_iter()
            .enumerate()
            .map(|(idx, err)| format!("{}: {}\n", idx, err))
            .collect::<String>()
    });

    for comment in scanner.comments {
        if comment.starts_with("+error") {
            let comment = &comment["+error".len()..];
            let _ = stderr_checker_builder.directive(comment).unwrap();
        } else {
            let _ = checker_builder.directive(comment).unwrap();
        }
    }

    let error_checker = stderr_checker_builder.finish();
    let checker = checker_builder.finish();

    let statements = match parse_result {
        Ok(statements) => statements,
        Err(stderr) => {
            let (did_match, explanation) =
                error_checker.explain(&stderr, filecheck::NO_VARIABLES)?;

            if !did_match {
                return Err(anyhow::anyhow!(explanation));
            } else if error_checker.is_empty() {
                return Err(anyhow::anyhow!(stderr));
            } else {
                return Ok(());
            }
        },
    };

    // Perform static analysis on the AST to check for misplaced `return`, `this`,
    // etc
    let mut validator = AstValidator::default();
    match validator.validate(&statements) {
        Ok(()) => {},
        Err(err) => {
            let (did_match, explanation) =
                error_checker.explain(&err.to_string(), filecheck::NO_VARIABLES)?;

            if !did_match {
                return Err(anyhow::anyhow!(explanation));
            } else if error_checker.is_empty() {
                return Err(anyhow::anyhow!(err));
            } else {
                return Ok(());
            }
        },
    }

    let mut interpreter = Interpreter::new(stdout_backing);
    let interp_result = interpreter.interpret(&statements);

    let _ = interpreter.stdout.flush().expect("failed to flush stdout");
    let stdout_output = String::from_utf8(interpreter.stdout).unwrap();

    let (is_ok, explanation) = match interp_result {
        Ok(_) => checker.explain(&stdout_output, filecheck::NO_VARIABLES)?,
        Err(err) => {
            let (is_ok, explanation) =
                error_checker.explain(&format!("{}", err), filecheck::NO_VARIABLES)?;

            if is_ok && error_checker.is_empty() {
                return Err(anyhow::anyhow!(err));
            }

            (is_ok, explanation)
        },
    };

    if is_ok {
        Ok(())
    } else {
        Err(anyhow::anyhow!("{}", explanation))
    }
}

fn collect_test_files(
    base_dir: &Path,
) -> Result<
    impl Iterator<Item = Result<globwalk::DirEntry, globwalk::WalkError>>,
    globwalk::GlobError,
> {
    globwalk::GlobWalkerBuilder::from_patterns(base_dir, TEST_DATA_PATTERNS)
        .file_type(FileType::FILE)
        .build()
}

const TEST_DATA_PATTERNS: &[&str] = &[
    "*.lox",
    "**/*.lox",
    "!benchmark/",
    "!class/inherit_self.lox",
    "!class/inherited_method.lox",
    "!class/local_inherit_other.lox",
    "!class/local_inherit_self.lox",
    "!expressions",
    "!inheritance/",
    "!limit/",
    "!regression/",
    "!scanning/",
    "!super/",
];
