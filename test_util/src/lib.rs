#![warn(missing_docs)]
//! Test utilities

use ansi_term::Colour::{Green, Red};
pub use anyhow;
pub use filecheck;
pub use globwalk;
pub use num_cpus;
pub use regex;
use std::{
    any::Any,
    fmt::Display,
    io,
    ops::Deref,
    panic::{catch_unwind, UnwindSafe}, convert::TryInto, path::PathBuf
};
pub use threadpool;
pub use tracing_subscriber;

pub mod filecheck_helpers;

/// Ascending from the current directory, find the workspace root of this
/// project
pub fn get_workspace_root() -> anyhow::Result<PathBuf> {
    let metadata = cargo_metadata::MetadataCommand::new().exec()?;

    metadata.workspace_root.try_into().map_err(anyhow::Error::from)
}

/// Take an `Any` trait object and attempt to cast it to some form of string.
pub fn get_panic_message(panic: &(dyn Any)) -> Option<&str> {
    panic
        // Try to convert it to a String, then turn that into a str
        .downcast_ref::<String>()
        .map(String::as_str)
        // If that fails, try to turn it into a &'static str
        .or_else(|| panic.downcast_ref::<&'static str>().map(Deref::deref))
}

fn handle_err_result(e: Box<dyn Any>) -> TestResult {
    TestResult::Error {
        reason: get_panic_message(&e).map(String::from).unwrap_or_else(|| {
            format!(
                "Panic! Unable to display playload [TypeId: {:?}].",
                e.type_id()
            )
        }),
    }
}

/// Print a list of `TestOutput`s and a summary.
pub fn output_test_outputs(
    writer: &mut dyn io::Write,
    outputs: impl IntoIterator<Item = TestOutput>,
) -> anyhow::Result<()> {
    const FAILED_STR: &str = "FAILED";
    const PASSED_STR: &str = "ok";

    let mut passed = 0;
    let mut failed = 0;
    let mut max_name_len = 0;

    let mut outputs: Vec<_> = outputs
        .into_iter()
        .inspect(|output| {
            max_name_len = core::cmp::max(max_name_len, output.name.len());
        })
        .collect();
    outputs.sort_unstable_by(|a, b| a.name.cmp(&b.name));

    writeln!(writer, "\nrunning {} tests", outputs.len())?;

    for output in outputs {
        let spacer: String = core::iter::repeat(' ')
            .take(max_name_len - output.name.len())
            .collect();
        let test_result = match output.result {
            TestResult::Ok => {
                passed += 1;
                Green.paint(PASSED_STR)
            },
            TestResult::Error { .. } => {
                failed += 1;
                Red.paint(FAILED_STR)
            },
        };

        writeln!(writer, "{}{} ... {}", output.name, spacer, test_result)?;

        match output.result {
            TestResult::Error { reason } => {
                writeln!(writer, "{}", reason)?;
            },
            _ => {},
        }
    }

    let overall_result = if failed > 0 {
        Red.paint(FAILED_STR)
    } else {
        Green.paint(PASSED_STR)
    };

    //test result: ok. 0 passed; 0 failed;
    writeln!(
        writer,
        "\ntest result: {}. {} passed; {} failed;\n",
        overall_result, passed, failed
    )?;

    if failed > 0 {
        Err(anyhow::anyhow!("test suite failed!"))
    } else {
        Ok(())
    }
}

/// The result of a named test execution
#[derive(Debug, Clone)]
pub struct TestOutput {
    /// The name of the test instance
    pub name: String,
    /// The outcome of the test instance
    pub result: TestResult,
}

/// The outcome of a test.
#[derive(Debug, Clone)]
pub enum TestResult {
    /// The test completed successfully
    Ok,
    /// The test failed with a specific reason
    Error {
        /// The reason the test failed
        reason: String,
    },
}

/// A family of tests
pub trait Test {
    /// The arguments, if any, to the tests
    type Args;

    /// Run the test and return the result.
    fn execute(&self, args: Self::Args) -> TestResult;
}

impl<A, E> Test for fn(A) -> Result<(), E>
where
    A: UnwindSafe,
    E: Display,
{
    type Args = A;

    fn execute(&self, args: Self::Args) -> TestResult {
        let res = catch_unwind(|| (*self)(args));

        match res {
            Ok(Ok(())) => TestResult::Ok,
            Ok(Err(e)) => TestResult::Error {
                reason: e.to_string(),
            },
            Err(e) => handle_err_result(e),
        }
    }
}

impl<A, B, E> Test for fn(A, B) -> Result<(), E>
where
    A: UnwindSafe,
    B: UnwindSafe,
    E: Display,
{
    type Args = (A, B);

    fn execute(&self, args: Self::Args) -> TestResult {
        let res = catch_unwind(|| (*self)(args.0, args.1));

        match res {
            Ok(Ok(())) => TestResult::Ok,
            Ok(Err(e)) => TestResult::Error {
                reason: e.to_string(),
            },
            Err(e) => handle_err_result(e),
        }
    }
}

impl<A> Test for fn(A) -> ()
where
    A: UnwindSafe,
{
    type Args = A;

    fn execute(&self, args: Self::Args) -> TestResult {
        let res = catch_unwind(|| (*self)(args));

        match res {
            Ok(()) => TestResult::Ok,
            Err(e) => handle_err_result(e),
        }
    }
}

impl<A, B> Test for fn(A, B) -> ()
where
    A: UnwindSafe,
    B: UnwindSafe,
{
    type Args = (A, B);

    fn execute(&self, args: Self::Args) -> TestResult {
        let res = catch_unwind(|| (*self)(args.0, args.1));

        match res {
            Ok(()) => TestResult::Ok,
            Err(e) => handle_err_result(e),
        }
    }
}
