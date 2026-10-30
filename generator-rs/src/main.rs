// poseidon2-gen: the Huff and Yul generators, writing their files relative
// to the working directory (the repository root), `schedule`, which prints
// the schedule `huff` selects for stacksearch/gas-floor.mjs, `verify`, which
// compiles and runs the generated Huff (huff/verify.rs), `lean-export`, which
// writes the bytecode the formal verification checks (lean_export.rs), and
// `eip8024-corpus`, which runs programs around DUPN / SWAPN / EXCHANGE in revm
// for the Lean overlay to be compared with (eip8024.rs).

use std::path::Path;
use std::process::ExitCode;

use clap::{Parser, Subcommand};
use poseidon2_gen::assert_known::assert_known;
use poseidon2_gen::error::Result;
use poseidon2_gen::huff::fork::{DEFAULT_HARDFORK, Fork, fork};
use poseidon2_gen::huff::render::{memory_gas, overhead};
use poseidon2_gen::huff::schedule::describe_options;
use poseidon2_gen::huff::verify::verify;
use poseidon2_gen::round_constants::generate_params;
use poseidon2_gen::vectors::test_inputs;
use poseidon2_gen::{bail, eip8024, huff, lean_export, yul};

#[derive(Parser)]
#[command(
    version,
    about = "Generates the Poseidon2 BN254 Huff and Yul permutations"
)]
struct Cli {
    #[command(subcommand)]
    command: Command,
}

#[derive(Subcommand)]
enum Command {
    /// Huff permutation for each state width (default: 4)
    Huff {
        /// hardfork whose opcodes and code size the output targets
        #[arg(long, default_value = DEFAULT_HARDFORK)]
        hardfork: String,
        /// then compile the output with huff-neo and run it in revm, as
        /// `verify` does
        #[arg(long)]
        verify: bool,
        widths: Vec<usize>,
    },
    /// Builds the Huff like `huff` without writing it, compiles it with
    /// huff-neo and runs it in revm: outputs against the reference, gas
    /// against the model (default: 4)
    Verify {
        /// hardfork whose opcodes and code size the output targets
        #[arg(long, default_value = DEFAULT_HARDFORK)]
        hardfork: String,
        widths: Vec<usize>,
    },
    /// Prints the schedule `huff` selects for each width (default: 4) as
    /// JSON: its options, gas, the gas around it and its lines, for
    /// stacksearch/gas-floor.mjs
    Schedule {
        /// hardfork whose opcodes and code size the output targets
        #[arg(long, default_value = DEFAULT_HARDFORK)]
        hardfork: String,
        widths: Vec<usize>,
    },
    /// Yul library for each state width (default: 4)
    Yul { widths: Vec<usize> },
    /// Writes the runtime bytecode of the Huff contracts (per hardfork), the
    /// Yul wrappers (per forge out/ directory) and the deployed artifacts as
    /// Lean data for formal-verification/
    LeanExport {
        /// directory of the Lean files
        #[arg(long, default_value = "formal-verification/Poseidon2/Bytecode")]
        out: String,
        /// hardforks of the Huff contracts
        #[arg(long = "hardfork", default_values = ["amsterdam", "osaka"])]
        hardforks: Vec<String>,
        /// label=dir: a forge out/ directory with the Yul wrappers, its label
        /// naming the solc settings it was built with; label:2,3,8=dir reads
        /// only those wrappers (and Poseidon2Yul_BN254)
        #[arg(long)]
        yul: Vec<String>,
    },
    /// Writes a corpus of programs around EIP-8024 (DUPN, SWAPN, EXCHANGE)
    /// with what revm (Amsterdam) does with each, one per line, for
    /// formal-verification/scripts/Eip8024Diff.lean to compare with
    Eip8024Corpus {
        /// file to write (default: standard output)
        #[arg(long)]
        out: Option<String>,
    },
}

/// The widths to build, 4 when none are given; Poseidon2 defines t = 2, 3
/// or 4k.
fn widths(widths: Vec<usize>) -> Result<Vec<usize>> {
    let widths = if widths.is_empty() { vec![4] } else { widths };
    for &t in &widths {
        if t < 2 {
            bail!("invalid t: {t}");
        }
        if !(t == 2 || t == 3 || t.is_multiple_of(4)) {
            bail!("unsupported t = {t}: Poseidon2 defines t = 2, 3 or 4k");
        }
    }
    Ok(widths)
}

/// The selected raw entry and, separately, the public permutation trace.
fn schedule(fork: &Fork, t: usize) -> Result<String> {
    let params = generate_params(t);
    let Some(plan) = huff::build_entry_plan(&params, &test_inputs(t), *fork)? else {
        bail!("no {} schedule for t = {t}", fork.name);
    };
    let kind = match (plan.terminal_result().is_some(), t) {
        (false, _) => "permutation",
        (true, 2) => "t2-terminal",
        (true, 3) => "t3-terminal",
        (true, _) => bail!("unsupported terminal entry width {t}"),
    };
    Ok(format!(
        "{{\"t\":{t},\"roundsF\":{},\"roundsP\":{},\"options\":{:?},\"hardfork\":{:?},\"entryKind\":{kind:?},{},\"permutation\":{{{}}}}}",
        params.rounds_f,
        params.rounds_p,
        describe_options(&plan.permutation().opts),
        fork.name,
        schedule_cost(fork, t, plan.entry_result()),
        schedule_cost(fork, t, &plan.permutation().result),
    ))
}

fn schedule_cost(fork: &Fork, t: usize, result: &huff::schedule::BuildResult) -> String {
    let o = overhead(
        *fork,
        t,
        &result.input_slots,
        result.state_in_memory,
        false,
        false,
        result.memory,
    );
    let memory = memory_gas(result.memory.max(32 * t));
    let wrapper = o.entry_gas + o.tail_gas + memory;
    // Debug escapes the ASCII lines as JSON does
    let lines: Vec<String> = result.lines.iter().map(|l| format!("{l:?}")).collect();
    format!(
        "\"gas\":{},\"wrapper\":{wrapper},\"entryGas\":{},\"tailGas\":{},\"memoryGas\":{memory},\"runtimeBytes\":{},\"lines\":[{}]",
        result.gas,
        o.entry_gas,
        o.tail_gas,
        result.bytes + o.bytes,
        lines.join(",")
    )
}

fn run(cli: Cli) -> Result<()> {
    let root = Path::new(".");
    match cli.command {
        Command::Huff {
            hardfork,
            verify: check,
            widths: w,
        } => {
            let fork = fork(&hardfork)?;
            let w = widths(w)?;
            // the parameter derivation must reproduce the known values
            // before anything is written
            let built = huff::run(root, &fork, &w, true, assert_known)?;
            if check {
                verify(root, &fork, &built)?;
            }
            Ok(())
        }
        Command::Verify {
            hardfork,
            widths: w,
        } => {
            let fork = fork(&hardfork)?;
            let w = widths(w)?;
            let built = huff::run(root, &fork, &w, false, assert_known)?;
            verify(root, &fork, &built)?;
            Ok(())
        }
        Command::Schedule {
            hardfork,
            widths: w,
        } => {
            assert_known()?;
            let fork = fork(&hardfork)?;
            let rows = widths(w)?
                .into_iter()
                .map(|t| schedule(&fork, t))
                .collect::<Result<Vec<_>>>()?;
            println!("[{}]", rows.join(",\n"));
            Ok(())
        }
        Command::Yul { widths: w } => {
            let w = widths(w)?;
            yul::run(root, &w, assert_known)
        }
        Command::LeanExport {
            out,
            hardforks,
            yul,
        } => lean_export::run(root, Path::new(&out), &hardforks, &yul),
        Command::Eip8024Corpus { out } => {
            let text = eip8024::lines().join("\n") + "\n";
            match out {
                Some(path) => std::fs::write(path, text)?,
                None => print!("{text}"),
            }
            Ok(())
        }
    }
}

fn main() -> ExitCode {
    match run(Cli::parse()) {
        Ok(()) => ExitCode::SUCCESS,
        Err(err) => {
            eprintln!("error: {err}");
            ExitCode::FAILURE
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn number(json: &str, key: &str) -> u64 {
        json.split_once(&format!("\"{key}\":"))
            .unwrap()
            .1
            .split(',')
            .next()
            .unwrap()
            .parse()
            .unwrap()
    }

    #[test]
    fn schedule_entry_budget_matches_t28_execution_pin() {
        let json = schedule(&fork("osaka").unwrap(), 28).unwrap();
        // Independently compiled call gas is pinned in tests/verify.rs.
        assert_eq!(number(&json, "gas") + number(&json, "wrapper"), 90740);
    }

    #[test]
    fn schedule_gas_matches_execution() {
        let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("..");
        for name in ["paris", "osaka", "amsterdam"] {
            let fork = fork(name).unwrap();
            let built = huff::run(&root, &fork, &[2, 3, 4], false, || Ok(())).unwrap();
            let reports = verify(&root, &fork, &built).unwrap();
            for report in reports {
                let json = schedule(&fork, report.t).unwrap();
                let measured = report.permutation.as_ref().unwrap_or(&report.gas).measured;
                assert_eq!(
                    number(&json, "gas") + number(&json, "wrapper"),
                    measured,
                    "{report}"
                );
            }
        }
    }
}
