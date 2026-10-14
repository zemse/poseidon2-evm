// poseidon2-gen: the Huff and Yul generators of generator/huff/generate.ts
// and generator/yul/generate.ts, writing the same files relative to the
// working directory (the repository root), and `verify`, which compiles and
// runs the generated Huff (huff/verify.rs), and `lean-export`, which writes
// the bytecode the formal verification checks (lean_export.rs), and
// `eip8024-corpus`, which runs programs around DUPN / SWAPN / EXCHANGE in revm
// for the Lean overlay to be compared with (eip8024.rs).

use std::path::Path;
use std::process::ExitCode;

use clap::{Parser, Subcommand};
use poseidon2_gen::assert_known::assert_known;
use poseidon2_gen::error::Result;
use poseidon2_gen::huff::fork::{DEFAULT_HARDFORK, fork};
use poseidon2_gen::huff::verify::verify;
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
        /// naming the solc settings it was built with
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
