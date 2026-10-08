// poseidon2-gen: the Huff and Yul generators of generator/huff/generate.ts
// and generator/yul/generate.ts, writing the same files relative to the
// working directory (the repository root).

use std::path::Path;
use std::process::ExitCode;

use clap::{Parser, Subcommand};
use poseidon2_gen::assert_known::assert_known;
use poseidon2_gen::error::Result;
use poseidon2_gen::huff::fork::{DEFAULT_HARDFORK, fork};
use poseidon2_gen::{bail, huff, yul};

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
        widths: Vec<usize>,
    },
    /// Yul library for each state width (default: 4)
    Yul { widths: Vec<usize> },
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
            widths: w,
        } => {
            let fork = fork(&hardfork)?;
            let w = widths(w)?;
            // the parameter derivation must reproduce the known values
            assert_known()?;
            huff::run(root, &fork, &w)
        }
        Command::Yul { widths: w } => {
            let w = widths(w)?;
            assert_known()?;
            yul::run(root, &w)
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
