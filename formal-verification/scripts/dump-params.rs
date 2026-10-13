// Dumps the parameters the repository generator derives (generator-rs
// round_constants::generate_params_uncached) as JSON lines, input of genwide.mjs.
// Build it as the main.rs of a scratch binary crate with
// `poseidon2-gen = { path = "../generator-rs" }`; with the argument `kat` it prints
// the reference permutation of [0, 1, .., t - 1] instead (repo_kat.jsonl).

use poseidon2_gen::field::u256;
use poseidon2_gen::reference::permutation;
use poseidon2_gen::round_constants::generate_params_uncached;

fn main() {
    let mode = std::env::args().nth(1).unwrap_or_default();
    for t in [2usize, 3, 4, 8, 12, 16, 20, 24, 28] {
        let p = generate_params_uncached(t);
        if mode == "kat" {
            let input: Vec<_> = (0..t as u64).map(u256).collect();
            let out: Vec<String> = permutation(&p, &input).iter().map(|v| format!("{v:#x}")).collect();
            println!("{{\"t\":{t},\"out\":{out:?}}}");
            continue;
        }
        let rc: Vec<Vec<String>> = p
            .round_constants
            .iter()
            .map(|r| r.iter().map(|v| format!("{v:#x}")).collect())
            .collect();
        let d: Vec<String> = p.internal_diag_minus_one.iter().map(|v| format!("{v:#x}")).collect();
        println!(
            "{{\"t\":{t},\"rf\":{},\"rp\":{},\"rc\":{:?},\"diag\":{:?}}}",
            p.rounds_f, p.rounds_p, rc, d
        );
    }
}
