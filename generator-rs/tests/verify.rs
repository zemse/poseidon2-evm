// Compiles the generated Huff with huff-neo and runs it in revm (huff/verify.rs):
// outputs against the reference, measured gas against the model. The model
// is exact for these widths, so the tolerance is 0 gas.

use std::path::{Path, PathBuf};

use poseidon2_gen::huff;
use poseidon2_gen::huff::fork::fork;
use poseidon2_gen::huff::verify::{Report, verify};

const GAS_TOLERANCE: i64 = 0;

fn repo() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("..")
}

/// builds the widths in memory, compiles, deploys and checks them
fn run(name: &str, widths: &[usize]) -> Vec<Report> {
    let fork = fork(name).unwrap();
    let built = huff::run(&repo(), &fork, widths, false, || Ok(())).expect("build");
    verify(&repo(), &fork, &built).expect("verify")
}

fn within(report: &Report) {
    let mut gas = vec![Some(report.gas), report.warm, report.permutation];
    if let Some(hashes) = report.hashes {
        gas.extend(hashes.map(Some));
    }
    for g in gas.into_iter().flatten() {
        assert!(g.diff().abs() <= GAS_TOLERANCE, "{report}");
    }
}

#[test]
fn amsterdam_t2_t3_t4() {
    let reports = run("amsterdam", &[2, 3, 4]);
    for report in &reports {
        within(report);
    }
    // forge: test/Poseidon2T2.t.sol and the hash_* of test/Poseidon2.t.sol
    assert_eq!(reports[0].gas.measured, 5912);
    assert_eq!(reports[1].gas.measured, 7653);
    let hashes = reports[2].hashes.expect("hash entry");
    assert_eq!(hashes.map(|g| g.measured), [11895, 11902, 11975]);
}

#[test]
fn osaka_t2_t3_t4() {
    let reports = run("osaka", &[2, 3, 4]);
    for report in &reports {
        within(report);
    }
    assert_eq!(reports[0].gas.measured, 5912);
    assert_eq!(reports[1].gas.measured, 7653);
    assert_eq!(reports[2].permutation.unwrap().measured, 12083);
    let hashes = reports[2].hashes.expect("hash entry");
    assert_eq!(hashes.map(|g| g.measured), [11895, 11902, 11975]);
}

/// t = 16 fits one contract with the shared body of the internal rounds
/// and the streamed external rounds
#[test]
fn osaka_body_t16() {
    let reports = run("osaka", &[16]);
    within(&reports[0]);
    assert_eq!(reports[0].bytes.len(), 1);
    assert_eq!(reports[0].gas.measured, 49550);
}

/// t = 24 fits one contract with PRIME loaded from memory
#[test]
fn osaka_prime_in_memory_t24() {
    let reports = run("osaka", &[24]);
    within(&reports[0]);
    assert_eq!(reports[0].bytes.len(), 1);
    assert_eq!(reports[0].gas.measured, 79583);
}

/// t = 28 fits one contract once the external rounds stream
#[test]
fn osaka_t28() {
    let reports = run("osaka", &[28]);
    within(&reports[0]);
    assert_eq!(reports[0].bytes.len(), 1);
    assert_eq!(reports[0].gas.measured, 97714);
}
