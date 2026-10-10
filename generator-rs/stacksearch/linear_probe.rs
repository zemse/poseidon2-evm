// Compiled checks for the finite Python probe, not production opcode support.
use super::*;
use crate::field::PRIME;
use crate::huff::fork::fork;
use crate::reference::matmul_external;

fn render(dsl: &str) -> String {
    let params = generate_params(4);
    dsl.split_whitespace()
        .map(|token| {
            if let Some(lane) = token.strip_prefix("sbox") {
                let lane: usize = lane.parse().unwrap();
                format!(
                    "{:#x} add dup2 dup1 dup3 dup1 mulmod dup1 mulmod mulmod",
                    params.round_constants[63][lane]
                )
            } else if token == "P" {
                format!("{PRIME:#x}")
            } else if token == "2" || token == "4" {
                format!("0x0{token}")
            } else {
                token.split('=').next().unwrap().to_string()
            }
        })
        .collect::<Vec<_>>()
        .join(" ")
}

#[test]
fn finite_linear_arithmetic_candidates() {
    let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("..");
    let programs = include_str!("results/lane3-linear.program");
    assert_eq!(programs.lines().count(), 25);
    for name in ["osaka", "amsterdam"] {
        let fork = fork(name).unwrap();
        let width = super::super::generate(4, &fork).unwrap();
        let mut files: HashMap<String, String> = width
            .files()
            .map(|(path, text)| (path.to_string(), text.to_string()))
            .collect();
        let Target::Hash {
            entry,
            source,
            entry_gas,
            ..
        } = &width.target
        else {
            panic!("expected t4 hash target");
        };
        files.insert(entry.clone(), source.clone());
        let path = files
            .keys()
            .find(|path| path.ends_with("/Permutation.huff"))
            .unwrap()
            .clone();
        let original = files[&path].clone();
        let marker = "// Round 63 (external)";
        assert_eq!(original.matches(marker).count(), 1);
        let (prefix, _) = original.split_once(marker).unwrap();
        for program in programs.lines() {
            let fields: Vec<_> = program.splitn(4, '\t').collect();
            assert_eq!(fields.len(), 4);
            let kind = fields[0];
            assert!(matches!(kind, "final" | "linear"));
            let label = fields[1];
            let gas: u64 = fields[2].parse().unwrap();
            let code = render(fields[3]);
            let mut candidate = files.clone();
            let (contract, expected_gas) = if kind == "final" {
                candidate.insert(path.clone(), format!("{prefix}{marker}\n{code}\n}}\n"));
                (entry.as_str(), entry_gas - 352 + gas)
            } else {
                // Same four-input reduction and output wrapper for every linear case.
                let loads = ["0x60", "0x40", "0x20", "0x00"]
                    .map(|offset| format!("{PRIME:#x} {offset} calldataload mod"))
                    .join(" ");
                candidate.insert(
                    "linear.huff".into(),
                    format!(
                        "#define macro MAIN() = takes(0) returns(0) {{\n{loads}\n{code}\n\
                         0x00 mstore 0x20 mstore 0x40 mstore 0x60 mstore 0x80 0x00 return\n}}"
                    ),
                );
                // 55 input + 23 stores + 5 return + 12 memory, with three PUSH0s.
                ("linear.huff", 95 + gas)
            };
            let sources = Arc::new(Sources {
                root: root.clone(),
                files: candidate,
            });
            let compiled = compile(&sources, contract, &fork).unwrap();
            let mut chain = Chain::new(&fork);
            let to = chain.deploy(compiled.initcode).unwrap();
            let measured = if kind == "final" {
                check_permutation(&mut chain, to, &[], 4, label).unwrap()
            } else {
                let mut gas = Vec::new();
                for input in inputs(4) {
                    let (output, spent) = chain.call(to, words(&input), &[]).unwrap();
                    let mut expected: Vec<_> = input.iter().copied().map(reduce).collect();
                    matmul_external(&mut expected);
                    assert_eq!(from_words(&output), expected, "{name} {label}");
                    gas.push(spent);
                }
                gas
            };
            let actual = same_gas(&measured, label).unwrap();
            assert_eq!(actual, expected_gas, "{name} {kind} {label}");
            println!(
                "{name} {kind} {label}: {} reference-checked calls, {actual} call gas, {gas} segment model",
                measured.len()
            );
        }
    }
}
