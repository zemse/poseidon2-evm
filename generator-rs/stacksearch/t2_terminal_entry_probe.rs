// Test-only checked t2 terminal entry; the public permutation is unchanged.
use super::*;
use crate::field::{PRIME, UINT256_MAX, u256};
use crate::huff::fork::fork;
use crate::huff::render::{entry_bytes, huff_name, render_entry, render_permutation};
use crate::huff::schedule::step_count;
use crate::huff::schedule::t2_terminal_tests::{OPTIONS, build_fixture};

fn raw_inputs() -> Vec<Vec<U256>> {
    let mut raw = inputs(2);
    assert_eq!(raw.len(), 24);
    let l = PRIME - u256(1);
    raw.extend([vec![UINT256_MAX; 2], vec![PRIME; 2], vec![l; 2]]);
    raw.extend([vec![UINT256_MAX, U256::ZERO], vec![U256::ZERO, UINT256_MAX]]);
    for mut pair in [
        vec![UINT256_MAX, PRIME],
        vec![UINT256_MAX, l],
        vec![PRIME, l],
    ] {
        for _ in 0..2 {
            raw.push(pair.clone());
            pair.rotate_left(1);
        }
    }
    assert_eq!(raw.len(), 35);
    raw
}

fn tokens(lines: &[String]) -> Vec<&str> {
    lines
        .iter()
        .flat_map(|line| line.split("//").next().unwrap().split_whitespace())
        .collect()
}

fn calls(
    fork: &Fork,
    code: Compiled,
    params: &crate::round_constants::Params,
    raw: &[Vec<U256>],
    model: u64,
) -> Vec<u8> {
    assert!(code.runtime.len() <= fork.code_size);
    assert!(code.initcode.len() <= fork.initcode_size);
    let mut chain = Chain::new(fork);
    let to = chain.deploy(code.initcode).unwrap();
    let mut gas = Vec::new();
    for (i, input) in raw.iter().enumerate() {
        let (out, actual) = chain.call(to, words(input), &[]).unwrap();
        assert_eq!(out.len(), 64, "{} case {i}", fork.name);
        assert_eq!(
            from_words(&out),
            permutation(params, input),
            "{} case {i}",
            fork.name
        );
        assert!(from_words(&out).iter().all(|&word| word < PRIME));
        assert_eq!(actual, model, "{} case {i}", fork.name);
        gas.push(actual);
    }
    assert_eq!(same_gas(&gas, fork.name).unwrap(), model);
    code.runtime
}

#[test]
fn t2_terminal_compiled() {
    let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("..");
    let params = generate_params(2);
    let raw = raw_inputs();
    let clean: Vec<Vec<U256>> = raw
        .iter()
        .map(|input| input.iter().map(|&word| reduce(word)).collect())
        .collect();
    let mut baselines = Vec::new();
    // Reproduce every fork's baseline before running a terminal candidate.
    for name in ["amsterdam", "osaka", "paris"] {
        let fork = fork(name).unwrap();
        let selected = super::super::build_entry(&params, &clean, fork)
            .unwrap()
            .unwrap();
        assert_eq!(selected.opts, OPTIONS);
        let result = selected.result;
        let (checked, depth) = build_fixture(&params, &clean, fork, false, 0).unwrap();
        assert_eq!(checked.lines, result.lines);
        assert_eq!(
            (checked.gas, checked.bytes, checked.max_depth),
            (result.gas, result.bytes, result.max_depth)
        );
        assert_eq!(checked.step_bytes, result.step_bytes);
        let model = super::super::entry_gas(&fork, 2, &result);
        assert_eq!(model, if name == "paris" { 5914 } else { 5912 });
        let path = huff_name(&fork, 2, "Poseidon2");
        let permutation_path = huff_name(&fork, 2, "Permutation");
        let utils = if name == "amsterdam" {
            "../Utils.huff"
        } else {
            "../../Utils.huff"
        };
        let public = render_permutation(&params, &result, &selected.opts, utils, &fork);
        if name == "amsterdam" {
            assert_eq!(
                std::fs::read_to_string(root.join(&permutation_path)).unwrap(),
                public
            );
        }
        let files = HashMap::from([
            (permutation_path, public),
            (path.clone(), render_entry(&params, &fork, &result)),
        ]);
        let sources = Arc::new(Sources {
            root: root.clone(),
            files: files.clone(),
        });
        let code = compile(&sources, &path, &fork).unwrap();
        assert_eq!(
            code.runtime.len(),
            result.bytes + entry_bytes(fork, 2, &result.input_slots, false, 0)
        );
        let runtime = calls(&fork, code, &params, &raw, model);
        println!(
            "T2_TERMINAL baseline {name}: {} reference-checked calls, {model} gas, {} bytes, depth {}, dup {}",
            raw.len(),
            runtime.len(),
            result.max_depth,
            result.max_dup
        );
        baselines.push((fork, result, files, runtime, depth, model));
    }
    for (fork, original, files, runtime, depth, baseline_gas) in baselines {
        let (candidate, _) = build_fixture(&params, &clean, fork, true, 0).unwrap();
        let old_ops = tokens(&original.lines);
        let new_ops = tokens(&candidate.lines);
        assert_eq!(
            &old_ops[old_ops.len() - 9..],
            [
                "dup2", "dup2", "dup5", "add", "swap2", "dup3", "addmod", "swap3", "addmod"
            ]
        );
        assert_eq!(
            &new_ops[new_ops.len() - 12..],
            [
                "dup1", "dup4", "add", "dup3", "dup2", "dup6", "addmod", "msize", "mstore",
                "addmod", "msize", "mstore"
            ]
        );
        assert_eq!(
            &old_ops[..old_ops.len() - 9],
            &new_ops[..new_ops.len() - 12]
        );
        assert!(old_ops.iter().all(|op| !matches!(
            *op,
            "msize" | "mstore" | "mload" | "codecopy" | "calldatacopy"
        )));
        assert_eq!(
            (candidate.gas, candidate.bytes),
            (original.gas + 7, original.bytes + 3)
        );
        assert_eq!(
            (candidate.max_depth, candidate.max_dup),
            (original.max_depth, original.max_dup)
        );
        assert!(candidate.max_depth <= 1000);
        assert!(candidate.max_dup <= fork.reach);
        assert_eq!(candidate.step_bytes.len(), step_count(&params));
        assert_eq!(&candidate.step_bytes[..64], &original.step_bytes[..64]);
        assert_eq!(candidate.step_bytes.last(), Some(&candidate.bytes));
        assert_eq!((candidate.state_in_memory, candidate.memory), (true, 64));
        let model = super::super::entry_gas(&fork, 2, &candidate);
        assert_eq!(model + 3, baseline_gas);
        let path = huff_name(&fork, 2, "Poseidon2");
        let public_path = huff_name(&fork, 2, "Permutation");
        let wrapper = render_entry(&params, &fork, &candidate);
        assert_eq!(wrapper.matches("POSEIDON2_PERMUTATION()").count(), 1);
        let entry = wrapper.replacen("POSEIDON2_PERMUTATION()", &candidate.lines.join("\n"), 1);
        let mut trial = files.clone();
        trial.insert(path.clone(), entry);
        assert_eq!(trial[&public_path], files[&public_path]);
        let sources = Arc::new(Sources {
            root: root.clone(),
            files: trial.clone(),
        });
        let code = compile(&sources, &path, &fork).unwrap();
        assert_eq!(
            code.runtime.len(),
            candidate.bytes + entry_bytes(fork, 2, &candidate.input_slots, true, 64)
        );
        assert_eq!(code.runtime.len() + 1, runtime.len());
        let ret_bytes = if fork.push0 { 3 } else { 4 };
        assert_eq!(
            &runtime[..runtime.len() - 13 - ret_bytes],
            &code.runtime[..code.runtime.len() - 12 - ret_bytes]
        );
        let bytes = calls(&fork, code, &params, &raw, model).len();
        println!(
            "T2_TERMINAL candidate {}: {} reference-checked calls, {model} gas, {bytes} bytes, saving {}, depth {}, dup {}",
            fork.name,
            raw.len(),
            baseline_gas - model,
            candidate.max_depth,
            candidate.max_dup
        );

        // Pre-touched memory and distinct tails exercise the public macro,
        // not the private terminal entry's empty-memory assumption.
        let public_caller = format!(
            "#include \"./Permutation.huff\"\n#define macro MAIN() = {{\n0xbeef 0x200 mstore\n0x22 0x11 SETUP()\ndup1 0x20 calldataload mod\ndup2 0x0 calldataload mod\nPOSEIDON2_PERMUTATION()\n0x0 mstore 0x20 mstore 0x40 mstore\n{}\n0x60 mstore 0x80 mstore 0xa0 mstore\n0x200 mload 0xc0 mstore\n0xe0 0x0 return\n}}\n",
            "pop ".repeat(depth - 4),
        );
        let public_entry = huff_name(&fork, 2, "PublicCaller");
        let mut before = files;
        before.insert(public_entry.clone(), public_caller.clone());
        trial.insert(public_entry.clone(), public_caller);
        let before = compile(
            &Arc::new(Sources {
                root: root.clone(),
                files: before,
            }),
            &public_entry,
            &fork,
        )
        .unwrap();
        let after = compile(
            &Arc::new(Sources {
                root: root.clone(),
                files: trial,
            }),
            &public_entry,
            &fork,
        )
        .unwrap();
        assert_eq!(before.runtime, after.runtime);
        assert_eq!(before.initcode, after.initcode);
        let mut chain = Chain::new(&fork);
        let to = chain.deploy(after.initcode).unwrap();
        for input in &raw {
            let (out, _) = chain.call(to, words(input), &[]).unwrap();
            assert_eq!(out.len(), 224);
            let mut expected = permutation(&params, input);
            expected.extend([PRIME, PRIME, u256(0x11), u256(0x22), u256(0xbeef)]);
            assert_eq!(from_words(&out), expected);
        }
        println!(
            "T2_TERMINAL public {}: byte-identical init/runtime, {} checked calls with PRIME, caller tails and pre-touched memory",
            fork.name,
            raw.len()
        );
    }
}
