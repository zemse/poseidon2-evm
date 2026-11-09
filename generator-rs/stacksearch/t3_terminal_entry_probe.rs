// Test-only checked t3 terminal entry; the public permutation is unchanged.
use super::*;
use crate::field::{PRIME, UINT256_MAX, u256};
use crate::huff::fork::fork;
use crate::huff::render::{entry_bytes, huff_name, render_entry, render_permutation};
use crate::huff::schedule::step_count;
use crate::huff::schedule::t3_terminal_tests::{OPTIONS, SUFFIX, build_fixture};

fn raw_inputs() -> Vec<Vec<U256>> {
    let mut raw = inputs(3);
    assert_eq!(raw.len(), 24);
    let l = PRIME - u256(1);
    raw.extend([vec![UINT256_MAX; 3], vec![PRIME; 3], vec![l; 3]]);
    for lane in 0..3 {
        let mut words = vec![U256::ZERO; 3];
        words[lane] = UINT256_MAX;
        raw.push(words);
    }
    let mut mixed = vec![UINT256_MAX, PRIME, l];
    for _ in 0..3 {
        raw.push(mixed.clone());
        mixed.rotate_left(1);
    }
    raw.extend([vec![U256::ZERO, l, UINT256_MAX], vec![PRIME, U256::ZERO, l]]);
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
        assert_eq!(out.len(), 96, "{} case {i}", fork.name);
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
    for len in [0, 1, 31, 32, 33, 63, 64, 65, 95, 96, 97, 128] {
        let calldata = vec![0xff; len];
        let mut padded = calldata.clone();
        padded.resize(96, 0);
        padded.truncate(96);
        let (out, actual) = chain.call(to, calldata, &[]).unwrap();
        assert_eq!(out.len(), 96, "{} calldata length {len}", fork.name);
        assert_eq!(from_words(&out), permutation(params, &from_words(&padded)));
        assert!(from_words(&out).iter().all(|&word| word < PRIME));
        assert_eq!(actual, model);
    }
    println!(
        "T3_TERMINAL calldata {}: 12 short/exact/overlong cases passed at {model} gas",
        fork.name
    );
    code.runtime
}

#[test]
fn t3_terminal_compiled_whole_entry() {
    let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("..");
    let params = generate_params(3);
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
        let model = super::super::entry_gas(&fork, 3, &result);
        assert_eq!(model, if name == "paris" { 7646 } else { 7644 });
        let path = huff_name(&fork, 3, "Poseidon2");
        let public_path = huff_name(&fork, 3, "Permutation");
        let utils = if name == "amsterdam" {
            "../Utils.huff"
        } else {
            "../../Utils.huff"
        };
        let public = render_permutation(&params, &result, &selected.opts, utils, &fork);
        if name == "amsterdam" {
            assert_eq!(
                std::fs::read_to_string(root.join(&public_path)).unwrap(),
                public
            );
        }
        let files = HashMap::from([
            (public_path, public),
            (path.clone(), render_entry(&params, &fork, &result)),
        ]);
        let sources = Arc::new(Sources {
            root: root.clone(),
            files: files.clone(),
        });
        let code = compile(&sources, &path, &fork).unwrap();
        assert_eq!(
            code.runtime.len(),
            result.bytes + entry_bytes(fork, 3, &result.input_slots, false, 0)
        );
        assert_eq!(code.runtime.len(), if fork.push0 { 6745 } else { 6747 });
        let runtime = calls(&fork, code, &params, &raw, model);
        println!(
            "T3_TERMINAL baseline {name}: {} reference-checked calls, {model} gas, {} bytes, depth {}, dup {}",
            raw.len(),
            runtime.len(),
            result.max_depth,
            result.max_dup
        );
        baselines.push((fork, result, files, runtime, depth, model));
    }
    for (fork, original, files, runtime, depth, baseline_gas) in baselines {
        let candidate = build_fixture(&params, &clean, fork, true, 0).unwrap().0;
        let old_ops = tokens(&original.lines);
        let new_ops = tokens(&candidate.lines);
        let old_suffix: Vec<_> = "dup1 dup4 dup4 add add [PRIME] dup1 dup1 swap4 dup4 addmod swap4 dup3 addmod swap4 addmod [PRIME] swap3".split_whitespace().collect();
        let new_suffix: Vec<_> = SUFFIX.split_whitespace().collect();
        assert_eq!(&old_ops[old_ops.len() - old_suffix.len()..], old_suffix);
        assert_eq!(&new_ops[new_ops.len() - new_suffix.len()..], new_suffix);
        let last = |lines: &[String]| {
            lines
                .iter()
                .position(|line| line.contains("Round 61"))
                .unwrap()
        };
        assert_eq!(
            tokens(&original.lines[..last(&original.lines)]),
            tokens(&candidate.lines[..last(&candidate.lines)])
        );
        assert!(old_ops.iter().all(|op| !matches!(
            *op,
            "msize" | "mstore" | "mload" | "codecopy" | "calldatacopy"
        )));
        assert_eq!(
            (candidate.gas, candidate.bytes),
            (original.gas - 3, original.bytes - 96)
        );
        assert_eq!(
            (candidate.max_depth, candidate.max_dup),
            (original.max_depth, original.max_dup)
        );
        assert_eq!((candidate.max_depth, candidate.max_dup), (72, 9));
        assert!(candidate.max_depth <= 1000);
        assert!(candidate.max_dup <= fork.reach);
        assert_eq!(candidate.step_bytes.len(), step_count(&params));
        assert_eq!(&candidate.step_bytes[..62], &original.step_bytes[..62]);
        assert_eq!(candidate.step_bytes.last(), Some(&candidate.bytes));
        assert_eq!((candidate.state_in_memory, candidate.memory), (true, 96));
        let model = super::super::entry_gas(&fork, 3, &candidate);
        assert_eq!(model + 18, baseline_gas);
        let path = huff_name(&fork, 3, "Poseidon2");
        let public_path = huff_name(&fork, 3, "Permutation");
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
            candidate.bytes + entry_bytes(fork, 3, &candidate.input_slots, true, 96)
        );
        assert_eq!(code.runtime.len(), if fork.push0 { 6643 } else { 6645 });
        assert_eq!(code.runtime.len() + 102, runtime.len());
        // the same code up to the last round
        let common = runtime
            .iter()
            .zip(&code.runtime)
            .take_while(|(a, b)| a == b)
            .count();
        assert!(common + (original.bytes - original.step_bytes[61]) + 64 >= runtime.len());
        let bytes = calls(&fork, code, &params, &raw, model).len();
        println!(
            "T3_TERMINAL candidate {}: {} reference-checked calls, {model} gas, {bytes} bytes, saving {}, depth {}, dup {}",
            fork.name,
            raw.len(),
            baseline_gas - model,
            candidate.max_depth,
            candidate.max_dup
        );

        // Pre-touched memory and distinct tails exercise the public macro,
        // not the private terminal entry's empty-memory assumption.
        let public_caller = format!(
            "#include \"./Permutation.huff\"\n#define macro MAIN() = {{\n0xbeef 0x200 mstore\n0x22 0x11 SETUP()\ndup1 0x40 calldataload mod\ndup2 0x20 calldataload mod\ndup3 0x0 calldataload mod\nPOSEIDON2_PERMUTATION()\n0x0 mstore 0x20 mstore 0x40 mstore 0x60 mstore\n{}\n0x80 mstore 0xa0 mstore\n0x200 mload 0xc0 mstore\n0xe0 0x0 return\n}}\n",
            "pop ".repeat(depth - 4),
        );
        let public_entry = huff_name(&fork, 3, "PublicCaller");
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
            expected.extend([PRIME, u256(0x11), u256(0x22), u256(0xbeef)]);
            assert_eq!(from_words(&out), expected);
        }
        println!(
            "T3_TERMINAL public {}: byte-identical init/runtime, {} checked calls with PRIME, caller tails and pre-touched memory",
            fork.name,
            raw.len()
        );
    }
}

#[test]
fn t3_terminal_production_compiled_whole_entry() {
    let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("..");
    let params = generate_params(3);
    let raw = raw_inputs();
    let clean: Vec<Vec<U256>> = raw
        .iter()
        .map(|input| input.iter().map(|&word| reduce(word)).collect())
        .collect();
    for name in ["amsterdam", "osaka", "paris"] {
        let fork = fork(name).unwrap();
        let plan = super::super::build_entry_plan(&params, &clean, fork)
            .unwrap()
            .unwrap();
        let original = &plan.permutation().result;
        let selected = plan.terminal_result().expect("selected t3 terminal entry");
        let (fixture, _) = build_fixture(&params, &clean, fork, true, 0).unwrap();
        let (_, depth) = build_fixture(&params, &clean, fork, false, 0).unwrap();
        assert_eq!(tokens(&selected.lines), tokens(&fixture.lines));
        let baseline_gas = super::super::entry_gas(&fork, 3, original);
        let model = super::super::entry_gas(&fork, 3, selected);
        assert_eq!(baseline_gas, if fork.push0 { 7644 } else { 7646 });
        assert_eq!(model + 18, baseline_gas);
        let path = huff_name(&fork, 3, "Poseidon2");
        let public_path = huff_name(&fork, 3, "Permutation");
        let utils = if name == "amsterdam" {
            "../Utils.huff"
        } else {
            "../../Utils.huff"
        };
        let public = render_permutation(&params, original, &plan.permutation().opts, utils, &fork);
        let mut baseline = HashMap::from([
            (path.clone(), render_entry(&params, &fork, original)),
            (public_path.clone(), public.clone()),
        ]);
        let width = super::super::generate(3, &fork).unwrap();
        assert!(matches!(&width.target, super::super::Target::Entry { gas, .. } if *gas == model));
        let mut generated: HashMap<String, String> = width
            .files()
            .map(|(path, text)| (path.to_string(), text.to_string()))
            .collect();
        assert_eq!(generated[&public_path], public);
        assert!(generated[&path].contains("outputs stored at [0, 0x60)"));
        let compile_files = |files: &HashMap<String, String>, path: &str| {
            compile(
                &Arc::new(Sources {
                    root: root.clone(),
                    files: files.clone(),
                }),
                path,
                &fork,
            )
            .unwrap()
        };
        let canonical = compile_files(&baseline, &path);
        let baseline_runtime = calls(&fork, canonical, &params, &raw, baseline_gas);
        let mut fixture_files = baseline.clone();
        fixture_files.insert(
            path.clone(),
            render_entry(&params, &fork, &fixture).replacen(
                "POSEIDON2_PERMUTATION()",
                &fixture.lines.join("\n"),
                1,
            ),
        );
        let checked = compile_files(&fixture_files, &path);
        let production = compile_files(&generated, &path);
        assert_eq!(production.runtime, checked.runtime);
        assert_eq!(production.initcode, checked.initcode);
        assert_eq!(
            production.runtime.len(),
            if fork.push0 { 6643 } else { 6645 }
        );
        assert_eq!(production.runtime.len() + 102, baseline_runtime.len());
        assert_eq!(
            production.runtime.len(),
            selected.bytes + entry_bytes(fork, 3, &selected.input_slots, true, 96)
        );
        let runtime = calls(&fork, production, &params, &raw, model);
        println!(
            "T3_PRODUCTION {name}: {} reference-checked calls, {model} gas, {} runtime bytes, fixture-identical init/runtime",
            raw.len(),
            runtime.len()
        );
        let caller = huff_name(&fork, 3, "ProductionPublicCaller");
        let source = format!(
            "#include \"./Permutation.huff\"\n#define macro MAIN() = {{\n0xbeef 0x200 mstore\n0x22 0x11 SETUP()\ndup1 0x40 calldataload mod\ndup2 0x20 calldataload mod\ndup3 0x0 calldataload mod\nPOSEIDON2_PERMUTATION()\n0x0 mstore 0x20 mstore 0x40 mstore 0x60 mstore\n{}\n0x80 mstore 0xa0 mstore\n0x200 mload 0xc0 mstore\n0xe0 0x0 return\n}}\n",
            "pop ".repeat(depth - 4)
        );
        baseline.insert(caller.clone(), source.clone());
        generated.insert(caller.clone(), source);
        let before = compile_files(&baseline, &caller);
        let after = compile_files(&generated, &caller);
        assert_eq!(before.runtime, after.runtime);
        assert_eq!(before.initcode, after.initcode);
        let mut chain = Chain::new(&fork);
        let to = chain.deploy(after.initcode).unwrap();
        for input in &raw {
            let (out, _) = chain.call(to, words(input), &[]).unwrap();
            let mut expected = permutation(&params, input);
            expected.extend([PRIME, u256(0x11), u256(0x22), u256(0xbeef)]);
            assert_eq!(out.len(), 224);
            assert_eq!(from_words(&out), expected);
        }
        println!(
            "T3_PRODUCTION public {name}: {} calls, byte identity, PRIME, tails and pre-touched memory preserved",
            raw.len()
        );
    }
}
