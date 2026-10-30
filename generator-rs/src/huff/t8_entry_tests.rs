use super::*;
use crate::field::PRIME;
use crate::huff::fork::fork;
use crate::huff::render::{entry_bytes, huff_name, render_entry, render_permutation};
use crate::huff::schedule::{describe_options, step_count};

fn check_t8_stream_entry(name: &str) {
    let fork = fork(name).unwrap();
    let params = generate_params(8);
    let mut raw = inputs(8);
    assert_eq!(raw.len(), 24);
    let p1 = PRIME - U256::from(1);
    raw.extend([vec![U256::MAX; 8], vec![PRIME; 8], vec![p1; 8]]);
    let mut mixed = vec![
        U256::MAX,
        PRIME,
        p1,
        U256::ZERO,
        U256::from(1),
        p1,
        PRIME,
        U256::MAX,
    ];
    for _ in 0..8 {
        raw.push(mixed.clone());
        mixed.rotate_left(1);
    }
    assert_eq!(raw.len(), 35);
    let clean: Vec<Vec<U256>> = raw
        .iter()
        .map(|state| state.iter().map(|&x| reduce(x)).collect())
        .collect();
    let selected = super::super::build_entry(&params, &clean, fork)
        .unwrap()
        .unwrap();
    let result = &selected.result;
    assert_eq!(result.step_bytes.len(), step_count(&params));
    assert_eq!(result.step_bytes.last(), Some(&result.bytes));
    assert!(result.step_bytes.windows(2).all(|pair| pair[0] <= pair[1]));
    assert!(result.max_depth <= 1000);
    assert!(result.max_dup <= fork.reach);
    let model = super::super::entry_gas(&fork, 8, result);
    let path = huff_name(&fork, 8, "Poseidon2");
    let permutation_path = huff_name(&fork, 8, "Permutation");
    let utils = if name == "amsterdam" {
        "../Utils.huff"
    } else {
        "../../Utils.huff"
    };
    let sources = Arc::new(Sources {
        root: Path::new(env!("CARGO_MANIFEST_DIR")).join(".."),
        files: HashMap::from([
            (
                permutation_path,
                render_permutation(&params, result, &selected.opts, utils, &fork),
            ),
            (path.clone(), render_entry(&params, &fork, result)),
        ]),
    });
    let code = compile(&sources, &path, &fork).unwrap();
    assert_eq!(
        code.runtime.len(),
        result.bytes
            + entry_bytes(
                fork,
                8,
                &result.input_slots,
                result.state_in_memory,
                result.memory
            )
    );
    assert!(code.runtime.len() <= fork.code_size);
    assert!(code.initcode.len() <= fork.initcode_size);
    if std::env::var_os("T8_ENTRY_BYTES").is_some() {
        println!("T8_RUNTIME {name} {}", hex::encode(&code.runtime));
        println!("T8_INITCODE {name} {}", hex::encode(&code.initcode));
    }
    let mut chain = Chain::new(&fork);
    let to = chain.deploy(code.initcode).unwrap();
    let mut gas = Vec::new();
    for (i, input) in raw.iter().enumerate() {
        let (out, g) = chain.call(to, words(input), &[]).unwrap();
        assert_eq!(out.len(), 256, "{name} case {i}");
        assert_eq!(
            from_words(&out),
            permutation(&params, input),
            "{name} case {i}"
        );
        assert_eq!(g, model, "{name} case {i}");
        gas.push(g);
    }
    let actual = same_gas(&gas, name).unwrap();
    println!(
        "T8_ENTRY {name}: {} reference-checked calls, {actual} gas (model {model}), {} runtime bytes, core {}, depth {}, reach {}, options {}",
        gas.len(),
        code.runtime.len(),
        result.gas,
        result.max_depth,
        result.max_dup,
        describe_options(&selected.opts),
    );
}

#[test]
fn t8_stream_entry_amsterdam() {
    check_t8_stream_entry("amsterdam");
}

#[test]
fn t8_stream_entry_osaka() {
    check_t8_stream_entry("osaka");
}

#[test]
fn t8_stream_entry_paris() {
    check_t8_stream_entry("paris");
}
