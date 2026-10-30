use super::*;

fn args(values: &[u32]) -> Vec<String> {
    values.iter().map(u32::to_string).collect()
}

fn make(exchange: bool) -> Pb {
    problem(&args(&[3, 2, 4, 5, 2, 16, 2, 56]), exchange)
        .unwrap()
        .0
}

fn stack(top: &[u8]) -> St {
    let mut st = St {
        len: top.len() as u8,
        s: [0; MAXD],
    };
    for (i, &v) in top.iter().rev().enumerate() {
        st.s[i] = v;
    }
    st
}

#[test]
fn exchange_move_codes_are_legal_and_invertible() {
    let mut codes = Vec::new();
    for k in 2..MAXD {
        for j in 1..k {
            let code = exchange_code(j, k).unwrap();
            assert!(j <= 14 && j + k <= 30);
            assert_eq!(exchange_pair(code), Some((j, k)));
            assert_eq!(mvname(code), format!("exchange{j},{k}"));
            codes.push(code);
        }
    }
    codes.sort_unstable();
    assert_eq!(codes, (45..=149).collect::<Vec<u8>>());
    for (j, k) in [(0, 2), (1, 1), (3, 1), (1, 16), (15, 16)] {
        assert!(exchange_code(j, k).is_none());
    }
    for code in [0, 44, 150, 255] {
        assert!(exchange_pair(code).is_none());
    }
}

#[test]
fn exchange_moves_match_three_swaps_and_preserve_disabled_moves() {
    let on = make(true);
    let off = make(false);
    for n in 0..=MAXD {
        let top: Vec<_> = on.forms.iter().take(n).map(|&f| on.enc(f, 1)).collect();
        let st = stack(&top);
        let mut enabled = Vec::new();
        let mut disabled = Vec::new();
        on.moves(&st, &mut enabled);
        off.moves(&st, &mut disabled);
        let mut count = 0;
        for &(cost, code, next) in &enabled {
            if let Some((j, k)) = exchange_pair(code) {
                count += 1;
                assert!(k < n);
                let direct = on.replay(st, &mvname(code)).unwrap();
                let swaps = off.replay(st, &format!("swap{j} swap{k} swap{j}")).unwrap();
                assert_eq!(next, swaps.state);
                assert_eq!(direct.state, swaps.state);
                assert_eq!((cost, direct.cost, swaps.cost), (3, 3, 9));
                assert_eq!(next.s[n - 1], st.s[n - 1]);
            }
        }
        assert_eq!(count, n.saturating_sub(1) * n.saturating_sub(2) / 2);
        enabled.retain(|(_, code, _)| exchange_pair(*code).is_none());
        assert_eq!(enabled, disabled);
    }
    let mut moves = Vec::new();
    on.moves(&stack(&[0, 0, 0]), &mut moves);
    assert!(!moves
        .iter()
        .any(|(_, code, _)| exchange_pair(*code).is_some()));
}

#[test]
fn incumbent_programs_and_all_suffix_bounds() {
    let programs = [
        ([3, 2, 4, 5, 1, 16, 2, 56], 56, "P P dup4 dup6 dup5 add addmod dup1 dup6 add swap4 dup1 add dup2 add swap3 add"),
        ([3, 5, 4, 2, 1, 16, 2, 64], 64, "P P dup4 dup6 dup5 add addmod P dup2 dup7 add swap5 dup1 addmod dup2 add swap3 add"),
        ([4, 5, 1, 2, 1, 16, 2, 72], 72, "P P dup4 dup6 dup5 add addmod P P dup3 dup8 addmod swap5 dup1 addmod dup2 add swap3 add"),
        ([3, 2, 4, 1, 1, 16, 2, 64], 64, "P P dup4 dup6 dup5 add addmod P dup2 dup7 add swap5 dup1 dup4 add addmod swap3 add"),
        ([1, 1, 1, 1, 1, 16, 4, 64], 64, "P dup4 dup4 dup4 add add P P dup3 dup8 addmod swap5 dup1 dup4 add addmod swap3 add"),
        ([4, 4, 1, 1, 1, 16, 2, 72], 72, "P P dup5 dup5 dup5 add addmod P P dup3 dup8 addmod swap5 dup1 dup4 add addmod swap3 add"),
    ];
    for (config, cost, program) in programs {
        for exchange in [false, true] {
            let (pb, init, _) = problem(&args(&config), exchange).unwrap();
            let replay = pb.replay(init, program).unwrap();
            pb.check_replay(&replay).unwrap();
            assert_eq!(replay.cost, cost);
            assert_eq!(pb.h(&replay.state), Some(0));
        }
    }
}

#[test]
fn malformed_configs_and_replays_are_rejected() {
    for bad in ["0", "6", "257", "-1", "not-a-bound", "4294967296"] {
        assert!(problem(&[bad.to_string()], true).is_err());
    }
    for window in [0, 3, 17, 256] {
        assert!(problem(&args(&[3, 2, 4, 5, 1, window]), true).is_err());
    }
    assert!(problem(&args(&[3, 2, 4, 5, 1, 9, 0]), true).is_err());
    assert!(problem(&args(&[1; 9]), true).is_err());
    let (pb, init, _) = problem(&args(&[3, 2, 4, 5, 1, 9, 2, 56]), true).unwrap();
    for bad in [
        "exchange0,2",
        "exchange2,1",
        "exchange1,3",
        "exchange1,16",
        "exchange1,2 extra",
        "dup0",
        "dup16",
        "swap0",
        "P P P P P P P",
        "addmod",
    ] {
        assert!(pb.replay(init, bad).is_err(), "{bad}");
    }
    assert!(pb.check_replay(&pb.replay(init, "").unwrap()).is_err());
    assert!(pb
        .check_replay(&pb.replay(init, "P P dup4").unwrap())
        .is_err());
    let off = make(false);
    assert!(off.replay(init, "exchange1,2").is_err());
    for &f in &pb.forms {
        for bound in 1..=5 {
            assert_eq!(pb.dec(pb.enc(f, bound)), (f, bound));
        }
    }
}

#[test]
fn cleanup_and_recombination_states_do_not_overcharge() {
    let pb = make(true);
    let x = pb.enc([1, 0, 0], 1);
    let b = pb.enc([0, 1, 0], 3);
    let a = pb.enc(TARGETS[0], 2);
    let o1 = pb.enc(TARGETS[1], 4);
    let o2 = pb.enc(TARGETS[2], 5);
    let displaced = stack(&[x, 0, o2, o1, b, a]);
    let done = pb.replay(displaced, "swap5").unwrap();
    pb.check_replay(&done).unwrap();
    assert_eq!((pb.h(&displaced), done.cost), (Some(0), 3));

    let mut pb = make(true);
    pb.g = 0;
    let sum = pb.enc([1, 1, 1], 1);
    let spare_prime = stack(&[x, sum, 0, 0, o2, o1]);
    let done = pb.replay(spare_prime, "addmod").unwrap();
    pb.check_replay(&done).unwrap();
    assert_eq!((pb.h(&spare_prime), done.cost), (Some(3), 8));

    let u = pb.enc([1, 1, 0], 1);
    let v = pb.enc([1, 0, 1], 1);
    let recombine = stack(&[u, v, a, 0, o2, o1]);
    let done = pb.replay(recombine, "swap2 pop add").unwrap();
    pb.check_replay(&done).unwrap();
    assert_eq!((pb.h(&recombine), done.cost), (Some(0), 8));
    assert_eq!(pb.h(&stack(&[x])), None);
}
