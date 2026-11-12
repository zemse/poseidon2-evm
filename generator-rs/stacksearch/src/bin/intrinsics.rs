// Single-threaded floors for the search's hash, stack copy and memory access.
use std::hint::black_box;
use std::time::Instant;

fn median(mut run: impl FnMut() -> f64) -> f64 {
    run();
    let mut samples: Vec<f64> = (0..15).map(|_| run()).collect();
    samples.sort_by(f64::total_cmp);
    samples[7]
}

fn main() {
    let n = 1_000_000u64;
    let hash_ns = median(|| {
        let start = Instant::now();
        let mut key = black_box(42u64);
        for _ in 0..n {
            key = key
                .wrapping_mul(0x9E3779B97F4A7C15)
                .rotate_left(23)
                .wrapping_mul(0xD6E8FEB86659FD93);
        }
        black_box(key);
        start.elapsed().as_nanos() as f64 / n as f64
    });
    let copy_ns = median(|| {
        let start = Instant::now();
        let mut stack = [0u8; 19];
        for _ in 0..n {
            let mut copy = black_box(stack);
            copy[0] = copy[0].wrapping_add(1);
            stack = black_box(copy);
        }
        black_box(stack);
        start.elapsed().as_nanos() as f64 / n as f64
    });
    println!("{{\"hash_ns\":{hash_ns},\"stack_copy_ns\":{copy_ns}}}");
    for mib in [128, 768] {
        let len = mib * 1024 * 1024 / 8;
        let mut order: Vec<usize> = (0..len).collect();
        let mut random = 42u64;
        for i in (1..len).rev() {
            random ^= random << 13;
            random ^= random >> 7;
            random ^= random << 17;
            order.swap(i, random as usize % (i + 1));
        }
        let mut data = vec![0u64; len];
        for i in 0..len {
            data[order[i]] = order[(i + 1) % len] as u64;
        }
        drop(order);
        let scan_ns = median(|| {
            let start = Instant::now();
            let sum = black_box(&data)
                .iter()
                .fold(0u64, |s, &v| s.wrapping_add(v));
            black_box(sum);
            start.elapsed().as_nanos() as f64
        });
        let lookup_ns = median(|| {
            let start = Instant::now();
            let mut index = black_box(42usize);
            for _ in 0..n {
                index = data[index % len] as usize;
            }
            black_box(index);
            start.elapsed().as_nanos() as f64 / n as f64
        });
        let gb_s = (len * 8) as f64 / scan_ns;
        println!("{{\"working_set_mib\":{mib},\"scan_gb_s\":{gb_s},\"dependent_lookup_ns\":{lookup_ns}}}");
    }
}
