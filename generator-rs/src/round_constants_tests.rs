use super::*;
use std::process::{Child, Command, Stdio};
use std::sync::atomic::{AtomicUsize, Ordering};
use std::time::{Duration, Instant};

struct ChildGuard(Child);

impl Drop for ChildGuard {
    fn drop(&mut self) {
        let _ = self.0.kill();
        let _ = self.0.wait();
    }
}

fn bounded(name: &str, run: impl FnOnce()) {
    if std::env::var("POSEIDON2_CACHE_TEST").as_deref() == Ok(name) {
        run();
        return;
    }
    let mut child = ChildGuard(
        Command::new(std::env::current_exe().unwrap())
            .args([
                "--exact",
                &format!("round_constants::tests::{name}"),
                "--nocapture",
            ])
            .env("POSEIDON2_CACHE_TEST", name)
            .stdout(Stdio::null())
            .spawn()
            .unwrap(),
    );
    let start = Instant::now();
    loop {
        if let Some(status) = child.0.try_wait().unwrap() {
            assert!(status.success(), "{name}: {status}");
            return;
        }
        assert!(
            start.elapsed() < Duration::from_secs(30),
            "{name}: child timed out"
        );
        std::thread::sleep(Duration::from_millis(20));
    }
}

fn same(a: &Params, b: &Params) {
    assert_eq!(a.t, b.t);
    assert_eq!(a.alpha, b.alpha);
    assert_eq!(a.rounds_f, b.rounds_f);
    assert_eq!(a.rounds_p, b.rounds_p);
    assert_eq!(a.round_constants, b.round_constants);
    assert_eq!(a.internal_diag_minus_one, b.internal_diag_minus_one);
}

#[test]
fn parameter_cache_nested_rayon_request() {
    bounded("parameter_cache_nested_rayon_request", || {
        let pool = rayon::ThreadPoolBuilder::new()
            .num_threads(1)
            .build()
            .unwrap();
        let cache = Cache::default();
        let calls = AtomicUsize::new(0);
        let outer = pool.install(|| {
            cached_params(&cache, 8, || {
                calls.fetch_add(1, Ordering::Relaxed);
                let derived = generate_params_uncached(8);
                // Another request runs before this derivation is published.
                let (nested, ()) = rayon::join(
                    || {
                        cached_params(&cache, 8, || {
                            calls.fetch_add(1, Ordering::Relaxed);
                            generate_params_uncached(8)
                        })
                    },
                    || (),
                );
                same(&derived, &nested);
                derived
            })
        });
        assert_eq!(calls.load(Ordering::Relaxed), 2);
        let cached = cached_params(&cache, 8, || panic!("cached value recomputed"));
        assert!(Arc::ptr_eq(&outer, &cached));
        same(&outer, &generate_params_uncached(8));
    });
}

#[test]
fn parameter_cache_concurrent_same_width() {
    bounded("parameter_cache_concurrent_same_width", || {
        let pool = rayon::ThreadPoolBuilder::new()
            .num_threads(4)
            .build()
            .unwrap();
        let cache = Cache::default();
        let calls = AtomicUsize::new(0);
        let results: Vec<_> = pool.install(|| {
            (0..4)
                .into_par_iter()
                .map(|_| {
                    cached_params(&cache, 8, || {
                        calls.fetch_add(1, Ordering::Relaxed);
                        generate_params_uncached(8)
                    })
                })
                .collect()
        });
        assert!((1..=4).contains(&calls.load(Ordering::Relaxed)));
        let expected = generate_params_uncached(8);
        for result in &results {
            same(result, &expected);
            assert!(Arc::ptr_eq(result, &results[0]));
        }
        let global: Vec<_> =
            pool.install(|| (0..4).into_par_iter().map(|_| generate_params(8)).collect());
        for result in &global {
            same(result, &expected);
            assert!(Arc::ptr_eq(result, &global[0]));
        }
    });
}
