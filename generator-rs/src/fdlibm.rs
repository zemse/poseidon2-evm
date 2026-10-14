// Math.log and Math.log2 as node computes them: V8 (up to at least 14.1,
// node 25) implements both with the fdlibm routines of src/base/ieee754.cc,
// which differ from the platform libm in the last bit for some inputs (ln 9
// / ln 3 is 2 + 2^-51 in V8). The round-number search ceils such ratios, so
// it uses these ports, line for line, instead of f64::ln / f64::log2.
//
// clang contracts a * b + c within one C++ expression into a fused
// multiply-add on arm64 (-ffp-contract=on), so the ports do the same with
// mul_add: that reproduces node 25 on Apple silicon bit for bit (checked on
// 615,000 inputs). A node built without the contraction (x86-64) differs in
// the last bit for a few inputs; the round numbers of the Poseidon2 widths
// (t = 2, 3, 4k with alpha = 5) do not depend on it.

// the constants as written in fdlibm
#![allow(clippy::excessive_precision)]

const LG1: f64 = 6.666666666666735130e-01;
const LG2: f64 = 3.999999999940941908e-01;
const LG3: f64 = 2.857142874366239149e-01;
const LG4: f64 = 2.222219843214978396e-01;
const LG5: f64 = 1.818357216161805012e-01;
const LG6: f64 = 1.531383769920937332e-01;
const LG7: f64 = 1.479819860511658591e-01;
const TWO54: f64 = 1.80143985094819840000e+16;

fn high_word(x: f64) -> i32 {
    (x.to_bits() >> 32) as i32
}

fn low_word(x: f64) -> u32 {
    x.to_bits() as u32
}

fn with_high_word(x: f64, hi: i32) -> f64 {
    f64::from_bits((u64::from(hi as u32) << 32) | u64::from(low_word(x)))
}

fn with_low_word(x: f64, lo: u32) -> f64 {
    f64::from_bits((x.to_bits() & 0xFFFF_FFFF_0000_0000) | u64::from(lo))
}

/// a * b + c rounded once, what clang emits for a contracted a * b + c
fn fma(a: f64, b: f64, c: f64) -> f64 {
    a.mul_add(b, c)
}

/// t1 and t2 of the fdlibm log kernel: w (Lg2 + w (Lg4 + w Lg6)) and
/// z (Lg1 + w (Lg3 + w (Lg5 + w Lg7))), contracted
fn kernel(z: f64, w: f64) -> (f64, f64) {
    let t1 = w * fma(w, fma(w, LG6, LG4), LG2);
    let t2 = z * fma(w, fma(w, fma(w, LG7, LG5), LG3), LG1);
    (t1, t2)
}

/// fdlibm log (ieee754::log in V8).
pub fn log(x: f64) -> f64 {
    const LN2_HI: f64 = 6.93147180369123816490e-01;
    const LN2_LO: f64 = 1.90821492927058770002e-10;
    let mut x = x;
    let mut hx = high_word(x);
    let lx = low_word(x);
    let mut k: i32 = 0;
    if hx < 0x00100000 {
        if ((hx & 0x7FFFFFFF) as u32 | lx) == 0 {
            return f64::NEG_INFINITY;
        }
        if hx < 0 {
            return f64::NAN;
        }
        k -= 54;
        x *= TWO54;
        hx = high_word(x);
    }
    if hx >= 0x7FF00000 {
        return x + x;
    }
    k += (hx >> 20) - 1023;
    hx &= 0x000FFFFF;
    let mut i = (hx + 0x95F64) & 0x100000;
    let x = with_high_word(x, hx | (i ^ 0x3FF00000));
    k += i >> 20;
    let f = x - 1.0;
    if (0x000FFFFF & (2 + hx)) < 3 {
        if f == 0.0 {
            if k == 0 {
                return 0.0;
            }
            let dk = f64::from(k);
            return fma(dk, LN2_HI, dk * LN2_LO);
        }
        let r = f * f * fma(-0.33333333333333333, f, 0.5);
        if k == 0 {
            return f - r;
        }
        let dk = f64::from(k);
        return fma(dk, LN2_HI, -(fma(-dk, LN2_LO, r) - f));
    }
    let s = f / (2.0 + f);
    let dk = f64::from(k);
    let z = s * s;
    i = hx - 0x6147A;
    let w = z * z;
    let j = 0x6B851 - hx;
    let (t1, t2) = kernel(z, w);
    i |= j;
    let r = t2 + t1;
    if i > 0 {
        let hfsq = 0.5 * f * f;
        if k == 0 {
            f - fma(-s, hfsq + r, hfsq)
        } else {
            fma(dk, LN2_HI, -((hfsq - fma(s, hfsq + r, dk * LN2_LO)) - f))
        }
    } else if k == 0 {
        fma(-s, f - r, f)
    } else {
        fma(dk, LN2_HI, -(fma(s, f - r, -(dk * LN2_LO)) - f))
    }
}

/// log(1 + f) - f for 1 + f in ~[sqrt(2)/2, sqrt(2)]
fn k_log1p(f: f64) -> f64 {
    let s = f / (2.0 + f);
    let z = s * s;
    let w = z * z;
    let (t1, t2) = kernel(z, w);
    let r = t2 + t1;
    let hfsq = 0.5 * f * f;
    s * (hfsq + r)
}

/// fdlibm log2 (ieee754::log2 in V8).
pub fn log2(x: f64) -> f64 {
    const IVLN2HI: f64 = 1.44269504072144627571e+00;
    const IVLN2LO: f64 = 1.67517131648865118353e-10;
    let mut x = x;
    let mut hx = high_word(x);
    let lx = low_word(x);
    let mut k: i32 = 0;
    if hx < 0x00100000 {
        if ((hx & 0x7FFFFFFF) as u32 | lx) == 0 {
            return f64::NEG_INFINITY;
        }
        if hx < 0 {
            return f64::NAN;
        }
        k -= 54;
        x *= TWO54;
        hx = high_word(x);
    }
    if hx >= 0x7FF00000 {
        return x + x;
    }
    if hx == 0x3FF00000 && lx == 0 {
        return 0.0;
    }
    k += (hx >> 20) - 1023;
    hx &= 0x000FFFFF;
    let i = (hx + 0x95F64) & 0x100000;
    let x = with_high_word(x, hx | (i ^ 0x3FF00000));
    k += i >> 20;
    let y = f64::from(k);
    let f = x - 1.0;
    let hfsq = 0.5 * f * f;
    let r = k_log1p(f);
    let hi = with_low_word(f - hfsq, 0);
    let lo = (f - hi) - hfsq + r;
    let mut val_hi = hi * IVLN2HI;
    let mut val_lo = fma(lo + hi, IVLN2LO, lo * IVLN2HI);
    let w = y + val_hi;
    val_lo += (y - w) + val_hi;
    val_hi = w;
    val_lo + val_hi
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn known_values() {
        // node 25: Math.log(9), Math.log(3), Math.log(9) / Math.log(3),
        // Math.log(14) (2.6390573296152584 without the contraction)
        assert_eq!(log(14.0), 2.639057329615259);
        assert_eq!(log(9.0), 2.1972245773362196);
        assert_eq!(log(3.0), 1.0986122886681096);
        assert_eq!(log(9.0) / log(3.0), 2.0000000000000004);
        assert_eq!(log2(8.0), 3.0);
        assert_eq!(log(1.0), 0.0);
    }
}
