// Port of poseidon_calc_final_numbers_fixed (HorizenLabs poseidon2_rust_params.sage @ bb476b9), BN254, alpha 5, M 128
const p = 0x30644e72e131a029b85045b68181585d2833e84879b9709143e1f593f0000001n;
const log2p = blog2(p);
const FIELD_SIZE = p.toString(2).length;
const logb = (x, b) => Math.log(x) / Math.log(b);
function binom(n, k) { let r = 1n; for (let i = 0n; i < k; i++) { r = r * (n - i) / (i + 1n); if (2n * k <= n && r >= (1n << 64n)) return r; } return r; } // C(n,i) grows in i for i <= n/2: early exit once >= 2^64 cannot change ceil(2 log2) >= 128
function blog2(x) { const s = x.toString(2); const hi = Number(BigInt('0b' + s.slice(0, 53))); return s.length - 53 + Math.log2(hi); }
function sat(t, RF, RP, alpha, M) {
  const RF1 = M <= Math.floor(log2p - (alpha - 1) / 2) * (t + 1) ? 6 : 10;
  const RF2 = 1 + Math.ceil(logb(2, alpha) * Math.min(M, FIELD_SIZE)) + Math.ceil(logb(t, alpha)) - RP;
  const RF3 = logb(2, alpha) * Math.min(M, log2p) - RP;
  const RF4 = t - 1 + logb(2, alpha) * Math.min(M / (t + 1), log2p / 2) - RP;
  const RF5 = (t - 2 + M / (2 * logb(alpha, 2)) - RP) / (t - 1);
  const RFmax = Math.max(Math.ceil(RF1), Math.ceil(RF2), Math.ceil(RF3), Math.ceil(RF4), Math.ceil(RF5));
  if (RF < RFmax) return false; // short circuit, same result
  const r = Math.floor(t / 3);
  const over = (RF - 1) * t + RP + r + r * (RF / 2) + RP + alpha;
  const under = r * (RF / 2) + RP + alpha;
  const bl = blog2(binom(BigInt(over), BigInt(under)));
  return RF >= RFmax && Math.ceil(2 * bl) >= M;
}
function find(t, alpha, M) {
  let RP = 0, RF = 0, min = Infinity, maxrf = 0;
  for (let RPt0 = 1; RPt0 < 500; RPt0++) { let RPt = RPt0; for (let RFt0 = 4; RFt0 < 100; RFt0++) {
    let RFt = RFt0;
    if (RFt % 2 === 0 && sat(t, RFt, RPt, alpha, M)) {
      RFt += 2; RPt = Math.ceil(RPt * 1.075);
      const cost = t * RFt + RPt;
      if (cost < min || (cost === min && RFt < maxrf)) { RP = RPt; RF = RFt; min = cost; maxrf = RF; }
    }
  }}
  return [RF, RP];
}
console.log('FIELD_SIZE', FIELD_SIZE, 'log2p', log2p);
for (const t of [2, 3, 4, 8, 12, 16, 20, 24, 28]) console.log(t, find(t, 5, 128).join('/'));
