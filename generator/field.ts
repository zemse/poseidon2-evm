// BN254 scalar field arithmetic on BigInt.

export const PRIME =
  0x30644e72e131a029b85045b68181585d2833e84879b9709143e1f593f0000001n;

export const UINT256_MAX = (1n << 256n) - 1n;

export function mod(a: bigint): bigint {
  const r = a % PRIME;
  return r < 0n ? r + PRIME : r;
}

export function add(a: bigint, b: bigint): bigint {
  return mod(a + b);
}

export function mul(a: bigint, b: bigint): bigint {
  return mod(a * b);
}

export function pow(base: bigint, exp: bigint): bigint {
  let result = 1n;
  let b = mod(base);
  let e = exp;
  while (e > 0n) {
    if (e & 1n) result = mul(result, b);
    b = mul(b, b);
    e >>= 1n;
  }
  return result;
}

export function inv(a: bigint): bigint {
  if (mod(a) === 0n) throw new Error("inverse of zero");
  return pow(a, PRIME - 2n);
}

export function hex(value: bigint): string {
  return "0x" + value.toString(16).padStart(64, "0");
}
