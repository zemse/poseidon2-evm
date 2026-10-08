// Hardfork table: the EVM features the emitted code may use and the limits
// it must respect, per fork. Every fork here has EIP-170, EIP-2929 and
// STATICCALL; PUSH0 (EIP-3855) and the initcode limit (EIP-3860) arrive with
// Shanghai, DUPN / SWAPN (EIP-8024) and the larger code size (EIP-7954) with
// Amsterdam. Nothing emitted depends on Cancun (no MCOPY), Prague or Osaka,
// so their output equals Shanghai's.

export type Hardfork =
  | "paris"
  | "shanghai"
  | "cancun"
  | "prague"
  | "osaka"
  | "amsterdam";

export type Fork = {
  name: Hardfork;
  // a zero is PUSH0 (2 gas, 1 byte) instead of PUSH1 0x00 (3 gas, 2 bytes)
  push0: boolean;
  // deepest DUP / SWAP slot: 16, or 235 with DUPN / SWAPN (3 gas, 2 bytes)
  reach: number;
  // runtime code size limit of one contract
  codeSize: number;
  // initcode size limit (none before Shanghai)
  initcodeSize: number;
  // STATICCALL account access, cold (first touch in the transaction) / warm
  coldAccount: number;
  warmAccount: number;
};

const LEGACY = {
  push0: true,
  reach: 16,
  codeSize: 24576,
  initcodeSize: 49152,
  coldAccount: 2600,
  warmAccount: 100,
};

export const FORKS: Record<Hardfork, Fork> = {
  paris: { name: "paris", ...LEGACY, push0: false, initcodeSize: Infinity },
  shanghai: { name: "shanghai", ...LEGACY },
  cancun: { name: "cancun", ...LEGACY },
  prague: { name: "prague", ...LEGACY },
  osaka: { name: "osaka", ...LEGACY },
  amsterdam: {
    name: "amsterdam",
    ...LEGACY,
    reach: 235,
    codeSize: 65536,
    initcodeSize: 131072,
  },
};

// the fork the t = 2, 3, 4, 8, 12 output in src/bn254/huff/ targets
export const DEFAULT_HARDFORK: Hardfork = "shanghai";

export function fork(name: string): Fork {
  if (!(name in FORKS)) {
    throw new Error(
      `unknown hardfork: ${name} (one of ${Object.keys(FORKS).join(", ")})`,
    );
  }
  return FORKS[name as Hardfork];
}
