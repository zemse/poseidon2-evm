# Formal verification (Lean 4)

The goal of this directory is a kernel-checked proof that the generated runtime bytecode of the contracts (Huff t = 2, 3, 4, 8, 12, 16, 20, 24, 28; Yul t = 2, 3, 4, 8, 12 under legacy solc) returns the Poseidon2 output over BN254 for every input. The proofs are to be about the raw runtime bytes, so huff-neo, solc and the generators stay outside the trusted base.

**Status: specification only.** Nothing about any bytecode is proven yet. What exists is the Poseidon2 specification, its constants, known-answer tests against other implementations, and the EVM semantics wired in. Do not read anything here as "the contracts are formally verified".

## Layout

| Path | Contents |
| ---- | -------- |
| `Poseidon2/Spec/Permutation.lean` | The permutation, written once over an `Ops` record (zero, add, add and multiply by a constant, S-box with a threaded state), its `ZMod P` instance, `permutationWords` (inputs read modulo `P`, outputs below `P`) |
| `Poseidon2/Spec/Sponge.lean` | `hash` / `hashWords` (the t = 4 `hash_1` / `hash_2` / `hash_3`: `[x.., 0.., n · 2^64]` permuted once, element 0), the Barretenberg / Noir sponge, and proofs that the two agree for 1, 2 and 3 inputs |
| `Poseidon2/Spec/Constants/T<t>.lean` | Round numbers, round constants and internal diagonal per width, with their source in the file header |
| `Poseidon2/Spec/Vectors.lean` | 73 known-answer tests from other implementations and 3 agreement checks with this repository's reference (t = 20, 24, 28), all by `decide +kernel` |
| `Poseidon2/Spec/Grain.lean`, `GrainCheck.lean` | The HorizenLabs Grain LFSR round-constant generation in Lean, and proofs that every width's round constants are its output |
| `Poseidon2/Evm/Smoke.lean` | Shows EVMLean is wired in: decodes `PUSH1 1 PUSH1 2 ADD` and adds two words in the kernel |
| `Poseidon2/AxiomCheck.lean`, `Audit.lean` | `#assert_standard_axioms Poseidon2`: the build fails if any theorem depends on `sorry`, `native_decide` or an axiom other than `propext`, `Classical.choice`, `Quot.sound` |

Planned by later work, not present: `Evm/Eip8024.lean` (DUPN / SWAPN), `Checker/`, `Soundness.lean`, `Bytecode/`, `Theorems.lean`.

## Building

```sh
cd formal-verification
lake exe cache get   # Mathlib oleans
lake build
```

The toolchain is `leanprover/lean4:v4.29.0` (`lean-toolchain`), the one EVMLean pins; elan installs it on first use. Dependencies (`lakefile.toml`, pinned in `lake-manifest.json`):

- Mathlib `v4.29.0` (`8a17838`), the revision EVMLean's manifest pins.
- EVMLean, https://github.com/lefterislazar/EVMLean at `fd4f5e6` (the commit EquiVM pins). Only its Lean modules are built. Its lakefile also declares an `extern_lib` (C code for sha256 / keccak cloned from GitHub and compiled with `cc`, plus `git submodule update` for the Ethereum tests), but Lake links extern libraries only into executables and precompiled modules, and this package builds neither, so a plain `lake build` runs no C compiler and clones nothing. Some precompiles (BN_ADD, SNARKV, ...) shell out to `python3` when executed; that is runtime only and never happens in a proof. Logically those precompiles return `default` (`totallySafePerformIO`), so the model says nothing true about them; the Poseidon2 contracts call none.

Measured on an Apple M2 Max with 96 GB, one `lake build` of this package after the Mathlib cache and EVMLean are built: 394 s, 11.2 GB peak RSS. Nearly all of it is `GrainCheck.lean` (384 s, 11.2 GB); `Vectors.lean` takes 10 s at 4.6 GB. Building EVMLean's modules once takes about 30 s.

## Trusted base

Of what exists now:

- The Lean 4 kernel and the three standard axioms (`propext`, `Classical.choice`, `Quot.sound`), enforced by `Audit.lean`.
- The specification in `Permutation.lean` and `Sponge.lean`: that it states the Poseidon2 of the paper (https://eprint.iacr.org/2023/323) and the sponge the contracts expose. A reviewer has to read it; the known-answer tests are the evidence that it matches other implementations.
- The constant tables (see provenance below).

When bytecode proofs exist the trusted base will also include EVMLean's semantics (plus our EIP-8024 addition) and the theorem statements.

## Sorry and axiom list

None. No `sorry`, no `axiom` declared here, no `native_decide`. `Audit.lean` checks all 249 theorems under `Poseidon2` on every build.

## Constant provenance

| t | Rf / Rp | Round constants and diagonal | Cross-checked against | Test vectors |
| - | ------- | ---------------------------- | --------------------- | ------------ |
| 2 | 8 / 56 | TaceoLabs co-snarks `poseidon2_bn254_t2.rs` | noir-poseidon (round constants) | noir-poseidon (11) |
| 3 | 8 / 56 | TaceoLabs co-snarks `poseidon2_bn254_t3.rs` | noir-poseidon (round constants) | noir-poseidon (10), HorizenLabs |
| 4 | 8 / 56 | TaceoLabs co-snarks `poseidon2_bn254_t4.rs` | gnark-crypto, noir-poseidon | noir-poseidon (11), Barretenberg, co-snarks (inputs above P), noir-lang `hash_1` / `hash_2` / `hash_3`, Barretenberg sponge |
| 8 | 8 / 57 | TaceoLabs co-snarks `poseidon2_bn254_t8.rs` | gnark-crypto, noir-poseidon | noir-poseidon (11) |
| 12 | 8 / 57 | LeastAuthority TaceoLabs-nullifier-oracle-service `bn254_t12.rs` | gnark-crypto, noir-poseidon | noir-poseidon (11) |
| 16 | 8 / 57 | TaceoLabs co-snarks `poseidon2_bn254_t16.rs` | gnark-crypto, noir-poseidon | noir-poseidon (11) |
| 20 | 8 / 57 | **this repository's generator** (`generator-rs` at `93ee033`) | round constants: Grain LFSR in Lean | none external; agreement with `generator-rs/src/reference.rs` only |
| 24 | 8 / 57 | **this repository's generator** | round constants: Grain LFSR in Lean | as t = 20 |
| 28 | 8 / 59 | **this repository's generator** | round constants: Grain LFSR in Lean | as t = 20 |

- Exact URLs and commits are in each file header and next to each test. Every round constant of every width is also proven to be the Grain LFSR output of the HorizenLabs script for its t, Rf and Rp (`GrainCheck.lean`).
- For t = 2 and 3 the diagonal is `[1, 2]` and `[1, 1, 2]` (the paper's fixed internal matrices); for t >= 4 it is a random draw of the HorizenLabs script with a minimal-polynomial check.
- **Not independently referenced:** the internal diagonals for t = 20, 24, 28, and the round numbers for those widths (Rp = 59 for t = 28 comes from the script's security inequalities, which are not reproduced here). A claim about those widths is a claim about the permutation with these constants.
- The repository's generator reproduces every table for t <= 16 value for value, which was checked when the t >= 20 files were written.

## Conventions

- The state is a `List`; constants are natural numbers read in the field by `Nat.cast`.
- Contract inputs are raw 256-bit words. The spec reads each modulo `P` (`permutationWords`, `hashWords`) and returns canonical outputs (`ZMod.val`, below `P`).
- Kernel evaluation only: every computational check is `decide +kernel`. `native_decide` may only ever appear in a clearly separate development mode and never in anything a public claim depends on.
