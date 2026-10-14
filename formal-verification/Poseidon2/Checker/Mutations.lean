import Poseidon2.Checker.Check
import Poseidon2.Bytecode.Huff.Amsterdam.T2
import Poseidon2.Spec.Constants.T2

/-!
# Mutation tests

The checker accepts the Huff t = 2 Amsterdam bytecode and rejects three one-byte mutations of
it, all by kernel evaluation:

* a flipped stack index: the `DUP2` at byte 224 made `DUP3`;
* a removed reduction: the `ADDMOD` at byte 476 made `ADD` (the modulus stays on the stack);
* a wrong constant: bit 0 of the last byte (273) of the `PUSH32` round constant at 241 flipped.

Each mutation first checks that the byte it changes is the one described.
-/

namespace Poseidon2.Checker.Mutations

open Poseidon2.Spec

def bytes : List Nat := Poseidon2.Bytecode.Huff.Amsterdam.T2.artifact.bytes

def accepts (bs : List Nat) : Bool :=
  (huffPermCases Constants.T2.params).all (checkCase (Code.ofBytes bs))

theorem original : accepts bytes = true := by decide +kernel

theorem dup_flipped : bytes[224]? = some 0x81 ∧ accepts (bytes.set 224 0x82) = false := by
  decide +kernel

theorem reduction_removed : bytes[476]? = some 0x08 ∧ accepts (bytes.set 476 0x01) = false := by
  decide +kernel

theorem constant_changed :
    bytes[241]? = some 0x7f ∧ accepts (bytes.set 273 ((bytes.getD 273 0) ^^^ 1)) = false := by
  decide +kernel

end Poseidon2.Checker.Mutations
