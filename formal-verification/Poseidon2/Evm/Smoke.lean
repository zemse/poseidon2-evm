import Ethereum.Semantics

/-!
# EVMLean wiring check

Shows that EVMLean (lefterislazar/EVMLean at the commit pinned in `lakefile.toml`)
is imported and that its decoder and word arithmetic reduce in the kernel on a
tiny program, `PUSH1 1 PUSH1 2 ADD`. This proves nothing about Poseidon2.
-/

namespace Poseidon2.Evm.Smoke

open Ethereum

/-- `PUSH1 0x01 PUSH1 0x02 ADD` -/
def code : ByteArray := ⟨#[0x60, 0x01, 0x60, 0x02, 0x01]⟩

theorem decode_pc0 :
    EVM.decode code (.ofNat 0) = some (Operation.PUSH1, some (.ofNat 1, 1)) := by
  decide +kernel

theorem decode_pc2 :
    EVM.decode code (.ofNat 2) = some (Operation.PUSH1, some (.ofNat 2, 1)) := by
  decide +kernel

theorem decode_pc4 : EVM.decode code (.ofNat 4) = some (Operation.ADD, none) := by
  decide +kernel

theorem add_1_2 : UInt256.add (.ofNat 2) (.ofNat 1) = .ofNat 3 := by
  decide +kernel

end Poseidon2.Evm.Smoke
