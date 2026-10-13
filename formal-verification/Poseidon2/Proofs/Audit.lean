import Poseidon2.AxiomCheck
import Poseidon2.Proofs.Deployed.HuffV2
import Poseidon2.Proofs.Deployed.YulV2
import Poseidon2.Proofs.Huff.Amsterdam.T2
import Poseidon2.Proofs.Huff.Amsterdam.T3
import Poseidon2.Proofs.Huff.Amsterdam.T4
import Poseidon2.Proofs.Huff.Osaka.T2
import Poseidon2.Proofs.Huff.Osaka.T3
import Poseidon2.Proofs.Huff.Osaka.T4
import Poseidon2.Proofs.Yul.OptimizerOff.T2
import Poseidon2.Proofs.Yul.OptimizerOff.T3
import Poseidon2.Proofs.Yul.OptimizerOff.T4
import Poseidon2.Proofs.Yul.Runs1000000.T2
import Poseidon2.Proofs.Yul.Runs1000000.T3
import Poseidon2.Proofs.Yul.Runs1000000.T4
import Poseidon2.Proofs.Yul.Runs200.T2
import Poseidon2.Proofs.Yul.Runs200.T3
import Poseidon2.Proofs.Yul.Runs200.T4

/-! Fails the build of `Poseidon2Proofs` if a file under `Poseidon2/Proofs/` is not imported here,
declares an axiom, or depends on `sorry`, `native_decide` or a non-standard axiom. -/

#assert_standard_axioms Poseidon2.Proofs "Poseidon2/Proofs"
