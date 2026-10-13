import Poseidon2
import Poseidon2.AxiomCheck

/-! Fails the build if any `Poseidon2` theorem uses `sorry`, `native_decide` or an axiom of ours. -/

#assert_standard_axioms Poseidon2
