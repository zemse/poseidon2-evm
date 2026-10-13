import Poseidon2
import Poseidon2.AxiomCheck

/-! Fails the build if a file under `Poseidon2/` (outside `Proofs/`, which `Proofs/Audit.lean`
audits) is not imported here, if a `Poseidon2` module declares an axiom, or if any constant of a
`Poseidon2` module uses `sorry`, `native_decide` or a non-standard axiom. -/

#assert_standard_axioms Poseidon2 "Poseidon2" skipping Poseidon2.Proofs
