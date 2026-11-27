import SU2WignerNegativity
import Lean.Util.CollectAxioms

open Lean in
run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for decl in #[``SU2Wigner.pi_ortho_all, ``SU2Wigner.universal_wigner_negativity,
      ``SU2Wigner.uniform_wigner_negativity_bound, ``SU2Wigner.spinHalfStratonovichWeyl,
      ``SU2Wigner.spinOneStratonovichWeyl, ``SU2Wigner.spinOne_eq_diagonal,
      ``SU2Wigner.canonicalSpinOne_negativity, ``SU2Wigner.probeGram_criterion,
      ``SU2Wigner.coherent_expectation_injective, ``SU2Wigner.coherentSymbol_norm,
      ``SU2Wigner.sphereAvg_sq_pos, ``SU2Wigner.sphereAvg_actS2_poly,
      ``SU2Wigner.gramMatrix_comm_adMatrix, ``SU2Wigner.canonicalStratonovichWeyl,
      ``SU2Wigner.canonical_universal_wigner_negativity,
      ``SU2Wigner.canonical_uniform_wigner_negativity_bound] do
    let axioms ← collectAxioms decl
    for ax in axioms do
      unless allowed.contains ax do
        throwError "{decl} depends on unexpected axiom {ax}"
    logInfo m!"{decl}: {axioms}"
