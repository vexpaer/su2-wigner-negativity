import SU2WignerNegativity.SpinRep
import SU2WignerNegativity.SphericalHarmonicZero
import SU2WignerNegativity.EquatorialIntegral
import SU2WignerNegativity.WignerNegativity

/-!
# Universal Wigner Negativity for All Spin-j Pure States (Open Quantum Problem F18)

Root module importing the complete formalization:
- `SU2WignerNegativity.SpinRep`: Explicit unitary spin-`N/2` representation `D^{(N/2)}` of `SU(2)`
  and half-integer π-rotation orthogonality (`pi_ortho_odd`).
- `SU2WignerNegativity.SphericalHarmonicZero`: Lemma 2 — every smooth complex spherical harmonic
  of eigenvalue `λ > 0` on `S²` has a zero (`spherical_harmonic_has_zero`), proved via 1D calculus
  in spherical coordinates.
- `SU2WignerNegativity.EquatorialIntegral`: Equatorial Integral Identity (`equatorial_integral_identity`),
  integer-spin π-rotation orthogonality (`pi_ortho_even`), and Theorem 1 (`pi_ortho_all`) for all `N ≥ 1`.
- `SU2WignerNegativity.WignerNegativity`: Analytic vanishing lemma on `S²`, Lemma 1
  (`wigner_neg_of_ortho_partner`), Theorem 2 (`universal_wigner_negativity`), Corollary 1
  (`uniform_wigner_negativity_bound`), and concrete non-vacuity witness `spinHalfStratonovichWeyl`.
-/
