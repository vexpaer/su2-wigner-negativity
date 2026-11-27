import SU2WignerNegativity.DiagonalKernel
import SU2WignerNegativity.SphereMoments

/-! # Explicit self-dual spin-one symbols
The two independent signs select the rank-one and rank-two multipoles.
-/
open Real Complex Finset Polynomial
open scoped Matrix

noncomputable section
namespace SU2Wigner

private abbrev Features := Fin 10 → ℝ

-- Monomial order: 1, x, y, z, x², y², z², xy, xz, yz.
private def ex : Fin 10 → ℕ := ![0,1,0,0,2,0,0,1,1,0]
private def ey : Fin 10 → ℕ := ![0,0,1,0,0,2,0,1,0,1]
private def ez : Fin 10 → ℕ := ![0,0,0,1,0,0,2,0,1,1]
private def quad (v : Features) (u : S2) : ℝ :=
  ∑ i, v i * sphereMonomial (ex i) (ey i) (ez i) u

private theorem quad_avg (v : Features) :
    sphereAvg (quad v) = v 0 + (v 4 + v 5 + v 6)/3 := by
  unfold quad
  rw [sphereAvg_expansion]
  norm_num [Fin.sum_univ_succ, ex, ey, ez, cartesianMoment, circleMoment, cosMoment, polarMoment]
  ring

private theorem quad_gram (v w : Features) :
    sphereAvg (fun u => quad v u * quad w u) =
      v 0*w 0 + (v 0*(w 4+w 5+w 6) + w 0*(v 4+v 5+v 6) + v 1*w 1+v 2*w 2+v 3*w 3)/3
      + (v 4*w 4+v 5*w 5+v 6*w 6)/5
      + (v 4*(w 5+w 6)+v 5*(w 4+w 6)+v 6*(w 4+w 5)+v 7*w 7+v 8*w 8+v 9*w 9)/15 := by
  let a (p : Fin 10 × Fin 10) := ex p.1 + ex p.2
  let b (p : Fin 10 × Fin 10) := ey p.1 + ey p.2
  let c (p : Fin 10 × Fin 10) := ez p.1 + ez p.2
  let weight (p : Fin 10 × Fin 10) := v p.1 * w p.2
  have h (u : S2) : quad v u * quad w u =
      ∑ p, weight p * sphereMonomial (a p) (b p) (c p) u := by
    rw [Fintype.sum_prod_type]
    unfold quad
    rw [Finset.sum_mul]
    simp only [Finset.mul_sum, sphereMonomial, a,b,c,weight,pow_add]
    apply Finset.sum_congr rfl; intro i _
    apply Finset.sum_congr rfl; intro j _
    ring
  simp_rw [h]
  rw [sphereAvg_expansion, Fintype.sum_prod_type]
  norm_num [a,b,c,weight,Fin.sum_univ_succ, ex,ey,ez,cartesianMoment,circleMoment,cosMoment,polarMoment]
  ring

-- The coordinate expression of the scalar, dipole and traceless quadrupole terms.
private def spinOneFeatures (s t : ℝ) (ψ : Fin 3 → ℂ) : Features :=
  let a := ψ 0; let b := ψ 1; let c := ψ 2
  let ab := star a*b; let bc := star b*c; let ac := star a*c
  let d := (normSq a + normSq c)/2 - normSq b
  let q := t * Real.sqrt 10 / 6
  ![(normSq a + normSq b + normSq c)/3 - q*d,
    s*(ab.re+bc.re), s*(ab.im+bc.im), s*Real.sqrt 2/2*(normSq a-normSq c),
    3*q*ac.re, -3*q*ac.re, 3*q*d, 6*q*ac.im,
    3*Real.sqrt 2*q*(ab.re-bc.re), 3*Real.sqrt 2*q*(ab.im-bc.im)]

private theorem spinOne_norm (s t : ℝ) (ψ : Fin 3 → ℂ) :
    swIntegral 2 (quad (spinOneFeatures s t ψ)) = (innerC ψ ψ).re := by
  rw [swIntegral, quad_avg]
  simp [spinOneFeatures, innerC, Fin.sum_univ_succ, Complex.normSq_apply, Complex.mul_re,
    RCLike.star_def]
  ring

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
private theorem spinOne_trace (s t : ℝ) (hs : s^2=1) (ht : t^2=1) (φ ψ : Fin 3 → ℂ) :
    swIntegral 2 (fun u => quad (spinOneFeatures s t φ) u * quad (spinOneFeatures s t ψ) u) =
      Complex.normSq (innerC φ ψ) := by
  rw [swIntegral, quad_gram]
  simp [spinOneFeatures, innerC, Fin.sum_univ_succ, Complex.normSq_apply, Complex.mul_re,
    Complex.mul_im, RCLike.star_def]
  ring_nf
  simp [hs, ht, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2), Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 10)]
  ring

private theorem spinRep_two (g : SU2) : spinRep 2 g =
    !![g.a^2, (Real.sqrt 2 : ℂ)*g.a*g.b, g.b^2;
      -(Real.sqrt 2 : ℂ)*g.a*star g.b, g.a*star g.a-g.b*star g.b, (Real.sqrt 2 : ℂ)*g.b*star g.a;
      (star g.b)^2, -(Real.sqrt 2 : ℂ)*star g.b*star g.a, (star g.a)^2] := by
  have hr : (Real.sqrt 2 : ℂ)^2 = 2 := by exact_mod_cast Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)
  have hn : (Real.sqrt 2 : ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.mpr (by norm_num : (0:ℝ)<2)).ne'
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [spinRep, rawRep, polyStep, binomWeight, Nat.choose, pow_two, coeff_X, coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, Finset.sum_range_succ, hn] <;>
    field_simp [hn] <;> ring_nf <;> simp [hr]

-- A quarter turn has real part I − Jᵤ² and imaginary part −Jᵤ in spin one.
private def spinOneSymbol (s t : ℝ) (ψ : Fin 3 → ℂ) (u : S2) : ℝ :=
  (1/3 + t * Real.sqrt 10/6) * (innerC ψ ψ).re -
    s*Real.sqrt 2/2 * (axisSymbol 2 (π/4) ψ u).im -
    t*Real.sqrt 10/2 * (axisSymbol 2 (π/4) ψ u).re

set_option maxRecDepth 8192 in
set_option maxHeartbeats 3000000 in
private theorem spinOneSymbol_eq (s t : ℝ) (ψ : Fin 3 → ℂ) (u : S2) :
    spinOneSymbol s t ψ u = quad (spinOneFeatures s t ψ) u := by
  have hy : u.1 1 ^ 2 = 1 - u.1 0 ^ 2 - u.1 2 ^ 2 := by
    have h := u.2; unfold dot3 at h; nlinarith [h]
  have sr (z : ℂ) : (z^2).re = z.re*z.re-z.im*z.im := by rw [pow_two, Complex.mul_re]
  have si (z : ℂ) : (z^2).im = z.re*z.im+z.im*z.re := by rw [pow_two, Complex.mul_im]
  have h2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have h3 : Real.sqrt 2 ^ 3 = 2 * Real.sqrt 2 := by rw [pow_succ, h2]
  have h4 : Real.sqrt 2 ^ 4 = 4 := by rw [show (4:ℕ) = 2*2 by decide,pow_mul,h2]; norm_num
  simp only [spinOneSymbol, axisSymbol, spinRep_two, innerC, Matrix.mulVec, dotProduct]
  simp [quad, spinOneFeatures, sphereMonomial, ex,ey,ez, Fin.sum_univ_succ, SU2.axisRot,
    Real.sin_pi_div_four, Real.cos_pi_div_four, SU2.piRot_a, SU2.piRot_b, Complex.normSq_apply,
    Complex.mul_re, Complex.mul_im, sr, si, RCLike.star_def]
  ring_nf
  simp [h2,h3,h4,hy]
  ring

/-- Spin-one self-dual kernel with independently chosen dipole and quadrupole signs. -/
def spinOneStratonovichWeyl (s t : ℝ) (hs : s^2 = 1) (ht : t^2 = 1) :
    StratonovichWeylSystem 2 where
  W := spinOneSymbol s t
  poly ψ := by
    obtain ⟨A,B,h⟩ := axisSymbol_poly 2 (π/4) ψ
    use MvPolynomial.C ((1/3 + t*Real.sqrt 10/6)*(innerC ψ ψ).re) -
      MvPolynomial.C (s*Real.sqrt 2/2)*B - MvPolynomial.C (t*Real.sqrt 10/2)*A
    intro u
    simp [spinOneSymbol, (h u).1, (h u).2]
  norm_eq ψ := by
    simpa only [funext (spinOneSymbol_eq s t ψ)] using spinOne_norm s t ψ
  covariant g ψ u := by
    simp only [spinOneSymbol, innerC_spinRep_unitary, axisSymbol_covariant]
  tracial φ ψ := by
    simpa only [spinOneSymbol_eq] using spinOne_trace s t hs ht φ ψ

/-- Polar eigenvalues in the order `m = 1, 0, -1`. -/
def spinOnePoleWeights (s t : ℝ) : Fin 3 → ℝ :=
  ![1/3 + s*Real.sqrt 2/2 + t*Real.sqrt 10/6, 1/3 - t*Real.sqrt 10/3,
    1/3 - s*Real.sqrt 2/2 + t*Real.sqrt 10/6]

theorem spinOne_eq_diagonal (s t : ℝ) (hs : s^2 = 1) (ht : t^2 = 1)
    (ψ : Fin 3 → ℂ) (u : S2) :
    (spinOneStratonovichWeyl s t hs ht).W ψ u = diagonalSymbol 2 (spinOnePoleWeights s t) ψ u := by
  let sw := spinOneStratonovichWeyl s t hs ht
  have hPole (v : Fin 3 → ℂ) : sw.W v SU2.northPole =
      ∑ k, spinOnePoleWeights s t k * normSq (v k) := by
    change spinOneSymbol s t v _ = _
    rw [spinOneSymbol_eq]
    simp [quad, spinOneFeatures, sphereMonomial, spinOnePoleWeights, SU2.northPole,
      ex,ey,ez, Fin.sum_univ_succ]
    ring
  obtain ⟨θ, _, φ, rfl⟩ := sphVec_surjective u
  rw [← SU2.actS2_rotZ_rotY_northPole, diagonalSymbol_rotated]
  let g := SU2.rotZ φ * SU2.rotY θ
  have h := sw.covariant g ((spinRep 2 g⁻¹).mulVec ψ) SU2.northPole
  rwa [Matrix.mulVec_mulVec, ← spinRep_mul, SU2.mul_inv_cancel, spinRep_one,
    Matrix.one_mulVec, hPole] at h

/-- The canonical positive-multipole-sign choice, with no kernel hypotheses. -/
def canonicalSpinOne : StratonovichWeylSystem 2 :=
  spinOneStratonovichWeyl 1 1 (by norm_num) (by norm_num)

theorem canonicalSpinOne_negativity (ψ : Fin 3 → ℂ) (hψ : innerC ψ ψ = 1) :
    ∃ u : S2, canonicalSpinOne.W ψ u < 0 :=
  universal_wigner_negativity (by decide) canonicalSpinOne hψ

end SU2Wigner
end
