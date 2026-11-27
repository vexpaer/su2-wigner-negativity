import SU2WignerNegativity.AxisKernel
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.RingTheory.RootsOfUnity.Complex

/-! # Polynomial transport of an arbitrary diagonal polar kernel

A rotation through angle `2π/(N+1)` has simple spectrum on spin `N/2`.
Interpolation on that spectrum transports any prescribed real diagonal seed
to a polynomial, covariant symbol on the entire sphere.
-/

open Real Complex Polynomial Finset
open scoped Matrix
noncomputable section
namespace SU2Wigner

private def phase (N : ℕ) (k : Fin (N+1)) (t : ℝ) : ℂ :=
  Complex.exp ((2 * (k.val : ℂ) - N) * (t : ℂ) * I)

private theorem spinRep_pole (N : ℕ) (t : ℝ) :
    spinRep N (SU2.axisRot t SU2.northPole) = Matrix.diagonal (fun k => phase N k t) := by
  let g := SU2.axisRot t SU2.northPole
  have ha : g.a = Complex.exp (-(t:ℂ)*I) := by
    rw [Complex.exp_mul_I]
    simp [g, SU2.axisRot, SU2.northPole, SU2.piRot_a]
  have hb : g.b = 0 := by simp [g, SU2.axisRot, SU2.northPole, SU2.piRot_b]
  have hc : star g.a = Complex.exp ((t:ℂ)*I) := by
    rw [ha, RCLike.star_def, ← Complex.exp_conj]; simp
  ext k j
  change ((binomWeight N k : ℂ) / (binomWeight N j : ℂ)) *
    ((C g.a + C g.b * X)^(N-k.val) * (C (-star g.b) + C (star g.a)*X)^k.val).coeff j.val = _
  rw [hb, hc, ha]
  simp only [map_zero, zero_mul, add_zero, star_zero, neg_zero, zero_add, mul_pow,
    ← C_pow, ← mul_assoc, ← C_mul, coeff_C_mul_X_pow]
  by_cases h : k=j
  · subst j
    have hw : (binomWeight N k : ℂ) ≠ 0 := by exact_mod_cast (binomWeight_pos N k).ne'
    simp only [div_self hw, one_mul, ite_true, Matrix.diagonal_apply_eq, phase]
    rw [← Complex.exp_nat_mul, ← Complex.exp_nat_mul, ← Complex.exp_add]
    congr 1
    rw [Nat.cast_sub (by omega : k.val ≤ N)]; ring
  · have hj : j.val ≠ k.val := fun e => h (Fin.ext e.symm)
    simp [h,hj]

private theorem axisSymbol_pole (N : ℕ) (t : ℝ) (ψ : Fin (N+1) → ℂ) :
    axisSymbol N t ψ SU2.northPole = ∑ k, (normSq (ψ k) : ℂ) * phase N k t := by
  simp only [axisSymbol, spinRep_pole, Matrix.mulVec_diagonal, innerC, Complex.normSq_eq_conj_mul_self]
  apply Finset.sum_congr rfl; intro k _
  simp [RCLike.star_def, mul_left_comm, mul_comm, mul_assoc]

private def stepAngle (N : ℕ) : ℝ := π/(N+1)

private theorem phase_injective (N : ℕ) : Function.Injective (fun k => phase N k (stepAngle N)) := by
  let ω := Complex.exp (2 * π * I / ((N+1:ℕ):ℂ))
  have hω : IsPrimitiveRoot ω (N+1) := Complex.isPrimitiveRoot_exp _ (by omega)
  have hf (k : Fin (N+1)) : phase N k (stepAngle N) =
      Complex.exp (-(N:ℂ)*(stepAngle N:ℂ)*I) * ω^k.val := by
    unfold phase
    rw [show ω^k.val = Complex.exp ((k.val:ℂ)*(2*π*I/((N+1:ℕ):ℂ))) by
      simp [ω, Complex.exp_nat_mul], ← Complex.exp_add]
    congr 1
    simp only [stepAngle, ofReal_div, ofReal_add, ofReal_natCast, ofReal_one, Nat.cast_add, Nat.cast_one]
    ring
  intro k j h
  change phase N k _ = phase N j _ at h
  rw [hf, hf] at h
  exact Fin.ext (hω.pow_inj k.isLt j.isLt (mul_left_cancel₀ (Complex.exp_ne_zero _) h))

private def seedPoly (N : ℕ) (d : Fin (N+1) → ℝ) : Polynomial ℂ :=
  Lagrange.interpolate Finset.univ (fun k => phase N k (stepAngle N)) (fun k => (d k : ℂ))

/-- Spherical symbol determined by its real diagonal eigenvalues at the north pole. -/
def diagonalSymbol (N : ℕ) (d : Fin (N+1) → ℝ) (ψ : Fin (N+1) → ℂ) (u : S2) : ℝ :=
  let P := seedPoly N d
  (∑ m ∈ Finset.range (P.natDegree+1), P.coeff m * axisSymbol N (m*stepAngle N) ψ u).re

theorem diagonalSymbol_covariant (N : ℕ) (d : Fin (N+1) → ℝ) (g : SU2)
    (ψ : Fin (N+1) → ℂ) (u : S2) :
    diagonalSymbol N d ((spinRep N g).mulVec ψ) (SU2.actS2 g u) = diagonalSymbol N d ψ u := by
  simp only [diagonalSymbol, axisSymbol_covariant]

/-- Take the real part coefficient by coefficient before evaluating on real coordinates. -/
private def realCoefficients (P : CoordPoly) : MvPolynomial (Fin 3) ℝ :=
  ∑ e ∈ P.support, MvPolynomial.monomial e (P.coeff e).re

private theorem eval_realCoefficients (P : CoordPoly) (u : S2) :
    MvPolynomial.eval u.1 (realCoefficients P) = (evalAxis u P).re := by
  unfold realCoefficients evalAxis
  rw [map_sum, MvPolynomial.eval_eq]
  simp only [Complex.re_sum, MvPolynomial.eval_monomial, Finsupp.prod,
    ← Complex.ofReal_pow, ← Complex.ofReal_prod, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, mul_zero, sub_zero]

/-- Explicit real Cartesian polynomial for a diagonal polar seed. -/
def diagonalPolynomial (N : ℕ) (d : Fin (N+1) → ℝ) (ψ : Fin (N+1) → ℂ) :
    MvPolynomial (Fin 3) ℝ :=
  let P := seedPoly N d
  realCoefficients (∑ m ∈ range (P.natDegree+1),
    MvPolynomial.C (P.coeff m) * axisPolynomial N (m*stepAngle N) ψ)

theorem diagonalPolynomial_eval (N : ℕ) (d : Fin (N+1) → ℝ) (ψ : Fin (N+1) → ℂ) (u : S2) :
    MvPolynomial.eval u.1 (diagonalPolynomial N d ψ) = diagonalSymbol N d ψ u := by
  simp only [diagonalPolynomial, eval_realCoefficients, map_sum, map_mul, axisPolynomial_eval,
    diagonalSymbol]
  simp [evalAxis]

theorem diagonalSymbol_poly (N : ℕ) (d : Fin (N+1) → ℝ) (ψ : Fin (N+1) → ℂ) :
    ∃ Q : MvPolynomial (Fin 3) ℝ, ∀ u : S2, diagonalSymbol N d ψ u = MvPolynomial.eval u.1 Q :=
  ⟨diagonalPolynomial N d ψ, fun u => (diagonalPolynomial_eval N d ψ u).symm⟩

theorem diagonalSymbol_northPole (N : ℕ) (d : Fin (N+1) → ℝ) (ψ : Fin (N+1) → ℂ) :
    diagonalSymbol N d ψ SU2.northPole = ∑ k, d k * normSq (ψ k) := by
  let P := seedPoly N d
  have hpow (m : ℕ) (k : Fin (N+1)) :
      phase N k (m*stepAngle N) = (phase N k (stepAngle N))^m := by
    unfold phase
    rw [← Complex.exp_nat_mul, ofReal_mul, ofReal_natCast]; congr 1; ring
  have hv (k : Fin (N+1)) : P.eval (phase N k (stepAngle N)) = (d k : ℂ) :=
    Lagrange.eval_interpolate_at_node _ (phase_injective N).injOn (mem_univ _)
  have h : (∑ m ∈ range (P.natDegree+1), P.coeff m * axisSymbol N (m*stepAngle N) ψ SU2.northPole) =
      ∑ k, (d k : ℂ) * (normSq (ψ k) : ℂ) := by
    simp_rw [axisSymbol_pole, Finset.mul_sum, hpow]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro k _
    rw [← hv, eval_eq_sum_range, Finset.sum_mul]
    apply Finset.sum_congr rfl; intro m _; ring
  change (∑ m ∈ range (P.natDegree+1), P.coeff m * axisSymbol N (m*stepAngle N) ψ SU2.northPole).re = _
  rw [h]
  simp [Complex.re_sum, Complex.mul_re]

/-- In the rotated magnetic basis the symbol is precisely the weighted sum of
occupation probabilities. This identifies the interpolation with the polar kernel. -/
theorem diagonalSymbol_rotated (N : ℕ) (d : Fin (N+1) → ℝ)
    (g : SU2) (ψ : Fin (N+1) → ℂ) :
    diagonalSymbol N d ψ (SU2.actS2 g SU2.northPole) =
      ∑ k, d k * normSq (((spinRep N g⁻¹).mulVec ψ) k) := by
  have h := diagonalSymbol_covariant N d g ((spinRep N g⁻¹).mulVec ψ) SU2.northPole
  rwa [Matrix.mulVec_mulVec, ← spinRep_mul, SU2.mul_inv_cancel, spinRep_one,
    Matrix.one_mulVec, diagonalSymbol_northPole] at h

/-- Sum over any rotated magnetic basis recovers the trace of the seed. -/
theorem diagonalSymbol_sum_basis (N : ℕ) (d : Fin (N+1) → ℝ) (u : S2) :
    ∑ k : Fin (N+1), diagonalSymbol N d (Pi.single k 1) u = ∑ k, d k := by
  obtain ⟨θ, _, φ, rfl⟩ := sphVec_surjective u
  rw [← SU2.actS2_rotZ_rotY_northPole]
  simp_rw [diagonalSymbol_rotated, Matrix.mulVec_single_one, Matrix.col_apply]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro j _
  rw [← Finset.mul_sum]
  let g := (SU2.rotZ φ * SU2.rotY θ)⁻¹
  have h := congrArg (fun M : Matrix (Fin (N+1)) (Fin (N+1)) ℂ => (M j j).re)
    (spinRep_mul_conjTranspose_self N g)
  simp only [Matrix.mul_apply, Complex.re_sum, Matrix.conjTranspose_apply,
    RCLike.star_def, Complex.mul_conj, Complex.ofReal_re, Matrix.one_apply_eq, Complex.one_re] at h
  change d j * (∑ k, normSq (spinRep N g j k)) = d j
  rw [h, mul_one]

theorem swIntegral_sum {ι : Type*} [Fintype ι] (N : ℕ) (f : ι → S2 → ℝ)
    (hf : ∀ i, Continuous (fun p : ℝ × ℝ => f i (SU2.sphVec p.1 p.2))) :
    swIntegral N (fun u => ∑ i, f i u) = ∑ i, swIntegral N (f i) := by
  let F (i : ι) (θ φ : ℝ) := Real.sin θ * f i (SU2.sphVec θ φ)
  have hc (i : ι) : Continuous (Function.uncurry (F i)) :=
    (Real.continuous_sin.comp continuous_fst).mul (hf i)
  have hφ (θ : ℝ) :
      (∫ φ in (0:ℝ)..(2*π), ∑ i, F i θ φ) = ∑ i, ∫ φ in (0:ℝ)..(2*π), F i θ φ :=
    intervalIntegral.integral_finsetSum fun i _ =>
      ((hc i).comp (continuous_const.prodMk continuous_id)).intervalIntegrable _ _
  have hθ (i : ι) : Continuous (fun θ => ∫ φ in (0:ℝ)..(2*π), F i θ φ) :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' (hc i) _ _
  simp only [swIntegral, sphereAvg, Finset.mul_sum]
  change _ * (_ * (∫ θ in (0:ℝ)..π, ∫ φ in (0:ℝ)..(2*π), ∑ i, F i θ φ)) = _
  simp_rw [hφ]
  rw [intervalIntegral.integral_finsetSum fun i _ => (hθ i).intervalIntegrable _ _]
  simp [F, Finset.mul_sum]

/-- For a trace-one seed the overlap law also gives the normalization law. -/
def diagonalStratonovichWeyl {N : ℕ} (d : Fin (N+1) → ℝ) (hd : ∑ k, d k = 1)
    (hOverlap : ∀ φ ψ, swIntegral N (fun u => diagonalSymbol N d φ u * diagonalSymbol N d ψ u) =
      normSq (innerC φ ψ)) : StratonovichWeylSystem N where
  W := diagonalSymbol N d
  poly := diagonalSymbol_poly N d
  covariant := diagonalSymbol_covariant N d
  tracial := hOverlap
  norm_eq ψ := by
    let e (k : Fin (N+1)) : Fin (N+1) → ℂ := Pi.single k 1
    have h (u : S2) : diagonalSymbol N d ψ u =
        ∑ k, diagonalSymbol N d (e k) u * diagonalSymbol N d ψ u := by
      rw [← Finset.sum_mul, diagonalSymbol_sum_basis, hd, one_mul]
    have hc (v : Fin (N+1) → ℂ) :
        Continuous (fun p : ℝ × ℝ => diagonalSymbol N d v (SU2.sphVec p.1 p.2)) := by
      obtain ⟨P,hP⟩ := diagonalSymbol_poly N d v
      simp_rw [hP]; exact continuous_mvPolynomial_sphVec P
    calc
      swIntegral N (diagonalSymbol N d ψ) = _ := congrArg (swIntegral N) (funext h)
      _ = _ := swIntegral_sum N _ (fun k => (hc (e k)).mul (hc ψ))
      _ = ∑ k, normSq (innerC (e k) ψ) := by simp_rw [hOverlap]
      _ = (innerC ψ ψ).re := by
        simp [e, innerC, Pi.single_apply, Complex.re_sum, Complex.normSq_apply, Complex.mul_re,
          RCLike.star_def]

end SU2Wigner
end
