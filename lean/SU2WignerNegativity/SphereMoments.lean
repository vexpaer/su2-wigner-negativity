import SU2WignerNegativity.WignerNegativity
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! # Exact Cartesian moments of the sphere

The recursions evaluate polynomials against the same spherical-coordinate
integral used in the Stratonovich–Weyl normalization and overlap laws.
-/

open Real MeasureTheory intervalIntegral
noncomputable section
namespace SU2Wigner

def cosMoment : ℕ → ℝ
  | 0 => 1
  | n+1 => (2*(n:ℝ)+1)/(2*n+2) * cosMoment n

def circleMoment (p q : ℕ) : ℝ :=
  match q with
  | 0 => cosMoment p
  | q+1 => circleMoment p q - circleMoment (p+1) q

def polarMoment (p k : ℕ) : ℝ :=
  match p with
  | 0 => (1 - (-1:ℝ)^(k+1))/(k+1)
  | p+1 => polarMoment p k - polarMoment p (k+2)

private theorem integral_cos_even (p : ℕ) :
    (∫ x in (0:ℝ)..(2*π), cos x ^ (2*p)) = (2*π)*cosMoment p := by
  induction p with
  | zero => simp [cosMoment]
  | succ p ih =>
    rw [Nat.mul_succ, integral_cos_pow, ih]
    simp [cosMoment, Real.sin_two_pi]
    ring

private theorem integral_circle_even (p q : ℕ) :
    (∫ x in (0:ℝ)..(2*π), cos x ^ (2*p) * sin x ^ (2*q)) =
      (2*π) * circleMoment p q := by
  induction q generalizing p with
  | zero => simpa [circleMoment] using integral_cos_even p
  | succ q ih =>
    have he (x : ℝ) : cos x ^ (2*p) * sin x ^ (2*(q+1)) =
        cos x ^ (2*p) * sin x ^ (2*q) - cos x ^ (2*(p+1)) * sin x ^ (2*q) := by
      rw [Nat.mul_succ, Nat.mul_succ, pow_add, Real.sin_sq, pow_add]; ring
    simp_rw [he]
    rw [intervalIntegral.integral_sub, ih, ih, circleMoment, mul_sub] <;>
      apply Continuous.intervalIntegrable <;> fun_prop

private theorem integral_polar (p k : ℕ) :
    (∫ z in (-1:ℝ)..1, z^k * (1-z^2)^p) = polarMoment p k := by
  induction p generalizing k with
  | zero => simp [polarMoment, integral_pow]
  | succ p ih =>
    have he (z : ℝ) : z^k * (1-z^2)^(p+1) =
        z^k * (1-z^2)^p - z^(k+2) * (1-z^2)^p := by rw [pow_succ, pow_add]; ring
    simp_rw [he]
    rw [intervalIntegral.integral_sub, ih, ih, polarMoment] <;>
      apply Continuous.intervalIntegrable <;> fun_prop

/-- Normalized spherical moment of `x^a y^b z^c`. -/
def cartesianMoment (a b c : ℕ) : ℝ :=
  if a % 2 = 0 ∧ b % 2 = 0 then
    circleMoment (a/2) (b/2) * polarMoment ((a+b)/2) c / 2
  else 0

def sphereMonomial (a b c : ℕ) (u : S2) : ℝ := u.1 0 ^ a * u.1 1 ^ b * u.1 2 ^ c

private theorem monomial_separate (a b c : ℕ) :
    sphereAvg (sphereMonomial a b c) = (1/(4*π)) *
      (∫ θ in (0:ℝ)..π, sin θ^(a+b+1)*cos θ^c) *
      (∫ φ in (0:ℝ)..(2*π), cos φ^a*sin φ^b) := by
  unfold sphereAvg sphereMonomial
  simp only [SU2.sphVec, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.tail_cons, Matrix.head_cons]
  have he (θ φ : ℝ) : sin θ * ((sin θ * cos φ)^a * (sin θ * sin φ)^b * cos θ^c) =
      (sin θ^(a+b+1)*cos θ^c)*(cos φ^a*sin φ^b) := by simp only [mul_pow, pow_add, pow_one]; ring
  simp_rw [he, intervalIntegral.integral_const_mul, intervalIntegral.integral_mul_const]
  ring

theorem sphereAvg_monomial (a b c : ℕ) :
    sphereAvg (sphereMonomial a b c) = cartesianMoment a b c := by
  rw [monomial_separate]
  by_cases ha : a % 2 = 0
  · by_cases hb : b % 2 = 0
    · rw [cartesianMoment, ite_eq_left ⟨ha,hb⟩]
      have hp : a+b+1 = 2*((a+b)/2)+1 := by omega
      rw [hp, integral_sin_pow_odd_mul_cos_pow, Real.cos_pi, Real.cos_zero, integral_polar]
      have hc := integral_circle_even (a/2) (b/2)
      rw [show 2*(a/2)=a by omega, show 2*(b/2)=b by omega] at hc
      rw [hc]; field_simp; ring
    · have he : b = 2*(b/2)+1 := by omega
      have h := @integral_sin_pow_odd_mul_cos_pow 0 (2*π) (b/2) a
      rw [← he, Real.cos_two_pi, Real.cos_zero, intervalIntegral.integral_same] at h
      simp_rw [mul_comm (cos _ ^ a) (sin _ ^ b)]
      simp [h, cartesianMoment, hb]
  · have he : a = 2*(a/2)+1 := by omega
    have h := @integral_sin_pow_mul_cos_pow_odd 0 (2*π) b (a/2)
    rw [← he, Real.sin_two_pi, Real.sin_zero, intervalIntegral.integral_same] at h
    simp_rw [mul_comm (cos _ ^ a) (sin _ ^ b)]
    simp [h, cartesianMoment, ha]

/-- Integration of a finite real Cartesian expansion, including terms of
arbitrary degree. -/
theorem sphereAvg_expansion {ι : Type*} (s : Finset ι) (w : ι → ℝ)
    (a b c : ι → ℕ) :
    sphereAvg (fun u => ∑ i ∈ s, w i * sphereMonomial (a i) (b i) (c i) u) =
      ∑ i ∈ s, w i * cartesianMoment (a i) (b i) (c i) := by
  let T (i : ι) (θ : ℝ) := sin θ ^ (a i + b i + 1) * cos θ ^ c i
  let F (i : ι) (φ : ℝ) := cos φ ^ a i * sin φ ^ b i
  have split (i : ι) (θ φ : ℝ) :
      sin θ * (w i * sphereMonomial (a i) (b i) (c i) (SU2.sphVec θ φ)) =
      (w i * T i θ) * F i φ := by
    simp only [sphereMonomial, SU2.sphVec, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons, T, F, mul_pow, pow_add, pow_one]
    ring
  have hinner (θ : ℝ) :
      (∫ φ in (0:ℝ)..(2*π), ∑ i ∈ s, (w i * T i θ) * F i φ) =
      ∑ i ∈ s, (w i * T i θ) * ∫ φ in (0:ℝ)..(2*π), F i φ := by
    rw [intervalIntegral.integral_finsetSum]
    · simp only [intervalIntegral.integral_const_mul]
    · intro i _; apply Continuous.intervalIntegrable; unfold F; fun_prop
  simp only [sphereAvg, Finset.mul_sum, split, hinner]
  rw [intervalIntegral.integral_finsetSum]
  · rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [← sphereAvg_monomial, monomial_separate, intervalIntegral.integral_mul_const,
      intervalIntegral.integral_const_mul]
    dsimp [T,F]; ring
  · intro i _
    apply Continuous.intervalIntegrable
    have hT : Continuous (T i) := by unfold T; fun_prop
    exact (continuous_const.mul hT).mul continuous_const

/-- Exact spherical average computed from the coefficients of a Cartesian polynomial. -/
def polynomialMoment (P : MvPolynomial (Fin 3) ℝ) : ℝ :=
  ∑ e ∈ P.support, P.coeff e * cartesianMoment (e 0) (e 1) (e 2)

theorem sphereAvg_eval (P : MvPolynomial (Fin 3) ℝ) :
    sphereAvg (fun u => MvPolynomial.eval u.1 P) = polynomialMoment P := by
  have he (u : S2) : MvPolynomial.eval u.1 P =
      ∑ e ∈ P.support, P.coeff e * sphereMonomial (e 0) (e 1) (e 2) u := by
    rw [MvPolynomial.eval_eq']
    simp [sphereMonomial, Fin.prod_univ_succ, mul_assoc]
  simp_rw [he]
  exact sphereAvg_expansion _ _ _ _ _

/-- The spherical average is positive definite on polynomial restrictions. -/
theorem sphereAvg_sq_pos (P : MvPolynomial (Fin 3) ℝ)
    (hnz : ∃ u : S2, MvPolynomial.eval u.1 P ≠ 0) :
    0 < sphereAvg (fun u => MvPolynomial.eval u.1 P ^ 2) := by
  let f (θ φ : ℝ) := MvPolynomial.eval (SU2.sphVec θ φ).1 P
  have hc : Continuous (Function.uncurry f) := continuous_mvPolynomial_sphVec P
  have hex : ∃ θ ∈ Set.Ioo (0:ℝ) π, ∃ φ ∈ Set.Ioo (0:ℝ) (2*π), f θ φ ≠ 0 := by
    by_contra! h
    have hπ : 0 < π := Real.pi_pos
    have hθ : Set.Ioo (0:ℝ) π ∈ nhds (π/2) := Ioo_mem_nhds (by linarith) (by linarith)
    have hφ : Set.Ioo (0:ℝ) (2*π) ∈ nhds π := Ioo_mem_nhds hπ (by linarith)
    have he : (fun p : ℝ × ℝ => MvPolynomial.eval (SU2.sphVec p.1 p.2).1 P)
        =ᶠ[nhds (π/2,π)] 0 := by
      rw [nhds_prod_eq]
      exact Filter.mem_prod_iff.mpr ⟨_, hθ, _, hφ, fun p hp => h p.1 hp.1 p.2 hp.2⟩
    obtain ⟨u,hu⟩ := hnz
    exact hu (mvPolynomial_vanish_on_S2_of_eventuallyEq_zero P he u)
  obtain ⟨θ0,hθ,φ0,hφ,hval⟩ := hex
  let F (θ φ : ℝ) := Real.sin θ * f θ φ ^ 2
  let G (θ : ℝ) := ∫ φ in (0:ℝ)..(2*π), F θ φ
  have hF : Continuous (Function.uncurry F) :=
    (Real.continuous_sin.comp continuous_fst).mul (hc.pow 2)
  have hG : Continuous G :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' hF _ _
  have hnn (θ : ℝ) (ht : θ ∈ Set.Icc (0:ℝ) π) (φ : ℝ) : 0 ≤ F θ φ :=
    mul_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi ht.1 ht.2) (sq_nonneg _)
  have hG0 : 0 < G θ0 := by
    apply intervalIntegral.integral_pos (by positivity)
      (hF.comp (continuous_const.prodMk continuous_id)).continuousOn
      (fun φ _ => hnn θ0 ⟨hθ.1.le,hθ.2.le⟩ φ)
    exact ⟨φ0, ⟨hφ.1.le,hφ.2.le⟩, mul_pos (Real.sin_pos_of_pos_of_lt_pi hθ.1 hθ.2) (sq_pos_of_ne_zero hval)⟩
  have hi : 0 < ∫ θ in (0:ℝ)..π, G θ := by
    apply intervalIntegral.integral_pos Real.pi_pos hG.continuousOn
    · intro θ hθ
      exact intervalIntegral.integral_nonneg (by positivity) (fun φ _ => hnn θ ⟨hθ.1.le,hθ.2⟩ φ)
    · exact ⟨θ0, ⟨hθ.1.le,hθ.2.le⟩, hG0⟩
  exact mul_pos (by positivity) hi

end SU2Wigner
end
