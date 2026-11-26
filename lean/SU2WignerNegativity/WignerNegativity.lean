import SU2WignerNegativity.EquatorialIntegral
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# Universal Wigner Negativity for All Spin-j Pure States (Open Quantum Problem F18)

We prove the main theorem solving Open Quantum Problem F18:
- **Analytic Vanishing Lemma**: If a real polynomial on `S² ⊂ ℝ³` vanishes on a neighborhood
  of any point in spherical coordinates, it vanishes identically on `S²`.
- **Lemma 1 (`wigner_neg_of_ortho_partner`)**: For any `SU(2)`-covariant self-dual
  Stratonovich–Weyl spherical Wigner function `W` and any unit state `ψ` admitting an
  orthogonal `SU(2)`-rotated partner `D(g) ψ ⟂ ψ`, `W_ψ` strictly attains negative values.
- **Theorem 2 (`universal_wigner_negativity`)**: Combining Theorem 1 (`pi_ortho_all`) with
  Lemma 1, for EVERY spin `j = N / 2 ≥ 1/2` (`N ≥ 1`), EVERY pure state `ψ` (`⟨ψ | ψ⟩ = 1`),
  and EVERY Stratonovich–Weyl Wigner system `sw`, there exists `u ∈ S²` with `sw.W ψ u < 0`.
- **Corollary 1 (`uniform_wigner_negativity_bound`)**: For every `N ≥ 1`, there exists a
  spin-dependent constant `c_N > 0` such that `∃ u ∈ S², sw.W ψ u ≤ -c_N` for all unit states `ψ`.
- **Non-Vacuity Witness (`spinHalfStratonovichWeyl`)**: Explicit construction of the canonical
  spin-`1/2` (`N = 1`) Stratonovich–Weyl spherical Wigner function `W_ψ(u) = 1/2 + (√3/2) ⟨ψ | u·σ | ψ⟩`,
  with complete proofs of all four Stratonovich–Weyl axioms.
-/

open Complex Finset BigOperators MeasureTheory intervalIntegral Filter Topology Real
open scoped Matrix

noncomputable section

namespace SU2Wigner

/-! ### Spherical Surface Integrals & Surjectivity of Spherical Coordinates -/

/-- Normalized spherical surface average `(1 / (4π)) ∫_0^π ∫_0^{2π} sin θ · f(n(θ, φ)) dφ dθ`. -/
def sphereAvg (f : S2 → ℝ) : ℝ :=
  (1 / (4 * Real.pi)) *
    ∫ θ in (0 : ℝ)..Real.pi, ∫ φ in (0 : ℝ)..(2 * Real.pi),
      Real.sin θ * f (SU2.sphVec θ φ)

/-- Stratonovich–Weyl phase-space integral `((N + 1) / (4π)) ∫_{S²} f dΩ`. -/
def swIntegral (N : ℕ) (f : S2 → ℝ) : ℝ :=
  ((N + 1 : ℕ) : ℝ) * sphereAvg f

/-- Surjectivity of spherical coordinates `(θ, φ) ↦ sphVec θ φ` onto `S²`. -/
lemma sphVec_surjective (u : S2) :
    ∃ θ ∈ Set.Icc (0 : ℝ) Real.pi, ∃ φ : ℝ, SU2.sphVec θ φ = u := by
  have hu : u.1 0 ^ 2 + u.1 1 ^ 2 + u.1 2 ^ 2 = 1 := by
    have h := u.2; simp only [dot3] at h; nlinarith
  have hu2_le : u.1 2 ≤ 1 := by nlinarith [sq_nonneg (u.1 0), sq_nonneg (u.1 1), sq_nonneg (u.1 2 - 1)]
  have hu2_ge : -1 ≤ u.1 2 := by nlinarith [sq_nonneg (u.1 0), sq_nonneg (u.1 1), sq_nonneg (u.1 2 + 1)]
  let θ : ℝ := Real.arccos (u.1 2)
  have hθ_mem : θ ∈ Set.Icc (0 : ℝ) Real.pi := ⟨Real.arccos_nonneg _, Real.arccos_le_pi _⟩
  have hcos_θ : Real.cos θ = u.1 2 := Real.cos_arccos hu2_ge hu2_le
  have hsin_θ : Real.sin θ = Real.sqrt (u.1 0 ^ 2 + u.1 1 ^ 2) := by
    simp only [θ, Real.sin_arccos]
    congr 1; linarith
  by_cases hs0 : Real.sin θ = 0
  · refine ⟨θ, hθ_mem, 0, ?_⟩
    have hxy0 : u.1 0 ^ 2 + u.1 1 ^ 2 = 0 := by
      have hsq : Real.sqrt (u.1 0 ^ 2 + u.1 1 ^ 2) = 0 := hsin_θ ▸ hs0
      have hnn : 0 ≤ u.1 0 ^ 2 + u.1 1 ^ 2 := by positivity
      nlinarith [Real.sq_sqrt hnn]
    have hx0 : u.1 0 = 0 := by nlinarith [sq_nonneg (u.1 0), sq_nonneg (u.1 1)]
    have hy0 : u.1 1 = 0 := by nlinarith [sq_nonneg (u.1 0), sq_nonneg (u.1 1)]
    apply Subtype.ext; funext i; fin_cases i
    · simp [SU2.sphVec, hs0, hx0]
    · simp [SU2.sphVec, hs0, hy0]
    · simp [SU2.sphVec, hcos_θ]
  · have hs_pos : 0 < Real.sin θ := lt_of_le_of_ne (by rw [hsin_θ]; positivity) (Ne.symm hs0)
    let x : ℝ := u.1 0 / Real.sin θ
    let y : ℝ := u.1 1 / Real.sin θ
    have hxy1 : x ^ 2 + y ^ 2 = 1 := by
      have hsin_sq : Real.sin θ ^ 2 = u.1 0 ^ 2 + u.1 1 ^ 2 := by
        rw [hsin_θ, Real.sq_sqrt (by positivity)]
      simp only [x, y]
      field_simp [hs_pos.ne']
      linarith
    have hx_le : x ≤ 1 := by nlinarith [sq_nonneg y, sq_nonneg (x - 1)]
    have hx_ge : -1 ≤ x := by nlinarith [sq_nonneg y, sq_nonneg (x + 1)]
    have hsqrt_x : Real.sqrt (1 - x ^ 2) = |y| := by
      rw [show 1 - x ^ 2 = y ^ 2 by linarith, Real.sqrt_sq_eq_abs]
    let φ : ℝ := if 0 ≤ y then Real.arccos x else -Real.arccos x
    refine ⟨θ, hθ_mem, φ, ?_⟩
    have hcos_φ : Real.cos φ = x := by
      simp only [φ]
      split_ifs
      · exact Real.cos_arccos hx_ge hx_le
      · rw [Real.cos_neg]; exact Real.cos_arccos hx_ge hx_le
    have hsin_φ : Real.sin φ = y := by
      simp only [φ]
      split_ifs with hy
      · rw [Real.sin_arccos, hsqrt_x, abs_of_nonneg hy]
      · rw [Real.sin_neg, Real.sin_arccos, hsqrt_x, abs_of_neg (not_le.mp hy), neg_neg]
    apply Subtype.ext; funext i; fin_cases i
    · change Real.sin θ * Real.cos φ = u.1 0
      rw [hcos_φ]; simp only [x]; field_simp [hs_pos.ne']
    · change Real.sin θ * Real.sin φ = u.1 1
      rw [hsin_φ]; simp only [y]; field_simp [hs_pos.ne']
    · change Real.cos θ = u.1 2
      exact hcos_θ

/-! ### Real-Analytic Vanishing Lemma on `S²` -/

/-- Continuity of `(θ, φ) ↦ P(sin θ cos φ, sin θ sin φ, cos θ)` for any polynomial `P ∈ ℝ[x₀, x₁, x₂]`. -/
lemma continuous_mvPolynomial_sphVec (P : MvPolynomial (Fin 3) ℝ) :
    Continuous (fun p : ℝ × ℝ => MvPolynomial.eval (SU2.sphVec p.1 p.2).1 P) := by
  induction P using MvPolynomial.induction_on with
  | C a => simpa [MvPolynomial.eval_C] using continuous_const
  | add p q hp hq => simp only [map_add]; exact hp.add hq
  | mul_X p i hp =>
    simp only [map_mul, MvPolynomial.eval_X]
    fin_cases i
    · exact hp.mul ((Real.continuous_sin.comp continuous_fst).mul (Real.continuous_cos.comp continuous_snd))
    · exact hp.mul ((Real.continuous_sin.comp continuous_fst).mul (Real.continuous_sin.comp continuous_snd))
    · exact hp.mul (Real.continuous_cos.comp continuous_fst)

private lemma exp_mul_ofReal_cos (t : ℝ) :
    Complex.exp (I * (t : ℂ)) * (Real.cos t : ℂ) = (1 / 2 : ℂ) * (Complex.exp (I * (t : ℂ)) ^ 2 + 1) := by
  have hp : Complex.exp (I * (t : ℂ)) = (Real.cos t : ℂ) + (Real.sin t : ℂ) * I := by
    rw [mul_comm, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
  have hm : Complex.exp (-(I * (t : ℂ))) = (Real.cos t : ℂ) - (Real.sin t : ℂ) * I := by
    rw [show -(I * (t : ℂ)) = ((-t : ℝ) : ℂ) * I by push_cast; ring,
        Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin,
        Real.cos_neg, Real.sin_neg, ofReal_neg]
    ring
  have hprod : Complex.exp (I * (t : ℂ)) * Complex.exp (-(I * (t : ℂ))) = 1 := by
    rw [← Complex.exp_add, add_neg_cancel, Complex.exp_zero]
  linear_combination -(1 / 2 : ℂ) * Complex.exp (I * (t : ℂ)) * (hp + hm) + (1 / 2 : ℂ) * hprod

private lemma exp_mul_ofReal_sin (t : ℝ) :
    Complex.exp (I * (t : ℂ)) * (Real.sin t : ℂ) = (-I / 2 : ℂ) * (Complex.exp (I * (t : ℂ)) ^ 2 - 1) := by
  have hp : Complex.exp (I * (t : ℂ)) = (Real.cos t : ℂ) + (Real.sin t : ℂ) * I := by
    rw [mul_comm, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
  have hm : Complex.exp (-(I * (t : ℂ))) = (Real.cos t : ℂ) - (Real.sin t : ℂ) * I := by
    rw [show -(I * (t : ℂ)) = ((-t : ℝ) : ℂ) * I by push_cast; ring,
        Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin,
        Real.cos_neg, Real.sin_neg, ofReal_neg]
    ring
  have hprod : Complex.exp (I * (t : ℂ)) * Complex.exp (-(I * (t : ℂ))) = 1 := by
    rw [← Complex.exp_add, add_neg_cancel, Complex.exp_zero]
  linear_combination (I / 2 : ℂ) * Complex.exp (I * (t : ℂ)) * (hp - hm) +
    (I / 2 : ℂ) * hprod + Complex.exp (I * (t : ℂ)) * (Real.sin t : ℂ) * I_sq

/-- If a trigonometric polynomial `e^{i d t} f(t) = Q(e^{i t})` vanishes on a nonempty open interval
`(a, b)`, then `f` vanishes identically on `ℝ` (by `Polynomial.card_roots'`). -/
private lemma trigPoly_eq_zero_of_vanish_on_Ioo {f : ℝ → ℂ} {d : ℕ} {Q : Polynomial ℂ}
    (hQ : ∀ t : ℝ, Complex.exp (I * (t : ℂ)) ^ d * f t = Q.eval (Complex.exp (I * (t : ℂ))))
    {a b : ℝ} (hab : a < b) (hvan : ∀ t ∈ Set.Ioo a b, f t = 0) :
    ∀ t : ℝ, f t = 0 := by
  have hQ0 : Q = 0 := by
    by_contra hne
    let δ : ℝ := min (b - a) Real.pi
    have hδ_pos : 0 < δ := lt_min (sub_pos.mpr hab) Real.pi_pos
    have hδ_le_ba : δ ≤ b - a := min_le_left _ _
    have hδ_le_pi : δ ≤ Real.pi := min_le_right _ _
    let n : ℕ := Q.natDegree + 1
    let t : Fin n → ℝ := fun k => a + ((k.val + 1 : ℕ) : ℝ) * (δ / ((n + 1 : ℕ) : ℝ))
    let z : Fin n → ℂ := fun k => Complex.exp (I * (t k : ℂ))
    have ht_small : ∀ k : Fin n, a < t k ∧ t k < a + δ := by
      intro k
      have hk_pos : (0 : ℝ) < ((k.val + 1 : ℕ) : ℝ) := by positivity
      have hn_pos : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
      have hk_lt : ((k.val + 1 : ℕ) : ℝ) < ((n + 1 : ℕ) : ℝ) := by
        exact_mod_cast Nat.succ_lt_succ k.isLt
      have hpos_step : 0 < ((k.val + 1 : ℕ) : ℝ) * (δ / ((n + 1 : ℕ) : ℝ)) := by positivity
      have hfrac : ((k.val + 1 : ℕ) : ℝ) * (δ / ((n + 1 : ℕ) : ℝ)) < δ := by
        rw [mul_div_assoc', div_lt_iff₀ hn_pos]
        nlinarith
      exact ⟨by linarith, by linarith⟩
    have ht_mem : ∀ k : Fin n, t k ∈ Set.Ioo a b := fun k =>
      ⟨(ht_small k).1, by linarith [(ht_small k).2]⟩
    have hz_inj : Function.Injective z := by
      intro k₁ k₂ heq
      obtain ⟨m, hm⟩ := Complex.exp_eq_exp_iff_exists_int.mp heq
      have hm_eq : ((t k₁ - t k₂ : ℝ) : ℂ) = (((m : ℝ) * (2 * Real.pi) : ℝ) : ℂ) := by
        have hI : I * (((t k₁ - t k₂ : ℝ) : ℂ) - (((m : ℝ) * (2 * Real.pi) : ℝ) : ℂ)) = 0 := by
          push_cast; linear_combination hm
        have hsub := (mul_eq_zero.mp hI).resolve_left Complex.I_ne_zero
        linear_combination hsub
      have hreal : t k₁ - t k₂ = (m : ℝ) * (2 * Real.pi) := Complex.ofReal_injective hm_eq
      have hm0 : m = 0 := by
        by_contra hm_ne
        have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
        rcases lt_or_gt_of_ne hm_ne with hlt | hgt
        · have hm_le : (m : ℝ) ≤ -1 := by exact_mod_cast (by omega : m ≤ -1)
          nlinarith [(ht_small k₁).1, (ht_small k₂).2]
        · have hm_ge : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast (by omega : 1 ≤ m)
          nlinarith [(ht_small k₁).2, (ht_small k₂).1]
      have ht_eq : t k₁ = t k₂ := by simp only [hm0, Int.cast_zero, zero_mul] at hreal; linarith
      have hdiv_pos : (0 : ℝ) < δ / ((n + 1 : ℕ) : ℝ) := by positivity
      have hk_eq : ((k₁.val + 1 : ℕ) : ℝ) = ((k₂.val + 1 : ℕ) : ℝ) := by
        have : (((k₁.val + 1 : ℕ) : ℝ) - ((k₂.val + 1 : ℕ) : ℝ)) * (δ / ((n + 1 : ℕ) : ℝ)) = 0 := by
          simp only [t] at ht_eq; linarith
        linarith [(mul_eq_zero.mp this).resolve_right hdiv_pos.ne']
      have hk_nat : k₁.val + 1 = k₂.val + 1 := by exact_mod_cast hk_eq
      exact Fin.ext (by omega)
    have hsub : Finset.univ.image z ⊆ Q.roots.toFinset := by
      intro w hw
      obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hw
      rw [Multiset.mem_toFinset, Polynomial.mem_roots hne, Polynomial.IsRoot.def, ← hQ (t k),
          hvan (t k) (ht_mem k), mul_zero]
    have hcard : n ≤ Q.natDegree := by
      calc n = (Finset.univ : Finset (Fin n)).card := (Fintype.card_fin n).symm
        _ = (Finset.univ.image z).card := (Finset.card_image_of_injective _ hz_inj).symm
        _ ≤ Q.roots.toFinset.card := Finset.card_le_card hsub
        _ ≤ Q.roots.card := Multiset.toFinset_card_le Q.roots
        _ ≤ Q.natDegree := Polynomial.card_roots' Q
    omega
  intro t
  have h0 := hQ t
  rw [hQ0, Polynomial.eval_zero] at h0
  exact (mul_eq_zero.mp h0).resolve_left (pow_ne_zero d (Complex.exp_ne_zero _))

private lemma mvPolynomial_sphVec_trigPoly_phi (P : MvPolynomial (Fin 3) ℝ) (θ : ℝ) :
    ∃ (d : ℕ) (Q : Polynomial ℂ), ∀ φ : ℝ,
      Complex.exp (I * (φ : ℂ)) ^ d * (MvPolynomial.eval (SU2.sphVec θ φ).1 P : ℂ) =
        Q.eval (Complex.exp (I * (φ : ℂ))) := by
  induction P using MvPolynomial.induction_on with
  | C a =>
    exact ⟨0, Polynomial.C (a : ℂ), fun φ => by simp [MvPolynomial.eval_C]⟩
  | add p q hp hq =>
    obtain ⟨d₁, Q₁, hQ₁⟩ := hp
    obtain ⟨d₂, Q₂, hQ₂⟩ := hq
    refine ⟨d₁ + d₂, Polynomial.X ^ d₂ * Q₁ + Polynomial.X ^ d₁ * Q₂, fun φ => ?_⟩
    simp only [map_add, ofReal_add, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow,
      Polynomial.eval_X, ← hQ₁ φ, ← hQ₂ φ, pow_add]
    ring
  | mul_X p i hp =>
    obtain ⟨d, Q, hQ⟩ := hp
    fin_cases i
    · refine ⟨d + 1, Q * (Polynomial.C ((Real.sin θ : ℂ) * (1 / 2 : ℂ)) * (Polynomial.X ^ 2 + 1)), fun φ => ?_⟩
      rw [map_mul, MvPolynomial.eval_X]
      change Complex.exp (I * (φ : ℂ)) ^ (d + 1) *
          ((MvPolynomial.eval (SU2.sphVec θ φ).1 p * (Real.sin θ * Real.cos φ) : ℝ) : ℂ) = _
      simp only [ofReal_mul, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_add,
        Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_one, ← hQ φ, pow_succ]
      linear_combination (Complex.exp (I * (φ : ℂ)) ^ d *
        (MvPolynomial.eval (SU2.sphVec θ φ).1 p : ℂ) * (Real.sin θ : ℂ)) * exp_mul_ofReal_cos φ
    · refine ⟨d + 1, Q * (Polynomial.C ((Real.sin θ : ℂ) * (-I / 2 : ℂ)) * (Polynomial.X ^ 2 - 1)), fun φ => ?_⟩
      rw [map_mul, MvPolynomial.eval_X]
      change Complex.exp (I * (φ : ℂ)) ^ (d + 1) *
          ((MvPolynomial.eval (SU2.sphVec θ φ).1 p * (Real.sin θ * Real.sin φ) : ℝ) : ℂ) = _
      simp only [ofReal_mul, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_sub,
        Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_one, ← hQ φ, pow_succ]
      linear_combination (Complex.exp (I * (φ : ℂ)) ^ d *
        (MvPolynomial.eval (SU2.sphVec θ φ).1 p : ℂ) * (Real.sin θ : ℂ)) * exp_mul_ofReal_sin φ
    · refine ⟨d, Q * Polynomial.C (Real.cos θ : ℂ), fun φ => ?_⟩
      rw [map_mul, MvPolynomial.eval_X]
      change Complex.exp (I * (φ : ℂ)) ^ d *
          ((MvPolynomial.eval (SU2.sphVec θ φ).1 p * Real.cos θ : ℝ) : ℂ) = _
      simp only [ofReal_mul, Polynomial.eval_mul, Polynomial.eval_C, ← hQ φ]
      ring

private lemma mvPolynomial_sphVec_trigPoly_theta (P : MvPolynomial (Fin 3) ℝ) (φ : ℝ) :
    ∃ (d : ℕ) (Q : Polynomial ℂ), ∀ θ : ℝ,
      Complex.exp (I * (θ : ℂ)) ^ d * (MvPolynomial.eval (SU2.sphVec θ φ).1 P : ℂ) =
        Q.eval (Complex.exp (I * (θ : ℂ))) := by
  induction P using MvPolynomial.induction_on with
  | C a =>
    exact ⟨0, Polynomial.C (a : ℂ), fun θ => by simp [MvPolynomial.eval_C]⟩
  | add p q hp hq =>
    obtain ⟨d₁, Q₁, hQ₁⟩ := hp
    obtain ⟨d₂, Q₂, hQ₂⟩ := hq
    refine ⟨d₁ + d₂, Polynomial.X ^ d₂ * Q₁ + Polynomial.X ^ d₁ * Q₂, fun θ => ?_⟩
    simp only [map_add, ofReal_add, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow,
      Polynomial.eval_X, ← hQ₁ θ, ← hQ₂ θ, pow_add]
    ring
  | mul_X p i hp =>
    obtain ⟨d, Q, hQ⟩ := hp
    fin_cases i
    · refine ⟨d + 1, Q * (Polynomial.C ((Real.cos φ : ℂ) * (-I / 2 : ℂ)) * (Polynomial.X ^ 2 - 1)), fun θ => ?_⟩
      rw [map_mul, MvPolynomial.eval_X]
      change Complex.exp (I * (θ : ℂ)) ^ (d + 1) *
          ((MvPolynomial.eval (SU2.sphVec θ φ).1 p * (Real.sin θ * Real.cos φ) : ℝ) : ℂ) = _
      simp only [ofReal_mul, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_sub,
        Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_one, ← hQ θ, pow_succ]
      linear_combination (Complex.exp (I * (θ : ℂ)) ^ d *
        (MvPolynomial.eval (SU2.sphVec θ φ).1 p : ℂ) * (Real.cos φ : ℂ)) * exp_mul_ofReal_sin θ
    · refine ⟨d + 1, Q * (Polynomial.C ((Real.sin φ : ℂ) * (-I / 2 : ℂ)) * (Polynomial.X ^ 2 - 1)), fun θ => ?_⟩
      rw [map_mul, MvPolynomial.eval_X]
      change Complex.exp (I * (θ : ℂ)) ^ (d + 1) *
          ((MvPolynomial.eval (SU2.sphVec θ φ).1 p * (Real.sin θ * Real.sin φ) : ℝ) : ℂ) = _
      simp only [ofReal_mul, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_sub,
        Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_one, ← hQ θ, pow_succ]
      linear_combination (Complex.exp (I * (θ : ℂ)) ^ d *
        (MvPolynomial.eval (SU2.sphVec θ φ).1 p : ℂ) * (Real.sin φ : ℂ)) * exp_mul_ofReal_sin θ
    · refine ⟨d + 1, Q * (Polynomial.C (1 / 2 : ℂ) * (Polynomial.X ^ 2 + 1)), fun θ => ?_⟩
      rw [map_mul, MvPolynomial.eval_X]
      change Complex.exp (I * (θ : ℂ)) ^ (d + 1) *
          ((MvPolynomial.eval (SU2.sphVec θ φ).1 p * Real.cos θ : ℝ) : ℂ) = _
      simp only [ofReal_mul, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_add,
        Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_one, ← hQ θ, pow_succ]
      linear_combination (Complex.exp (I * (θ : ℂ)) ^ d *
        (MvPolynomial.eval (SU2.sphVec θ φ).1 p : ℂ)) * exp_mul_ofReal_cos θ

/-- **Analytic / Algebraic Vanishing Lemma on `S²`**:
If a real polynomial `P ∈ ℝ[x₀, x₁, x₂]` restricted to `S²` vanishes on a neighborhood of
some `(θ₀, φ₀)` in spherical coordinates, then `P` vanishes identically on all of `S²`. -/
lemma mvPolynomial_vanish_on_S2_of_eventuallyEq_zero (P : MvPolynomial (Fin 3) ℝ)
    {p₀ : ℝ × ℝ}
    (hzero : (fun p : ℝ × ℝ => MvPolynomial.eval (SU2.sphVec p.1 p.2).1 P) =ᶠ[𝓝 p₀] 0) :
    ∀ u : S2, MvPolynomial.eval u.1 P = 0 := by
  have hprod : { p : ℝ × ℝ | MvPolynomial.eval (SU2.sphVec p.1 p.2).1 P = 0 } ∈ 𝓝 p₀ := hzero
  rw [nhds_prod_eq, Filter.mem_prod_iff] at hprod
  obtain ⟨s, hs, t, ht, hst⟩ := hprod
  obtain ⟨ε₁, hε₁, hball₁⟩ := Metric.mem_nhds_iff.mp hs
  obtain ⟨ε₂, hε₂, hball₂⟩ := Metric.mem_nhds_iff.mp ht
  have hbox : ∀ θ ∈ Set.Ioo (p₀.1 - ε₁) (p₀.1 + ε₁), ∀ φ ∈ Set.Ioo (p₀.2 - ε₂) (p₀.2 + ε₂),
      MvPolynomial.eval (SU2.sphVec θ φ).1 P = 0 := by
    intro θ hθ φ hφ
    have hθs : θ ∈ s := hball₁ (by rw [Metric.mem_ball, Real.dist_eq, abs_lt]; constructor <;> linarith [hθ.1, hθ.2])
    have hφt : φ ∈ t := hball₂ (by rw [Metric.mem_ball, Real.dist_eq, abs_lt]; constructor <;> linarith [hφ.1, hφ.2])
    exact @hst (θ, φ) ⟨hθs, hφt⟩
  -- Step 1: For every `θ ∈ (p₀.1 - ε₁, p₀.1 + ε₁)`, `φ ↦ P(sphVec θ φ)` vanishes identically on `ℝ`.
  have hslice_phi : ∀ θ ∈ Set.Ioo (p₀.1 - ε₁) (p₀.1 + ε₁),
      ∀ φ : ℝ, MvPolynomial.eval (SU2.sphVec θ φ).1 P = 0 := by
    intro θ hθ φ
    obtain ⟨d, Q, hQ⟩ := mvPolynomial_sphVec_trigPoly_phi P θ
    have hc0 : (MvPolynomial.eval (SU2.sphVec θ φ).1 P : ℂ) = 0 :=
      trigPoly_eq_zero_of_vanish_on_Ioo hQ (a := p₀.2 - ε₂) (b := p₀.2 + ε₂) (by linarith)
        (fun q hq => by rw [hbox θ hθ q hq, Complex.ofReal_zero]) φ
    exact Complex.ofReal_injective hc0
  -- Step 2: For every `φ : ℝ`, `θ ↦ P(sphVec θ φ)` vanishes identically on `ℝ`.
  have hslice_all : ∀ θ φ : ℝ, MvPolynomial.eval (SU2.sphVec θ φ).1 P = 0 := by
    intro θ φ
    obtain ⟨d, Q, hQ⟩ := mvPolynomial_sphVec_trigPoly_theta P φ
    have hc0 : (MvPolynomial.eval (SU2.sphVec θ φ).1 P : ℂ) = 0 :=
      trigPoly_eq_zero_of_vanish_on_Ioo hQ (a := p₀.1 - ε₁) (b := p₀.1 + ε₁) (by linarith)
        (fun q hq => by rw [hslice_phi q hq φ, Complex.ofReal_zero]) θ
    exact Complex.ofReal_injective hc0
  -- Step 3: Pull back any `u ∈ S²` via `sphVec_surjective`.
  intro u
  obtain ⟨θ, _, φ, rfl⟩ := sphVec_surjective u
  exact hslice_all θ φ

/-- Continuity of a 1D slice of a jointly continuous `ℝ × ℝ → ℝ` map. -/
private lemma continuous_slice_snd {F : ℝ → ℝ → ℝ} (hF : Continuous (Function.uncurry F)) (t : ℝ) :
    Continuous (fun q : ℝ => F t q) :=
  hF.comp (continuous_const.prodMk continuous_id)

/-- Continuity of `p ↦ MvPolynomial.eval (actS2 g (sphVec p.1 p.2)).1 P`. -/
lemma continuous_mvPolynomial_actS2_sphVec (g : SU2) (P : MvPolynomial (Fin 3) ℝ) :
    Continuous (fun p : ℝ × ℝ => MvPolynomial.eval (SU2.actS2 g (SU2.sphVec p.1 p.2)).1 P) := by
  have hcoord : ∀ i : Fin 3, Continuous (fun p : ℝ × ℝ => (SU2.actS2 g (SU2.sphVec p.1 p.2)).1 i) := by
    intro i
    fin_cases i
    · change Continuous (fun p : ℝ × ℝ => (SU2.toSO3 g (SU2.sphVec p.1 p.2).1) 0)
      simp only [SU2.toSO3, SU2.sphVec, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]
      fun_prop
    · change Continuous (fun p : ℝ × ℝ => (SU2.toSO3 g (SU2.sphVec p.1 p.2).1) 1)
      simp only [SU2.toSO3, SU2.sphVec, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]
      fun_prop
    · change Continuous (fun p : ℝ × ℝ => (SU2.toSO3 g (SU2.sphVec p.1 p.2).1) 2)
      simp only [SU2.toSO3, SU2.sphVec, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]
      fun_prop
  induction P using MvPolynomial.induction_on with
  | C a => simpa [MvPolynomial.eval_C] using continuous_const
  | add p q hp hq => simp only [map_add]; exact hp.add hq
  | mul_X p i hp => simp only [map_mul, MvPolynomial.eval_X]; exact hp.mul (hcoord i)

/-! ### Stratonovich–Weyl Axioms and Universal Wigner Negativity -/

/-- An `SU(2)`-covariant, self-dual Stratonovich–Weyl spherical Wigner function for spin `j = N / 2`.
Encodes the four Stratonovich–Weyl axioms:
1. `poly`: finite spherical-harmonic / polynomial expansion on `S² ⊂ ℝ³`;
2. `norm_eq`: normalization `((N + 1) / (4π)) ∫_{S²} W_ψ dΩ = ⟨ψ | ψ⟩`;
3. `covariant`: `SU(2)`-covariance `W_{D(g) ψ}(R_g u) = W_ψ(u)`;
4. `tracial`: self-dual Moyal overlap `((N + 1) / (4π)) ∫_{S²} W_φ W_ψ dΩ = |⟨φ | ψ⟩|²`. -/
structure StratonovichWeylSystem (N : ℕ) where
  W : (Fin (N + 1) → ℂ) → S2 → ℝ
  poly : ∀ ψ : Fin (N + 1) → ℂ, ∃ P : MvPolynomial (Fin 3) ℝ,
    ∀ u : S2, W ψ u = MvPolynomial.eval u.1 P
  norm_eq : ∀ ψ : Fin (N + 1) → ℂ, swIntegral N (W ψ) = (innerC ψ ψ).re
  covariant : ∀ (g : SU2) (ψ : Fin (N + 1) → ℂ) (u : S2),
    W ((spinRep N g).mulVec ψ) (SU2.actS2 g u) = W ψ u
  tracial : ∀ φ ψ : Fin (N + 1) → ℂ,
    swIntegral N (fun u => W φ u * W ψ u) = Complex.normSq (innerC φ ψ)

/-- **Lemma 1 (Orthogonal Rotated Partner ⇒ Strict Wigner Negativity)**:
If a unit pure state `ψ` (`innerC ψ ψ = 1`) admits a rotation `g ∈ SU(2)` with
`⟨ψ | D^{(N/2)}(g) | ψ⟩ = 0`, then every Stratonovich–Weyl Wigner function `sw.W ψ`
strictly attains negative values on `S²`. -/
theorem wigner_neg_of_ortho_partner {N : ℕ} (sw : StratonovichWeylSystem N)
    {ψ : Fin (N + 1) → ℂ} (hψ : innerC ψ ψ = 1)
    {g : SU2} (hortho : innerC ψ ((spinRep N g).mulVec ψ) = 0) :
    ∃ u : S2, sw.W ψ u < 0 := by
  by_contra hnonneg
  push Not at hnonneg
  let φ : Fin (N + 1) → ℂ := (spinRep N g).mulVec ψ
  -- `W_φ ≥ 0` everywhere on `S²` by `SU(2)`-covariance
  have hφ_nonneg : ∀ u : S2, 0 ≤ sw.W φ u := by
    intro u
    have hact : SU2.actS2 g (SU2.actS2 g⁻¹ u) = u := by
      rw [← SU2.actS2_mul, SU2.mul_inv_cancel, SU2.actS2_one]
    rw [← hact, sw.covariant]
    exact hnonneg _
  -- By traciality and orthogonality, `∫_0^π ∫_0^{2π} sin θ · W_φ · W_ψ = 0`!
  have htr : swIntegral N (fun u => sw.W φ u * sw.W ψ u) = 0 := by
    rw [sw.tracial]
    have h0 : innerC φ ψ = 0 := by
      rw [← innerC_conj_symm, hortho, star_zero]
    rw [h0, map_zero]
  have hint0 :
      ∫ θ in (0 : ℝ)..Real.pi, ∫ p in (0 : ℝ)..(2 * Real.pi),
        Real.sin θ * (sw.W φ (SU2.sphVec θ p) * sw.W ψ (SU2.sphVec θ p)) = 0 := by
    simp only [swIntegral, sphereAvg] at htr
    have hNpos : ((N + 1 : ℕ) : ℝ) ≠ 0 := by positivity
    have hpipos : (1 / (4 * Real.pi) : ℝ) ≠ 0 := by positivity
    have hmul : ((N + 1 : ℕ) : ℝ) * (1 / (4 * Real.pi)) ≠ 0 := mul_ne_zero hNpos hpipos
    rw [← mul_assoc] at htr
    exact (mul_eq_zero.mp htr).resolve_left hmul
  -- Obtain polynomials representing `W_ψ` and `W_φ`
  obtain ⟨Pψ, hPψ⟩ := sw.poly ψ
  obtain ⟨Pφ, hPφ⟩ := sw.poly φ
  have hWψ_cont : Continuous (fun p : ℝ × ℝ => sw.W ψ (SU2.sphVec p.1 p.2)) := by
    have heq : (fun p : ℝ × ℝ => sw.W ψ (SU2.sphVec p.1 p.2)) =
        fun p => MvPolynomial.eval (SU2.sphVec p.1 p.2).1 Pψ := funext fun p => hPψ _
    rw [heq]; exact continuous_mvPolynomial_sphVec Pψ
  have hWφ_cont : Continuous (fun p : ℝ × ℝ => sw.W φ (SU2.sphVec p.1 p.2)) := by
    have heq : (fun p : ℝ × ℝ => sw.W φ (SU2.sphVec p.1 p.2)) =
        fun p => MvPolynomial.eval (SU2.sphVec p.1 p.2).1 Pφ := funext fun p => hPφ _
    rw [heq]; exact continuous_mvPolynomial_sphVec Pφ
  -- Deduce `W_φ u * W_ψ u = 0` for EVERY `u ∈ S²`!
  have hprod_zero_sph : ∀ θ ∈ Set.Ioo (0 : ℝ) Real.pi, ∀ p ∈ Set.Icc (0 : ℝ) (2 * Real.pi),
      sw.W φ (SU2.sphVec θ p) * sw.W ψ (SU2.sphVec θ p) = 0 := by
    let F : ℝ → ℝ → ℝ := fun θ p => Real.sin θ * (sw.W φ (SU2.sphVec θ p) * sw.W ψ (SU2.sphVec θ p))
    have hF_cont : Continuous (Function.uncurry F) :=
      (Real.continuous_sin.comp continuous_fst).mul (hWφ_cont.mul hWψ_cont)
    have hF_nn : ∀ θ ∈ Set.Icc (0 : ℝ) Real.pi, ∀ p ∈ Set.Icc (0 : ℝ) (2 * Real.pi), 0 ≤ F θ p := by
      intro θ hθ p _
      have hs : 0 ≤ Real.sin θ := Real.sin_nonneg_of_nonneg_of_le_pi hθ.1 hθ.2
      have h1 := hφ_nonneg (SU2.sphVec θ p)
      have h2 := hnonneg (SU2.sphVec θ p)
      simp only [F]; positivity
    -- First show `G θ := ∫ p in 0..(2π), F θ p = 0` for all `θ ∈ (0, π)`
    have hG_zero : ∀ θ ∈ Set.Ioo (0 : ℝ) Real.pi, ∫ p in (0 : ℝ)..(2 * Real.pi), F θ p = 0 := by
      intro θ₀ hθ₀
      by_contra hne
      have hG_nn : ∀ θ ∈ Set.Icc (0 : ℝ) Real.pi, 0 ≤ ∫ p in (0 : ℝ)..(2 * Real.pi), F θ p :=
        fun θ hθ => intervalIntegral.integral_nonneg (by positivity) (fun p hp => hF_nn θ hθ p hp)
      have hpos0 : 0 < ∫ p in (0 : ℝ)..(2 * Real.pi), F θ₀ p :=
        lt_of_le_of_ne (hG_nn θ₀ ⟨hθ₀.1.le, hθ₀.2.le⟩) (Ne.symm hne)
      -- Since `F` is continuous on `[0, π] × [0, 2π]`, `G` is continuous on `[0, π]`!
      -- Even simpler: prove `F θ₀ p₀ = 0` directly via a tiny 2D box, just like `SphericalHarmonicZero`!
      have hinner_nn : ∀ p ∈ Set.Icc (0 : ℝ) (2 * Real.pi), 0 ≤ F θ₀ p := hF_nn θ₀ ⟨hθ₀.1.le, hθ₀.2.le⟩
      have hex_p : ∃ p₀ ∈ Set.Icc (0 : ℝ) (2 * Real.pi), 0 < F θ₀ p₀ := by
        by_contra hall0
        push Not at hall0
        have hz : ∀ p ∈ Set.Icc (0 : ℝ) (2 * Real.pi), F θ₀ p = 0 :=
          fun p hp => le_antisymm (hall0 p hp) (hinner_nn p hp)
        have h0 : ∫ p in (0 : ℝ)..(2 * Real.pi), F θ₀ p = 0 := by
          rw [intervalIntegral.integral_congr (fun p hp => hz p (by rwa [Set.uIcc_of_le (by positivity)] at hp))]
          simp
        linarith
      obtain ⟨p₀, hp₀, hFp₀⟩ := hex_p
      -- Since `F` is continuous at `(θ₀, p₀)`, `F ≥ F θ₀ p₀ / 2` on a tiny box `[t₁, t₂] × [q₁, q₂]`!
      obtain ⟨δ, hδ_pos, hδ⟩ := Metric.continuous_iff.mp hF_cont (θ₀, p₀) (F θ₀ p₀ / 2) (by linarith)
      set r : ℝ := min (min (δ / 2) (Real.pi / 4)) (min (θ₀ / 2) ((Real.pi - θ₀) / 2))
      have hr_pos : 0 < r := by
        have : 0 < θ₀ := hθ₀.1; have : 0 < Real.pi - θ₀ := sub_pos.mpr hθ₀.2; positivity
      have hr_lt_δ : r < δ := by
        have : r ≤ δ / 2 := le_trans (min_le_left _ _) (min_le_left _ _); linarith
      have hr_le_pi4 : r ≤ Real.pi / 4 := le_trans (min_le_left _ _) (min_le_right _ _)
      have hr_le_t0 : r ≤ θ₀ / 2 := le_trans (min_le_right _ _) (min_le_left _ _)
      have hr_le_pit0 : r ≤ (Real.pi - θ₀) / 2 := le_trans (min_le_right _ _) (min_le_right _ _)
      set t₁ : ℝ := θ₀ - r; set t₂ : ℝ := θ₀ + r
      have ht₁_nn : 0 ≤ t₁ := by linarith [hθ₀.1]
      have ht₂_le : t₂ ≤ Real.pi := by linarith [hθ₀.2]
      have ht₁_lt_t₂ : t₁ < t₂ := by linarith
      have hq_ex : ∃ q₁ q₂ : ℝ, 0 ≤ q₁ ∧ q₁ < q₂ ∧ q₂ ≤ 2 * Real.pi ∧
          ∀ q ∈ Set.Icc q₁ q₂, |q - p₀| ≤ r := by
        by_cases hp : p₀ ≤ Real.pi
        · refine ⟨p₀, p₀ + r, hp₀.1, by linarith, by linarith, fun q hq => ?_⟩
          rw [abs_le]; constructor <;> linarith [hq.1, hq.2]
        · refine ⟨p₀ - r, p₀, by linarith, by linarith, hp₀.2, fun q hq => ?_⟩
          rw [abs_le]; constructor <;> linarith [hq.1, hq.2]
      obtain ⟨q₁, q₂, hq₁_nn, hq₁_lt_q₂, hq₂_le, hq_dist⟩ := hq_ex
      have hF_ge : ∀ t ∈ Set.Icc t₁ t₂, ∀ q ∈ Set.Icc q₁ q₂, F θ₀ p₀ / 2 ≤ F t q := by
        intro t ht q hq
        have hdist : dist (t, q) (θ₀, p₀) < δ := by
          rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq]
          apply max_lt
          · have : |t - θ₀| ≤ r := by rw [abs_le]; constructor <;> linarith [ht.1, ht.2]
            linarith
          · exact lt_of_le_of_lt (hq_dist q hq) hr_lt_δ
        have hsub := hδ (t, q) hdist
        simp only [Function.uncurry, Real.dist_eq, abs_lt] at hsub
        linarith [hsub.1]
      have hinner_ge : ∀ t ∈ Set.Icc t₁ t₂,
          (q₂ - q₁) * (F θ₀ p₀ / 2) ≤ ∫ q in (0 : ℝ)..(2 * Real.pi), F t q := by
        intro t ht
        have hFt_cont : Continuous (fun q => F t q) := continuous_slice_snd hF_cont t
        have h1 : (q₂ - q₁) * (F θ₀ p₀ / 2) ≤ ∫ q in q₁..q₂, F t q := by
          have hc : ∫ _ in q₁..q₂, (F θ₀ p₀ / 2) = (q₂ - q₁) * (F θ₀ p₀ / 2) := by simp; ring
          rw [← hc]
          exact intervalIntegral.integral_mono_on hq₁_lt_q₂.le intervalIntegrable_const
            (hFt_cont.intervalIntegrable q₁ q₂) (fun q hq => hF_ge t ht q hq)
        have h2 : ∫ q in q₁..q₂, F t q ≤ ∫ q in (0 : ℝ)..(2 * Real.pi), F t q := by
          apply intervalIntegral.integral_mono_interval hq₁_nn hq₁_lt_q₂.le hq₂_le
          · exact (ae_restrict_iff' measurableSet_Ioc).mpr
              (ae_of_all _ fun q hq => hF_nn t ⟨by linarith [ht.1], by linarith [ht.2]⟩ q ⟨hq.1.le, hq.2⟩)
          · exact hFt_cont.intervalIntegrable 0 (2 * Real.pi)
        linarith
      have houter_int : IntervalIntegrable (fun t => ∫ q in (0 : ℝ)..(2 * Real.pi), F t q)
          volume 0 Real.pi := by
        have hprod : Integrable (Function.uncurry F)
            ((volume.restrict (Set.Ioc 0 Real.pi)).prod (volume.restrict (Set.Ioc 0 (2 * Real.pi)))) := by
          rw [Measure.prod_restrict, ← Measure.volume_eq_prod]
          exact (hF_cont.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)).mono_set
            (Set.prod_mono Set.Ioc_subset_Icc_self Set.Ioc_subset_Icc_self)
        rw [intervalIntegrable_iff_integrableOn_Ioc_of_le Real.pi_pos.le]
        have heq : (fun t => ∫ q in (0 : ℝ)..(2 * Real.pi), F t q) =
            fun t => ∫ q, F t q ∂volume.restrict (Set.Ioc 0 (2 * Real.pi)) := by
          funext t; rw [intervalIntegral.integral_of_le (by positivity)]
        rw [heq]; exact hprod.integral_prod_left
      have houter_sub : IntervalIntegrable (fun t => ∫ q in (0 : ℝ)..(2 * Real.pi), F t q)
          volume t₁ t₂ :=
        houter_int.mono_set (by
          rw [Set.uIcc_of_le ht₁_lt_t₂.le, Set.uIcc_of_le Real.pi_pos.le]
          exact fun t ht => ⟨by linarith [ht.1], by linarith [ht.2]⟩)
      have h1 : (t₂ - t₁) * ((q₂ - q₁) * (F θ₀ p₀ / 2)) ≤
          ∫ t in t₁..t₂, ∫ q in (0 : ℝ)..(2 * Real.pi), F t q := by
        have hc : ∫ _ in t₁..t₂, ((q₂ - q₁) * (F θ₀ p₀ / 2)) =
            (t₂ - t₁) * ((q₂ - q₁) * (F θ₀ p₀ / 2)) := by simp; ring
        rw [← hc]
        exact intervalIntegral.integral_mono_on ht₁_lt_t₂.le intervalIntegrable_const houter_sub hinner_ge
      have h2 : ∫ t in t₁..t₂, ∫ q in (0 : ℝ)..(2 * Real.pi), F t q ≤
          ∫ t in (0 : ℝ)..Real.pi, ∫ q in (0 : ℝ)..(2 * Real.pi), F t q := by
        apply intervalIntegral.integral_mono_interval ht₁_nn ht₁_lt_t₂.le ht₂_le
        · exact (ae_restrict_iff' measurableSet_Ioc).mpr
            (ae_of_all _ fun t ht => hG_nn t ⟨ht.1.le, ht.2⟩)
        · exact houter_int
      have hpos_box : 0 < (t₂ - t₁) * ((q₂ - q₁) * (F θ₀ p₀ / 2)) := by
        have : 0 < t₂ - t₁ := by linarith
        have : 0 < q₂ - q₁ := by linarith
        positivity
      linarith [hint0]
    intro θ hθ p hp
    have hGt := hG_zero θ hθ
    have hFt_cont : Continuous (fun q => F θ q) := continuous_slice_snd hF_cont θ
    have hF0 : F θ p = 0 := by
      by_contra hne
      have hpos : 0 < F θ p := lt_of_le_of_ne (hF_nn θ ⟨hθ.1.le, hθ.2.le⟩ p hp) (Ne.symm hne)
      have h2pi_pos : (0 : ℝ) < 2 * Real.pi := by positivity
      have hpos_int : 0 < ∫ q in (0 : ℝ)..(2 * Real.pi), F θ q :=
        intervalIntegral.integral_pos h2pi_pos hFt_cont.continuousOn
          (fun q hq => hF_nn θ ⟨hθ.1.le, hθ.2.le⟩ q ⟨hq.1.le, hq.2⟩) ⟨p, hp, hpos⟩
      linarith
    have hs_ne : Real.sin θ ≠ 0 := (Real.sin_pos_of_pos_of_lt_pi hθ.1 hθ.2).ne'
    exact (mul_eq_zero.mp hF0).resolve_left hs_ne
  -- Extend `W_φ (sphVec θ p) * W_ψ (sphVec θ p) = 0` from `(0, π) × [0, 2π]` to ALL of `S²` by
  -- analyticity (since `Pφ * Pψ` is a polynomial vanishing on the open set `(0, π) × (0, 2π)`)!
  have hprod_zero_all : ∀ u : S2, sw.W φ u * sw.W ψ u = 0 := by
    have hvan : ∀ u : S2, MvPolynomial.eval u.1 (Pφ * Pψ) = 0 := by
      apply mvPolynomial_vanish_on_S2_of_eventuallyEq_zero (Pφ * Pψ) (p₀ := (Real.pi / 2, Real.pi))
      have hmem : Set.Ioo (0 : ℝ) Real.pi ×ˢ Set.Ioo (0 : ℝ) (2 * Real.pi) ∈
          𝓝 ((Real.pi / 2 : ℝ), Real.pi) :=
        IsOpen.mem_nhds (isOpen_Ioo.prod isOpen_Ioo)
          ⟨⟨by positivity, by linarith [Real.pi_pos]⟩, ⟨Real.pi_pos, by linarith [Real.pi_pos]⟩⟩
      filter_upwards [hmem] with p hp
      simp only [map_mul, Pi.zero_apply, ← hPφ, ← hPψ]
      exact hprod_zero_sph p.1 hp.1 p.2 ⟨hp.2.1.le, hp.2.2.le⟩
    intro u
    have h := hvan u
    simp only [map_mul, ← hPφ, ← hPψ] at h
    exact h
  -- Since `swIntegral N (W_ψ) = 1 ≠ 0`, `W_ψ` is strictly positive at some `u₀ ∈ S²`!
  have hex_pos : ∃ u₀ : S2, 0 < sw.W ψ u₀ := by
    by_contra hall
    push Not at hall
    have hall0 : ∀ u : S2, sw.W ψ u = 0 := fun u => le_antisymm (hall u) (hnonneg u)
    have h0 : swIntegral N (sw.W ψ) = 0 := by
      simp [swIntegral, sphereAvg, hall0]
    have h1 : swIntegral N (sw.W ψ) = 1 := by rw [sw.norm_eq, hψ]; simp
    linarith
  obtain ⟨u₀, hu₀_pos⟩ := hex_pos
  -- Pull back `u₀` via `g⁻¹` to `p₀ = (θ₀, φ₀)` with `actS2 g (sphVec θ₀ φ₀) = u₀`!
  obtain ⟨θ₀, _, φ₀, hsph₀⟩ := sphVec_surjective (SU2.actS2 g⁻¹ u₀)
  have hact₀ : SU2.actS2 g (SU2.sphVec θ₀ φ₀) = u₀ := by
    rw [hsph₀, ← SU2.actS2_mul, SU2.mul_inv_cancel, SU2.actS2_one]
  -- On a neighborhood of `(θ₀, φ₀)`, `W_ψ(actS2 g (sphVec p)) > 0`, hence `W_ψ(sphVec p) = W_φ(actS2 g (sphVec p)) = 0`!
  have hcont_rot : Continuous (fun p : ℝ × ℝ => sw.W ψ (SU2.actS2 g (SU2.sphVec p.1 p.2))) := by
    have heq : (fun p : ℝ × ℝ => sw.W ψ (SU2.actS2 g (SU2.sphVec p.1 p.2))) =
        fun p => MvPolynomial.eval (SU2.actS2 g (SU2.sphVec p.1 p.2)).1 Pψ := funext fun p => hPψ _
    rw [heq]; exact continuous_mvPolynomial_actS2_sphVec g Pψ
  have hpos_nbhd : ∀ᶠ p : ℝ × ℝ in 𝓝 (θ₀, φ₀), 0 < sw.W ψ (SU2.actS2 g (SU2.sphVec p.1 p.2)) :=
    hcont_rot.continuousAt.eventually (isOpen_Ioi.mem_nhds (by simpa [hact₀] using hu₀_pos))
  have hzero_nbhd : (fun p : ℝ × ℝ => MvPolynomial.eval (SU2.sphVec p.1 p.2).1 Pψ) =ᶠ[𝓝 (θ₀, φ₀)] 0 := by
    filter_upwards [hpos_nbhd] with p hp
    simp only [Pi.zero_apply, ← hPψ]
    have hmul0 := hprod_zero_all (SU2.actS2 g (SU2.sphVec p.1 p.2))
    have hφ0 : sw.W φ (SU2.actS2 g (SU2.sphVec p.1 p.2)) = 0 :=
      (mul_eq_zero.mp hmul0).resolve_right hp.ne'
    rwa [sw.covariant] at hφ0
  -- By the Analytic Vanishing Lemma, `W_ψ ≡ 0` on all of `S²`, contradicting `∫ W_ψ = 1`!
  have hWψ_zero : ∀ u : S2, sw.W ψ u = 0 := fun u => by
    rw [hPψ]; exact mvPolynomial_vanish_on_S2_of_eventuallyEq_zero Pψ hzero_nbhd u
  have h0 : swIntegral N (sw.W ψ) = 0 := by simp [swIntegral, sphereAvg, hWψ_zero]
  have h1 : swIntegral N (sw.W ψ) = 1 := by rw [sw.norm_eq, hψ]; simp
  linarith

/-- **Main Theorem (Theorem 2 — Solution to Open Quantum Problem F18)**:
For EVERY spin `j = N / 2` with `N ≥ 1` (`j ∈ {1/2, 1, 3/2, 2, ...}`), EVERY unit pure state
`ψ : Fin (N + 1) → ℂ` (`⟨ψ | ψ⟩ = 1`), and EVERY `SU(2)`-covariant self-dual Stratonovich–Weyl
spherical Wigner function `sw`, `sw.W ψ` strictly attains negative values on `S²`. -/
theorem universal_wigner_negativity {N : ℕ} (hN : 1 ≤ N) (sw : StratonovichWeylSystem N)
    {ψ : Fin (N + 1) → ℂ} (hψ : innerC ψ ψ = 1) :
    ∃ u : S2, sw.W ψ u < 0 := by
  obtain ⟨u₀, hu₀⟩ := pi_ortho_all hN ψ
  exact wigner_neg_of_ortho_partner sw hψ hu₀

/-- **Corollary 1 (Uniform Spin-Dependent Negativity Bound)**:
If `ψ ↦ sw.W ψ u` is continuous for each fixed `u ∈ S²`, then for every spin `j = N / 2 ≥ 1/2`
there exists a uniform constant `c > 0` such that every unit pure state `ψ` satisfies
`∃ u ∈ S², sw.W ψ u ≤ -c`. -/
theorem uniform_wigner_negativity_bound {N : ℕ} (hN : 1 ≤ N) (sw : StratonovichWeylSystem N)
    (hcont : ∀ u : S2, Continuous (fun ψ : Fin (N + 1) → ℂ => sw.W ψ u)) :
    ∃ c : ℝ, 0 < c ∧ ∀ ψ : Fin (N + 1) → ℂ, innerC ψ ψ = 1 → ∃ u : S2, sw.W ψ u ≤ -c := by
  let S : Set (Fin (N + 1) → ℂ) := { ψ | innerC ψ ψ = 1 }
  -- `S` is compact (closed subset of the closed unit ball in finite-dimensional `Fin (N+1) → ℂ`)
  have hS_closed : IsClosed S := by
    have hinner_cont : Continuous (fun ψ : Fin (N + 1) → ℂ => innerC ψ ψ) := by
      unfold innerC
      apply continuous_finsetSum; intro k _
      exact (continuous_star.comp (continuous_apply k)).mul (continuous_apply k)
    exact isClosed_singleton.preimage hinner_cont
  have hS_sub : S ⊆ Metric.closedBall (0 : Fin (N + 1) → ℂ) 1 := by
    intro ψ hψ
    rw [Metric.mem_closedBall, dist_zero_right, pi_norm_le_iff_of_nonneg zero_le_one]
    intro k
    have hre : ∑ i : Fin (N + 1), Complex.normSq (ψ i) = 1 := by
      have h := congrArg Complex.re hψ
      simp only [innerC, Complex.re_sum, Complex.one_re] at h
      convert h using 1
      apply Finset.sum_congr rfl; intro i _
      simp [Complex.normSq_apply, mul_comm]
    have hle : Complex.normSq (ψ k) ≤ 1 := by
      rw [← hre]
      exact Finset.single_le_sum (fun i _ => Complex.normSq_nonneg (ψ i)) (Finset.mem_univ k)
    have hsq : ‖ψ k‖ ^ 2 ≤ 1 := by rwa [Complex.sq_norm]
    nlinarith [norm_nonneg (ψ k)]
  have hS_compact : IsCompact S := (isCompact_closedBall (0 : Fin (N + 1) → ℂ) 1).of_isClosed_subset
    hS_closed hS_sub
  -- Construct an open cover of `S` where `W_ψ(u_i) < -c_i`
  let U : S → Set (Fin (N + 1) → ℂ) := fun s =>
    let u := (universal_wigner_negativity hN sw s.2).choose
    { φ | sw.W φ u < sw.W s.1 u / 2 }
  have hU_open : ∀ s : S, IsOpen (U s) := fun s =>
    isOpen_Iio.preimage (hcont (universal_wigner_negativity hN sw s.2).choose)
  have hS_cov : S ⊆ ⋃ s : S, U s := by
    intro ψ hψ
    refine Set.mem_iUnion.mpr ⟨⟨ψ, hψ⟩, ?_⟩
    have hlt := (universal_wigner_negativity hN sw hψ).choose_spec
    change sw.W ψ _ < sw.W ψ _ / 2
    linarith
  obtain ⟨T, hT_cov⟩ := hS_compact.elim_finite_subcover U hU_open hS_cov
  -- `S` is nonempty (standard basis vector `e₀`)
  have hS_nonempty : S.Nonempty := by
    refine ⟨fun k => if k.val = 0 then 1 else 0, ?_⟩
    simp only [S, Set.mem_ofPred_eq, innerC]
    rw [Finset.sum_eq_single (⟨0, Nat.succ_pos N⟩ : Fin (N + 1))]
    · simp
    · intro k _ hne
      have hk : k.val ≠ 0 := fun h0 => hne (Fin.ext h0)
      simp [hk]
    · intro h; exact absurd (Finset.mem_univ _) h
  have hT_nonempty : T.Nonempty := by
    obtain ⟨ψ₀, hψ₀⟩ := hS_nonempty
    obtain ⟨s, hs, _⟩ := Set.mem_iUnion₂.mp (hT_cov hψ₀)
    exact ⟨s, hs⟩
  let c : ℝ := T.inf' hT_nonempty (fun s => -(sw.W s.1 (universal_wigner_negativity hN sw s.2).choose / 2))
  refine ⟨c, ?_, ?_⟩
  · rw [Finset.lt_inf'_iff]
    intro s _
    have hlt := (universal_wigner_negativity hN sw s.2).choose_spec
    linarith
  · intro ψ hψ
    obtain ⟨s, hsT, hmem⟩ := Set.mem_iUnion₂.mp (hT_cov hψ)
    refine ⟨(universal_wigner_negativity hN sw s.2).choose, ?_⟩
    have hcle : c ≤ -(sw.W s.1 (universal_wigner_negativity hN sw s.2).choose / 2) :=
      Finset.inf'_le _ hsT
    change sw.W ψ (universal_wigner_negativity hN sw s.2).choose <
      sw.W s.1 (universal_wigner_negativity hN sw s.2).choose / 2 at hmem
    linarith

/-! ### Non-Vacuity Witness: Explicit Canonical Spin-`1/2` (`N = 1`) Stratonovich–Weyl System -/

private lemma int_0_2pi_cos : ∫ φ in (0 : ℝ)..(2 * Real.pi), Real.cos φ = 0 := by
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := (0 : ℝ)) (b := 2 * Real.pi)
    (fun φ _ => Real.hasDerivAt_sin φ) (Real.continuous_cos.intervalIntegrable 0 (2 * Real.pi))
  simpa [Real.sin_two_pi] using h

private lemma int_0_2pi_sin : ∫ φ in (0 : ℝ)..(2 * Real.pi), Real.sin φ = 0 := by
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := (0 : ℝ)) (b := 2 * Real.pi)
    (fun φ _ => by simpa using (Real.hasDerivAt_cos φ).neg)
    (Real.continuous_sin.intervalIntegrable 0 (2 * Real.pi))
  simpa [Real.cos_two_pi] using h

private lemma int_0_2pi_cos_sin : ∫ φ in (0 : ℝ)..(2 * Real.pi), Real.cos φ * Real.sin φ = 0 := by
  have hd : ∀ φ : ℝ, HasDerivAt (fun t => Real.sin t ^ 2 / 2) (Real.cos φ * Real.sin φ) φ := by
    intro φ
    have h := ((Real.hasDerivAt_sin φ).pow 2).div_const 2
    convert h using 1; ring
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := (0 : ℝ)) (b := 2 * Real.pi)
    (fun φ _ => hd φ) ((Real.continuous_cos.mul Real.continuous_sin).intervalIntegrable 0 (2 * Real.pi))
  simpa [Real.sin_two_pi] using h

private lemma int_0_2pi_cos_sq : ∫ φ in (0 : ℝ)..(2 * Real.pi), Real.cos φ ^ 2 = Real.pi := by
  have hd : ∀ φ : ℝ, HasDerivAt (fun t => (t + Real.sin t * Real.cos t) / 2) (Real.cos φ ^ 2) φ := by
    intro φ
    have h1 := ((hasDerivAt_id φ).add ((Real.hasDerivAt_sin φ).mul (Real.hasDerivAt_cos φ))).div_const 2
    have hval : (1 + (Real.cos φ * Real.cos φ + Real.sin φ * -Real.sin φ)) / 2 = Real.cos φ ^ 2 := by
      linear_combination -(1 / 2 : ℝ) * Real.cos_sq_add_sin_sq φ
    exact hval ▸ h1
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := (0 : ℝ)) (b := 2 * Real.pi)
    (fun φ _ => hd φ) ((Real.continuous_cos.pow 2).intervalIntegrable 0 (2 * Real.pi))
  rw [h]; simp [Real.sin_two_pi]

private lemma int_0_2pi_sin_sq : ∫ φ in (0 : ℝ)..(2 * Real.pi), Real.sin φ ^ 2 = Real.pi := by
  have hd : ∀ φ : ℝ, HasDerivAt (fun t => (t - Real.sin t * Real.cos t) / 2) (Real.sin φ ^ 2) φ := by
    intro φ
    have h1 := ((hasDerivAt_id φ).sub ((Real.hasDerivAt_sin φ).mul (Real.hasDerivAt_cos φ))).div_const 2
    have hval : (1 - (Real.cos φ * Real.cos φ + Real.sin φ * -Real.sin φ)) / 2 = Real.sin φ ^ 2 := by
      linear_combination -(1 / 2 : ℝ) * Real.cos_sq_add_sin_sq φ
    exact hval ▸ h1
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := (0 : ℝ)) (b := 2 * Real.pi)
    (fun φ _ => hd φ) ((Real.continuous_sin.pow 2).intervalIntegrable 0 (2 * Real.pi))
  rw [h]; simp [Real.sin_two_pi]

private lemma int_0_pi_sin : ∫ θ in (0 : ℝ)..Real.pi, Real.sin θ = 2 := by
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := (0 : ℝ)) (b := Real.pi)
    (fun θ _ => by simpa using (Real.hasDerivAt_cos θ).neg)
    (Real.continuous_sin.intervalIntegrable 0 Real.pi)
  rw [h]; norm_num

private lemma int_0_pi_sin_cos : ∫ θ in (0 : ℝ)..Real.pi, Real.sin θ * Real.cos θ = 0 := by
  have hd : ∀ θ : ℝ, HasDerivAt (fun t => Real.sin t ^ 2 / 2) (Real.sin θ * Real.cos θ) θ := by
    intro θ
    have h := ((Real.hasDerivAt_sin θ).pow 2).div_const 2
    convert h using 1; ring
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := (0 : ℝ)) (b := Real.pi)
    (fun θ _ => hd θ) ((Real.continuous_sin.mul Real.continuous_cos).intervalIntegrable 0 Real.pi)
  rw [h]; simp

private lemma int_0_pi_sin_cos_sq : ∫ θ in (0 : ℝ)..Real.pi, Real.sin θ * Real.cos θ ^ 2 = 2 / 3 := by
  have hd : ∀ θ : ℝ, HasDerivAt (fun t => -(Real.cos t ^ 3 / 3)) (Real.sin θ * Real.cos θ ^ 2) θ := by
    intro θ
    have h := (((Real.hasDerivAt_cos θ).pow 3).div_const 3).neg
    convert h using 1; ring
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := (0 : ℝ)) (b := Real.pi)
    (fun θ _ => hd θ) ((Real.continuous_sin.mul (Real.continuous_cos.pow 2)).intervalIntegrable 0 Real.pi)
  rw [h]; norm_num

private lemma int_0_pi_sin_cube : ∫ θ in (0 : ℝ)..Real.pi, Real.sin θ ^ 3 = 4 / 3 := by
  have hd : ∀ θ : ℝ, HasDerivAt (fun t => -Real.cos t + Real.cos t ^ 3 / 3) (Real.sin θ ^ 3) θ := by
    intro θ
    have h := (Real.hasDerivAt_cos θ).neg.add (((Real.hasDerivAt_cos θ).pow 3).div_const 3)
    have hval : - -Real.sin θ + 3 * Real.cos θ ^ (3 - 1) * -Real.sin θ / 3 = Real.sin θ ^ 3 := by
      linear_combination -Real.sin θ * Real.cos_sq_add_sin_sq θ
    exact hval ▸ h
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := (0 : ℝ)) (b := Real.pi)
    (fun θ _ => hd θ) ((Real.continuous_sin.pow 3).intervalIntegrable 0 Real.pi)
  rw [h]; norm_num

/-- Exact spherical average of a product of two affine functions on `S²`. -/
private lemma sphereAvg_prod_affine (c a₀ a₁ a₂ d b₀ b₁ b₂ : ℝ) :
    sphereAvg (fun u => (c + a₀ * u.1 0 + a₁ * u.1 1 + a₂ * u.1 2) *
                        (d + b₀ * u.1 0 + b₁ * u.1 1 + b₂ * u.1 2)) =
      c * d + (1 / 3 : ℝ) * (a₀ * b₀ + a₁ * b₁ + a₂ * b₂) := by
  unfold sphereAvg
  have hinner : ∀ θ : ℝ,
      ∫ φ in (0 : ℝ)..(2 * Real.pi),
        Real.sin θ * ((c + a₀ * (Real.sin θ * Real.cos φ) + a₁ * (Real.sin θ * Real.sin φ) + a₂ * Real.cos θ) *
          (d + b₀ * (Real.sin θ * Real.cos φ) + b₁ * (Real.sin θ * Real.sin φ) + b₂ * Real.cos θ)) =
      (2 * Real.pi * c * d) * Real.sin θ +
      (2 * Real.pi * (c * b₂ + a₂ * d)) * (Real.sin θ * Real.cos θ) +
      (2 * Real.pi * a₂ * b₂) * (Real.sin θ * Real.cos θ ^ 2) +
      (Real.pi * (a₀ * b₀ + a₁ * b₁)) * Real.sin θ ^ 3 := by
    intro θ
    set A : ℝ := Real.sin θ * ((c + a₂ * Real.cos θ) * (d + b₂ * Real.cos θ))
    set B : ℝ := Real.sin θ ^ 2 * ((c + a₂ * Real.cos θ) * b₀ + (d + b₂ * Real.cos θ) * a₀)
    set C : ℝ := Real.sin θ ^ 2 * ((c + a₂ * Real.cos θ) * b₁ + (d + b₂ * Real.cos θ) * a₁)
    set D : ℝ := Real.sin θ ^ 3 * (a₀ * b₁ + a₁ * b₀)
    set E : ℝ := Real.sin θ ^ 3 * (a₀ * b₀)
    set F : ℝ := Real.sin θ ^ 3 * (a₁ * b₁)
    have hexp : ∀ φ : ℝ,
        Real.sin θ * ((c + a₀ * (Real.sin θ * Real.cos φ) + a₁ * (Real.sin θ * Real.sin φ) + a₂ * Real.cos θ) *
          (d + b₀ * (Real.sin θ * Real.cos φ) + b₁ * (Real.sin θ * Real.sin φ) + b₂ * Real.cos θ)) =
        A + B * Real.cos φ + C * Real.sin φ + D * (Real.cos φ * Real.sin φ) +
        E * Real.cos φ ^ 2 + F * Real.sin φ ^ 2 := by
      intro φ; simp only [A, B, C, D, E, F]; ring
    simp_rw [hexp]
    have i1 : IntervalIntegrable (fun _ : ℝ => A) volume 0 (2 * Real.pi) := intervalIntegrable_const
    have i2 : IntervalIntegrable (fun φ => B * Real.cos φ) volume 0 (2 * Real.pi) :=
      (continuous_const.mul Real.continuous_cos).intervalIntegrable 0 (2 * Real.pi)
    have i3 : IntervalIntegrable (fun φ => C * Real.sin φ) volume 0 (2 * Real.pi) :=
      (continuous_const.mul Real.continuous_sin).intervalIntegrable 0 (2 * Real.pi)
    have i4 : IntervalIntegrable (fun φ => D * (Real.cos φ * Real.sin φ)) volume 0 (2 * Real.pi) :=
      (continuous_const.mul (Real.continuous_cos.mul Real.continuous_sin)).intervalIntegrable 0 (2 * Real.pi)
    have i5 : IntervalIntegrable (fun φ => E * Real.cos φ ^ 2) volume 0 (2 * Real.pi) :=
      (continuous_const.mul (Real.continuous_cos.pow 2)).intervalIntegrable 0 (2 * Real.pi)
    have i6 : IntervalIntegrable (fun φ => F * Real.sin φ ^ 2) volume 0 (2 * Real.pi) :=
      (continuous_const.mul (Real.continuous_sin.pow 2)).intervalIntegrable 0 (2 * Real.pi)
    rw [intervalIntegral.integral_add ((((i1.add i2).add i3).add i4).add i5) i6,
        intervalIntegral.integral_add (((i1.add i2).add i3).add i4) i5,
        intervalIntegral.integral_add ((i1.add i2).add i3) i4,
        intervalIntegral.integral_add (i1.add i2) i3,
        intervalIntegral.integral_add i1 i2]
    simp only [intervalIntegral.integral_const, smul_eq_mul, sub_zero,
      intervalIntegral.integral_const_mul, int_0_2pi_cos, int_0_2pi_sin,
      int_0_2pi_cos_sin, int_0_2pi_cos_sq, int_0_2pi_sin_sq]
    simp only [A, E, F]; ring
  have hcongr :
      ∫ θ in (0 : ℝ)..Real.pi, ∫ φ in (0 : ℝ)..(2 * Real.pi),
        Real.sin θ * ((c + a₀ * (SU2.sphVec θ φ).1 0 + a₁ * (SU2.sphVec θ φ).1 1 + a₂ * (SU2.sphVec θ φ).1 2) *
          (d + b₀ * (SU2.sphVec θ φ).1 0 + b₁ * (SU2.sphVec θ φ).1 1 + b₂ * (SU2.sphVec θ φ).1 2)) =
      ∫ θ in (0 : ℝ)..Real.pi,
        ((2 * Real.pi * c * d) * Real.sin θ +
         (2 * Real.pi * (c * b₂ + a₂ * d)) * (Real.sin θ * Real.cos θ) +
         (2 * Real.pi * a₂ * b₂) * (Real.sin θ * Real.cos θ ^ 2) +
         (Real.pi * (a₀ * b₀ + a₁ * b₁)) * Real.sin θ ^ 3) := by
    apply intervalIntegral.integral_congr
    intro θ _
    simpa [SU2.sphVec] using hinner θ
  rw [hcongr]
  have j1 : IntervalIntegrable (fun θ => (2 * Real.pi * c * d) * Real.sin θ) volume 0 Real.pi :=
    (continuous_const.mul Real.continuous_sin).intervalIntegrable 0 Real.pi
  have j2 : IntervalIntegrable (fun θ => (2 * Real.pi * (c * b₂ + a₂ * d)) * (Real.sin θ * Real.cos θ)) volume 0 Real.pi :=
    (continuous_const.mul (Real.continuous_sin.mul Real.continuous_cos)).intervalIntegrable 0 Real.pi
  have j3 : IntervalIntegrable (fun θ => (2 * Real.pi * a₂ * b₂) * (Real.sin θ * Real.cos θ ^ 2)) volume 0 Real.pi :=
    (continuous_const.mul (Real.continuous_sin.mul (Real.continuous_cos.pow 2))).intervalIntegrable 0 Real.pi
  have j4 : IntervalIntegrable (fun θ => (Real.pi * (a₀ * b₀ + a₁ * b₁)) * Real.sin θ ^ 3) volume 0 Real.pi :=
    (continuous_const.mul (Real.continuous_sin.pow 3)).intervalIntegrable 0 Real.pi
  rw [intervalIntegral.integral_add ((j1.add j2).add j3) j4,
      intervalIntegral.integral_add (j1.add j2) j3,
      intervalIntegral.integral_add j1 j2]
  simp only [intervalIntegral.integral_const_mul, int_0_pi_sin, int_0_pi_sin_cos,
    int_0_pi_sin_cos_sq, int_0_pi_sin_cube]
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  field_simp [hpi]
  ring

/-- Explicit Pauli linear expansion for spin-`1/2`:
`⟨χ | i D^{(1/2)}(g_π(u)) | χ⟩ = u₀ (χ₀* χ₁ + χ₁* χ₀) + u₁ (-i χ₀* χ₁ + i χ₁* χ₀) + u₂ (|χ₀|² - |χ₁|²)`. -/
private lemma spinHalf_pauli_linear (χ : Fin 2 → ℂ) (u : S2) :
    innerC χ (((I : ℂ) • spinRep 1 (SU2.piRot u)).mulVec χ) =
      (u.1 0 : ℂ) * (star (χ 0) * χ 1 + star (χ 1) * χ 0) +
      (u.1 1 : ℂ) * (-I * star (χ 0) * χ 1 + I * star (χ 1) * χ 0) +
      (u.1 2 : ℂ) * (star (χ 0) * χ 0 - star (χ 1) * χ 1) := by
  have hbw0 : (binomWeight 1 0 : ℂ) = 1 := by simp [binomWeight]
  have hbw1 : (binomWeight 1 1 : ℂ) = 1 := by simp [binomWeight]
  have hD00 : spinRep 1 (SU2.piRot u) 0 0 = -I * (u.1 2 : ℂ) := by
    simp [spinRep, rawRep, polyStep, hbw0, SU2.piRot_a, SU2.piRot_b]
  have hD01 : spinRep 1 (SU2.piRot u) 0 1 = -I * ((u.1 0 : ℂ) - I * (u.1 1 : ℂ)) := by
    simp [spinRep, rawRep, polyStep, hbw0, hbw1, SU2.piRot_a, SU2.piRot_b]
  have hD10 : spinRep 1 (SU2.piRot u) 1 0 = -I * ((u.1 0 : ℂ) + I * (u.1 1 : ℂ)) := by
    simp only [spinRep, rawRep, polyStep, hbw0, hbw1, SU2.piRot_a, SU2.piRot_b,
      Fin.val_one, Fin.val_zero, Nat.sub_self, pow_zero, one_mul, pow_one,
      div_one, Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_C,
      Polynomial.coeff_X, ↓reduceIte, Nat.one_ne_zero, mul_zero, add_zero,
      star_mul', star_sub, star_neg, RCLike.star_def, conj_I, conj_ofReal]
    ring
  have hD11 : spinRep 1 (SU2.piRot u) 1 1 = I * (u.1 2 : ℂ) := by
    simp only [spinRep, rawRep, polyStep, hbw1, SU2.piRot_a, SU2.piRot_b,
      Fin.val_one, Nat.sub_self, pow_zero, one_mul, pow_one, div_one,
      Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_C,
      Polynomial.coeff_X, ↓reduceIte, Nat.one_ne_zero, mul_one, zero_add,
      star_mul', star_neg, RCLike.star_def, conj_I, conj_ofReal]
    ring
  simp only [innerC, Matrix.mulVec, dotProduct, Matrix.smul_apply, smul_eq_mul]
  rw [Fin.sum_univ_two, Fin.sum_univ_two, Fin.sum_univ_two, hD00, hD01, hD10, hD11]
  linear_combination
    (-(star (χ 0) * χ 0 * (u.1 2 : ℂ)) - star (χ 0) * χ 1 * (u.1 0 : ℂ) -
     star (χ 1) * χ 0 * (u.1 0 : ℂ) + star (χ 1) * χ 1 * (u.1 2 : ℂ) +
     I * star (χ 0) * χ 1 * (u.1 1 : ℂ) - I * star (χ 1) * χ 0 * (u.1 1 : ℂ)) * I_sq

/-- Explicit canonical spin-`1/2` (`N = 1`) Stratonovich–Weyl spherical Wigner function:
`W_ψ(u) = (1/2) ⟨ψ | ψ⟩ + (√3 / 2) ⟨ψ | (u · σ) | ψ⟩`, where `u · σ = i D^{(1/2)}(g_π(u))`.
This concrete instance certifies that `StratonovichWeylSystem` is non-vacuous and faithful
to the exact quantum-mechanical definition. -/
def spinHalfStratonovichWeyl : StratonovichWeylSystem 1 where
  W ψ u := (1 / 2 : ℝ) * (innerC ψ ψ).re +
    (Real.sqrt 3 / 2) * (innerC ψ (((I : ℂ) • spinRep 1 (SU2.piRot u)).mulVec ψ)).re
  poly ψ := by
    let c0 : ℝ := (1 / 2 : ℝ) * (innerC ψ ψ).re
    let sx : ℝ := (Real.sqrt 3 / 2) * (star (ψ 0) * ψ 1 + star (ψ 1) * ψ 0).re
    let sy : ℝ := (Real.sqrt 3 / 2) * (-I * star (ψ 0) * ψ 1 + I * star (ψ 1) * ψ 0).re
    let sz : ℝ := (Real.sqrt 3 / 2) * (star (ψ 0) * ψ 0 - star (ψ 1) * ψ 1).re
    refine ⟨MvPolynomial.C c0 + MvPolynomial.C sx * MvPolynomial.X 0 +
            MvPolynomial.C sy * MvPolynomial.X 1 + MvPolynomial.C sz * MvPolynomial.X 2, ?_⟩
    intro u
    rw [spinHalf_pauli_linear]
    simp only [map_add, map_mul, MvPolynomial.eval_C, MvPolynomial.eval_X,
      add_re, mul_re, ofReal_re, ofReal_im, zero_mul, sub_zero, c0, sx, sy, sz]
    ring
  norm_eq ψ := by
    let c0 : ℝ := (1 / 2 : ℝ) * (innerC ψ ψ).re
    let sx : ℝ := (Real.sqrt 3 / 2) * (star (ψ 0) * ψ 1 + star (ψ 1) * ψ 0).re
    let sy : ℝ := (Real.sqrt 3 / 2) * (-I * star (ψ 0) * ψ 1 + I * star (ψ 1) * ψ 0).re
    let sz : ℝ := (Real.sqrt 3 / 2) * (star (ψ 0) * ψ 0 - star (ψ 1) * ψ 1).re
    have hW : ∀ u : S2,
        (1 / 2 : ℝ) * (innerC ψ ψ).re +
          (Real.sqrt 3 / 2) * (innerC ψ (((I : ℂ) • spinRep 1 (SU2.piRot u)).mulVec ψ)).re =
        (c0 + sx * u.1 0 + sy * u.1 1 + sz * u.1 2) * (1 + 0 * u.1 0 + 0 * u.1 1 + 0 * u.1 2) := by
      intro u
      rw [spinHalf_pauli_linear]
      simp only [add_re, mul_re, ofReal_re, ofReal_im, zero_mul, sub_zero, c0, sx, sy, sz]
      ring
    simp only [swIntegral]
    have havg := sphereAvg_prod_affine c0 sx sy sz 1 0 0 0
    have heq : (fun u => (1 / 2 : ℝ) * (innerC ψ ψ).re +
        (Real.sqrt 3 / 2) * (innerC ψ (((I : ℂ) • spinRep 1 (SU2.piRot u)).mulVec ψ)).re) =
        fun u => (c0 + sx * u.1 0 + sy * u.1 1 + sz * u.1 2) * (1 + 0 * u.1 0 + 0 * u.1 1 + 0 * u.1 2) :=
      funext hW
    rw [heq, havg]
    simp only [c0, Nat.cast_add, Nat.cast_one]
    ring
  covariant g ψ u := by
    have hnorm : innerC ((spinRep 1 g).mulVec ψ) ((spinRep 1 g).mulVec ψ) = innerC ψ ψ :=
      innerC_spinRep_unitary g ψ ψ
    have hpauli :
        innerC ((spinRep 1 g).mulVec ψ)
          (((I : ℂ) • spinRep 1 (SU2.piRot (SU2.actS2 g u))).mulVec ((spinRep 1 g).mulVec ψ)) =
        innerC ψ (((I : ℂ) • spinRep 1 (SU2.piRot u)).mulVec ψ) := by
      have hM : (spinRep 1 g)ᴴ * (((I : ℂ) • (spinRep 1 g * spinRep 1 (SU2.piRot u) * (spinRep 1 g)ᴴ)) *
          spinRep 1 g) = (I : ℂ) • spinRep 1 (SU2.piRot u) := by
        rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_assoc, Matrix.mul_assoc,
            spinRep_conjTranspose_mul_self, Matrix.mul_one, ← Matrix.mul_assoc,
            spinRep_conjTranspose_mul_self, Matrix.one_mul]
      rw [spinRep_piRot_actS2, innerC_mulVec_left, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
          Matrix.mul_assoc, hM]
    rw [hnorm, hpauli]
  tracial φ ψ := by
    let cφ : ℝ := (1 / 2 : ℝ) * (innerC φ φ).re
    let ax : ℝ := (Real.sqrt 3 / 2) * (star (φ 0) * φ 1 + star (φ 1) * φ 0).re
    let ay : ℝ := (Real.sqrt 3 / 2) * (-I * star (φ 0) * φ 1 + I * star (φ 1) * φ 0).re
    let az : ℝ := (Real.sqrt 3 / 2) * (star (φ 0) * φ 0 - star (φ 1) * φ 1).re
    let cψ : ℝ := (1 / 2 : ℝ) * (innerC ψ ψ).re
    let bx : ℝ := (Real.sqrt 3 / 2) * (star (ψ 0) * ψ 1 + star (ψ 1) * ψ 0).re
    let by_ : ℝ := (Real.sqrt 3 / 2) * (-I * star (ψ 0) * ψ 1 + I * star (ψ 1) * ψ 0).re
    let bz : ℝ := (Real.sqrt 3 / 2) * (star (ψ 0) * ψ 0 - star (ψ 1) * ψ 1).re
    have hlin : ∀ (χ : Fin 2 → ℂ) (u : S2),
        (1 / 2 : ℝ) * (innerC χ χ).re +
          (Real.sqrt 3 / 2) * (innerC χ (((I : ℂ) • spinRep 1 (SU2.piRot u)).mulVec χ)).re =
        (1 / 2 : ℝ) * (innerC χ χ).re +
        ((Real.sqrt 3 / 2) * (star (χ 0) * χ 1 + star (χ 1) * χ 0).re) * u.1 0 +
        ((Real.sqrt 3 / 2) * (-I * star (χ 0) * χ 1 + I * star (χ 1) * χ 0).re) * u.1 1 +
        ((Real.sqrt 3 / 2) * (star (χ 0) * χ 0 - star (χ 1) * χ 1).re) * u.1 2 := by
      intro χ u
      rw [spinHalf_pauli_linear]
      simp only [add_re, mul_re, ofReal_re, ofReal_im, zero_mul, sub_zero]
      ring
    simp only [swIntegral]
    have hfun : (fun u => ((1 / 2 : ℝ) * (innerC φ φ).re +
          (Real.sqrt 3 / 2) * (innerC φ (((I : ℂ) • spinRep 1 (SU2.piRot u)).mulVec φ)).re) *
        ((1 / 2 : ℝ) * (innerC ψ ψ).re +
          (Real.sqrt 3 / 2) * (innerC ψ (((I : ℂ) • spinRep 1 (SU2.piRot u)).mulVec ψ)).re)) =
        fun u => (cφ + ax * u.1 0 + ay * u.1 1 + az * u.1 2) *
          (cψ + bx * u.1 0 + by_ * u.1 1 + bz * u.1 2) :=
      funext fun u => by rw [hlin φ u, hlin ψ u]
    rw [hfun, sphereAvg_prod_affine]
    have hsq3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
    have hinner2 : ∀ (a b : Fin (1 + 1) → ℂ),
        innerC a b = star (a 0) * b 0 + star (a 1) * b 1 := fun a b => by
      unfold innerC
      exact Fin.sum_univ_two (fun k : Fin 2 => star (a k) * b k)
    simp only [cφ, ax, ay, az, cψ, bx, by_, bz, hinner2,
      Complex.normSq_apply, add_re, sub_re, mul_re, neg_re, I_re, I_im,
      add_im, mul_im, neg_im, RCLike.star_def, conj_re, conj_im,
      Nat.cast_add, Nat.cast_one]
    linear_combination
      (((φ 0).re * (φ 1).re + (φ 0).im * (φ 1).im) * ((ψ 0).re * (ψ 1).re + (ψ 0).im * (ψ 1).im) +
       ((φ 0).re * (φ 1).im - (φ 0).im * (φ 1).re) * ((ψ 0).re * (ψ 1).im - (ψ 0).im * (ψ 1).re) +
       ((φ 0).re ^ 2 + (φ 0).im ^ 2 - ((φ 1).re ^ 2 + (φ 1).im ^ 2)) *
         ((ψ 0).re ^ 2 + (ψ 0).im ^ 2 - ((ψ 1).re ^ 2 + (ψ 1).im ^ 2)) / 4) * (2 / 3 * hsq3)

end SU2Wigner

end
