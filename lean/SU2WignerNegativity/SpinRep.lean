import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Data.Matrix.Basic
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Instances.Matrix
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp

/-!
# Explicit Spin-j Representation of SU(2) and Half-Integer π-Rotation Orthogonality

We construct the `(N + 1)`-dimensional irreducible unitary representation `D^{(N/2)}`
of `SU(2)` (where `N = 2j`) explicitly via homogeneous degree-`N` polynomials
(`Sym^N(ℂ^2)`), prove unitarity and all group homomorphism laws from first principles,
and prove the π-rotation orthogonality theorem for all odd `N` (all half-integer spins `j`).
-/

open Complex Polynomial Finset BigOperators
open scoped Matrix

noncomputable section

namespace SU2Wigner

/-- 3D real vectors represented as `Fin 3 → ℝ`. -/
abbrev Vec3 := Fin 3 → ℝ

/-- Euclidean inner product on `Vec3`. -/
def dot3 (u v : Vec3) : ℝ := u 0 * v 0 + u 1 * v 1 + u 2 * v 2

/-- Unit sphere `S² ⊂ ℝ³`. -/
abbrev S2 := { u : Vec3 // dot3 u u = 1 }

/-- Antipodal map on `S²`. -/
def S2.neg (u : S2) : S2 :=
  ⟨fun i => -u.1 i, by
    have h := u.2
    simp only [dot3] at h ⊢
    linarith⟩

/-- Special unitary group `SU(2)` parameterized by `(a, b) ∈ ℂ²` with `|a|² + |b|² = 1`,
representing the matrix `[[a, b], [-star b, star a]]`. -/
@[ext]
structure SU2 where
  a : ℂ
  b : ℂ
  norm_eq : a * star a + b * star b = 1

namespace SU2

def one : SU2 := ⟨1, 0, by simp⟩

def neg (g : SU2) : SU2 :=
  ⟨-g.a, -g.b, by
    have h := g.norm_eq
    simp only [star_neg]
    linear_combination h⟩

def mul (g₁ g₂ : SU2) : SU2 :=
  ⟨g₁.a * g₂.a - g₁.b * star g₂.b,
   g₁.a * g₂.b + g₁.b * star g₂.a,
   by
    have h₁ := g₁.norm_eq
    have h₂ := g₂.norm_eq
    simp only [star_sub, star_add, star_mul', star_star]
    linear_combination (g₁.a * star g₁.a + g₁.b * star g₁.b) * h₂ + h₁⟩

def inv (g : SU2) : SU2 :=
  ⟨star g.a, -g.b, by
    have h := g.norm_eq
    simp only [star_star, star_neg]
    linear_combination h⟩

instance : One SU2 := ⟨one⟩
instance : Mul SU2 := ⟨mul⟩
instance : Inv SU2 := ⟨inv⟩
instance : Neg SU2 := ⟨neg⟩

@[simp] lemma one_a : (1 : SU2).a = 1 := rfl
@[simp] lemma one_b : (1 : SU2).b = 0 := rfl
@[simp] lemma neg_a (g : SU2) : (-g).a = -g.a := rfl
@[simp] lemma neg_b (g : SU2) : (-g).b = -g.b := rfl
@[simp] lemma mul_a (g₁ g₂ : SU2) : (g₁ * g₂).a = g₁.a * g₂.a - g₁.b * star g₂.b := rfl
@[simp] lemma mul_b (g₁ g₂ : SU2) : (g₁ * g₂).b = g₁.a * g₂.b + g₁.b * star g₂.a := rfl
@[simp] lemma inv_a (g : SU2) : g⁻¹.a = star g.a := rfl
@[simp] lemma inv_b (g : SU2) : g⁻¹.b = -g.b := rfl

lemma mul_assoc (g₁ g₂ g₃ : SU2) : (g₁ * g₂) * g₃ = g₁ * (g₂ * g₃) := by
  ext <;> simp only [mul_a, mul_b, star_add, star_sub, star_mul', star_star] <;> ring

lemma one_mul (g : SU2) : (1 : SU2) * g = g := by
  ext <;> simp

lemma mul_one (g : SU2) : g * (1 : SU2) = g := by
  ext <;> simp

lemma mul_inv_cancel (g : SU2) : g * g⁻¹ = 1 := by
  ext
  · simp only [mul_a, inv_a, inv_b, one_a, star_neg]
    linear_combination g.norm_eq
  · simp only [mul_b, inv_a, inv_b, one_b, star_star]
    ring

lemma inv_mul_cancel (g : SU2) : g⁻¹ * g = 1 := by
  ext
  · simp only [mul_a, inv_a, inv_b, one_a]
    linear_combination g.norm_eq
  · simp only [mul_b, inv_a, inv_b, one_b]
    ring

/-- The SU(2) lift `g_π(u) = -i (u · σ)` of a π-rotation around unit axis `u ∈ S²`. -/
def piRot (u : S2) : SU2 :=
  ⟨-I * (u.1 2 : ℂ), -I * ((u.1 0 : ℂ) - I * (u.1 1 : ℂ)), by
    have hu : (u.1 0 : ℂ) ^ 2 + (u.1 1 : ℂ) ^ 2 + (u.1 2 : ℂ) ^ 2 = 1 := by
      have h := u.2
      simp only [dot3] at h
      exact_mod_cast (by nlinarith : u.1 0 ^ 2 + u.1 1 ^ 2 + u.1 2 ^ 2 = 1)
    simp only [star_mul', star_sub, star_neg, RCLike.star_def, conj_I, conj_ofReal]
    have hcalc : (-I * (u.1 2 : ℂ)) * (-( -I ) * (u.1 2 : ℂ)) +
        (-I * ((u.1 0 : ℂ) - I * (u.1 1 : ℂ))) * (-(-I) * ((u.1 0 : ℂ) - (-I) * (u.1 1 : ℂ))) =
        -((I ^ 2) * ((u.1 0 : ℂ) ^ 2 - (I ^ 2) * (u.1 1 : ℂ) ^ 2 + (u.1 2 : ℂ) ^ 2)) := by ring
    rw [hcalc, I_sq]
    linear_combination hu⟩

@[simp] lemma piRot_a (u : S2) : (piRot u).a = -I * (u.1 2 : ℂ) := rfl
@[simp] lemma piRot_b (u : S2) : (piRot u).b = -I * ((u.1 0 : ℂ) - I * (u.1 1 : ℂ)) := rfl

lemma piRot_injective {u v : S2} (h : piRot u = piRot v) : u = v := by
  have ha : (piRot u).a = (piRot v).a := congrArg SU2.a h
  have hb : (piRot u).b = (piRot v).b := congrArg SU2.b h
  simp only [piRot_a, piRot_b] at ha hb
  apply Subtype.ext
  funext i
  fin_cases i
  · have h0 := congrArg (fun z => (I * z).re) hb
    simpa [mul_sub, I_mul_I] using h0
  · have h1 := congrArg (fun z => (-z).re) hb
    simpa [mul_sub, I_mul_I] using h1
  · have h2 := congrArg (fun z => (I * z).re) ha
    simpa [I_mul_I] using h2

lemma piRot_sq (u : S2) : piRot u * piRot u = -(1 : SU2) := by
  have hu : (u.1 0 : ℂ) ^ 2 + (u.1 1 : ℂ) ^ 2 + (u.1 2 : ℂ) ^ 2 = 1 := by
    have h := u.2
    simp only [dot3] at h
    exact_mod_cast (by nlinarith : u.1 0 ^ 2 + u.1 1 ^ 2 + u.1 2 ^ 2 = 1)
  ext
  · simp only [mul_a, neg_a, one_a, piRot_a, piRot_b, star_mul', star_sub, star_neg,
      RCLike.star_def, conj_I, conj_ofReal]
    have hcalc : (-I * (u.1 2 : ℂ)) * (-I * (u.1 2 : ℂ)) -
        (-I * ((u.1 0 : ℂ) - I * (u.1 1 : ℂ))) * (-(-I) * ((u.1 0 : ℂ) - (-I) * (u.1 1 : ℂ))) =
        I ^ 2 * ((u.1 2 : ℂ) ^ 2 + (u.1 0 : ℂ) ^ 2 - I ^ 2 * (u.1 1 : ℂ) ^ 2) := by ring
    rw [hcalc, I_sq]
    linear_combination -hu
  · simp only [mul_b, neg_b, one_b, piRot_a, piRot_b, star_mul', star_neg,
      RCLike.star_def, conj_I, conj_ofReal]
    ring

lemma piRot_neg (u : S2) : piRot u.neg = -(piRot u) := by
  ext <;> simp only [piRot_a, piRot_b, neg_a, neg_b, S2.neg, ofReal_neg] <;> ring

/-- The SO(3) adjoint action `R_g(u)` of `g ∈ SU(2)` on `ℝ³`, characterized by
`g * (-i u · σ) * g⁻¹ = -i (R_g u · σ)`. -/
def toSO3 (g : SU2) (u : Vec3) : Vec3 :=
  let a := g.a; let b := g.b
  let ua : ℂ := -I * (u 2 : ℂ)
  let ub : ℂ := -I * ((u 0 : ℂ) - I * (u 1 : ℂ))
  let p_a := a * ua - b * star ub
  let p_b := a * ub + b * star ua
  let r_a := p_a * star a - p_b * star (-b)
  let r_b := p_a * (-b) + p_b * star (star a)
  ![(I * r_b).re, (-r_b).re, (I * r_a).re]

private lemma conj_piRot_re_zero (g : SU2) (u : S2) : (g * piRot u * g⁻¹).a.re = 0 := by
  simp only [mul_a, mul_b, inv_a, inv_b, piRot_a, piRot_b,
    star_mul', star_sub, star_neg, RCLike.star_def, conj_I, conj_ofReal]
  simp only [sub_re, add_re, mul_re, neg_re, I_re, I_im, ofReal_re, ofReal_im,
    conj_re, conj_im, mul_im, add_im, sub_im, neg_im]
  ring

/-- Action of `SU2` on the unit sphere `S²`. -/
def actS2 (g : SU2) (u : S2) : S2 :=
  ⟨toSO3 g u.1, by
    set h := g * piRot u * g⁻¹
    have h_im_a : h.a.re = 0 := conj_piRot_re_zero g u
    have hnorm_re : (h.a * star h.a + h.b * star h.b).re = 1 := by rw [h.norm_eq]; simp
    simp only [add_re, mul_re, RCLike.star_def, conj_re, conj_im, mul_neg, sub_neg_eq_add] at hnorm_re
    have h_eq_0 : (toSO3 g u.1) 0 = (I * h.b).re := rfl
    have h_eq_1 : (toSO3 g u.1) 1 = (-h.b).re := rfl
    have h_eq_2 : (toSO3 g u.1) 2 = (I * h.a).re := rfl
    rw [dot3, h_eq_0, h_eq_1, h_eq_2]
    simp only [mul_re, I_re, I_im, zero_mul, zero_sub, neg_re]
    nlinarith⟩

lemma piRot_actS2 (g : SU2) (u : S2) : piRot (actS2 g u) = g * piRot u * g⁻¹ := by
  set h := g * piRot u * g⁻¹
  have h_im_a : h.a.re = 0 := conj_piRot_re_zero g u
  ext
  · change -I * ((I * h.a).re : ℂ) = h.a
    apply Complex.ext
    · simp [h_im_a]
    · simp
  · change -I * (((I * h.b).re : ℂ) - I * ((-h.b).re : ℂ)) = h.b
    apply Complex.ext <;> simp

lemma actS2_one (u : S2) : actS2 1 u = u := by
  apply piRot_injective
  rw [piRot_actS2, one_mul]
  have h1 : (1 : SU2)⁻¹ = 1 := by ext <;> simp
  rw [h1, mul_one]

lemma actS2_mul (g₁ g₂ : SU2) (u : S2) : actS2 (g₁ * g₂) u = actS2 g₁ (actS2 g₂ u) := by
  apply piRot_injective
  rw [piRot_actS2, piRot_actS2, piRot_actS2]
  have hinv : (g₁ * g₂)⁻¹ = g₂⁻¹ * g₁⁻¹ := by
    have h : (g₁ * g₂)⁻¹ * (g₁ * g₂) * (g₂⁻¹ * g₁⁻¹) = g₂⁻¹ * g₁⁻¹ := by
      rw [inv_mul_cancel, one_mul]
    rw [mul_assoc, mul_assoc, ← mul_assoc g₂ g₂⁻¹ g₁⁻¹, mul_inv_cancel, one_mul,
        mul_inv_cancel, mul_one] at h
    exact h
  rw [hinv]
  simp only [mul_assoc]

/-- Standard rotation `R_z(φ)` in `SU(2)`: `diag(e^{-iφ/2}, e^{iφ/2})`. -/
def rotZ (φ : ℝ) : SU2 :=
  ⟨Complex.exp (-I * (φ / 2 : ℂ)), 0, by
    rw [zero_mul, add_zero, RCLike.star_def, ← Complex.exp_conj]
    simp only [map_mul, map_neg, conj_I, map_div₀, conj_ofReal, map_ofNat]
    rw [← Complex.exp_add]
    have : -I * (↑φ / 2) + - -I * (↑φ / 2) = 0 := by ring
    rw [this, Complex.exp_zero]⟩

@[simp] lemma rotZ_a (φ : ℝ) : (rotZ φ).a = Complex.exp (-I * (φ / 2 : ℂ)) := rfl
@[simp] lemma rotZ_b (φ : ℝ) : (rotZ φ).b = 0 := rfl

/-- Standard rotation `R_y(θ)` in `SU(2)`: `[[cos(θ/2), -sin(θ/2)], [sin(θ/2), cos(θ/2)]]`. -/
def rotY (θ : ℝ) : SU2 :=
  ⟨(Real.cos (θ / 2) : ℂ), (-Real.sin (θ / 2) : ℂ), by
    simp only [RCLike.star_def, conj_ofReal, ← ofReal_neg]
    exact_mod_cast (by linear_combination Real.cos_sq_add_sin_sq (θ / 2) :
      Real.cos (θ / 2) * Real.cos (θ / 2) + (-Real.sin (θ / 2)) * (-Real.sin (θ / 2)) = 1)⟩

@[simp] lemma rotY_a (θ : ℝ) : (rotY θ).a = (Real.cos (θ / 2) : ℂ) := rfl
@[simp] lemma rotY_b (θ : ℝ) : (rotY θ).b = (-Real.sin (θ / 2) : ℂ) := rfl

/-- Standard spherical axis `n(θ, φ) = (sin θ cos φ, sin θ sin φ, cos θ) ∈ S²`. -/
def sphVec (θ φ : ℝ) : S2 :=
  ⟨![Real.sin θ * Real.cos φ, Real.sin θ * Real.sin φ, Real.cos θ], by
    simp only [dot3, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.tail_cons, Matrix.head_cons]
    have h1 := Real.cos_sq_add_sin_sq φ
    have h2 := Real.cos_sq_add_sin_sq θ
    nlinarith⟩

/-- North pole `ẑ = (0, 0, 1) ∈ S²`. -/
def northPole : S2 := ⟨![0, 0, 1], by simp [dot3]⟩

lemma actS2_rotZ_rotY_northPole (θ φ : ℝ) :
    actS2 (rotZ φ * rotY θ) northPole = sphVec θ φ := by
  apply piRot_injective
  rw [piRot_actS2]
  set c : ℂ := (Real.cos (θ / 2) : ℂ)
  set s : ℂ := (Real.sin (θ / 2) : ℂ)
  set e : ℂ := Complex.exp (-I * (φ / 2 : ℂ))
  have he_star : star e = Complex.exp (I * (φ / 2 : ℂ)) := by
    simp only [e, RCLike.star_def, ← Complex.exp_conj, map_mul, map_neg, conj_I, map_div₀,
      conj_ofReal, map_ofNat, neg_neg]
  have he_mul : e * star e = 1 := by
    rw [he_star, ← Complex.exp_add]
    have : -I * (↑φ / 2) + I * (↑φ / 2) = 0 := by ring
    rw [this, Complex.exp_zero]
  have he2 : e * e = Complex.exp (-I * (φ : ℂ)) := by
    simp only [e, ← Complex.exp_add]
    congr 1; ring
  have hcos : c ^ 2 - s ^ 2 = (Real.cos θ : ℂ) := by
    simp only [c, s]
    have h := Real.cos_two_mul (θ / 2)
    rw [show 2 * (θ / 2) = θ by ring] at h
    exact_mod_cast (by rw [h]; linear_combination -Real.cos_sq_add_sin_sq (θ / 2) :
      Real.cos (θ / 2) ^ 2 - Real.sin (θ / 2) ^ 2 = Real.cos θ)
  have hsin : 2 * s * c = (Real.sin θ : ℂ) := by
    simp only [c, s]
    have h := Real.sin_two_mul (θ / 2)
    rw [show 2 * (θ / 2) = θ by ring] at h
    exact_mod_cast (by rw [h] : 2 * Real.sin (θ / 2) * Real.cos (θ / 2) = Real.sin θ)
  have hexp_phi : Complex.exp (-I * (φ : ℂ)) = (Real.cos φ : ℂ) - I * (Real.sin φ : ℂ) := by
    have h := Complex.exp_mul_I (-φ)
    rw [show (-↑φ : ℂ) * I = -I * ↑φ by ring] at h
    rw [h]
    simp [Complex.cos_neg, Complex.sin_neg, Complex.ofReal_cos, Complex.ofReal_sin]
    ring
  have hnp_a : (piRot northPole).a = -I := by
    simp [piRot_a, northPole]
  have hnp_b : (piRot northPole).b = 0 := by
    simp [piRot_b, northPole]
  have hsp_a : (piRot (sphVec θ φ)).a = -I * (Real.cos θ : ℂ) := by
    simp [piRot_a, sphVec]
  have hsp_b : (piRot (sphVec θ φ)).b =
      -I * ((Real.sin θ : ℂ) * (Real.cos φ : ℂ) - I * ((Real.sin θ : ℂ) * (Real.sin φ : ℂ))) := by
    simp [piRot_b, sphVec, ofReal_mul]
  ext
  · simp only [mul_a, mul_b, inv_a, inv_b, rotZ_a, rotZ_b, rotY_a, rotY_b, hnp_a, hnp_b, hsp_a,
      star_zero, star_neg, star_mul', RCLike.star_def, conj_I, conj_ofReal, mul_zero, zero_mul,
      add_zero, zero_add, sub_zero, neg_neg]
    change (e * c * -I) * (star e * c) - (e * -s * I) * -(star e * -s) = -I * ↑(Real.cos θ)
    linear_combination -I * (c ^ 2 - s ^ 2) * he_mul - I * hcos
  · simp only [mul_a, mul_b, inv_a, inv_b, rotZ_a, rotZ_b, rotY_a, rotY_b, hnp_a, hnp_b, hsp_b,
      star_zero, star_neg, star_mul', RCLike.star_def, conj_I, conj_ofReal, mul_zero,
      zero_mul, add_zero, zero_add, sub_zero, neg_neg, Complex.conj_conj]
    change (e * c * -I) * -(e * -s) + (e * -s * I) * (e * c) =
      -I * (↑(Real.sin θ) * ↑(Real.cos φ) - I * (↑(Real.sin θ) * ↑(Real.sin φ)))
    have hLHS : (e * c * -I) * -(e * -s) + (e * -s * I) * (e * c) =
        -I * (2 * s * c) * (e * e) := by ring
    rw [hLHS, hsin, he2, hexp_phi]
    ring

end SU2

/-! ### Homogeneous Evaluation Helper & Explicit Spin-`N/2` Representation `D^{(N/2)}` -/

/-- Homogeneous evaluation of a polynomial of degree `≤ m` at `(p, q)` in any `ℂ`-algebra. -/
def homogEval {R : Type*} [CommRing R] [Algebra ℂ R] (m : ℕ) (p q : R) (P : Polynomial ℂ) : R :=
  ∑ s ∈ range (m + 1), algebraMap ℂ R (P.coeff s) * p ^ (m - s) * q ^ s

lemma homogEval_mul_linear {R : Type*} [CommRing R] [Algebra ℂ R]
    (m : ℕ) (u v : ℂ) (p q : R) (P : Polynomial ℂ) (hdeg : P.natDegree ≤ m) :
    homogEval (m + 1) p q ((C u + C v * X) * P) =
      (algebraMap ℂ R u * p + algebraMap ℂ R v * q) * homogEval m p q P := by
  unfold homogEval
  have hcoeff : ∀ s : ℕ, ((C u + C v * X) * P).coeff s =
      u * P.coeff s + (if s = 0 then 0 else v * P.coeff (s - 1)) := by
    intro s
    rw [add_mul, coeff_add, coeff_C_mul, mul_assoc, coeff_C_mul]
    cases s with
    | zero => simp
    | succ s' => simp [coeff_X_mul]
  have hzero_top : P.coeff (m + 1) = 0 :=
    coeff_eq_zero_of_natDegree_lt (Nat.lt_succ_of_le hdeg)
  simp_rw [hcoeff, map_add, map_mul, add_mul]
  rw [Finset.sum_add_distrib]
  have hS1 : ∑ s ∈ range (m + 2),
      algebraMap ℂ R u * algebraMap ℂ R (P.coeff s) * p ^ (m + 1 - s) * q ^ s =
      algebraMap ℂ R u * p * ∑ s ∈ range (m + 1), algebraMap ℂ R (P.coeff s) * p ^ (m - s) * q ^ s := by
    rw [Finset.sum_range_succ, hzero_top, map_zero, mul_zero, zero_mul, zero_mul, add_zero,
        Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro s hs
    have hsm : s ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hs)
    have hsub : m + 1 - s = (m - s) + 1 := by omega
    rw [hsub, pow_succ]
    ring
  have hS2 : ∑ s ∈ range (m + 2),
      algebraMap ℂ R (if s = 0 then 0 else v * P.coeff (s - 1)) * p ^ (m + 1 - s) * q ^ s =
      algebraMap ℂ R v * q * ∑ s ∈ range (m + 1), algebraMap ℂ R (P.coeff s) * p ^ (m - s) * q ^ s := by
    rw [Finset.sum_range_succ', Finset.mul_sum]
    simp only [↓reduceIte, map_zero, zero_mul, add_zero, Nat.succ_ne_zero, Nat.add_sub_cancel,
      map_mul]
    apply Finset.sum_congr rfl
    intro s _
    have hsub : m + 1 - (s + 1) = m - s := by omega
    rw [hsub, pow_succ]
    ring
  rw [hS1, hS2]

lemma natDegree_linear_pow_le (u v : ℂ) (m : ℕ) :
    ((C u + C v * X) ^ m).natDegree ≤ m := by
  have h1 : (C u + C v * X).natDegree ≤ 1 := by
    calc (C u + C v * X).natDegree
        ≤ max (C u).natDegree (C v * X).natDegree := natDegree_add_le _ _
      _ ≤ max 0 (0 + 1) := by
          apply max_le_max
          · simp
          · calc (C v * X).natDegree ≤ (C v).natDegree + X.natDegree := natDegree_mul_le
              _ ≤ 0 + 1 := by simp
      _ = 1 := by norm_num
  calc ((C u + C v * X) ^ m).natDegree
      ≤ m * (C u + C v * X).natDegree := natDegree_pow_le
    _ ≤ m * 1 := Nat.mul_le_mul_left m h1
    _ = m := mul_one m

lemma homogEval_linear_pow_mul {R : Type*} [CommRing R] [Algebra ℂ R]
    (m₁ m₂ : ℕ) (u₁ v₁ u₂ v₂ : ℂ) (p q : R) :
    homogEval (m₁ + m₂) p q ((C u₁ + C v₁ * X) ^ m₁ * (C u₂ + C v₂ * X) ^ m₂) =
      (algebraMap ℂ R u₁ * p + algebraMap ℂ R v₁ * q) ^ m₁ *
      (algebraMap ℂ R u₂ * p + algebraMap ℂ R v₂ * q) ^ m₂ := by
  induction m₁ with
  | zero =>
    simp only [Nat.zero_add, pow_zero, one_mul]
    induction m₂ with
    | zero => simp [homogEval]
    | succ k ih =>
      rw [pow_succ', homogEval_mul_linear k u₂ v₂ p q _ (natDegree_linear_pow_le u₂ v₂ k),
          ih, pow_succ']
  | succ k ih =>
    rw [Nat.succ_add, pow_succ', mul_assoc]
    have hdeg : ((C u₁ + C v₁ * X) ^ k * (C u₂ + C v₂ * X) ^ m₂).natDegree ≤ k + m₂ :=
      le_trans natDegree_mul_le (add_le_add (natDegree_linear_pow_le _ _ _) (natDegree_linear_pow_le _ _ _))
    rw [homogEval_mul_linear (k + m₂) u₁ v₁ p q _ hdeg, ih, pow_succ', mul_assoc]

/-- Basis transformation polynomial `q_k(g)(X) = (a + b X)^{N-k} (-b̄ + ā X)^k`. -/
def polyStep (N : ℕ) (g : SU2) (k : Fin (N + 1)) : Polynomial ℂ :=
  (C g.a + C g.b * X) ^ (N - k.val) * (C (-star g.b) + C (star g.a) * X) ^ k.val

/-- Unnormalized matrix `M_{k,s}(g) = coeff_s (polyStep N g k)`. -/
def rawRep (N : ℕ) (g : SU2) : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ :=
  fun k s => (polyStep N g k).coeff s.val

lemma rawRep_one (N : ℕ) : rawRep N 1 = 1 := by
  ext k s
  simp only [rawRep, polyStep, SU2.one_a, SU2.one_b, map_one, map_zero, zero_mul,
    add_zero, neg_zero, zero_add, one_pow, one_mul, star_zero, star_one,
    coeff_X_pow, Matrix.one_apply]
  by_cases h : k = s
  · subst h; simp
  · have hne : s.val ≠ k.val := fun heq => h (Fin.ext heq.symm)
    simp [h, hne]

lemma rawRep_neg (N : ℕ) (g : SU2) : rawRep N (-g) = ((-1 : ℂ) ^ N) • rawRep N g := by
  ext k s
  simp only [rawRep, polyStep, SU2.neg_a, SU2.neg_b, Matrix.smul_apply, smul_eq_mul,
    star_neg, neg_neg, map_neg]
  have h1 : -C g.a + -C g.b * X = C (-1 : ℂ) * (C g.a + C g.b * X) := by simp; ring
  have h2 : C (star g.b) + -C (star g.a) * X = C (-1 : ℂ) * (-C (star g.b) + C (star g.a) * X) := by
    simp; ring
  rw [h1, h2, mul_pow, mul_pow]
  have hcomb :
      C (-1 : ℂ) ^ (N - k.val) * (C g.a + C g.b * X) ^ (N - k.val) *
        (C (-1 : ℂ) ^ k.val * (-C (star g.b) + C (star g.a) * X) ^ k.val) =
      C ((-1 : ℂ) ^ N) * ((C g.a + C g.b * X) ^ (N - k.val) *
        (-C (star g.b) + C (star g.a) * X) ^ k.val) := by
    have hk : (N - k.val) + k.val = N := Nat.sub_add_cancel (Nat.le_of_lt_succ k.isLt)
    calc _ = (C (-1 : ℂ) ^ (N - k.val) * C (-1 : ℂ) ^ k.val) *
              ((C g.a + C g.b * X) ^ (N - k.val) * (-C (star g.b) + C (star g.a) * X) ^ k.val) := by ring
      _ = C (-1 : ℂ) ^ ((N - k.val) + k.val) * _ := by rw [← pow_add]
      _ = C ((-1 : ℂ) ^ N) * _ := by rw [hk, C_pow]
  rw [hcomb, coeff_C_mul]

lemma rawRep_mul (N : ℕ) (g₁ g₂ : SU2) : rawRep N (g₁ * g₂) = rawRep N g₁ * rawRep N g₂ := by
  ext k t
  rw [Matrix.mul_apply]
  have hpoly :
      ∑ s : Fin (N + 1), C (rawRep N g₁ k s) * polyStep N g₂ s = polyStep N (g₁ * g₂) k := by
    have hsum :
        ∑ s : Fin (N + 1), C (rawRep N g₁ k s) * polyStep N g₂ s =
        homogEval N (C g₂.a + C g₂.b * X) (C (-star g₂.b) + C (star g₂.a) * X) (polyStep N g₁ k) := by
      unfold homogEval
      rw [← Fin.sum_univ_eq_sum_range]
      apply Finset.sum_congr rfl
      intro s _
      change C ((polyStep N g₁ k).coeff s.val) *
        ((C g₂.a + C g₂.b * X) ^ (N - s.val) * (C (-star g₂.b) + C (star g₂.a) * X) ^ s.val) = _
      rw [Polynomial.C_eq_algebraMap, mul_assoc]
    rw [hsum]
    have hk : N - k.val + k.val = N := Nat.sub_add_cancel (Nat.le_of_lt_succ k.isLt)
    have hlin := homogEval_linear_pow_mul (N - k.val) k.val g₁.a g₁.b (-star g₁.b) (star g₁.a)
      (C g₂.a + C g₂.b * X) (C (-star g₂.b) + C (star g₂.a) * X)
    rw [hk] at hlin
    change homogEval N (C g₂.a + C g₂.b * X) (C (-star g₂.b) + C (star g₂.a) * X)
      ((C g₁.a + C g₁.b * X) ^ (N - k.val) * (C (-star g₁.b) + C (star g₁.a) * X) ^ k.val) = _
    rw [hlin]
    unfold polyStep
    have ha :
        algebraMap ℂ (Polynomial ℂ) g₁.a * (C g₂.a + C g₂.b * X) +
        algebraMap ℂ (Polynomial ℂ) g₁.b * (C (-star g₂.b) + C (star g₂.a) * X) =
        C (g₁ * g₂).a + C (g₁ * g₂).b * X := by
      simp only [SU2.mul_a, SU2.mul_b, ← Polynomial.C_eq_algebraMap, map_sub, map_add,
        map_mul, map_neg]
      ring
    have hb :
        algebraMap ℂ (Polynomial ℂ) (-star g₁.b) * (C g₂.a + C g₂.b * X) +
        algebraMap ℂ (Polynomial ℂ) (star g₁.a) * (C (-star g₂.b) + C (star g₂.a) * X) =
        C (-star (g₁ * g₂).b) + C (star (g₁ * g₂).a) * X := by
      simp only [SU2.mul_a, SU2.mul_b, ← Polynomial.C_eq_algebraMap, star_add, star_sub,
        star_mul', star_star, map_sub, map_add, map_mul, map_neg]
      ring
    rw [ha, hb]
  have hcoeff := congrArg (fun P => P.coeff t.val) hpoly
  rw [finsetSum_coeff] at hcoeff
  simp_rw [coeff_C_mul] at hcoeff
  exact hcoeff.symm

/-- Weight factor `w_k = √(C(N, k))` for the orthonormal basis of `Sym^N(ℂ^2)`. -/
def binomWeight (N : ℕ) (k : Fin (N + 1)) : ℝ :=
  Real.sqrt (N.choose k.val : ℝ)

lemma binomWeight_pos (N : ℕ) (k : Fin (N + 1)) : 0 < binomWeight N k := by
  unfold binomWeight
  apply Real.sqrt_pos.mpr
  exact_mod_cast Nat.choose_pos (Nat.le_of_lt_succ k.isLt)

lemma binomWeight_sq (N : ℕ) (k : Fin (N + 1)) :
    (binomWeight N k : ℂ) ^ 2 = (N.choose k.val : ℂ) := by
  unfold binomWeight
  norm_cast
  exact Real.sq_sqrt (Nat.cast_nonneg _)

/-- The explicit `(N + 1) × (N + 1)` unitary spin-`N/2` representation matrix `D^{(N/2)}(g)`. -/
def spinRep (N : ℕ) (g : SU2) : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ :=
  fun k s => ((binomWeight N k : ℂ) / (binomWeight N s : ℂ)) * rawRep N g k s

lemma spinRep_one (N : ℕ) : spinRep N 1 = 1 := by
  ext k s
  simp only [spinRep, rawRep_one, Matrix.one_apply]
  by_cases h : k = s
  · subst h
    have hne : (binomWeight N k : ℂ) ≠ 0 := by exact_mod_cast (binomWeight_pos N k).ne'
    simp [div_self hne]
  · simp [h]

lemma spinRep_neg (N : ℕ) (g : SU2) : spinRep N (-g) = ((-1 : ℂ) ^ N) • spinRep N g := by
  ext k s
  simp only [spinRep, rawRep_neg, Matrix.smul_apply, smul_eq_mul]
  ring

lemma spinRep_mul (N : ℕ) (g₁ g₂ : SU2) : spinRep N (g₁ * g₂) = spinRep N g₁ * spinRep N g₂ := by
  ext k t
  rw [Matrix.mul_apply]
  simp only [spinRep, rawRep_mul, Matrix.mul_apply, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s _
  have hs : (binomWeight N s : ℂ) ≠ 0 := by exact_mod_cast (binomWeight_pos N s).ne'
  field_simp [hs]

/-- Reproducing-kernel proof of unitarity:
`∑_k C(N,k) * star(M_{k,r}(g)) * M_{k,s}(g) = C(N,r) δ_{r,s}`. -/
lemma rawRep_weighted_orthog (N : ℕ) (g : SU2) (r s : Fin (N + 1)) :
    ∑ k : Fin (N + 1), (N.choose k.val : ℂ) * star (rawRep N g k r) * rawRep N g k s =
      if r = s then (N.choose r.val : ℂ) else 0 := by
  let A : Polynomial (Polynomial ℂ) :=
    (C (C g.a + C g.b * X)) * (C (C (star g.a)) + C (C (star g.b)) * Polynomial.X)
  let B : Polynomial (Polynomial ℂ) :=
    (C (C (-star g.b) + C (star g.a) * X)) * (C (C (-g.b)) + C (C g.a) * Polynomial.X)
  have hAB : A + B = 1 + C X * Polynomial.X := by
    have hnorm := g.norm_eq
    have hCnorm : C (C (g.a * star g.a + g.b * star g.b)) = (1 : Polynomial (Polynomial ℂ)) := by
      rw [hnorm]; simp
    have hcalc : A + B =
        C (C (g.a * star g.a + g.b * star g.b)) +
        C (C (g.a * star g.a + g.b * star g.b)) * (C X * Polynomial.X) := by
      simp only [A, B, map_add, map_mul, map_neg]
      ring
    rw [hcalc, hCnorm, one_mul]
  have hpow : (A + B) ^ N = (1 + C X * Polynomial.X) ^ N := by rw [hAB]
  have hRHS : (((1 + C X * Polynomial.X) ^ N).coeff r.val).coeff s.val =
      if r = s then (N.choose r.val : ℂ) else 0 := by
    rw [add_pow, finsetSum_coeff]
    have hterm : ∀ i ∈ range (N + 1),
        ((1 : Polynomial (Polynomial ℂ)) ^ i * (C X * Polynomial.X) ^ (N - i) *
          ((N.choose i : ℕ) : Polynomial (Polynomial ℂ))).coeff r.val =
        if r.val = N - i then C (N.choose i : ℂ) * X ^ r.val else 0 := by
      intro i _
      rw [one_pow, one_mul, mul_pow, ← C_pow]
      have hre : C (X ^ (N - i)) * Polynomial.X ^ (N - i) * (↑(N.choose i) : Polynomial (Polynomial ℂ)) =
          C ((N.choose i : Polynomial ℂ) * X ^ (N - i)) * Polynomial.X ^ (N - i) := by
        rw [map_mul, C_eq_natCast]; ring
      rw [hre, coeff_C_mul_X_pow]
      split_ifs with h
      · rw [h, C_eq_natCast]
      · rfl
    rw [Finset.sum_congr rfl hterm]
    rw [Finset.sum_eq_single (N - r.val)]
    · have hr : r.val ≤ N := Nat.le_of_lt_succ r.isLt
      simp only [Nat.sub_sub_self hr, ↓reduceIte, Nat.choose_symm hr, coeff_C_mul_X_pow]
      by_cases hrs : r = s
      · subst hrs; simp
      · have hne : s.val ≠ r.val := fun heq => hrs (Fin.ext heq.symm)
        simp [hrs, hne]
    · intro i hi hne
      have hi' : i ≤ N := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
      have hr : r.val ≤ N := Nat.le_of_lt_succ r.isLt
      have hne' : r.val ≠ N - i := by omega
      simp [hne']
    · intro hmem
      exfalso; apply hmem; rw [Finset.mem_range]; omega
  have hconj_poly : ∀ (k : Fin (N + 1)),
      ((C (star g.a) + C (star g.b) * X) ^ (N - k.val) *
       (C (-g.b) + C g.a * X) ^ k.val).coeff r.val = star (rawRep N g k r) := by
    intro k
    have hmap : Polynomial.map (starRingEnd ℂ) (polyStep N g k) =
        (C (star g.a) + C (star g.b) * X) ^ (N - k.val) * (C (-g.b) + C g.a * X) ^ k.val := by
      unfold polyStep
      simp [Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_add, Polynomial.map_C,
        Polynomial.map_X, RCLike.star_def]
    rw [← hmap, coeff_map]
    rfl
  have hLHS : (((A + B) ^ N).coeff r.val).coeff s.val =
      ∑ k : Fin (N + 1), (N.choose k.val : ℂ) * star (rawRep N g k r) * rawRep N g k s := by
    rw [add_pow, finsetSum_coeff, finsetSum_coeff]
    rw [← Fin.sum_univ_eq_sum_range]
    have hrev :
        ∑ i : Fin (N + 1), ((A ^ i.val * B ^ (N - i.val) * ↑(N.choose i.val)).coeff r.val).coeff s.val =
        ∑ k : Fin (N + 1), ((A ^ (N - k.val) * B ^ k.val * ↑(N.choose k.val)).coeff r.val).coeff s.val := by
      let e : Equiv.Perm (Fin (N + 1)) :=
        { toFun := fun k => ⟨N - k.val, by omega⟩
          invFun := fun k => ⟨N - k.val, by omega⟩
          left_inv := fun k => by ext; dsimp; omega
          right_inv := fun k => by ext; dsimp; omega }
      refine Finset.sum_equiv e (fun _ => by simp) ?_
      intro k _
      have hk : k.val ≤ N := Nat.le_of_lt_succ k.isLt
      simp only [e, Equiv.coe_fn_mk, Nat.sub_sub_self hk, Nat.choose_symm hk]
    rw [hrev]
    apply Finset.sum_congr rfl
    intro k _
    have hfac : A ^ (N - k.val) * B ^ k.val * (↑(N.choose k.val) : Polynomial (Polynomial ℂ)) =
        C (C (N.choose k.val : ℂ) * polyStep N g k) *
        Polynomial.map Polynomial.C
          ((C (star g.a) + C (star g.b) * X) ^ (N - k.val) * (C (-g.b) + C g.a * X) ^ k.val) := by
      simp only [A, B, polyStep, mul_pow, Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_add,
        Polynomial.map_C, Polynomial.map_X, map_mul, map_add, map_pow, ← C_eq_natCast]
      ring
    rw [hfac, coeff_C_mul, coeff_map, coeff_mul_C, coeff_C_mul, hconj_poly k]
    unfold rawRep
    ring
  rw [← hLHS, hpow, hRHS]

/-- Unitarity of `spinRep N g`: `D(g)ᴴ * D(g) = 1`. -/
lemma spinRep_conjTranspose_mul_self (N : ℕ) (g : SU2) :
    (spinRep N g)ᴴ * spinRep N g = 1 := by
  ext r s
  rw [Matrix.mul_apply, Matrix.one_apply]
  simp only [Matrix.conjTranspose_apply, spinRep, star_mul', star_div₀]
  have hr : (binomWeight N r : ℂ) ≠ 0 := by exact_mod_cast (binomWeight_pos N r).ne'
  have hs : (binomWeight N s : ℂ) ≠ 0 := by exact_mod_cast (binomWeight_pos N s).ne'
  have hsum :
      ∑ k : Fin (N + 1),
        (star (binomWeight N k : ℂ) / star (binomWeight N r : ℂ) * star (rawRep N g k r)) *
        ((binomWeight N k : ℂ) / (binomWeight N s : ℂ) * rawRep N g k s) =
      (1 / ((binomWeight N r : ℂ) * (binomWeight N s : ℂ))) *
        ∑ k : Fin (N + 1), (N.choose k.val : ℂ) * star (rawRep N g k r) * rawRep N g k s := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    have hwk : star (binomWeight N k : ℂ) = (binomWeight N k : ℂ) := by simp
    have hwr : star (binomWeight N r : ℂ) = (binomWeight N r : ℂ) := by simp
    have hsq := binomWeight_sq N k
    rw [hwk, hwr, ← hsq]
    ring
  rw [hsum, rawRep_weighted_orthog]
  split_ifs with h
  · subst h
    have hsq := binomWeight_sq N r
    rw [← hsq]
    field_simp [hr]
  · simp

lemma spinRep_inv (N : ℕ) (g : SU2) : spinRep N g⁻¹ = (spinRep N g)ᴴ := by
  have h1 : (spinRep N g)ᴴ * spinRep N g = 1 := spinRep_conjTranspose_mul_self N g
  have h2 : spinRep N g * spinRep N g⁻¹ = 1 := by
    rw [← spinRep_mul, SU2.mul_inv_cancel, spinRep_one]
  calc spinRep N g⁻¹
      = 1 * spinRep N g⁻¹ := (Matrix.one_mul _).symm
    _ = ((spinRep N g)ᴴ * spinRep N g) * spinRep N g⁻¹ := by rw [h1]
    _ = (spinRep N g)ᴴ * (spinRep N g * spinRep N g⁻¹) := Matrix.mul_assoc _ _ _
    _ = (spinRep N g)ᴴ := by rw [h2, Matrix.mul_one]

lemma spinRep_mul_conjTranspose_self (N : ℕ) (g : SU2) :
    spinRep N g * (spinRep N g)ᴴ = 1 := by
  rw [← spinRep_inv, ← spinRep_mul, SU2.mul_inv_cancel, spinRep_one]

lemma spinRep_piRot_sq (N : ℕ) (u : S2) :
    spinRep N (SU2.piRot u) * spinRep N (SU2.piRot u) = ((-1 : ℂ) ^ N) • (1 : Matrix _ _ ℂ) := by
  rw [← spinRep_mul, SU2.piRot_sq, spinRep_neg, spinRep_one]

lemma spinRep_piRot_conjTranspose (N : ℕ) (u : S2) :
    (spinRep N (SU2.piRot u))ᴴ = ((-1 : ℂ) ^ N) • spinRep N (SU2.piRot u) := by
  have hsq := spinRep_piRot_sq N u
  have hmul : (spinRep N (SU2.piRot u))ᴴ * (spinRep N (SU2.piRot u) * spinRep N (SU2.piRot u)) =
      (spinRep N (SU2.piRot u))ᴴ * (((-1 : ℂ) ^ N) • 1) := congrArg _ hsq
  rw [← Matrix.mul_assoc, spinRep_conjTranspose_mul_self, Matrix.one_mul,
      Matrix.mul_smul, Matrix.mul_one] at hmul
  have hsign : ((-1 : ℂ) ^ N) * ((-1 : ℂ) ^ N) = 1 := by
    rw [← mul_pow]; norm_num
  have h2 := congrArg (fun M => ((-1 : ℂ) ^ N) • M) hmul
  simp only [smul_smul, hsign, one_smul] at h2
  exact h2.symm

lemma spinRep_piRot_neg (N : ℕ) (u : S2) :
    spinRep N (SU2.piRot u.neg) = ((-1 : ℂ) ^ N) • spinRep N (SU2.piRot u) := by
  rw [SU2.piRot_neg, spinRep_neg]

lemma spinRep_piRot_actS2 (N : ℕ) (g : SU2) (u : S2) :
    spinRep N (SU2.piRot (SU2.actS2 g u)) =
      spinRep N g * spinRep N (SU2.piRot u) * (spinRep N g)ᴴ := by
  rw [SU2.piRot_actS2, spinRep_mul, spinRep_mul, spinRep_inv]

/-! ### Complex Inner Product and Half-Integer π-Rotation Orthogonality -/

/-- Standard sesquilinear inner product `⟨φ | ψ⟩ = ∑_k star(φ_k) * ψ_k` on `ℂ^{N+1}`. -/
def innerC {N : ℕ} (φ ψ : Fin (N + 1) → ℂ) : ℂ :=
  ∑ k : Fin (N + 1), star (φ k) * ψ k

lemma innerC_conj_symm {N : ℕ} (φ ψ : Fin (N + 1) → ℂ) :
    star (innerC φ ψ) = innerC ψ φ := by
  simp [innerC, mul_comm]

lemma innerC_mulVec_left {N : ℕ} (M : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ)
    (φ ψ : Fin (N + 1) → ℂ) :
    innerC (M.mulVec φ) ψ = innerC φ (Mᴴ.mulVec ψ) := by
  simp only [innerC, Matrix.mulVec, dotProduct, Matrix.conjTranspose_apply,
    star_sum, star_mul', Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro i _
  ring

lemma innerC_spinRep_unitary {N : ℕ} (g : SU2) (φ ψ : Fin (N + 1) → ℂ) :
    innerC ((spinRep N g).mulVec φ) ((spinRep N g).mulVec ψ) = innerC φ ψ := by
  rw [innerC_mulVec_left, Matrix.mulVec_mulVec, spinRep_conjTranspose_mul_self, Matrix.one_mulVec]

/-- Continuity of `t ↦ spinRep N (g(t))` along a continuous path in `SU(2)`. -/
lemma continuous_rawRep_entry (N : ℕ) (k s : Fin (N + 1))
    {α : Type*} [TopologicalSpace α] (g : α → SU2)
    (ha : Continuous (fun x => (g x).a)) (hb : Continuous (fun x => (g x).b)) :
    Continuous (fun x => rawRep N (g x) k s) := by
  have hpow_cont : ∀ (m : ℕ) (u v : α → ℂ), Continuous u → Continuous v →
      ∀ j : ℕ, Continuous (fun x => ((C (u x) + C (v x) * X) ^ m).coeff j) := by
    intro m u v hu hv j
    have hcoeff : ∀ x, ((C (u x) + C (v x) * X) ^ m).coeff j =
        ∑ i ∈ range (m + 1),
          if j = m - i then (m.choose i : ℂ) * (u x) ^ i * (v x) ^ (m - i) else 0 := by
      intro x
      rw [add_pow, finsetSum_coeff]
      apply Finset.sum_congr rfl
      intro i _
      rw [mul_pow, ← C_pow, ← C_pow, ← C_eq_natCast]
      have hre : C (u x ^ i) * (C (v x ^ (m - i)) * X ^ (m - i)) * C (m.choose i : ℂ) =
          C ((m.choose i : ℂ) * u x ^ i * v x ^ (m - i)) * X ^ (m - i) := by
        simp only [map_mul]; ring
      rw [hre, coeff_C_mul_X_pow]
    simp_rw [hcoeff]
    apply continuous_finsetSum
    intro i _
    by_cases hij : j = m - i
    · simp only [hij, ↓reduceIte]
      fun_prop
    · simp only [hij, ↓reduceIte]
      exact continuous_const
  have hmul_cont : ∀ x, rawRep N (g x) k s =
      ∑ p ∈ Finset.antidiagonal s.val,
        ((C (g x).a + C (g x).b * X) ^ (N - k.val)).coeff p.1 *
        ((C (-star (g x).b) + C (star (g x).a) * X) ^ k.val).coeff p.2 := by
    intro x
    exact coeff_mul _ _ _
  simp_rw [hmul_cont]
  apply continuous_finsetSum
  intro p _
  apply Continuous.mul
  · exact hpow_cont (N - k.val) _ _ ha hb p.1
  · exact hpow_cont k.val _ _ (continuous_neg.comp (continuous_star.comp hb))
      (continuous_star.comp ha) p.2

lemma continuous_spinRep_entry (N : ℕ) (k s : Fin (N + 1))
    {α : Type*} [TopologicalSpace α] (g : α → SU2)
    (ha : Continuous (fun x => (g x).a)) (hb : Continuous (fun x => (g x).b)) :
    Continuous (fun x => spinRep N (g x) k s) := by
  unfold spinRep
  exact continuous_const.mul (continuous_rawRep_entry N k s g ha hb)

/-- **Theorem (Half-Integer π-Rotation Orthogonality)**:
For every odd `N` (i.e. half-integer spin `j = N / 2 ∈ {1/2, 3/2, 5/2, ...}`) and every
state `ψ : Fin (N + 1) → ℂ`, there exists an axis `u_* ∈ S²` such that
`⟨ψ | D^{(N/2)}(g_π(u_*)) | ψ⟩ = 0`. -/
theorem pi_ortho_odd {N : ℕ} (hN : Odd N) (ψ : Fin (N + 1) → ℂ) :
    ∃ u : S2, innerC ψ ((spinRep N (SU2.piRot u)).mulVec ψ) = 0 := by
  have hsign : (-1 : ℂ) ^ N = -1 := hN.neg_one_pow
  let γ : ℝ → S2 := fun t => SU2.sphVec t 0
  let F : ℝ → ℂ := fun t => I * innerC ψ ((spinRep N (SU2.piRot (γ t))).mulVec ψ)
  have hreal : ∀ t : ℝ, star (F t) = F t := by
    intro t
    simp only [F, star_mul', RCLike.star_def, conj_I]
    rw [← RCLike.star_def, innerC_conj_symm, innerC_mulVec_left,
        spinRep_piRot_conjTranspose, hsign]
    have hsmul : ((-1 : ℂ) • spinRep N (SU2.piRot (γ t))).mulVec ψ =
        (-1 : ℂ) • ((spinRep N (SU2.piRot (γ t))).mulVec ψ) := Matrix.smul_mulVec _ _ _
    rw [hsmul]
    simp only [innerC, Pi.smul_apply, smul_eq_mul]
    have hneg : ∑ x : Fin (N + 1), star (ψ x) * (-1 * (spinRep N (SU2.piRot (γ t))).mulVec ψ x) =
        -(∑ x : Fin (N + 1), star (ψ x) * (spinRep N (SU2.piRot (γ t))).mulVec ψ x) := by
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl; intro x _; ring
    rw [hneg]; ring
  have hFim : ∀ t : ℝ, (F t).im = 0 := by
    intro t
    have h := congrArg Complex.im (hreal t)
    simp only [RCLike.star_def, conj_im] at h
    linarith
  have hγ_pi : γ Real.pi = (γ 0).neg := by
    apply Subtype.ext
    funext i
    fin_cases i <;> simp [γ, SU2.sphVec, S2.neg]
  have hF_pi : F Real.pi = -F 0 := by
    simp only [F, hγ_pi, spinRep_piRot_neg, hsign]
    have hsmul : ((-1 : ℂ) • spinRep N (SU2.piRot (γ 0))).mulVec ψ =
        (-1 : ℂ) • ((spinRep N (SU2.piRot (γ 0))).mulVec ψ) := Matrix.smul_mulVec _ _ _
    rw [hsmul]
    simp only [innerC, Pi.smul_apply, smul_eq_mul]
    have hneg : ∑ x : Fin (N + 1), star (ψ x) * (-1 * (spinRep N (SU2.piRot (γ 0))).mulVec ψ x) =
        -(∑ x : Fin (N + 1), star (ψ x) * (spinRep N (SU2.piRot (γ 0))).mulVec ψ x) := by
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl; intro x _; ring
    rw [hneg]; ring
  let f : ℝ → ℝ := fun t => (F t).re
  have hf_cont : Continuous f := by
    apply Complex.continuous_re.comp
    apply continuous_const.mul
    simp only [innerC, Matrix.mulVec, dotProduct]
    apply continuous_finsetSum
    intro k _
    apply continuous_const.mul
    apply continuous_finsetSum
    intro s _
    apply Continuous.mul _ continuous_const
    apply continuous_spinRep_entry
    · have h : (fun t => (SU2.piRot (γ t)).a) = fun t => -I * (Real.cos t : ℂ) := by
        funext t; simp [SU2.piRot_a, γ, SU2.sphVec]
      rw [h]; fun_prop
    · have h : (fun t => (SU2.piRot (γ t)).b) =
          fun t => -I * (((Real.sin t * Real.cos 0 : ℝ) : ℂ) - I * ((Real.sin t * Real.sin 0 : ℝ) : ℂ)) := by
        funext t; simp [SU2.piRot_b, γ, SU2.sphVec]
      rw [h]; fun_prop
  have hf_pi : f Real.pi = -f 0 := by
    simp only [f, hF_pi, neg_re]
  have h0_mem : (0 : ℝ) ∈ Set.uIcc (f 0) (f Real.pi) := by
    rw [hf_pi]
    by_cases h0 : 0 ≤ f 0
    · rw [Set.uIcc_of_ge (by linarith)]; exact ⟨by linarith, h0⟩
    · rw [Set.uIcc_of_le (by linarith)]; exact ⟨by linarith, by linarith⟩
  have hIVT : Set.uIcc (f 0) (f Real.pi) ⊆ f '' Set.Icc 0 Real.pi := by
    rw [← Set.uIcc_of_le Real.pi_pos.le]
    exact intermediate_value_uIcc hf_cont.continuousOn
  obtain ⟨t₀, _, ht₀⟩ := hIVT h0_mem
  refine ⟨γ t₀, ?_⟩
  have hFt₀ : F t₀ = 0 := Complex.ext ht₀ (hFim t₀)
  have hI : (I : ℂ) ≠ 0 := Complex.I_ne_zero
  exact (mul_eq_zero.mp hFt₀).resolve_left hI

end SU2Wigner

end
