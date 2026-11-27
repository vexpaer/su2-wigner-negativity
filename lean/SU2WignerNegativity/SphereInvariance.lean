import SU2WignerNegativity.SphereMoments
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

/-! # Rotation invariance of the spherical average on polynomials

We prove that `sphereAvg` is invariant under the full `SU(2)` / `SO(3)` rotation action
on all Cartesian polynomials restricted to `S²`:
1. Closed-form factorial formulas for `cosMoment`, `circleMoment`, `polarMoment`, and
   `cartesianMoment` show that `cartesianMoment a b c` is cyclically symmetric in `(a, b, c)`.
2. Therefore `sphereAvg` is invariant under the cyclic coordinate permutation `SU2.cyc`.
3. By `2π`-periodicity of the azimuthal integral, `sphereAvg` is invariant under `SU2.rotZ α`.
4. Since `SU2.rotY β = SU2.cyc⁻¹ * SU2.rotZ β * SU2.cyc` and every `g ∈ SU(2)` admits an
   Euler-angle factorization `rotZ α * rotY β * rotZ γ`, `sphereAvg` is invariant under all `g : SU2`.
-/

open Real Complex Finset MeasureTheory intervalIntegral
open scoped Matrix

noncomputable section
namespace SU2Wigner

/-! ### Closed Forms and Cyclic Symmetry of `cartesianMoment` -/

private theorem cosMoment_eq (p : ℕ) :
    cosMoment p = ((2 * p).factorial : ℝ) / ((4 : ℝ) ^ p * (p.factorial : ℝ) ^ 2) := by
  induction p with
  | zero => simp [cosMoment]
  | succ p ih =>
    rw [cosMoment, ih, Nat.mul_succ, Nat.factorial_succ (2 * p + 1), Nat.factorial_succ (2 * p),
      Nat.factorial_succ p, pow_succ]
    push_cast
    have h1 : ((p.factorial : ℝ)) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero p
    have h2 : (4 : ℝ) ^ p ≠ 0 := by positivity
    have h3 : ((p : ℝ) + 1) ≠ 0 := by positivity
    have h4 : (2 * (p : ℝ) + 2) ≠ 0 := by positivity
    field_simp
    ring

private theorem circleMoment_eq (p q : ℕ) :
    circleMoment p q =
      (((2 * p).factorial : ℝ) * ((2 * q).factorial : ℝ)) /
        ((4 : ℝ) ^ (p + q) * (p.factorial : ℝ) * (q.factorial : ℝ) * ((p + q).factorial : ℝ)) := by
  induction q generalizing p with
  | zero =>
    rw [circleMoment, cosMoment_eq]
    simp only [Nat.add_zero, Nat.mul_zero, Nat.factorial_zero, Nat.cast_one, mul_one]
    ring
  | succ q ih =>
    rw [circleMoment, ih p, ih (p + 1)]
    have hadd : p + 1 + q = p + q + 1 := by omega
    have hadd' : p + (q + 1) = p + q + 1 := by omega
    rw [hadd, hadd', Nat.mul_succ 2 p, Nat.mul_succ 2 q,
      Nat.factorial_succ (2 * p + 1), Nat.factorial_succ (2 * p),
      Nat.factorial_succ (2 * q + 1), Nat.factorial_succ (2 * q),
      Nat.factorial_succ p, Nat.factorial_succ q, Nat.factorial_succ (p + q), pow_succ]
    push_cast
    have hp : (p.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero p
    have hq : (q.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero q
    have hpq : ((p + q).factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero (p + q)
    have h4 : (4 : ℝ) ^ (p + q) ≠ 0 := by positivity
    have hp1 : ((p : ℝ) + 1) ≠ 0 := by positivity
    have hq1 : ((q : ℝ) + 1) ≠ 0 := by positivity
    have hpq1 : ((p : ℝ) + (q : ℝ) + 1) ≠ 0 := by positivity
    field_simp
    ring

private theorem polarMoment_odd (m r : ℕ) : polarMoment m (2 * r + 1) = 0 := by
  induction m generalizing r with
  | zero =>
    rw [polarMoment]
    have hpow : (-1 : ℝ) ^ (2 * r + 1 + 1) = 1 := by
      rw [show 2 * r + 1 + 1 = 2 * (r + 1) by omega, pow_mul]
      norm_num
    rw [hpow, sub_self, zero_div]
  | succ m ih =>
    rw [polarMoment, ih r, show 2 * r + 1 + 2 = 2 * (r + 1) + 1 by omega, ih (r + 1), sub_self]

private theorem polarMoment_even (m r : ℕ) :
    polarMoment m (2 * r) =
      2 * ((4 : ℝ) ^ m * (m.factorial : ℝ) * ((2 * r).factorial : ℝ) * ((m + r).factorial : ℝ)) /
        ((r.factorial : ℝ) * ((2 * (m + r) + 1).factorial : ℝ)) := by
  induction m generalizing r with
  | zero =>
    rw [polarMoment]
    have hpow : (-1 : ℝ) ^ (2 * r + 1) = -1 := by
      rw [pow_succ, pow_mul]; norm_num
    rw [hpow, Nat.zero_add, Nat.factorial_succ (2 * r), Nat.factorial_zero, pow_zero]
    push_cast
    have hr : (r.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero r
    have h2r : ((2 * r).factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero (2 * r)
    have h2r1 : (2 * (r : ℝ) + 1) ≠ 0 := by positivity
    field_simp
    ring
  | succ m ih =>
    rw [polarMoment, ih r, show 2 * r + 2 = 2 * (r + 1) by omega, ih (r + 1)]
    have hadd1 : m + (r + 1) = m + r + 1 := by omega
    have hadd2 : m + 1 + r = m + r + 1 := by omega
    have h2mr : 2 * (m + r + 1) + 1 = 2 * (m + r) + 1 + 2 := by omega
    rw [hadd1, hadd2, h2mr,
      Nat.mul_succ 2 r, Nat.factorial_succ (2 * r + 1), Nat.factorial_succ (2 * r),
      Nat.factorial_succ (2 * (m + r) + 1 + 1), Nat.factorial_succ (2 * (m + r) + 1),
      Nat.factorial_succ r, Nat.factorial_succ m, Nat.factorial_succ (m + r), pow_succ]
    push_cast
    have hr : (r.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero r
    have hr1 : ((r : ℝ) + 1) ≠ 0 := by positivity
    have h2mrf : ((2 * (m + r) + 1).factorial : ℝ) ≠ 0 := by
      exact_mod_cast Nat.factorial_ne_zero (2 * (m + r) + 1)
    have hden1 : (2 * ((m : ℝ) + (r : ℝ)) + 1 + 1) ≠ 0 := by positivity
    have hden2 : (2 * ((m : ℝ) + (r : ℝ)) + 1 + 1 + 1) ≠ 0 := by positivity
    field_simp
    ring

private theorem cartesianMoment_even (p q r : ℕ) :
    cartesianMoment (2 * p) (2 * q) (2 * r) =
      (((2 * p).factorial : ℝ) * ((2 * q).factorial : ℝ) * ((2 * r).factorial : ℝ) *
        ((p + q + r).factorial : ℝ)) /
      ((p.factorial : ℝ) * (q.factorial : ℝ) * (r.factorial : ℝ) *
        ((2 * (p + q + r) + 1).factorial : ℝ)) := by
  have ha : (2 * p) % 2 = 0 := by omega
  have hb : (2 * q) % 2 = 0 := by omega
  rw [cartesianMoment, ite_eq_left ⟨ha, hb⟩,
    show (2 * p) / 2 = p by omega, show (2 * q) / 2 = q by omega,
    show (2 * p + 2 * q) / 2 = p + q by omega,
    circleMoment_eq, polarMoment_even]
  have hp : (p.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero p
  have hq : (q.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero q
  have hr : (r.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero r
  have hpq : ((p + q).factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero (p + q)
  have h4 : (4 : ℝ) ^ (p + q) ≠ 0 := by positivity
  have hden : ((2 * (p + q + r) + 1).factorial : ℝ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero (2 * (p + q + r) + 1)
  field_simp

private theorem cartesianMoment_odd_right (a b r : ℕ) :
    cartesianMoment a b (2 * r + 1) = 0 := by
  unfold cartesianMoment
  split_ifs
  · rw [polarMoment_odd, mul_zero, zero_div]
  · rfl

theorem cartesianMoment_cyc (a b c : ℕ) :
    cartesianMoment c a b = cartesianMoment a b c := by
  by_cases ha : a % 2 = 0
  · by_cases hb : b % 2 = 0
    · by_cases hc : c % 2 = 0
      · have ha' : a = 2 * (a / 2) := by omega
        have hb' : b = 2 * (b / 2) := by omega
        have hc' : c = 2 * (c / 2) := by omega
        conv_lhs => rw [ha', hb', hc']
        conv_rhs => rw [ha', hb', hc']
        rw [cartesianMoment_even, cartesianMoment_even,
          show c / 2 + a / 2 + b / 2 = a / 2 + b / 2 + c / 2 by omega]
        ring
      · have hc' : c = 2 * (c / 2) + 1 := by omega
        rw [cartesianMoment, ite_eq_right (fun h => hc h.1), hc', cartesianMoment_odd_right]
    · have hb' : b = 2 * (b / 2) + 1 := by omega
      conv_lhs => rw [hb', cartesianMoment_odd_right]
      rw [cartesianMoment, ite_eq_right (fun h => hb h.2)]
  · rw [cartesianMoment, ite_eq_right (fun h => ha h.2), cartesianMoment, ite_eq_right (fun h => ha h.1)]

/-! ### Polynomial Rotation Action on `ℝ[x₀, x₁, x₂]` -/

private theorem toSO3_linear (g : SU2) (u : Vec3) (i : Fin 3) :
    SU2.toSO3 g u i =
      u 0 * SU2.toSO3 g ![1, 0, 0] i +
      u 1 * SU2.toSO3 g ![0, 1, 0] i +
      u 2 * SU2.toSO3 g ![0, 0, 1] i := by
  fin_cases i <;>
    simp [SU2.toSO3, RCLike.star_def, Complex.mul_re, Complex.mul_im] <;>
    ring

/-- Pull back a real Cartesian polynomial along `u ↦ actS2 g u`. -/
def rotatePoly (g : SU2) (P : MvPolynomial (Fin 3) ℝ) : MvPolynomial (Fin 3) ℝ :=
  MvPolynomial.eval₂Hom MvPolynomial.C
    (fun i =>
      MvPolynomial.C (SU2.toSO3 g ![1, 0, 0] i) * MvPolynomial.X 0 +
      MvPolynomial.C (SU2.toSO3 g ![0, 1, 0] i) * MvPolynomial.X 1 +
      MvPolynomial.C (SU2.toSO3 g ![0, 0, 1] i) * MvPolynomial.X 2) P

theorem eval_rotatePoly (g : SU2) (P : MvPolynomial (Fin 3) ℝ) (u : S2) :
    MvPolynomial.eval u.1 (rotatePoly g P) = MvPolynomial.eval (SU2.actS2 g u).1 P := by
  unfold rotatePoly
  induction P using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p i hp =>
    simp only [map_mul, MvPolynomial.eval₂Hom_X', MvPolynomial.eval_X, map_add,
      MvPolynomial.eval_C, hp]
    congr 1
    change SU2.toSO3 g ![1, 0, 0] i * u.1 0 + SU2.toSO3 g ![0, 1, 0] i * u.1 1 +
        SU2.toSO3 g ![0, 0, 1] i * u.1 2 = SU2.toSO3 g u.1 i
    rw [toSO3_linear g u.1 i]
    ring

/-! ### Generators of `SU(2)`: `rotZ`, `cyc`, and Euler Factorization -/

/-- `SU(2)` lift of the cyclic coordinate permutation `(x, y, z) ↦ (z, x, y)`. -/
def SU2.cyc : SU2 where
  a := (1 - I) / 2
  b := (-1 - I) / 2
  norm_eq := by
    simp only [RCLike.star_def, map_div₀, map_sub, map_neg, map_one, Complex.conj_I, map_ofNat]
    linear_combination -(1 / 2 : ℂ) * Complex.I_sq

private theorem SU2.actS2_cyc_coords (u : S2) :
    (SU2.actS2 SU2.cyc u).1 0 = u.1 2 ∧
    (SU2.actS2 SU2.cyc u).1 1 = u.1 0 ∧
    (SU2.actS2 SU2.cyc u).1 2 = u.1 1 := by
  refine ⟨?_, ?_, ?_⟩ <;>
    simp only [SU2.actS2, SU2.toSO3, SU2.cyc, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons, RCLike.star_def,
      map_div₀, map_sub, map_mul, map_neg, map_one, map_ofNat,
      Complex.conj_I, Complex.conj_ofReal,
      Complex.div_ofNat_re, Complex.div_ofNat_im,
      Complex.sub_re, Complex.add_re, Complex.mul_re, Complex.neg_re,
      Complex.sub_im, Complex.add_im, Complex.mul_im, Complex.neg_im,
      Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.one_re, Complex.one_im] <;>
    ring

private theorem SU2.rotZ_mul (α β : ℝ) : SU2.rotZ α * SU2.rotZ β = SU2.rotZ (α + β) := by
  ext
  · simp only [SU2.mul_a, SU2.rotZ_a, SU2.rotZ_b, zero_mul, sub_zero, ← Complex.exp_add]
    congr 1; push_cast; ring
  · simp

private theorem SU2.actS2_rotZ_sphVec (α θ φ : ℝ) :
    SU2.actS2 (SU2.rotZ α) (SU2.sphVec θ φ) = SU2.sphVec θ (φ + α) := by
  rw [← SU2.actS2_rotZ_rotY_northPole, ← SU2.actS2_mul, ← SU2.mul_assoc,
    SU2.rotZ_mul, add_comm α φ, SU2.actS2_rotZ_rotY_northPole]

private theorem SU2.cyc_inv_mul_rotZ_mul_cyc (β : ℝ) :
    SU2.cyc⁻¹ * SU2.rotZ β * SU2.cyc = SU2.rotY β := by
  set e : ℂ := Complex.exp (-I * ((β : ℂ) / 2))
  have he_star : star e = Complex.exp (I * ((β : ℂ) / 2)) := by
    simp only [e, RCLike.star_def, ← Complex.exp_conj, map_mul, map_neg, Complex.conj_I,
      map_div₀, Complex.conj_ofReal, map_ofNat, neg_neg]
  have he_val : e = (Real.cos (β / 2) : ℂ) - (Real.sin (β / 2) : ℂ) * I := by
    rw [show e = Complex.exp (((-(β / 2) : ℝ) : ℂ) * I) by
      simp only [e]; congr 1; push_cast; ring, Complex.exp_mul_I,
      ← Complex.ofReal_cos, ← Complex.ofReal_sin, Real.cos_neg, Real.sin_neg, Complex.ofReal_neg]
    ring
  have hes_val : star e = (Real.cos (β / 2) : ℂ) + (Real.sin (β / 2) : ℂ) * I := by
    rw [he_star, show I * ((β : ℂ) / 2) = ((β / 2 : ℝ) : ℂ) * I by push_cast; ring,
      Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
  ext
  · simp only [SU2.mul_a, SU2.mul_b, SU2.inv_a, SU2.inv_b, SU2.rotZ_a, SU2.rotZ_b,
      SU2.rotY_a, SU2.cyc, RCLike.star_def, map_zero, mul_zero, sub_zero, zero_add,
      map_div₀, map_sub, map_neg, map_one, Complex.conj_I, map_ofNat]
    change ((1 - -I) / 2 * e) * ((1 - I) / 2) -
        (-((-1 - I) / 2) * star e) * ((-1 - -I) / 2) = (Real.cos (β / 2) : ℂ)
    rw [hes_val, he_val]; ring_nf; simp [Complex.I_sq]; ring
  · simp only [SU2.mul_a, SU2.mul_b, SU2.inv_a, SU2.inv_b, SU2.rotZ_a, SU2.rotZ_b,
      SU2.rotY_b, SU2.cyc, RCLike.star_def, map_zero, mul_zero, sub_zero, zero_add,
      map_div₀, map_sub, map_one, Complex.conj_I, map_ofNat]
    change ((1 - -I) / 2 * e) * ((-1 - I) / 2) +
        (-((-1 - I) / 2) * star e) * ((1 - -I) / 2) = -(Real.sin (β / 2) : ℂ)
    rw [hes_val, he_val]; ring_nf; simp [Complex.I_sq]

private theorem SU2.exists_euler (g : SU2) :
    ∃ α β γ : ℝ, g = SU2.rotZ α * SU2.rotY β * SU2.rotZ γ := by
  have hnorm : ‖g.a‖ ^ 2 + ‖g.b‖ ^ 2 = 1 := by
    have h := congrArg Complex.re g.norm_eq
    simp only [Complex.add_re, RCLike.star_def, Complex.mul_conj, Complex.ofReal_re,
      Complex.one_re, Complex.normSq_eq_norm_sq] at h
    exact h
  have ha_le : ‖g.a‖ ≤ 1 := by nlinarith [norm_nonneg g.a, sq_nonneg ‖g.b‖]
  have ha_ge : -1 ≤ ‖g.a‖ := by linarith [norm_nonneg g.a]
  let β : ℝ := 2 * Real.arccos ‖g.a‖
  have hcos : Real.cos (β / 2) = ‖g.a‖ := by
    simp only [β, show 2 * Real.arccos ‖g.a‖ / 2 = Real.arccos ‖g.a‖ by ring]
    exact Real.cos_arccos ha_ge ha_le
  have hsin : Real.sin (β / 2) = ‖g.b‖ := by
    simp only [β, show 2 * Real.arccos ‖g.a‖ / 2 = Real.arccos ‖g.a‖ by ring, Real.sin_arccos]
    rw [show 1 - ‖g.a‖ ^ 2 = ‖g.b‖ ^ 2 by linarith, Real.sqrt_sq (norm_nonneg g.b)]
  let θa : ℝ := Complex.arg g.a
  let θb : ℝ := Complex.arg (-g.b)
  refine ⟨-(θa + θb), β, -(θa - θb), ?_⟩
  ext
  · simp only [SU2.mul_a, SU2.mul_b, SU2.rotZ_a, SU2.rotZ_b, SU2.rotY_a, SU2.rotY_b,
      zero_mul, mul_zero, sub_zero, add_zero, star_zero, hcos]
    rw [_root_.mul_assoc, mul_comm (‖g.a‖ : ℂ), ← _root_.mul_assoc, ← Complex.exp_add]
    have hexp : -I * ((-(θa + θb) : ℝ) / 2 : ℂ) + -I * ((-(θa - θb) : ℝ) / 2 : ℂ) =
        (θa : ℂ) * I := by push_cast; ring
    rw [hexp, mul_comm]
    exact (Complex.norm_mul_exp_arg_mul_I g.a).symm
  · simp only [SU2.mul_a, SU2.mul_b, SU2.rotZ_a, SU2.rotZ_b, SU2.rotY_a, SU2.rotY_b,
      zero_mul, mul_zero, sub_zero, add_zero, zero_add, hsin]
    rw [RCLike.star_def, ← Complex.exp_conj]
    simp only [map_mul, map_neg, Complex.conj_I, map_div₀, Complex.conj_ofReal, map_ofNat, neg_neg]
    rw [_root_.mul_assoc, mul_comm (-(‖g.b‖ : ℂ)), ← _root_.mul_assoc, ← Complex.exp_add]
    have hexp : -I * ((-(θa + θb) : ℝ) / 2 : ℂ) + I * ((-(θa - θb) : ℝ) / 2 : ℂ) =
        (θb : ℂ) * I := by push_cast; ring
    rw [hexp]
    have harg := Complex.norm_mul_exp_arg_mul_I (-g.b)
    rw [show -((‖g.b‖ : ℂ)) = -(‖-g.b‖ : ℂ) by simp]
    calc g.b = -(-g.b) := (neg_neg g.b).symm
      _ = -((‖-g.b‖ : ℂ) * Complex.exp ((θb : ℂ) * I)) := by rw [harg]
      _ = Complex.exp ((θb : ℂ) * I) * -(‖-g.b‖ : ℂ) := by ring

/-! ### Rotation Invariance of `sphereAvg` and `swIntegral` -/

theorem sphereAvg_rotZ (α : ℝ) (f : S2 → ℝ) :
    sphereAvg (fun u => f (SU2.actS2 (SU2.rotZ α) u)) = sphereAvg f := by
  unfold sphereAvg
  apply congrArg ((1 / (4 * Real.pi)) * ·)
  apply intervalIntegral.integral_congr
  intro θ _
  have hper : Function.Periodic (fun φ : ℝ => Real.sin θ * f (SU2.sphVec θ φ)) (2 * π) := by
    intro φ
    have hsph : SU2.sphVec θ (φ + 2 * π) = SU2.sphVec θ φ := by
      apply Subtype.ext; funext i; fin_cases i <;>
        simp [SU2.sphVec, Real.cos_add_two_pi, Real.sin_add_two_pi]
    dsimp only; rw [hsph]
  simp_rw [SU2.actS2_rotZ_sphVec]
  rw [intervalIntegral.integral_comp_add_right (fun φ : ℝ => Real.sin θ * f (SU2.sphVec θ φ)) α,
    zero_add, add_comm (2 * π) α]
  simpa only [zero_add] using hper.intervalIntegral_add_eq α 0

private theorem sphereAvg_cyc_poly (P : MvPolynomial (Fin 3) ℝ) :
    sphereAvg (fun u => MvPolynomial.eval (SU2.actS2 SU2.cyc u).1 P) =
      sphereAvg (fun u => MvPolynomial.eval u.1 P) := by
  have he_rot (u : S2) : MvPolynomial.eval (SU2.actS2 SU2.cyc u).1 P =
      ∑ e ∈ P.support, P.coeff e * sphereMonomial (e 1) (e 2) (e 0) u := by
    rw [MvPolynomial.eval_eq']
    apply Finset.sum_congr rfl; intro e _
    have hc := SU2.actS2_cyc_coords u
    simp only [sphereMonomial, Fin.prod_univ_three, hc.1, hc.2.1, hc.2.2]
    ring
  have he_orig (u : S2) : MvPolynomial.eval u.1 P =
      ∑ e ∈ P.support, P.coeff e * sphereMonomial (e 0) (e 1) (e 2) u := by
    rw [MvPolynomial.eval_eq']
    simp [sphereMonomial, Fin.prod_univ_three, mul_assoc]
  simp_rw [he_rot, he_orig, sphereAvg_expansion]
  apply Finset.sum_congr rfl; intro e _
  rw [cartesianMoment_cyc (e 1) (e 2) (e 0)]

/-- Rotation invariance of `sphereAvg` on all Cartesian polynomials on `S²`. -/
theorem sphereAvg_actS2_poly (g : SU2) (P : MvPolynomial (Fin 3) ℝ) :
    sphereAvg (fun u => MvPolynomial.eval (SU2.actS2 g u).1 P) =
      sphereAvg (fun u => MvPolynomial.eval u.1 P) := by
  let Inv (h : SU2) : Prop :=
    ∀ Q : MvPolynomial (Fin 3) ℝ,
      sphereAvg (fun u => MvPolynomial.eval (SU2.actS2 h u).1 Q) =
        sphereAvg (fun u => MvPolynomial.eval u.1 Q)
  have hmul : ∀ {g₁ g₂ : SU2}, Inv g₁ → Inv g₂ → Inv (g₁ * g₂) := by
    intro g₁ g₂ h₁ h₂ Q
    have hstep : (fun u : S2 => MvPolynomial.eval (SU2.actS2 (g₁ * g₂) u).1 Q) =
        fun u : S2 => MvPolynomial.eval (SU2.actS2 g₂ u).1 (rotatePoly g₁ Q) := by
      funext u; rw [SU2.actS2_mul, eval_rotatePoly]
    rw [hstep, h₂ (rotatePoly g₁ Q)]
    simp_rw [eval_rotatePoly]
    exact h₁ Q
  have hinv : ∀ {h : SU2}, Inv h → Inv h⁻¹ := by
    intro h hh Q
    calc sphereAvg (fun u => MvPolynomial.eval (SU2.actS2 h⁻¹ u).1 Q)
        = sphereAvg (fun u => MvPolynomial.eval u.1 (rotatePoly h⁻¹ Q)) := by
            simp_rw [eval_rotatePoly]
      _ = sphereAvg (fun u => MvPolynomial.eval (SU2.actS2 h u).1 (rotatePoly h⁻¹ Q)) :=
            (hh (rotatePoly h⁻¹ Q)).symm
      _ = sphereAvg (fun u => MvPolynomial.eval u.1 Q) := by
            congr 1; funext u
            rw [eval_rotatePoly, ← SU2.actS2_mul, SU2.inv_mul_cancel, SU2.actS2_one]
  have hrotZ (α : ℝ) : Inv (SU2.rotZ α) := fun Q =>
    sphereAvg_rotZ α (fun u => MvPolynomial.eval u.1 Q)
  have hcyc : Inv SU2.cyc := sphereAvg_cyc_poly
  have hrotY (β : ℝ) : Inv (SU2.rotY β) := by
    rw [← SU2.cyc_inv_mul_rotZ_mul_cyc β]
    exact hmul (hmul (hinv hcyc) (hrotZ β)) hcyc
  obtain ⟨α, β, γ, rfl⟩ := SU2.exists_euler g
  exact hmul (hmul (hrotZ α) (hrotY β)) (hrotZ γ) P

/-- Rotation invariance of `sphereAvg` on any function admitting a Cartesian polynomial representation. -/
theorem sphereAvg_actS2 {f : S2 → ℝ}
    (hf : ∃ P : MvPolynomial (Fin 3) ℝ, ∀ u : S2, f u = MvPolynomial.eval u.1 P) (g : SU2) :
    sphereAvg (fun u => f (SU2.actS2 g u)) = sphereAvg f := by
  obtain ⟨P, hP⟩ := hf
  have hf' : f = fun u => MvPolynomial.eval u.1 P := funext hP
  rw [hf']
  exact sphereAvg_actS2_poly g P

/-- Rotation invariance of `swIntegral` on polynomial spherical functions. -/
theorem swIntegral_actS2 (N : ℕ) {f : S2 → ℝ}
    (hf : ∃ P : MvPolynomial (Fin 3) ℝ, ∀ u : S2, f u = MvPolynomial.eval u.1 P) (g : SU2) :
    swIntegral N (fun u => f (SU2.actS2 g u)) = swIntegral N f := by
  unfold swIntegral
  rw [sphereAvg_actS2 hf g]

end SU2Wigner
end
