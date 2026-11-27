import SU2WignerNegativity.CoherentSymbol
import SU2WignerNegativity.SphereMoments

/-! # Resolution of the identity for spin coherent states -/

open Real Complex Finset MeasureTheory intervalIntegral
open scoped Matrix
noncomputable section
namespace SU2Wigner

private theorem integral_beta_nat (a b : ℕ) :
    (∫ x in (0:ℝ)..1, x^a*(1-x)^b) =
      ((a.factorial:ℝ)*(b.factorial:ℝ))/((a+b+1).factorial:ℝ) := by
  induction b generalizing a with
  | zero =>
    simp [integral_pow, Nat.factorial_succ, field]
  | succ b ih =>
    let F (x : ℝ) := x^a*(1-x)^(b+1)
    let G (x : ℝ) := x^(a+1)*(1-x)^b
    have hF : Continuous F := by unfold F; fun_prop
    have hG : Continuous G := by unfold G; fun_prop
    have hd (x : ℝ) : HasDerivAt (fun t : ℝ => t^(a+1)*(1-t)^(b+1))
        (((a:ℝ)+1)*F x - ((b:ℝ)+1)*G x) x := by
      convert (((hasDerivAt_id x).pow (a+1)).mul
        (((hasDerivAt_const x (1:ℝ)).sub (hasDerivAt_id x)).pow (b+1))) using 1
      · rfl
      · simp [F, G, Pi.pow_apply, Pi.sub_apply]; ring
    have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (a := (0:ℝ)) (b := 1) (fun x _ => hd x)
      ((hF.const_mul ((a:ℝ)+1)).sub (hG.const_mul ((b:ℝ)+1)) |>.intervalIntegrable _ _)
    rw [intervalIntegral.integral_sub (hF.const_mul _ |>.intervalIntegrable _ _)
      (hG.const_mul _ |>.intervalIntegrable _ _), intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul] at h
    simp only [one_pow, sub_self, zero_pow (Nat.succ_ne_zero _), mul_zero, zero_mul] at h
    change ((a:ℝ)+1)*(∫ x in (0:ℝ)..1, x^a*(1-x)^(b+1)) -
      ((b:ℝ)+1)*(∫ x in (0:ℝ)..1, x^(a+1)*(1-x)^b) = 0 at h
    rw [ih, show a+1+b+1 = a+(b+1)+1 by omega, Nat.factorial_succ a, Nat.factorial_succ b] at *
    push_cast at *
    have hn : ((a:ℝ)+1) ≠ 0 := by positivity
    apply mul_left_cancel₀ hn
    linear_combination h

private theorem beta_spherical (a b : ℕ) :
    (∫ θ in (0:ℝ)..π, Real.sin θ * Real.cos (θ/2)^(2*a) * Real.sin (θ/2)^(2*b)) =
      2 * ((b.factorial:ℝ)*(a.factorial:ℝ))/((b+a+1).factorial:ℝ) := by
  let T (θ : ℝ) := Real.sin (θ/2)^2
  have hd (θ : ℝ) : HasDerivAt T (Real.sin θ / 2) θ := by
    have h := ((Real.hasDerivAt_sin (θ/2)).comp θ ((hasDerivAt_id θ).div_const 2)).pow 2
    convert h using 1
    · rfl
    have he : 2*(θ/2) = θ := by ring
    rw [← he, Real.sin_two_mul, he]
    simp only [Nat.cast_ofNat, Nat.reduceSub, pow_one, id_eq, Function.comp_apply]; ring
  have h := intervalIntegral.integral_comp_mul_deriv (a := (0:ℝ)) (b := π)
    (g := fun x : ℝ => x^b*(1-x)^a) (fun θ _ => hd θ)
    (by fun_prop) (by fun_prop)
  have hT0 : T 0 = 0 := by simp [T]
  have hTπ : T π = 1 := by simp [T]
  rw [hT0,hTπ,integral_beta_nat] at h
  simp only [Function.comp_apply] at h
  have he (θ : ℝ) : Real.sin θ * Real.cos (θ/2)^(2*a) * Real.sin (θ/2)^(2*b) =
      2 * (T θ ^ b * (1-T θ)^a * (Real.sin θ/2)) := by
    rw [pow_mul, pow_mul]
    simp only [T, ← Real.cos_sq']; ring
  simp_rw [he, intervalIntegral.integral_const_mul]
  rw [h]; ring

/-- The coherent-state (Husimi) symbol of a vector. -/
def coherentSymbol (N : ℕ) (ψ : Fin (N+1) → ℂ) : S2 → ℝ :=
  diagonalSymbol N (Pi.single 0 1) ψ

theorem coherentSymbol_rotated (N : ℕ) (ψ : Fin (N+1) → ℂ) (g : SU2) :
    coherentSymbol N ψ (SU2.actS2 g SU2.northPole) =
      normSq (innerC (coherentVector N g) ψ) := by
  rw [coherentSymbol, diagonalSymbol_rotated, spinRep_inv]
  have h : ((spinRep N g)ᴴ.mulVec ψ) 0 = innerC (coherentVector N g) ψ := by
    simp [innerC, coherentVector, Matrix.mulVec, dotProduct, Matrix.conjTranspose_apply]
  simp [h, Pi.single_apply]

private def polarAmplitude (N : ℕ) (k : Fin (N+1)) (θ : ℝ) :=
  binomWeight N k * Real.cos (θ/2)^(N-k.val) * Real.sin (θ/2)^k.val

private theorem coherent_sph (N : ℕ) (k : Fin (N+1)) (θ φ : ℝ) :
    coherentVector N (SU2.rotZ φ * SU2.rotY θ) k =
      (polarAmplitude N k θ : ℂ) * Complex.exp (I * (2*(k.val:ℂ)-N) * ((φ:ℂ)/2)) := by
  unfold coherentVector
  rw [spinRep_highestColumn]
  have ha : (SU2.rotZ φ * SU2.rotY θ).a =
      (Real.cos (θ/2):ℂ) * Complex.exp (-I * ((φ:ℂ)/2)) := by
    simp [SU2.mul_a, mul_comm]
  have hb : -star (SU2.rotZ φ * SU2.rotY θ).b =
      (Real.sin (θ/2):ℂ) * Complex.exp (I * ((φ:ℂ)/2)) := by
    simp only [SU2.mul_b, SU2.rotZ_a, SU2.rotZ_b, SU2.rotY_a, SU2.rotY_b, zero_mul, add_zero,
      star_mul', star_neg, neg_neg, RCLike.star_def, conj_ofReal,
      ← Complex.exp_conj, map_mul, map_neg, conj_I, map_div₀, map_ofNat, neg_neg]
    ring
  rw [ha,hb,mul_pow,mul_pow]
  have he : Complex.exp (-I*((φ:ℂ)/2))^(N-k.val) * Complex.exp (I*((φ:ℂ)/2))^k.val =
      Complex.exp (I*(2*(k.val:ℂ)-N)*((φ:ℂ)/2)) := by
    rw [← Complex.exp_nat_mul, ← Complex.exp_nat_mul, ← Complex.exp_add]
    congr 1
    rw [Nat.cast_sub (by omega : k.val ≤ N)]
    ring
  rw [polarAmplitude]
  push_cast
  rw [← he]
  ring

private def polarCoefficient {N : ℕ} (ψ : Fin (N+1) → ℂ) (θ : ℝ)
    (k l : Fin (N+1)) : ℂ :=
  (polarAmplitude N k θ:ℂ) * (polarAmplitude N l θ:ℂ) * ψ k * star (ψ l)

private def frequency {N : ℕ} (k l : Fin (N+1)) : ℤ := (l.val:ℤ)-(k.val:ℤ)

private def polarMode {N : ℕ} (ψ : Fin (N+1) → ℂ) (θ : ℝ)
    (k l : Fin (N+1)) (φ : ℝ) : ℝ :=
  (polarCoefficient ψ θ k l * Complex.exp (I*(frequency k l:ℂ)*(φ:ℂ))).re

private theorem coherent_sph_inner (N : ℕ) (ψ : Fin (N+1) → ℂ) (θ φ : ℝ) :
    coherentSymbol N ψ (SU2.sphVec θ φ) = ∑ k, ∑ l, polarMode ψ θ k l φ := by
  rw [← SU2.actS2_rotZ_rotY_northPole, coherentSymbol_rotated]
  nth_rw 1 [← Complex.ofReal_re (normSq _)]
  rw [Complex.normSq_eq_conj_mul_self]
  rw [mul_comm ((starRingEnd ℂ) (innerC _ _))]
  simp only [innerC, coherent_sph, star_mul', RCLike.star_def, map_sum, conj_ofReal,
    ]
  rw [Finset.sum_mul]
  simp only [Finset.mul_sum, Complex.re_sum]
  apply Finset.sum_congr rfl; intro k _
  apply Finset.sum_congr rfl; intro l _
  unfold polarMode polarCoefficient
  congr 1
  simp only [map_mul, conj_ofReal, RingHomCompTriple.comp_apply, RingHom.id_apply, RCLike.star_def]
  have hphase :
      (starRingEnd ℂ) (Complex.exp (I*(2*(k.val:ℂ)-N)*((φ:ℂ)/2))) *
          Complex.exp (I*(2*(l.val:ℂ)-N)*((φ:ℂ)/2)) =
        Complex.exp (I*(frequency k l:ℂ)*(φ:ℂ)) := by
    rw [← Complex.exp_conj, ← Complex.exp_add]
    congr 1
    unfold frequency
    push_cast
    simp only [map_mul, map_sub, Complex.conj_I, Complex.conj_natCast, Complex.conj_ofReal, map_div₀,
      map_ofNat, neg_mul]
    ring
  rw [← hphase]
  ring

private theorem angular_average (m : ℤ) (c : ℂ) :
    (∫ φ in (0:ℝ)..(2*π), (c*Complex.exp (I*(m:ℂ)*(φ:ℂ))).re) =
      if m = 0 then (2*π)*c.re else 0 := by
  have hc : Continuous (fun φ : ℝ => c*Complex.exp (I*(m:ℂ)*(φ:ℂ))) := by fun_prop
  rw [show (∫ φ in (0:ℝ)..(2*π), (c*Complex.exp (I*(m:ℂ)*(φ:ℂ))).re) =
      (∫ φ in (0:ℝ)..(2*π), c*Complex.exp (I*(m:ℂ)*(φ:ℂ))).re from
        intervalIntegral_re (hc.intervalIntegrable _ _), intervalIntegral.integral_const_mul]
  by_cases hm : m = 0
  · subst m; simp [Complex.mul_re, mul_comm]
  · simp [hm, integral_exp_int_mul_I m hm]

private theorem polar_average (N : ℕ) (k : Fin (N+1)) :
    (∫ θ in (0:ℝ)..π, Real.sin θ * (polarAmplitude N k θ)^2) = 2/(N+1:ℝ) := by
  have he (θ : ℝ) : Real.sin θ * (polarAmplitude N k θ)^2 =
      (binomWeight N k)^2 * (Real.sin θ*Real.cos (θ/2)^(2*(N-k.val))*Real.sin (θ/2)^(2*k.val)) := by
    simp only [polarAmplitude, mul_pow, pow_mul]
    ring
  simp_rw [he, intervalIntegral.integral_const_mul, beta_spherical]
  have hk : k.val + (N-k.val) = N := by omega
  have hc : (N.choose k.val : ℝ) * (k.val.factorial:ℝ) * ((N-k.val).factorial:ℝ) =
      (N.factorial:ℝ) := by exact_mod_cast Nat.choose_mul_factorial_mul_factorial (by omega : k.val ≤ N)
  have hw : (binomWeight N k)^2 = (N.choose k.val : ℝ) := by exact_mod_cast binomWeight_sq N k
  rw [hw, hk, Nat.factorial_succ]
  push_cast
  have hn : (N.factorial:ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero N
  field_simp
  exact hc

private theorem coherent_innerAverage (N : ℕ) (ψ : Fin (N+1) → ℂ) (θ : ℝ) :
    (∫ φ in (0:ℝ)..(2*π), Real.sin θ*coherentSymbol N ψ (SU2.sphVec θ φ)) =
      (2*π) * ∑ k, normSq (ψ k) * (Real.sin θ * (polarAmplitude N k θ)^2) := by
  let F := polarMode ψ θ
  have hF (k l) : Continuous (F k l) := by unfold F polarMode; fun_prop
  have hrow (k : Fin (N+1)) :
      (∫ φ in (0:ℝ)..(2*π), ∑ l, F k l φ) = (2*π)*(polarCoefficient ψ θ k k).re := by
    rw [intervalIntegral.integral_finsetSum (fun l _ => (hF k l).intervalIntegrable _ _)]
    simp_rw [F, polarMode, angular_average]
    have hm (l) : frequency k l = 0 ↔ l=k := by
      simp only [frequency, sub_eq_zero, Int.natCast_inj, Fin.ext_iff]
    simp [hm]
  have hf : (fun φ => coherentSymbol N ψ (SU2.sphVec θ φ)) =
      fun φ : ℝ => ∑ k, ∑ l, F k l φ := funext (coherent_sph_inner N ψ θ)
  rw [intervalIntegral.integral_const_mul, hf]
  have hcol (k : Fin (N+1)) : Continuous (fun φ : ℝ => ∑ l, F k l φ) :=
    continuous_finsetSum _ (fun l _ => hF k l)
  have hI :
      (∫ φ in (0:ℝ)..(2*π), ∑ k, ∑ l, F k l φ) =
        ∑ k, ∫ φ in (0:ℝ)..(2*π), ∑ l, F k l φ :=
    intervalIntegral.integral_finsetSum (fun k _ => (hcol k).intervalIntegrable _ _)
  rw [hI]
  simp only [hrow, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  have hck : (polarCoefficient ψ θ k k).re = (polarAmplitude N k θ)^2 * normSq (ψ k) := by
    simp [polarCoefficient, RCLike.star_def, Complex.mul_re, Complex.mul_im, Complex.normSq_apply]; ring
  rw [hck]; ring

/-- The rotated highest-weight projectors resolve the identity for every spin. -/
theorem coherentSymbol_norm (N : ℕ) (ψ : Fin (N+1) → ℂ) :
    swIntegral N (coherentSymbol N ψ) = (innerC ψ ψ).re := by
  unfold swIntegral sphereAvg
  simp only [coherent_innerAverage]
  rw [intervalIntegral.integral_const_mul]
  rw [intervalIntegral.integral_finsetSum
    (fun k _ => (show Continuous (fun θ => normSq (ψ k) *
      (Real.sin θ * (polarAmplitude N k θ)^2)) by unfold polarAmplitude; fun_prop).intervalIntegrable _ _)]
  simp only [intervalIntegral.integral_const_mul, polar_average, Finset.mul_sum, innerC, Complex.re_sum]
  apply Finset.sum_congr rfl; intro k _
  rw [RCLike.star_def, ← Complex.normSq_eq_conj_mul_self, Complex.ofReal_re]
  rw [Nat.cast_add, Nat.cast_one]
  have hn : (N:ℝ)+1 ≠ 0 := by positivity
  field_simp
  ring

end SU2Wigner
end
