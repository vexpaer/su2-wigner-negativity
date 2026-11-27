import SU2WignerNegativity.DiagonalKernel
import Mathlib.Algebra.MvPolynomial.Funext

/-! # Informational completeness of spin coherent states

The north-pole seed is the highest-weight projector. Its orbit separates all
complex matrices. This follows from independence of the monomials
`(conj z)^i z^j` on the stereographic chart.
-/

open Complex Finset
open scoped Matrix
noncomputable section
namespace SU2Wigner

private abbrev Poly₂ := MvPolynomial (Fin 2) ℂ
private def x : Poly₂ := MvPolynomial.X 0
private def y : Poly₂ := MvPolynomial.X 1
private def i : Poly₂ := MvPolynomial.C I

private def mix : Poly₂ →+* Poly₂ :=
  MvPolynomial.eval₂Hom MvPolynomial.C ![x-i*y,x+i*y]

private def unmix : Poly₂ →+* Poly₂ :=
  MvPolynomial.eval₂Hom MvPolynomial.C
    ![(x+y)*MvPolynomial.C (1/2), (y-x)*MvPolynomial.C (-I/2)]

private theorem unmix_mix (p : Poly₂) : unmix (mix p) = p := by
  let half : Poly₂ := MvPolynomial.C (1/2 : ℂ)
  have htwo : half + half = 1 := by
    dsimp [half]
    rw [← map_add]
    norm_num
  have hii : i * MvPolynomial.C (-I/2) = half := by
    unfold i
    rw [← map_mul, show I * (-I/2) = (1/2:ℂ) by linear_combination -(1/2) * Complex.I_sq]
  have hx : unmix x = (x+y)*half := by
    exact MvPolynomial.eval₂Hom_X' _ _ 0
  have hy : unmix y = (y-x)*MvPolynomial.C (-I/2) := by
    exact MvPolynomial.eval₂Hom_X' _ _ 1
  have hi : unmix i = i := by simp [i, unmix]
  have hxy : unmix (i*y) = (y-x)*half := by rw [map_mul, hi, hy, ← hii]; ring
  have h : unmix.comp mix = RingHom.id Poly₂ := by
    apply MvPolynomial.ringHom_ext
    · intro c; simp [mix, unmix]
    · intro j
      fin_cases j
      · simp only [RingHom.comp_apply, RingHom.id_apply, mix, MvPolynomial.eval₂Hom_X']
        change unmix (x-i*y) = x
        rw [map_sub, hx, hxy]
        linear_combination x * htwo
      · simp only [RingHom.comp_apply, RingHom.id_apply, mix, MvPolynomial.eval₂Hom_X']
        change unmix (x+i*y) = y
        rw [map_add, hx, hxy]
        linear_combination y * htwo
  exact DFunLike.congr_fun h p

private theorem realSlice (p : Poly₂)
    (h : ∀ z : ℂ, MvPolynomial.eval ![star z,z] p = 0) : p = 0 := by
  have hm : mix p = 0 := by
    let R : Set ℂ := Set.range ((↑) : ℝ → ℂ)
    have hR : R.Infinite := Set.infinite_range_of_injective Complex.ofReal_injective
    apply MvPolynomial.funext_set (fun _ => R) (fun _ => hR)
    intro v hv
    obtain ⟨a, ha⟩ := hv 0 (Set.mem_univ _)
    obtain ⟨b, hb⟩ := hv 1 (Set.mem_univ _)
    have he : (fun j => MvPolynomial.eval v (![x-i*y,x+i*y] j)) =
        ![star ((a:ℂ) + I*(b:ℂ)), (a:ℂ) + I*(b:ℂ)] := by
      funext j
      fin_cases j <;> simp [x,y,i,← ha,← hb, RCLike.star_def, Complex.conj_I, sub_eq_add_neg]
    change MvPolynomial.eval v (MvPolynomial.eval₂Hom MvPolynomial.C _ p) = _
    rw [MvPolynomial.map_eval₂Hom, he]
    have hc : (MvPolynomial.eval v).comp MvPolynomial.C = RingHom.id ℂ := by ext w; simp
    rw [hc]
    exact h _
  simpa only [unmix_mix, map_zero] using congrArg unmix hm

private def powers (k l : ℕ) : Fin 2 →₀ ℕ :=
  Finsupp.single 0 k + Finsupp.single 1 l

private theorem powers_eval (k l : ℕ) (a b c : ℂ) :
    MvPolynomial.eval ![a,b] (MvPolynomial.monomial (powers k l) c) = c*a^k*b^l := by
  rw [MvPolynomial.eval_monomial, Finsupp.prod_pow]
  simp [powers, Fin.prod_univ_two, mul_assoc]

/-- The diagonal anti-holomorphic/holomorphic monomials are independent. -/
theorem conjugateMonomials_independent {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℂ)
    (h : ∀ z : ℂ, ∑ k, ∑ l, A k l * (star z)^k.val * z^l.val = 0) :
    A = 0 := by
  let p : Poly₂ := ∑ k, ∑ l, MvPolynomial.monomial (powers k.val l.val) (A k l)
  have hp : p = 0 := realSlice p (fun z => by simpa [p, map_sum, powers_eval] using h z)
  ext k l
  have hpow (r : Fin m) (s : Fin n) : powers k.val l.val = powers r.val s.val ↔ k=r ∧ l=s := by
    constructor
    · intro he
      exact ⟨Fin.ext (by simpa [powers] using congrArg (fun d : Fin 2 →₀ ℕ => d 0) he),
        Fin.ext (by simpa [powers] using congrArg (fun d : Fin 2 →₀ ℕ => d 1) he)⟩
    · rintro ⟨rfl,rfl⟩; rfl
  have hc := congrArg (fun q : Poly₂ => q.coeff (powers k.val l.val)) hp
  simpa [p, MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial, eq_comm (a := powers _ _) (b := powers k.val l.val), hpow, ite_and] using hc

private def chartScale (z : ℂ) : ℝ := (Real.sqrt (1+normSq z))⁻¹

private theorem chartScale_pos (z : ℂ) : 0 < chartScale z :=
  inv_pos.mpr (Real.sqrt_pos.mpr (by linarith [normSq_nonneg z]))

private def chart (z : ℂ) : SU2 where
  a := (chartScale z : ℂ)
  b := -star z * (chartScale z : ℂ)
  norm_eq := by
    have hv : 0 < 1+normSq z := by linarith [normSq_nonneg z]
    have h : chartScale z ^ 2 * (1 + normSq z) = 1 := by
      rw [chartScale, inv_pow, Real.sq_sqrt hv.le, inv_mul_cancel₀ hv.ne']
    have hc : (chartScale z : ℂ)^2 * (1+(normSq z:ℂ)) = 1 := by exact_mod_cast h
    simp only [star_mul', star_neg, star_star]
    rw [show star (chartScale z : ℂ) = (chartScale z:ℂ) by simp [RCLike.star_def]]
    rw [normSq_eq_conj_mul_self, ← RCLike.star_def] at hc
    linear_combination hc

theorem spinRep_highestColumn (N : ℕ) (g : SU2) (k : Fin (N+1)) :
    spinRep N g k 0 = (binomWeight N k : ℂ)*g.a^(N-k.val)*(-star g.b)^k.val := by
  have h0 : binomWeight N 0 = 1 := by simp [binomWeight]
  have h (p : Polynomial ℂ) (n : ℕ) : (p^n).coeff 0 = (p.coeff 0)^n :=
    map_pow Polynomial.constantCoeff p n
  simp [spinRep, rawRep, polyStep, h0, Polynomial.mul_coeff_zero, h, mul_assoc]

private theorem chartColumn (N : ℕ) (z : ℂ) (k : Fin (N+1)) :
    spinRep N (chart z) k 0 = (chartScale z : ℂ)^N * (binomWeight N k : ℂ) * z^k.val := by
  rw [spinRep_highestColumn]
  have ha : (chart z).a = (chartScale z : ℂ) := rfl
  have hb : -star (chart z).b = z * (chartScale z : ℂ) := by
    change -star (-star z * (chartScale z : ℂ)) = _
    simp [star_mul', show star (chartScale z : ℂ) = (chartScale z : ℂ) by simp [RCLike.star_def], mul_comm]
  have hp : (chartScale z : ℂ)^N = (chartScale z : ℂ)^(N-k.val) * (chartScale z : ℂ)^k.val := by
    rw [← pow_add, Nat.sub_add_cancel (show k.val ≤ N by omega)]
  rw [ha,hb,mul_pow,hp]
  ring

/-- The highest-weight vector transported by the spin representation. -/
def coherentVector (N : ℕ) (g : SU2) : Fin (N+1) → ℂ :=
  fun k => spinRep N g k 0

/-- A complex quadratic form is determined by its spin coherent expectations. -/
theorem coherent_expectation_injective {N : ℕ} (A : Matrix (Fin (N+1)) (Fin (N+1)) ℂ)
    (h : ∀ g : SU2, innerC (coherentVector N g) (A.mulVec (coherentVector N g)) = 0) :
    A = 0 := by
  let B : Matrix (Fin (N+1)) (Fin (N+1)) ℂ :=
    fun k l => (binomWeight N k : ℂ) * A k l * (binomWeight N l : ℂ)
  have hB : B = 0 := by
    apply conjugateMonomials_independent
    intro z
    have hz : (chartScale z : ℂ) ≠ 0 := by exact_mod_cast (chartScale_pos z).ne'
    apply (mul_eq_zero.mp (show (chartScale z : ℂ)^(N+N) * _ = 0 from ?_)).resolve_left (pow_ne_zero _ hz)
    rw [← h (chart z)]
    simp only [innerC, Matrix.mulVec, dotProduct, coherentVector, chartColumn, star_mul',
      star_pow, RCLike.star_def, conj_ofReal, Finset.mul_sum, B]
    apply Finset.sum_congr rfl; intro k _
    apply Finset.sum_congr rfl; intro l _
    rw [pow_add]
    ring
  ext k l
  have hkl : B k l = 0 := congrFun (congrFun hB k) l
  have hk : (binomWeight N k : ℂ) ≠ 0 := by exact_mod_cast (binomWeight_pos N k).ne'
  have hl : (binomWeight N l : ℂ) ≠ 0 := by exact_mod_cast (binomWeight_pos N l).ne'
  exact (mul_eq_zero.mp ((mul_eq_zero.mp hkl).resolve_right hl)).resolve_left hk

end SU2Wigner
end
