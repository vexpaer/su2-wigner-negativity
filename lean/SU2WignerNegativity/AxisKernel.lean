import SU2WignerNegativity.WignerNegativity

/-! # Matrix coefficients of rotations about a variable axis

At the north pole these are the Fourier modes of a diagonal spin kernel.
Their real and imaginary parts are polynomials on the sphere for every spin.
-/

open Complex Polynomial Finset
open scoped Matrix

noncomputable section
namespace SU2Wigner

/-- Rotation about `u` through physical angle `2*t`. -/
def SU2.axisRot (t : ℝ) (u : S2) : SU2 where
  a := (Real.cos t : ℂ) + (Real.sin t : ℂ) * (SU2.piRot u).a
  b := (Real.sin t : ℂ) * (SU2.piRot u).b
  norm_eq := by
    have h := (SU2.piRot u).norm_eq
    have htr : star (SU2.piRot u).a = -(SU2.piRot u).a := by
      simp [SU2.piRot_a, RCLike.star_def]
    have hc : (Real.cos t : ℂ)^2 + (Real.sin t : ℂ)^2 = 1 := by
      exact_mod_cast Real.cos_sq_add_sin_sq t
    simp only [star_add, star_mul', RCLike.star_def, conj_ofReal] at *
    rw [htr] at h ⊢
    linear_combination (Real.sin t : ℂ)^2 * h + hc

theorem SU2.axisRot_actS2 (g : SU2) (t : ℝ) (u : S2) :
    axisRot t (actS2 g u) = g * axisRot t u * g⁻¹ := by
  have h := g.norm_eq
  ext <;> simp only [axisRot, piRot_actS2, mul_a, mul_b, inv_a, inv_b,
    star_add, star_mul', star_neg, RCLike.star_def, conj_ofReal, Complex.conj_conj] at *
  · linear_combination -(Real.cos t : ℂ) * h
  · ring

/-- The expectation of the spin rotation; at the pole its Fourier coefficients are
the magnetic-level occupation probabilities. -/
def axisSymbol (N : ℕ) (t : ℝ) (ψ : Fin (N + 1) → ℂ) (u : S2) : ℂ :=
  innerC ψ ((spinRep N (SU2.axisRot t u)).mulVec ψ)

theorem axisSymbol_covariant (N : ℕ) (t : ℝ) (g : SU2)
    (ψ : Fin (N + 1) → ℂ) (u : S2) :
    axisSymbol N t ((spinRep N g).mulVec ψ) (SU2.actS2 g u) = axisSymbol N t ψ u := by
  unfold axisSymbol
  rw [SU2.axisRot_actS2, spinRep_mul, spinRep_mul, spinRep_inv, Matrix.mulVec_mulVec,
    Matrix.mul_assoc, spinRep_conjTranspose_mul_self, Matrix.mul_one,
    ← Matrix.mulVec_mulVec, innerC_spinRep_unitary]

abbrev CoordPoly := MvPolynomial (Fin 3) ℂ

def evalAxis (u : S2) : CoordPoly →+* ℂ :=
  MvPolynomial.eval (fun i => (u.1 i : ℂ))

/-- An explicit polynomial for every entry of the rotation matrix. The outer
univariate polynomial supplies the coefficient formula for the symmetric power. -/
private def rotationEntry (N : ℕ) (t : ℝ) (k s : Fin (N + 1)) : CoordPoly :=
  let c : CoordPoly := MvPolynomial.C (Real.cos t : ℂ)
  let d : CoordPoly := MvPolynomial.C ((Real.sin t : ℂ) * -I)
  let i : CoordPoly := MvPolynomial.C I
  let x : CoordPoly := MvPolynomial.X 0
  let y : CoordPoly := MvPolynomial.X 1
  let z : CoordPoly := MvPolynomial.X 2
  let p : Polynomial CoordPoly := C (c + d*z) + C (d*(x-i*y)) * X
  let q : Polynomial CoordPoly := C (d*(x+i*y)) + C (c - d*z) * X
  MvPolynomial.C ((binomWeight N k : ℂ) / (binomWeight N s : ℂ)) *
    (p^(N-k.val) * q^k.val).coeff s.val

private theorem rotationEntry_eval (N : ℕ) (t : ℝ) (k s : Fin (N+1)) (u : S2) :
    evalAxis u (rotationEntry N t k s) = spinRep N (SU2.axisRot t u) k s := by
  let c : CoordPoly := MvPolynomial.C (Real.cos t : ℂ)
  let d : CoordPoly := MvPolynomial.C ((Real.sin t : ℂ) * -I)
  let i : CoordPoly := MvPolynomial.C I
  let x : CoordPoly := MvPolynomial.X 0
  let y : CoordPoly := MvPolynomial.X 1
  let z : CoordPoly := MvPolynomial.X 2
  let e := evalAxis u
  let g := SU2.axisRot t u
  have ec (v : ℂ) : e (MvPolynomial.C v) = v := MvPolynomial.eval_C v
  have ex (j : Fin 3) : e (MvPolynomial.X j) = (u.1 j : ℂ) := MvPolynomial.eval_X j
  have ha : e (c+d*z) = g.a := by simp only [c,d,z, map_add, map_mul, ec, ex, g, SU2.axisRot, SU2.piRot_a]; ring
  have hb : e (d*(x-i*y)) = g.b := by simp only [d,x,y,i,map_mul,map_sub,ec,ex,g,SU2.axisRot,SU2.piRot_b]; ring
  have hc : e (d*(x+i*y)) = -star g.b := by
    simp only [d,x,y,i,map_mul,map_add,ec,ex,g,SU2.axisRot,SU2.piRot_b,star_mul',star_sub,
      star_neg,RCLike.star_def,conj_I,conj_ofReal]; ring
  have hd : e (c-d*z) = star g.a := by
    simp only [c,d,z,map_sub,map_mul,ec,ex,g,SU2.axisRot,SU2.piRot_a,star_add,star_mul',
      star_neg,RCLike.star_def,conj_I,conj_ofReal]; ring
  let p : Polynomial CoordPoly := C (c+d*z) + C (d*(x-i*y))*X
  let q : Polynomial CoordPoly := C (d*(x+i*y)) + C (c-d*z)*X
  change e (MvPolynomial.C _ * (p^(N-k.val)*q^k.val).coeff s.val) = _
  rw [map_mul, ec, ← Polynomial.coeff_map e]
  simp only [p,q,Polynomial.map_mul,Polynomial.map_pow,Polynomial.map_add,Polynomial.map_C,
    Polynomial.map_X,ha,hb,hc,hd]
  rfl

private theorem evalAxis_parts (P : CoordPoly) :
    ∃ A B : MvPolynomial (Fin 3) ℝ, ∀ u : S2,
      (evalAxis u P).re = MvPolynomial.eval u.1 A ∧
      (evalAxis u P).im = MvPolynomial.eval u.1 B := by
  induction P using MvPolynomial.induction_on with
  | C a => exact ⟨MvPolynomial.C a.re, MvPolynomial.C a.im, fun u => by simp [evalAxis]⟩
  | add p q hp hq =>
    obtain ⟨a,b,hab⟩ := hp
    obtain ⟨c,d,hcd⟩ := hq
    exact ⟨a+c,b+d,fun u => by simp [map_add, (hab u).1, (hab u).2, (hcd u).1, (hcd u).2]⟩
  | mul_X p j hp =>
    obtain ⟨a,b,hab⟩ := hp
    refine ⟨a * MvPolynomial.X j, b * MvPolynomial.X j, fun u => ?_⟩
    have hx : evalAxis u (MvPolynomial.X j) = (u.1 j : ℂ) := by simp [evalAxis]
    simp [map_mul, hx, mul_re, mul_im, (hab u).1, (hab u).2]

/-- Cartesian polynomial for the complex expectation of an axis rotation. -/
def axisPolynomial (N : ℕ) (t : ℝ) (ψ : Fin (N+1) → ℂ) : CoordPoly :=
  ∑ k, MvPolynomial.C (star (ψ k)) * ∑ s, rotationEntry N t k s * MvPolynomial.C (ψ s)

theorem axisPolynomial_eval (N : ℕ) (t : ℝ) (ψ : Fin (N+1) → ℂ) (u : S2) :
    evalAxis u (axisPolynomial N t ψ) = axisSymbol N t ψ u := by
  simp only [axisPolynomial, map_sum, map_mul, rotationEntry_eval, axisSymbol, innerC,
    Matrix.mulVec, dotProduct]
  simp [evalAxis]

theorem axisSymbol_poly (N : ℕ) (t : ℝ) (ψ : Fin (N+1) → ℂ) :
    ∃ A B : MvPolynomial (Fin 3) ℝ, ∀ u : S2,
      (axisSymbol N t ψ u).re = MvPolynomial.eval u.1 A ∧
      (axisSymbol N t ψ u).im = MvPolynomial.eval u.1 B := by
  obtain ⟨A,B,hAB⟩ := evalAxis_parts (axisPolynomial N t ψ)
  exact ⟨A,B,fun u => axisPolynomial_eval N t ψ u ▸ hAB u⟩

end SU2Wigner
end
