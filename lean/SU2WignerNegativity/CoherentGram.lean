import SU2WignerNegativity.CoherentNormalization
import SU2WignerNegativity.SphereInvariance
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.LinearAlgebra.Matrix.Trace

/-! # Coherent-state Gram operator and all-spin Stratonovich–Weyl systems

For every spin `j = N / 2` (`N : ℕ`), we construct a concrete `SU(2)`-covariant,
self-dual `StratonovichWeylSystem N` by symmetric orthonormalization (`G⁻¹/²`) of the
coherent-state (Husimi) symbol map on the `(N + 1)²`-dimensional real space of
Hermitian `(N + 1) × (N + 1)` matrices:

1. `hermBasis N` is an explicit Hilbert–Schmidt orthonormal basis of Hermitian matrices
   indexed by `HermIdx N := Fin (N + 1) × Fin (N + 1)`, with coordinate isomorphism
   `hermCoords` / `ofHermCoords`.
2. Each basis matrix is a real linear combination of 1 or 3 pure-state projectors, so
   `matrixSymbol N x` extends `coherentSymbol N` linearly to all Hermitian matrices while
   inheriting polynomiality on `S²`, `SU(2)`-covariance, and normalization
   `swIntegral N (matrixSymbol N x) = (trace (ofHermCoords x)).re`.
3. The coherent-state Gram matrix `gramMatrix N` is real symmetric, strictly positive
   definite (by `sphereAvg_sq_pos` and `coherent_expectation_injective`), fixes the
   identity coordinate vector `idVec N` (by `coherentSymbol_norm`), and commutes with
   the orthogonal adjoint representation `adMatrix N g` (by `swIntegral_actS2`).
4. Spectral calculus (`Matrix.IsHermitian.spectral_theorem`) yields `invSqrtGram N = G⁻¹/²`,
   which is symmetric, satisfies `T * G * T = 1`, fixes `idVec N`, and commutes with
   `adMatrix N g`.
5. `canonicalStratonovichWeyl N` defines `W_ψ(u) = matrixSymbol N (T *ᵥ hermCoords |ψ⟩⟨ψ|) u`
   and proves all four `StratonovichWeylSystem N` axioms, continuity in `ψ`, and hence
   unconditional universal Wigner negativity and uniform negativity bounds for all `N ≥ 1`.
-/

open Real Complex Finset Matrix
open scoped Matrix

noncomputable section
namespace SU2Wigner

/-! ### Orthonormal Basis of Hermitian Matrices -/

/-- Index set for the `(N + 1)²`-dimensional real space of Hermitian `(N + 1) × (N + 1)` matrices. -/
abbrev HermIdx (N : ℕ) := Fin (N + 1) × Fin (N + 1)

/-- Pure-state rank-one projector `|ψ⟩⟨ψ|`. -/
def pureProj {N : ℕ} (ψ : Fin (N + 1) → ℂ) : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ :=
  fun a b => ψ a * star (ψ b)

lemma pureProj_isHermitian {N : ℕ} (ψ : Fin (N + 1) → ℂ) : (pureProj ψ).IsHermitian := by
  ext a b
  simp [pureProj, Matrix.conjTranspose_apply, mul_comm]

private lemma innerC_smul_right {N : ℕ} (c : ℂ) (v w : Fin (N + 1) → ℂ) :
    innerC v (c • w) = c * innerC v w := by
  simp only [innerC, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl; intro i _; ring

private lemma innerC_sub_right {N : ℕ} (v w₁ w₂ : Fin (N + 1) → ℂ) :
    innerC v (w₁ - w₂) = innerC v w₁ - innerC v w₂ := by
  simp only [innerC, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]

lemma pureProj_mulVec_inner {N : ℕ} (v ψ : Fin (N + 1) → ℂ) :
    innerC v ((pureProj ψ).mulVec v) = (normSq (innerC v ψ) : ℂ) := by
  rw [Complex.normSq_eq_conj_mul_self, ← RCLike.star_def]
  simp only [innerC, pureProj, Matrix.mulVec, dotProduct, star_sum, star_mul', star_star,
    Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl; intro a _
  apply Finset.sum_congr rfl; intro b _
  ring

private def stdBasis {N : ℕ} (i : Fin (N + 1)) : Fin (N + 1) → ℂ := Pi.single i 1

/-- Hilbert–Schmidt orthonormal Hermitian basis, expressed directly via pure-state projectors. -/
def hermBasis (N : ℕ) (p : HermIdx N) : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ :=
  if p.1 = p.2 then pureProj (stdBasis p.1)
  else if p.1 < p.2 then
    ((Real.sqrt 2 : ℂ)⁻¹) •
      (pureProj (stdBasis p.1 + stdBasis p.2) - pureProj (stdBasis p.1) - pureProj (stdBasis p.2))
  else
    ((Real.sqrt 2 : ℂ)⁻¹) •
      (pureProj (stdBasis p.2 - I • stdBasis p.1) - pureProj (stdBasis p.2) - pureProj (stdBasis p.1))

private lemma hermBasis_apply (N : ℕ) (p : HermIdx N) (a b : Fin (N + 1)) :
    hermBasis N p a b =
      if p.1 = p.2 then (if a = p.1 ∧ b = p.1 then 1 else 0)
      else if p.1 < p.2 then
        ((Real.sqrt 2 : ℂ)⁻¹) *
          ((if a = p.1 ∧ b = p.2 then 1 else 0) + (if a = p.2 ∧ b = p.1 then 1 else 0))
      else
        ((Real.sqrt 2 : ℂ)⁻¹) *
          ((if a = p.2 ∧ b = p.1 then I else 0) + (if a = p.1 ∧ b = p.2 then -I else 0)) := by
  unfold hermBasis
  by_cases h1 : p.1 = p.2
  · simp only [h1, ↓reduceIte, pureProj, stdBasis, Pi.single_apply]
    by_cases ha : a = p.2 <;> by_cases hb : b = p.2 <;> simp [ha, hb]
  · by_cases h2 : p.1 < p.2
    · simp only [h1, h2, ↓reduceIte, Matrix.smul_apply, Matrix.sub_apply, pureProj, stdBasis,
        Pi.add_apply, Pi.single_apply, smul_eq_mul, star_add]
      congr 1
      by_cases ha1 : a = p.1 <;> by_cases ha2 : a = p.2 <;>
        by_cases hb1 : b = p.1 <;> by_cases hb2 : b = p.2 <;>
        simp_all
    · simp only [h1, h2, ↓reduceIte, Matrix.smul_apply, Matrix.sub_apply, pureProj, stdBasis,
        Pi.sub_apply, Pi.smul_apply, Pi.single_apply, smul_eq_mul, star_sub, star_mul',
        RCLike.star_def, Complex.conj_I]
      congr 1
      by_cases ha1 : a = p.1 <;> by_cases ha2 : a = p.2 <;>
        by_cases hb1 : b = p.1 <;> by_cases hb2 : b = p.2 <;>
        simp_all

lemma hermBasis_isHermitian (N : ℕ) (p : HermIdx N) : (hermBasis N p).IsHermitian := by
  ext a b
  simp only [Matrix.conjTranspose_apply, hermBasis_apply]
  by_cases h1 : p.1 = p.2
  · simp only [h1, ↓reduceIte]
    by_cases ha : a = p.2 <;> by_cases hb : b = p.2 <;> simp [ha, hb]
  · by_cases h2 : p.1 < p.2
    · simp only [h1, h2, ↓reduceIte, star_mul', star_add, RCLike.star_def, map_inv₀, Complex.conj_ofReal]
      congr 1
      by_cases ha1 : a = p.1 <;> by_cases ha2 : a = p.2 <;>
        by_cases hb1 : b = p.1 <;> by_cases hb2 : b = p.2 <;>
        simp_all
    · simp only [h1, h2, ↓reduceIte, star_mul', star_add, RCLike.star_def, map_inv₀, Complex.conj_ofReal]
      congr 1
      by_cases ha1 : a = p.1 <;> by_cases ha2 : a = p.2 <;>
        by_cases hb1 : b = p.1 <;> by_cases hb2 : b = p.2 <;>
        simp_all

/-- Real coordinates of a Hermitian matrix in the orthonormal basis `hermBasis N`. -/
def hermCoords {N : ℕ} (A : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ) (p : HermIdx N) : ℝ :=
  if p.1 = p.2 then (A p.1 p.1).re
  else if p.1 < p.2 then Real.sqrt 2 * (A p.1 p.2).re
  else Real.sqrt 2 * (A p.2 p.1).im

/-- Reconstruct a Hermitian matrix from its real coordinates `x : HermIdx N → ℝ`. -/
def ofHermCoords {N : ℕ} (x : HermIdx N → ℝ) : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ :=
  ∑ p : HermIdx N, (x p : ℂ) • hermBasis N p

lemma ofHermCoords_apply {N : ℕ} (x : HermIdx N → ℝ) (a b : Fin (N + 1)) :
    ofHermCoords x a b =
      if a = b then (x (a, a) : ℂ)
      else if a < b then ((Real.sqrt 2 : ℂ)⁻¹) * ((x (a, b) : ℂ) + I * (x (b, a) : ℂ))
      else ((Real.sqrt 2 : ℂ)⁻¹) * ((x (b, a) : ℂ) - I * (x (a, b) : ℂ)) := by
  unfold ofHermCoords
  simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, hermBasis_apply]
  by_cases hab : a = b
  · subst hab
    rw [Finset.sum_eq_single (a, a)]
    · simp
    · intro p _ hp
      by_cases h1 : p.1 = p.2
      · have hne : a ≠ p.2 := fun h => hp (Prod.ext (h1.trans h.symm) h.symm)
        simp [h1, hne]
      · have hne1 : ¬ (a = p.1 ∧ a = p.2) := fun h => h1 (h.1.symm.trans h.2)
        have hne2 : ¬ (a = p.2 ∧ a = p.1) := fun h => h1 (h.2.symm.trans h.1)
        by_cases h2 : p.1 < p.2 <;> simp [h1, h2, hne1, hne2]
    · intro h; exact absurd (Finset.mem_univ _) h
  · have hsum : ∀ p : HermIdx N, p ∉ ({(a, b), (b, a)} : Finset (HermIdx N)) →
        (x p : ℂ) * (if p.1 = p.2 then (if a = p.1 ∧ b = p.1 then 1 else 0)
          else if p.1 < p.2 then ((Real.sqrt 2 : ℂ)⁻¹) *
            ((if a = p.1 ∧ b = p.2 then 1 else 0) + (if a = p.2 ∧ b = p.1 then 1 else 0))
          else ((Real.sqrt 2 : ℂ)⁻¹) *
            ((if a = p.2 ∧ b = p.1 then I else 0) + (if a = p.1 ∧ b = p.2 then -I else 0))) = 0 := by
      intro p hp
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hp
      have hp1 : ¬ (a = p.1 ∧ b = p.2) := fun h => hp.1 (Prod.ext h.1.symm h.2.symm)
      have hp2 : ¬ (a = p.2 ∧ b = p.1) := fun h => hp.2 (Prod.ext h.2.symm h.1.symm)
      by_cases h1 : p.1 = p.2
      · have hp0' : ¬ (a = p.2 ∧ b = p.2) := fun h => hab (h.1.trans h.2.symm)
        simp [h1, hp0']
      · by_cases h2 : p.1 < p.2 <;> simp [h1, h2, hp1, hp2]
    rw [← Finset.sum_subset (Finset.subset_univ {(a, b), (b, a)}) (fun p _ hp => hsum p hp)]
    have hne_pair : (a, b) ≠ (b, a) := fun h => hab (congrArg Prod.fst h)
    rw [Finset.sum_pair hne_pair]
    by_cases hlt : a < b
    · have hgt : ¬ (b < a) := not_lt.mpr hlt.le
      have hba : b ≠ a := Ne.symm hab
      simp only [hab, hba, hlt, hgt, ↓reduceIte, and_true, and_false, add_zero]
      ring
    · have hgt : b < a := lt_of_le_of_ne (not_lt.mp hlt) (Ne.symm hab)
      have hba : b ≠ a := Ne.symm hab
      simp only [hab, hba, hlt, hgt, ↓reduceIte, and_true, and_false, zero_add]
      ring

lemma ofHermCoords_isHermitian {N : ℕ} (x : HermIdx N → ℝ) : (ofHermCoords x).IsHermitian := by
  ext a b
  simp only [Matrix.conjTranspose_apply, ofHermCoords_apply]
  by_cases hab : a = b
  · subst hab; simp [RCLike.star_def]
  · have hba : b ≠ a := Ne.symm hab
    by_cases hlt : a < b
    · have hgt : ¬ (b < a) := not_lt.mpr hlt.le
      simp only [hab, hba, hlt, hgt, ↓reduceIte, star_mul', star_sub,
        RCLike.star_def, map_inv₀, Complex.conj_ofReal, Complex.conj_I, neg_mul, sub_neg_eq_add]
    · have hgt : b < a := lt_of_le_of_ne (not_lt.mp hlt) hba
      simp only [hab, hba, hlt, hgt, ↓reduceIte, star_mul', star_add,
        RCLike.star_def, map_inv₀, Complex.conj_ofReal, Complex.conj_I, neg_mul, sub_eq_add_neg]

private lemma herm_entry_conj {N : ℕ} {A : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ}
    (hA : A.IsHermitian) (a b : Fin (N + 1)) : star (A b a) = A a b :=
  congrFun (congrFun hA a) b

lemma ofHermCoords_hermCoords {N : ℕ} {A : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ}
    (hA : A.IsHermitian) : ofHermCoords (hermCoords A) = A := by
  have h2 : (Real.sqrt 2 : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2)).ne'
  ext a b
  rw [ofHermCoords_apply]
  by_cases hab : a = b
  · subst hab
    simp only [↓reduceIte, hermCoords]
    have him : (A a a).im = 0 := by
      have h := congrArg Complex.im (herm_entry_conj hA a a)
      simp only [RCLike.star_def, Complex.conj_im] at h; linarith
    exact Complex.ext rfl (by simp [him])
  · have hba : b ≠ a := Ne.symm hab
    by_cases hlt : a < b
    · have hgt : ¬ (b < a) := not_lt.mpr hlt.le
      simp only [hab, hba, hlt, hgt, ↓reduceIte, hermCoords, Complex.ofReal_mul]
      have hreim : (A a b).re + I * (A a b).im = A a b := by
        rw [mul_comm]; exact Complex.re_add_im (A a b)
      calc (Real.sqrt 2 : ℂ)⁻¹ *
            ((Real.sqrt 2 : ℂ) * ((A a b).re : ℂ) + I * ((Real.sqrt 2 : ℂ) * ((A a b).im : ℂ)))
          = ((Real.sqrt 2 : ℂ)⁻¹ * (Real.sqrt 2 : ℂ)) * ((A a b).re + I * (A a b).im) := by ring
        _ = A a b := by rw [inv_mul_cancel₀ h2, one_mul, hreim]
    · have hgt : b < a := lt_of_le_of_ne (not_lt.mp hlt) hba
      simp only [hab, hba, hlt, hgt, ↓reduceIte, hermCoords, Complex.ofReal_mul]
      have hconj := herm_entry_conj hA a b
      have hre : (A b a).re = (A a b).re := by
        have h := congrArg Complex.re hconj; simpa [RCLike.star_def] using h
      have him : -(A b a).im = (A a b).im := by
        have h := congrArg Complex.im hconj; simpa [RCLike.star_def] using h
      have hreim : ((A b a).re : ℂ) - I * ((A b a).im : ℂ) = A a b := by
        apply Complex.ext <;> simp [hre, him]
      calc (Real.sqrt 2 : ℂ)⁻¹ *
            ((Real.sqrt 2 : ℂ) * ((A b a).re : ℂ) - I * ((Real.sqrt 2 : ℂ) * ((A b a).im : ℂ)))
          = ((Real.sqrt 2 : ℂ)⁻¹ * (Real.sqrt 2 : ℂ)) * (((A b a).re : ℂ) - I * ((A b a).im : ℂ)) := by ring
        _ = A a b := by rw [inv_mul_cancel₀ h2, one_mul, hreim]

lemma hermCoords_ofHermCoords {N : ℕ} (x : HermIdx N → ℝ) :
    hermCoords (ofHermCoords x) = x := by
  have h2 : Real.sqrt 2 ≠ 0 := (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2)).ne'
  funext ⟨a, b⟩
  unfold hermCoords
  by_cases hab : a = b
  · subst hab; simp [ofHermCoords_apply]
  · have hba : b ≠ a := Ne.symm hab
    by_cases hlt : a < b
    · simp only [hab, hlt, ↓reduceIte, ofHermCoords_apply]
      have hre : (((Real.sqrt 2 : ℂ)⁻¹) * ((x (a, b) : ℂ) + I * (x (b, a) : ℂ))).re =
          (Real.sqrt 2)⁻¹ * x (a, b) := by
        rw [← Complex.ofReal_inv]
        simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.add_re,
          Complex.add_im, Complex.I_re, Complex.I_im, zero_mul, sub_zero]
        ring
      rw [hre, ← mul_assoc, mul_inv_cancel₀ h2, one_mul]
    · have hgt : b < a := lt_of_le_of_ne (not_lt.mp hlt) hba
      simp only [hab, hba, hlt, hgt, ↓reduceIte, ofHermCoords_apply]
      have him : (((Real.sqrt 2 : ℂ)⁻¹) * ((x (b, a) : ℂ) + I * (x (a, b) : ℂ))).im =
          (Real.sqrt 2)⁻¹ * x (a, b) := by
        rw [← Complex.ofReal_inv]
        simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.add_re,
          Complex.add_im, Complex.mul_re, Complex.I_re, Complex.I_im, zero_mul, one_mul,
          sub_zero, zero_add, add_zero]
      rw [him, ← mul_assoc, mul_inv_cancel₀ h2, one_mul]

/-- `hermCoords` is an isometry from Hermitian matrices with Hilbert–Schmidt pairing to `ℝ^{(N+1)²}`. -/
lemma dotProduct_hermCoords {N : ℕ} {A B : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ}
    (hA : A.IsHermitian) (hB : B.IsHermitian) :
    dotProduct (hermCoords A) (hermCoords B) = (Matrix.trace (A * B)).re := by
  have hsq : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hpair (p : HermIdx N) :
      hermCoords A p * hermCoords B p + hermCoords A p.swap * hermCoords B p.swap =
        (A p.1 p.2 * B p.2 p.1).re + (A p.2 p.1 * B p.1 p.2).re := by
    rcases p with ⟨a, b⟩
    have hA_ab := herm_entry_conj hA a b
    have hB_ab := herm_entry_conj hB a b
    have hA_re : (A b a).re = (A a b).re := by
      have h := congrArg Complex.re hA_ab; simpa [RCLike.star_def] using h
    have hA_im : (A b a).im = -(A a b).im := by
      have h := congrArg Complex.im hA_ab; simp only [RCLike.star_def, Complex.conj_im] at h; linarith
    have hB_re : (B b a).re = (B a b).re := by
      have h := congrArg Complex.re hB_ab; simpa [RCLike.star_def] using h
    have hB_im : (B b a).im = -(B a b).im := by
      have h := congrArg Complex.im hB_ab; simp only [RCLike.star_def, Complex.conj_im] at h; linarith
    by_cases hab : a = b
    · subst hab
      have hA0 : (A a a).im = 0 := by linarith
      have hB0 : (B a a).im = 0 := by linarith
      simp [hermCoords, Complex.mul_re, hA0, hB0]
    · have hba : b ≠ a := Ne.symm hab
      by_cases hlt : a < b
      · have hgt : ¬ (b < a) := not_lt.mpr hlt.le
        simp only [Prod.swap, hermCoords, hab, hba, hlt, hgt, ↓reduceIte, Complex.mul_re,
          hA_re, hA_im, hB_re, hB_im]
        linear_combination ((A a b).re * (B a b).re + (A a b).im * (B a b).im) * hsq
      · have hgt : b < a := lt_of_le_of_ne (not_lt.mp hlt) hba
        simp only [Prod.swap, hermCoords, hab, hba, hlt, hgt, ↓reduceIte, Complex.mul_re,
          hA_re, hA_im, hB_re, hB_im]
        linear_combination ((A a b).re * (B a b).re + (A a b).im * (B a b).im) * hsq
  have hswap_sum (f : HermIdx N → ℝ) : ∑ p : HermIdx N, f p.swap = ∑ p : HermIdx N, f p :=
    Equiv.sum_comp (Equiv.prodComm (Fin (N + 1)) (Fin (N + 1))) f
  have h2lhs : 2 * dotProduct (hermCoords A) (hermCoords B) =
      ∑ p : HermIdx N, (hermCoords A p * hermCoords B p + hermCoords A p.swap * hermCoords B p.swap) := by
    rw [Finset.sum_add_distrib,
      hswap_sum (fun p : HermIdx N => hermCoords A p * hermCoords B p), two_mul, dotProduct]
  have h2rhs : 2 * (Matrix.trace (A * B)).re =
      ∑ p : HermIdx N, ((A p.1 p.2 * B p.2 p.1).re + (A p.2 p.1 * B p.1 p.2).re) := by
    rw [Finset.sum_add_distrib]
    have hs : (∑ p : HermIdx N, (A p.2 p.1 * B p.1 p.2).re) =
        ∑ p : HermIdx N, (A p.1 p.2 * B p.2 p.1).re :=
      hswap_sum (fun p : HermIdx N => (A p.1 p.2 * B p.2 p.1).re)
    rw [hs, ← two_mul]
    congr 1
    rw [Fintype.sum_prod_type]
    simp [Matrix.trace, Matrix.diag, Matrix.mul_apply]
  have heq : 2 * dotProduct (hermCoords A) (hermCoords B) = 2 * (Matrix.trace (A * B)).re := by
    rw [h2lhs, h2rhs]
    exact Finset.sum_congr rfl fun p _ => hpair p
  linarith

lemma trace_pureProj_mul {N : ℕ} (φ ψ : Fin (N + 1) → ℂ) :
    (Matrix.trace (pureProj φ * pureProj ψ)).re = normSq (innerC φ ψ) := by
  have htr : Matrix.trace (pureProj φ * pureProj ψ) = (normSq (innerC φ ψ) : ℂ) := by
    rw [Complex.normSq_eq_conj_mul_self, ← RCLike.star_def]
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, pureProj, innerC,
      star_sum, star_mul', star_star, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro a _
    apply Finset.sum_congr rfl; intro b _
    ring
  rw [htr, Complex.ofReal_re]

lemma dotProduct_hermCoords_pureProj {N : ℕ} (φ ψ : Fin (N + 1) → ℂ) :
    dotProduct (hermCoords (pureProj φ)) (hermCoords (pureProj ψ)) = normSq (innerC φ ψ) := by
  rw [dotProduct_hermCoords (pureProj_isHermitian φ) (pureProj_isHermitian ψ), trace_pureProj_mul]

/-- Coordinate vector of the identity matrix `1`. -/
def idVec (N : ℕ) : HermIdx N → ℝ := hermCoords (1 : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ)

lemma ofHermCoords_idVec (N : ℕ) :
    ofHermCoords (idVec N) = (1 : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ) :=
  ofHermCoords_hermCoords Matrix.isHermitian_one

lemma dotProduct_idVec {N : ℕ} (x : HermIdx N → ℝ) :
    dotProduct (idVec N) x = (Matrix.trace (ofHermCoords x)).re := by
  have h1 : dotProduct (idVec N) x =
      dotProduct (hermCoords (1 : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ)) (hermCoords (ofHermCoords x)) := by
    rw [idVec, hermCoords_ofHermCoords]
  rw [h1, dotProduct_hermCoords Matrix.isHermitian_one (ofHermCoords_isHermitian x), Matrix.one_mul]

lemma dotProduct_idVec_pureProj {N : ℕ} (ψ : Fin (N + 1) → ℂ) :
    dotProduct (idVec N) (hermCoords (pureProj ψ)) = (innerC ψ ψ).re := by
  rw [dotProduct_idVec, ofHermCoords_hermCoords (pureProj_isHermitian ψ)]
  simp only [Matrix.trace, Matrix.diag, pureProj, innerC, Complex.re_sum]
  apply Finset.sum_congr rfl; intro k _
  rw [mul_comm]

/-! ### Linear Extension of the Coherent-State Symbol to All Hermitian Matrices -/

/-- Coherent-state symbol of the `p`-th Hermitian basis matrix. -/
def basisSymbol (N : ℕ) (p : HermIdx N) (u : S2) : ℝ :=
  if p.1 = p.2 then coherentSymbol N (stdBasis p.1) u
  else if p.1 < p.2 then
    (Real.sqrt 2)⁻¹ *
      (coherentSymbol N (stdBasis p.1 + stdBasis p.2) u -
        coherentSymbol N (stdBasis p.1) u - coherentSymbol N (stdBasis p.2) u)
  else
    (Real.sqrt 2)⁻¹ *
      (coherentSymbol N (stdBasis p.2 - I • stdBasis p.1) u -
        coherentSymbol N (stdBasis p.2) u - coherentSymbol N (stdBasis p.1) u)

/-- Coherent-state symbol of an arbitrary Hermitian matrix in coordinates `x : HermIdx N → ℝ`. -/
def matrixSymbol (N : ℕ) (x : HermIdx N → ℝ) (u : S2) : ℝ :=
  ∑ p : HermIdx N, x p * basisSymbol N p u

lemma basisSymbol_poly (N : ℕ) (p : HermIdx N) :
    ∃ P : MvPolynomial (Fin 3) ℝ, ∀ u : S2, basisSymbol N p u = MvPolynomial.eval u.1 P := by
  unfold basisSymbol coherentSymbol
  split_ifs
  · exact diagonalSymbol_poly N _ _
  · obtain ⟨P1, hP1⟩ := diagonalSymbol_poly N (Pi.single 0 1) (stdBasis p.1 + stdBasis p.2)
    obtain ⟨P2, hP2⟩ := diagonalSymbol_poly N (Pi.single 0 1) (stdBasis p.1)
    obtain ⟨P3, hP3⟩ := diagonalSymbol_poly N (Pi.single 0 1) (stdBasis p.2)
    refine ⟨MvPolynomial.C (Real.sqrt 2)⁻¹ * (P1 - P2 - P3), fun u => ?_⟩
    simp [map_mul, map_sub, hP1 u, hP2 u, hP3 u]
  · obtain ⟨P1, hP1⟩ := diagonalSymbol_poly N (Pi.single 0 1) (stdBasis p.2 - I • stdBasis p.1)
    obtain ⟨P2, hP2⟩ := diagonalSymbol_poly N (Pi.single 0 1) (stdBasis p.2)
    obtain ⟨P3, hP3⟩ := diagonalSymbol_poly N (Pi.single 0 1) (stdBasis p.1)
    refine ⟨MvPolynomial.C (Real.sqrt 2)⁻¹ * (P1 - P2 - P3), fun u => ?_⟩
    simp [map_mul, map_sub, hP1 u, hP2 u, hP3 u]

lemma matrixSymbol_poly (N : ℕ) (x : HermIdx N → ℝ) :
    ∃ P : MvPolynomial (Fin 3) ℝ, ∀ u : S2, matrixSymbol N x u = MvPolynomial.eval u.1 P := by
  choose P hP using basisSymbol_poly N
  refine ⟨∑ p : HermIdx N, MvPolynomial.C (x p) * P p, fun u => ?_⟩
  simp [matrixSymbol, map_sum, map_mul, hP]

lemma matrixSymbol_continuous (N : ℕ) (x : HermIdx N → ℝ) :
    Continuous (fun p : ℝ × ℝ => matrixSymbol N x (SU2.sphVec p.1 p.2)) := by
  obtain ⟨P, hP⟩ := matrixSymbol_poly N x
  simp_rw [hP]
  exact continuous_mvPolynomial_sphVec P

lemma basisSymbol_rotated (N : ℕ) (p : HermIdx N) (g : SU2) :
    basisSymbol N p (SU2.actS2 g SU2.northPole) =
      (innerC (coherentVector N g) ((hermBasis N p).mulVec (coherentVector N g))).re := by
  set v := coherentVector N g
  have hproj (ψ : Fin (N + 1) → ℂ) :
      coherentSymbol N ψ (SU2.actS2 g SU2.northPole) =
        (innerC v ((pureProj ψ).mulVec v)).re := by
    rw [coherentSymbol_rotated, pureProj_mulVec_inner, Complex.ofReal_re]
  unfold basisSymbol hermBasis
  split_ifs
  · exact hproj (stdBasis p.1)
  · simp only [hproj, Matrix.smul_mulVec, Matrix.sub_mulVec, innerC_smul_right, innerC_sub_right]
    rw [← Complex.ofReal_inv, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
    simp [Complex.sub_re]
  · simp only [hproj, Matrix.smul_mulVec, Matrix.sub_mulVec, innerC_smul_right, innerC_sub_right]
    rw [← Complex.ofReal_inv, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
    simp [Complex.sub_re]

lemma matrixSymbol_rotated (N : ℕ) (x : HermIdx N → ℝ) (g : SU2) :
    matrixSymbol N x (SU2.actS2 g SU2.northPole) =
      (innerC (coherentVector N g) ((ofHermCoords x).mulVec (coherentVector N g))).re := by
  unfold matrixSymbol ofHermCoords
  simp_rw [basisSymbol_rotated]
  have hmul : (∑ p : HermIdx N, (x p : ℂ) • hermBasis N p).mulVec (coherentVector N g) =
      ∑ p : HermIdx N, (x p : ℂ) • ((hermBasis N p).mulVec (coherentVector N g)) := by
    ext i
    simp [Matrix.mulVec, dotProduct, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro p _
    apply Finset.sum_congr rfl; intro j _
    ring
  have hinner : innerC (coherentVector N g)
        (∑ p : HermIdx N, (x p : ℂ) • ((hermBasis N p).mulVec (coherentVector N g))) =
      ∑ p : HermIdx N, (x p : ℂ) * innerC (coherentVector N g) ((hermBasis N p).mulVec (coherentVector N g)) := by
    simp only [innerC, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro p _
    apply Finset.sum_congr rfl; intro i _
    ring
  rw [hmul, hinner, Complex.re_sum]
  apply Finset.sum_congr rfl; intro p _
  simp [Complex.mul_re]

lemma matrixSymbol_idVec (N : ℕ) (u : S2) : matrixSymbol N (idVec N) u = 1 := by
  obtain ⟨θ, _, φ, rfl⟩ := sphVec_surjective u
  rw [← SU2.actS2_rotZ_rotY_northPole, matrixSymbol_rotated, ofHermCoords_idVec, Matrix.one_mulVec]
  set g := SU2.rotZ φ * SU2.rotY θ
  have hu := congrFun (congrFun (spinRep_conjTranspose_mul_self N g) 0) 0
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply_eq] at hu
  change (∑ k : Fin (N + 1), star (spinRep N g k 0) * spinRep N g k 0).re = 1
  rw [hu, Complex.one_re]

private lemma swIntegral_sub_local (N : ℕ) {f g : S2 → ℝ}
    (hf : Continuous (fun p : ℝ × ℝ => f (SU2.sphVec p.1 p.2)))
    (hg : Continuous (fun p : ℝ × ℝ => g (SU2.sphVec p.1 p.2))) :
    swIntegral N (fun u => f u - g u) = swIntegral N f - swIntegral N g := by
  have hsub : (fun u => f u - g u) = fun u => ∑ b : Bool, if b then f u else (-g u) := by
    funext u; simp [sub_eq_add_neg]
  rw [hsub, swIntegral_sum N _ (fun b => by cases b <;> [exact hg.neg; exact hf])]
  simp only [Fintype.sum_bool, ↓reduceIte, Bool.false_eq_true]
  have hneg : swIntegral N (fun u => -g u) = -swIntegral N g := by
    unfold swIntegral sphereAvg
    simp_rw [mul_neg, intervalIntegral.integral_neg]
    ring
  rw [hneg]; ring

private lemma swIntegral_const_mul_local (N : ℕ) (a : ℝ) (f : S2 → ℝ) :
    swIntegral N (fun u => a * f u) = a * swIntegral N f := by
  unfold swIntegral sphereAvg
  simp_rw [mul_left_comm (Real.sin _) a, intervalIntegral.integral_const_mul]
  ring

private lemma coherentSymbol_continuous (N : ℕ) (ψ : Fin (N + 1) → ℂ) :
    Continuous (fun p : ℝ × ℝ => coherentSymbol N ψ (SU2.sphVec p.1 p.2)) := by
  obtain ⟨P, hP⟩ := diagonalSymbol_poly N (Pi.single 0 1) ψ
  simp_rw [coherentSymbol, hP]
  exact continuous_mvPolynomial_sphVec P

private lemma innerC_stdBasis_self {N : ℕ} (i : Fin (N + 1)) :
    innerC (stdBasis i) (stdBasis i) = 1 := by
  unfold innerC stdBasis
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hj; simp [Pi.single_eq_of_ne hj]
  · intro h; exact absurd (Finset.mem_univ _) h

private lemma innerC_stdBasis_add {N : ℕ} {i j : Fin (N + 1)} (hne : i ≠ j) :
    innerC (stdBasis i + stdBasis j) (stdBasis i + stdBasis j) = 2 := by
  have hsum : ∀ k : Fin (N + 1),
      star ((stdBasis i + stdBasis j) k) * (stdBasis i + stdBasis j) k =
        (if k = i then 1 else 0) + (if k = j then 1 else 0) := by
    intro k
    simp only [stdBasis, Pi.add_apply, Pi.single_apply]
    by_cases hki : k = i <;> by_cases hkj : k = j <;> simp_all
  simp only [innerC, hsum, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
  norm_num

private lemma innerC_stdBasis_sub_I {N : ℕ} {i j : Fin (N + 1)} (hne : i ≠ j) :
    innerC (stdBasis i - I • stdBasis j) (stdBasis i - I • stdBasis j) = 2 := by
  have hsum : ∀ k : Fin (N + 1),
      star ((stdBasis i - I • stdBasis j) k) * (stdBasis i - I • stdBasis j) k =
        (if k = i then 1 else 0) + (if k = j then 1 else 0) := by
    intro k
    simp only [stdBasis, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply,
      RCLike.star_def]
    by_cases hki : k = i <;> by_cases hkj : k = j <;> simp_all [Complex.conj_I]
  simp only [innerC, hsum, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
  norm_num

lemma swIntegral_basisSymbol (N : ℕ) (p : HermIdx N) :
    swIntegral N (basisSymbol N p) = idVec N p := by
  have hid : idVec N p = if p.1 = p.2 then 1 else 0 := by
    unfold idVec hermCoords
    split_ifs with h1 h2
    · simp
    · have hne : p.1 ≠ p.2 := h1
      simp [Matrix.one_apply_ne hne]
    · have hne : p.2 ≠ p.1 := Ne.symm h1
      simp [Matrix.one_apply_ne hne]
  rw [hid]
  unfold basisSymbol
  split_ifs with h1 h2
  · rw [coherentSymbol_norm, innerC_stdBasis_self]; simp
  · rw [swIntegral_const_mul_local,
      swIntegral_sub_local N ((coherentSymbol_continuous N _).sub (coherentSymbol_continuous N _))
        (coherentSymbol_continuous N _),
      swIntegral_sub_local N (coherentSymbol_continuous N _) (coherentSymbol_continuous N _),
      coherentSymbol_norm, coherentSymbol_norm, coherentSymbol_norm,
      innerC_stdBasis_add h1, innerC_stdBasis_self, innerC_stdBasis_self]
    norm_num
  · rw [swIntegral_const_mul_local,
      swIntegral_sub_local N ((coherentSymbol_continuous N _).sub (coherentSymbol_continuous N _))
        (coherentSymbol_continuous N _),
      swIntegral_sub_local N (coherentSymbol_continuous N _) (coherentSymbol_continuous N _),
      coherentSymbol_norm, coherentSymbol_norm, coherentSymbol_norm,
      innerC_stdBasis_sub_I (Ne.symm h1), innerC_stdBasis_self, innerC_stdBasis_self]
    norm_num

lemma swIntegral_matrixSymbol (N : ℕ) (x : HermIdx N → ℝ) :
    swIntegral N (matrixSymbol N x) = dotProduct (idVec N) x := by
  unfold matrixSymbol
  rw [swIntegral_sum N _ (fun p => by
    obtain ⟨P, hP⟩ := basisSymbol_poly N p
    simp_rw [hP]
    exact continuous_const.mul (continuous_mvPolynomial_sphVec P))]
  simp only [swIntegral_const_mul_local, swIntegral_basisSymbol, dotProduct]
  apply Finset.sum_congr rfl; intro p _; ring

/-- Informational completeness on Hermitian coordinates: a nonzero Hermitian matrix has a
nonzero coherent-state symbol at some point of `S²`. -/
lemma matrixSymbol_ne_zero {N : ℕ} {x : HermIdx N → ℝ} (hx : x ≠ 0) :
    ∃ u : S2, matrixSymbol N x u ≠ 0 := by
  by_contra h
  push Not at h
  have hA : ofHermCoords x = 0 := by
    apply coherent_expectation_injective
    intro g
    have hre : (innerC (coherentVector N g) ((ofHermCoords x).mulVec (coherentVector N g))).re = 0 := by
      rw [← matrixSymbol_rotated]; exact h _
    have hreal : star (innerC (coherentVector N g) ((ofHermCoords x).mulVec (coherentVector N g))) =
        innerC (coherentVector N g) ((ofHermCoords x).mulVec (coherentVector N g)) := by
      set v := coherentVector N g
      set A := ofHermCoords x
      have hAh : A.IsHermitian := ofHermCoords_isHermitian x
      simp only [innerC, Matrix.mulVec, dotProduct, star_sum, star_mul', star_star,
        Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl; intro a _
      apply Finset.sum_congr rfl; intro b _
      rw [herm_entry_conj hAh a b]
      ring
    have him : (innerC (coherentVector N g) ((ofHermCoords x).mulVec (coherentVector N g))).im = 0 := by
      have him' := congrArg Complex.im hreal
      simp only [RCLike.star_def, Complex.conj_im] at him'
      linarith
    exact Complex.ext hre him
  have hx0 : x = 0 := by
    rw [← hermCoords_ofHermCoords x, hA]
    funext p; unfold hermCoords; split_ifs <;> simp
  exact hx hx0

/-! ### Adjoint Action of `SU(2)` on Hermitian Coordinates -/

/-- Matrix of the adjoint action `A ↦ D(g) A D(g)ᴴ` in the orthonormal basis `hermBasis N`. -/
def adMatrix (N : ℕ) (g : SU2) : Matrix (HermIdx N) (HermIdx N) ℝ :=
  fun p q => hermCoords (spinRep N g * hermBasis N q * (spinRep N g)ᴴ) p

private lemma ad_isHermitian (N : ℕ) (g : SU2) {A : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ}
    (hA : A.IsHermitian) : (spinRep N g * A * (spinRep N g)ᴴ).IsHermitian := by
  change (spinRep N g * A * (spinRep N g)ᴴ)ᴴ = spinRep N g * A * (spinRep N g)ᴴ
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
    hA.eq, Matrix.mul_assoc]

lemma ofHermCoords_adMatrix (N : ℕ) (g : SU2) (x : HermIdx N → ℝ) :
    ofHermCoords ((adMatrix N g).mulVec x) =
      spinRep N g * ofHermCoords x * (spinRep N g)ᴴ := by
  have h1 : ofHermCoords ((adMatrix N g).mulVec x) =
      ∑ q : HermIdx N, (x q : ℂ) • ofHermCoords (fun p => adMatrix N g p q) := by
    unfold ofHermCoords
    simp only [Matrix.mulVec, dotProduct, Complex.ofReal_sum, Complex.ofReal_mul,
      Finset.sum_smul, Finset.smul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro q _
    apply Finset.sum_congr rfl; intro p _
    rw [smul_smul, mul_comm]
  rw [h1]
  have h2 (q : HermIdx N) : ofHermCoords (fun p => adMatrix N g p q) =
      spinRep N g * hermBasis N q * (spinRep N g)ᴴ :=
    ofHermCoords_hermCoords (ad_isHermitian N g (hermBasis_isHermitian N q))
  simp_rw [h2]
  unfold ofHermCoords
  rw [Matrix.mul_sum, Matrix.sum_mul]
  apply Finset.sum_congr rfl; intro q _
  simp

lemma adMatrix_hermCoords (N : ℕ) (g : SU2) {A : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ}
    (hA : A.IsHermitian) :
    (adMatrix N g).mulVec (hermCoords A) = hermCoords (spinRep N g * A * (spinRep N g)ᴴ) := by
  rw [← hermCoords_ofHermCoords ((adMatrix N g).mulVec (hermCoords A)),
    ofHermCoords_adMatrix, ofHermCoords_hermCoords hA]

lemma adMatrix_pureProj (N : ℕ) (g : SU2) (ψ : Fin (N + 1) → ℂ) :
    (adMatrix N g).mulVec (hermCoords (pureProj ψ)) =
      hermCoords (pureProj ((spinRep N g).mulVec ψ)) := by
  rw [adMatrix_hermCoords N g (pureProj_isHermitian ψ)]
  congr 1
  ext a b
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, pureProj, Matrix.mulVec, dotProduct,
    star_sum, star_mul', Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl; intro i _
  apply Finset.sum_congr rfl; intro j _
  ring

lemma dotProduct_adMatrix (N : ℕ) (g : SU2) (x y : HermIdx N → ℝ) :
    dotProduct ((adMatrix N g).mulVec x) ((adMatrix N g).mulVec y) = dotProduct x y := by
  have hx := ofHermCoords_isHermitian x
  have hy := ofHermCoords_isHermitian y
  rw [← hermCoords_ofHermCoords ((adMatrix N g).mulVec x),
    ← hermCoords_ofHermCoords ((adMatrix N g).mulVec y),
    ofHermCoords_adMatrix, ofHermCoords_adMatrix,
    dotProduct_hermCoords (ad_isHermitian N g hx) (ad_isHermitian N g hy)]
  have htr : Matrix.trace ((spinRep N g * ofHermCoords x * (spinRep N g)ᴴ) *
      (spinRep N g * ofHermCoords y * (spinRep N g)ᴴ)) =
      Matrix.trace (ofHermCoords x * ofHermCoords y) := by
    calc Matrix.trace ((spinRep N g * ofHermCoords x * (spinRep N g)ᴴ) *
          (spinRep N g * ofHermCoords y * (spinRep N g)ᴴ))
        = Matrix.trace (spinRep N g * (ofHermCoords x * ((spinRep N g)ᴴ * spinRep N g) *
            ofHermCoords y) * (spinRep N g)ᴴ) := by simp only [Matrix.mul_assoc]
      _ = Matrix.trace (spinRep N g * (ofHermCoords x * ofHermCoords y) * (spinRep N g)ᴴ) := by
            rw [spinRep_conjTranspose_mul_self, Matrix.mul_one]
      _ = Matrix.trace ((spinRep N g)ᴴ * (spinRep N g * (ofHermCoords x * ofHermCoords y))) :=
            Matrix.trace_mul_comm _ _
      _ = Matrix.trace (ofHermCoords x * ofHermCoords y) := by
            rw [← Matrix.mul_assoc, spinRep_conjTranspose_mul_self, Matrix.one_mul]
  rw [htr, ← dotProduct_hermCoords hx hy, hermCoords_ofHermCoords, hermCoords_ofHermCoords]

lemma adMatrix_transpose_mul_self (N : ℕ) (g : SU2) :
    (adMatrix N g)ᵀ * adMatrix N g = 1 := by
  ext p q
  have h := dotProduct_adMatrix N g (Pi.single p 1) (Pi.single q 1)
  simp only [Matrix.mulVec_single_one, dotProduct_single, mul_one, Pi.single_apply,
    eq_comm (a := q) (b := p)] at h
  simpa [Matrix.mul_apply, dotProduct, Matrix.one_apply] using h

lemma adMatrix_mul (N : ℕ) (g₁ g₂ : SU2) :
    adMatrix N (g₁ * g₂) = adMatrix N g₁ * adMatrix N g₂ := by
  ext p q
  have h1 : ((adMatrix N (g₁ * g₂)).mulVec (Pi.single q 1)) p =
      ((adMatrix N g₁ * adMatrix N g₂).mulVec (Pi.single q 1)) p := by
    rw [← Matrix.mulVec_mulVec]
    have hq : hermCoords (hermBasis N q) = Pi.single q 1 := by
      have : ofHermCoords (Pi.single q 1) = hermBasis N q := by
        unfold ofHermCoords
        rw [Finset.sum_eq_single q]
        · simp
        · intro r _ hr; simp [Pi.single_eq_of_ne hr]
        · intro h; exact absurd (Finset.mem_univ _) h
      rw [← this, hermCoords_ofHermCoords]
    rw [← hq, adMatrix_hermCoords N (g₁ * g₂) (hermBasis_isHermitian N q),
      adMatrix_hermCoords N g₂ (hermBasis_isHermitian N q),
      adMatrix_hermCoords N g₁ (ad_isHermitian N g₂ (hermBasis_isHermitian N q)),
      spinRep_mul, Matrix.conjTranspose_mul]
    simp only [Matrix.mul_assoc]
  simpa [Matrix.mulVec_single_one] using h1

lemma adMatrix_one (N : ℕ) : adMatrix N 1 = 1 := by
  ext p q
  have h : ofHermCoords ((adMatrix N 1).mulVec (Pi.single q 1)) = ofHermCoords (Pi.single q 1) := by
    rw [ofHermCoords_adMatrix, spinRep_one, Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one]
  have h2 := congrFun (congrArg hermCoords h) p
  rw [hermCoords_ofHermCoords, hermCoords_ofHermCoords] at h2
  simpa [Matrix.mulVec_single_one, Matrix.one_apply, Pi.single_apply] using h2

lemma matrixSymbol_covariant (N : ℕ) (g : SU2) (x : HermIdx N → ℝ) (u : S2) :
    matrixSymbol N ((adMatrix N g).mulVec x) (SU2.actS2 g u) = matrixSymbol N x u := by
  obtain ⟨θ, _, φ, rfl⟩ := sphVec_surjective u
  rw [← SU2.actS2_rotZ_rotY_northPole, ← SU2.actS2_mul, matrixSymbol_rotated, matrixSymbol_rotated,
    ofHermCoords_adMatrix]
  set h := SU2.rotZ φ * SU2.rotY θ
  have hvec : coherentVector N (g * h) = (spinRep N g).mulVec (coherentVector N h) := by
    ext k
    simp only [coherentVector, spinRep_mul, Matrix.mul_apply, Matrix.mulVec, dotProduct]
  rw [hvec]
  have hstep : (spinRep N g * ofHermCoords x * (spinRep N g)ᴴ).mulVec
        ((spinRep N g).mulVec (coherentVector N h)) =
      (spinRep N g).mulVec ((ofHermCoords x).mulVec (coherentVector N h)) := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_assoc (spinRep N g * ofHermCoords x),
      spinRep_conjTranspose_mul_self, Matrix.mul_one, Matrix.mulVec_mulVec]
  rw [hstep, innerC_spinRep_unitary]

/-! ### Coherent-State Gram Matrix and Its Inverse Square Root -/

/-- Real symmetric Gram matrix of the coherent-state basis symbols under `swIntegral N`. -/
def gramMatrix (N : ℕ) : Matrix (HermIdx N) (HermIdx N) ℝ :=
  fun p q => swIntegral N (fun u => basisSymbol N p u * basisSymbol N q u)

lemma gramMatrix_isHermitian (N : ℕ) : (gramMatrix N).IsHermitian := by
  ext p q
  simp only [Matrix.conjTranspose_apply, star_trivial, gramMatrix, mul_comm]

lemma dotProduct_gramMatrix (N : ℕ) (x y : HermIdx N → ℝ) :
    dotProduct x ((gramMatrix N).mulVec y) =
      swIntegral N (fun u => matrixSymbol N x u * matrixSymbol N y u) := by
  have hcb (p : HermIdx N) : Continuous (fun s : ℝ × ℝ => basisSymbol N p (SU2.sphVec s.1 s.2)) := by
    obtain ⟨P, hP⟩ := basisSymbol_poly N p
    simp_rw [hP]
    exact continuous_mvPolynomial_sphVec P
  have hexp (u : S2) : matrixSymbol N x u * matrixSymbol N y u =
      ∑ p : HermIdx N, ∑ q : HermIdx N, (x p * y q) * (basisSymbol N p u * basisSymbol N q u) := by
    unfold matrixSymbol
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl; intro p _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl; intro q _
    ring
  simp_rw [hexp]
  rw [swIntegral_sum N _ (fun p => continuous_finsetSum _ (fun q _ =>
    continuous_const.mul ((hcb p).mul (hcb q))))]
  simp only [dotProduct, Matrix.mulVec, gramMatrix, Finset.mul_sum]
  apply Finset.sum_congr rfl; intro p _
  rw [swIntegral_sum N _ (fun q => continuous_const.mul ((hcb p).mul (hcb q)))]
  apply Finset.sum_congr rfl; intro q _
  rw [swIntegral_const_mul_local]
  ring

lemma dotProduct_gramMatrix_pos (N : ℕ) {x : HermIdx N → ℝ} (hx : x ≠ 0) :
    0 < dotProduct x ((gramMatrix N).mulVec x) := by
  rw [dotProduct_gramMatrix]
  obtain ⟨P, hP⟩ := matrixSymbol_poly N x
  obtain ⟨u₀, hu₀⟩ := matrixSymbol_ne_zero hx
  have hsq : (fun u : S2 => matrixSymbol N x u * matrixSymbol N x u) =
      fun u : S2 => MvPolynomial.eval u.1 P ^ 2 := by
    funext u; rw [hP u, pow_two]
  rw [hsq, swIntegral]
  exact mul_pos (by positivity) (sphereAvg_sq_pos P ⟨u₀, hP u₀ ▸ hu₀⟩)

lemma gramMatrix_mulVec_idVec (N : ℕ) : (gramMatrix N).mulVec (idVec N) = idVec N := by
  funext p
  have h : dotProduct (Pi.single p 1) ((gramMatrix N).mulVec (idVec N)) =
      ((gramMatrix N).mulVec (idVec N)) p := by simp
  rw [← h, dotProduct_gramMatrix]
  have h1 (u : S2) : matrixSymbol N (Pi.single p 1) u = basisSymbol N p u := by
    unfold matrixSymbol
    rw [Finset.sum_eq_single p]
    · simp
    · intro q _ hq; simp [Pi.single_eq_of_ne hq]
    · intro hp; exact absurd (Finset.mem_univ _) hp
  simp_rw [h1, matrixSymbol_idVec, mul_one]
  exact swIntegral_basisSymbol N p

lemma gramMatrix_comm_adMatrix (N : ℕ) (g : SU2) :
    gramMatrix N * adMatrix N g = adMatrix N g * gramMatrix N := by
  have hbilin (x y : HermIdx N → ℝ) :
      dotProduct x (((adMatrix N g)ᵀ * gramMatrix N * adMatrix N g).mulVec y) =
        dotProduct x ((gramMatrix N).mulVec y) := by
    rw [Matrix.mul_assoc, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
      Matrix.dotProduct_mulVec, Matrix.vecMul_transpose, dotProduct_gramMatrix,
      dotProduct_gramMatrix]
    have hcov (u : S2) :
        matrixSymbol N ((adMatrix N g).mulVec x) u * matrixSymbol N ((adMatrix N g).mulVec y) u =
        matrixSymbol N x (SU2.actS2 g⁻¹ u) * matrixSymbol N y (SU2.actS2 g⁻¹ u) := by
      have hact : SU2.actS2 g (SU2.actS2 g⁻¹ u) = u := by
        rw [← SU2.actS2_mul, SU2.mul_inv_cancel, SU2.actS2_one]
      conv_lhs => rw [← hact, matrixSymbol_covariant, matrixSymbol_covariant]
    simp_rw [hcov]
    obtain ⟨Px, hPx⟩ := matrixSymbol_poly N x
    obtain ⟨Py, hPy⟩ := matrixSymbol_poly N y
    exact swIntegral_actS2 N (f := fun u => matrixSymbol N x u * matrixSymbol N y u)
      ⟨Px * Py, fun u => by simp [map_mul, hPx u, hPy u]⟩ g⁻¹
  have hconj : (adMatrix N g)ᵀ * gramMatrix N * adMatrix N g = gramMatrix N := by
    ext p q
    have h := hbilin (Pi.single p 1) (Pi.single q 1)
    simpa [dotProduct_single, Matrix.mulVec_single_one] using h
  have hmul_inv : adMatrix N g * (adMatrix N g)ᵀ = 1 := by
    have hinv : adMatrix N g⁻¹ = (adMatrix N g)ᵀ := by
      calc adMatrix N g⁻¹ = 1 * adMatrix N g⁻¹ := (Matrix.one_mul _).symm
        _ = ((adMatrix N g)ᵀ * adMatrix N g) * adMatrix N g⁻¹ := by rw [adMatrix_transpose_mul_self]
        _ = (adMatrix N g)ᵀ * (adMatrix N g * adMatrix N g⁻¹) := Matrix.mul_assoc _ _ _
        _ = (adMatrix N g)ᵀ := by rw [← adMatrix_mul, SU2.mul_inv_cancel, adMatrix_one, Matrix.mul_one]
    rw [← hinv, ← adMatrix_mul, SU2.mul_inv_cancel, adMatrix_one]
  calc gramMatrix N * adMatrix N g
      = 1 * (gramMatrix N * adMatrix N g) := (Matrix.one_mul _).symm
    _ = (adMatrix N g * (adMatrix N g)ᵀ) * (gramMatrix N * adMatrix N g) := by rw [hmul_inv]
    _ = adMatrix N g * ((adMatrix N g)ᵀ * gramMatrix N * adMatrix N g) := by simp only [Matrix.mul_assoc]
    _ = adMatrix N g * gramMatrix N := by rw [hconj]

/-! ### Spectral Inverse Square Root `G⁻¹/²` -/

private def gramU (N : ℕ) : Matrix (HermIdx N) (HermIdx N) ℝ :=
  (gramMatrix_isHermitian N).eigenvectorUnitary

private def gramEig (N : ℕ) : HermIdx N → ℝ :=
  (gramMatrix_isHermitian N).eigenvalues

private lemma gram_eigenvalues_pos (N : ℕ) (i : HermIdx N) :
    0 < gramEig N i := by
  have hG := gramMatrix_isHermitian N
  change 0 < hG.eigenvalues i
  rw [hG.eigenvalues_eq i]
  have hne : (⇑(hG.eigenvectorBasis i) : HermIdx N → ℝ) ≠ 0 := by
    intro h0
    have h1 := hG.eigenvectorBasis.orthonormal.1 i
    have hnorm0 : ‖hG.eigenvectorBasis i‖ = 0 := by
      rw [EuclideanSpace.norm_eq]
      simp [h0]
    linarith
  simpa using dotProduct_gramMatrix_pos N hne

/-- Inverse square root `G⁻¹/²` of the coherent-state Gram matrix via spectral diagonalization. -/
def invSqrtGram (N : ℕ) : Matrix (HermIdx N) (HermIdx N) ℝ :=
  gramU N * Matrix.diagonal (fun i => (Real.sqrt (gramEig N i))⁻¹) * (gramU N)ᵀ

private lemma gram_spectral (N : ℕ) :
    gramMatrix N = gramU N * Matrix.diagonal (gramEig N) * (gramU N)ᵀ := by
  have h := (gramMatrix_isHermitian N).spectral_theorem
  simpa [gramU, gramEig, Unitary.conjStarAlgAut_apply, Matrix.star_eq_conjTranspose,
    Matrix.conjTranspose_eq_transpose_of_trivial] using h

private lemma gram_diag (N : ℕ) :
    (gramU N)ᵀ * gramMatrix N * gramU N = Matrix.diagonal (gramEig N) := by
  have h := (gramMatrix_isHermitian N).conjStarAlgAut_star_eigenvectorUnitary
  simpa [gramU, gramEig, Unitary.conjStarAlgAut_star_apply, Matrix.star_eq_conjTranspose,
    Matrix.conjTranspose_eq_transpose_of_trivial] using h

private lemma gram_U_mul_UT (N : ℕ) :
    gramU N * (gramU N)ᵀ = 1 := by
  have h := Unitary.coe_mul_star_self (gramMatrix_isHermitian N).eigenvectorUnitary
  simpa [gramU, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial] using h

private lemma gram_UT_mul_U (N : ℕ) :
    (gramU N)ᵀ * gramU N = 1 := by
  have h := Unitary.coe_star_mul_self (gramMatrix_isHermitian N).eigenvectorUnitary
  simpa [gramU, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial] using h

lemma invSqrtGram_transpose (N : ℕ) : (invSqrtGram N)ᵀ = invSqrtGram N := by
  unfold invSqrtGram
  simp [Matrix.transpose_mul, Matrix.mul_assoc]

lemma invSqrtGram_mul_gram_mul_invSqrtGram (N : ℕ) :
    invSqrtGram N * gramMatrix N * invSqrtGram N = 1 := by
  let d : HermIdx N → ℝ := fun i => (Real.sqrt (gramEig N i))⁻¹
  have hUTU : (gramU N)ᵀ * gramU N = 1 := gram_UT_mul_U N
  have hUUT : gramU N * (gramU N)ᵀ = 1 := gram_U_mul_UT N
  have hspec : gramMatrix N = gramU N * Matrix.diagonal (gramEig N) * (gramU N)ᵀ := gram_spectral N
  have hdiag : Matrix.diagonal d * Matrix.diagonal (gramEig N) * Matrix.diagonal d = 1 := by
    rw [Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
    ext i j
    by_cases hij : i = j
    · subst hij
      have hpos : 0 < gramEig N i := gram_eigenvalues_pos N i
      have hne : Real.sqrt (gramEig N i) ≠ 0 := (Real.sqrt_pos.mpr hpos).ne'
      simp only [Matrix.diagonal_apply_eq, Matrix.one_apply_eq, d]
      field_simp [hne]
      exact (Real.sq_sqrt hpos.le).symm
    · simp [Matrix.diagonal_apply_ne _ hij, Matrix.one_apply_ne hij]
  calc invSqrtGram N * gramMatrix N * invSqrtGram N
      = (gramU N * Matrix.diagonal d * (gramU N)ᵀ) *
          (gramU N * Matrix.diagonal (gramEig N) * (gramU N)ᵀ) *
          (gramU N * Matrix.diagonal d * (gramU N)ᵀ) := by rw [invSqrtGram, hspec]
    _ = gramU N * Matrix.diagonal d * ((gramU N)ᵀ * gramU N) * Matrix.diagonal (gramEig N) *
          ((gramU N)ᵀ * gramU N) * Matrix.diagonal d * (gramU N)ᵀ := by simp only [Matrix.mul_assoc]
    _ = gramU N * (Matrix.diagonal d * Matrix.diagonal (gramEig N) * Matrix.diagonal d) * (gramU N)ᵀ := by
          rw [hUTU, Matrix.mul_one, Matrix.mul_one]; simp only [Matrix.mul_assoc]
    _ = 1 := by rw [hdiag, Matrix.mul_one, hUUT]

lemma invSqrtGram_comm_of_gram_comm (N : ℕ) (M : Matrix (HermIdx N) (HermIdx N) ℝ)
    (hM : gramMatrix N * M = M * gramMatrix N) :
    invSqrtGram N * M = M * invSqrtGram N := by
  let d : HermIdx N → ℝ := fun i => (Real.sqrt (gramEig N i))⁻¹
  let B : Matrix (HermIdx N) (HermIdx N) ℝ := (gramU N)ᵀ * M * gramU N
  have hUUT : gramU N * (gramU N)ᵀ = 1 := gram_U_mul_UT N
  have hGD : (gramU N)ᵀ * gramMatrix N * gramU N = Matrix.diagonal (gramEig N) := gram_diag N
  have hDB : Matrix.diagonal (gramEig N) * B = B * Matrix.diagonal (gramEig N) := by
    calc Matrix.diagonal (gramEig N) * B
        = ((gramU N)ᵀ * gramMatrix N * gramU N) * ((gramU N)ᵀ * M * gramU N) := by rw [hGD]
      _ = (gramU N)ᵀ * gramMatrix N * (gramU N * (gramU N)ᵀ) * M * gramU N := by
            simp only [Matrix.mul_assoc]
      _ = (gramU N)ᵀ * (gramMatrix N * M) * gramU N := by
            rw [hUUT, Matrix.mul_one]; simp only [Matrix.mul_assoc]
      _ = (gramU N)ᵀ * (M * gramMatrix N) * gramU N := by rw [hM]
      _ = (gramU N)ᵀ * M * (gramU N * (gramU N)ᵀ) * gramMatrix N * gramU N := by
            rw [hUUT, Matrix.mul_one]; simp only [Matrix.mul_assoc]
      _ = B * Matrix.diagonal (gramEig N) := by rw [← hGD]; simp only [B, Matrix.mul_assoc]
  have hdB : Matrix.diagonal d * B = B * Matrix.diagonal d := by
    ext i j
    have hij := congrFun (congrFun hDB i) j
    simp only [Matrix.diagonal_mul, Matrix.mul_diagonal] at hij ⊢
    by_cases heq : gramEig N i = gramEig N j
    · simp only [d, heq]; ring
    · have hB0 : B i j = 0 := by
        have hsub : (gramEig N i - gramEig N j) * B i j = 0 := by linarith
        exact (mul_eq_zero.mp hsub).resolve_left (sub_ne_zero.mpr heq)
      simp [hB0]
  calc invSqrtGram N * M
      = (gramU N * Matrix.diagonal d * (gramU N)ᵀ) * M * (gramU N * (gramU N)ᵀ) := by
          rw [invSqrtGram, hUUT, Matrix.mul_one]
    _ = gramU N * (Matrix.diagonal d * B) * (gramU N)ᵀ := by simp only [B, Matrix.mul_assoc]
    _ = gramU N * (B * Matrix.diagonal d) * (gramU N)ᵀ := by rw [hdB]
    _ = (gramU N * (gramU N)ᵀ) * M * (gramU N * Matrix.diagonal d * (gramU N)ᵀ) := by
          simp only [B, Matrix.mul_assoc]
    _ = M * invSqrtGram N := by rw [hUUT, Matrix.one_mul, invSqrtGram]

lemma invSqrtGram_mulVec_idVec (N : ℕ) : (invSqrtGram N).mulVec (idVec N) = idVec N := by
  let d : HermIdx N → ℝ := fun i => (Real.sqrt (gramEig N i))⁻¹
  let w : HermIdx N → ℝ := (gramU N)ᵀ.mulVec (idVec N)
  have hUUT : gramU N * (gramU N)ᵀ = 1 := gram_U_mul_UT N
  have hGD : (gramU N)ᵀ * gramMatrix N * gramU N = Matrix.diagonal (gramEig N) := gram_diag N
  have hDw : (Matrix.diagonal (gramEig N)).mulVec w = w := by
    calc (Matrix.diagonal (gramEig N)).mulVec w
        = ((gramU N)ᵀ * gramMatrix N * gramU N).mulVec ((gramU N)ᵀ.mulVec (idVec N)) := by rw [hGD]
      _ = ((gramU N)ᵀ * gramMatrix N * (gramU N * (gramU N)ᵀ)).mulVec (idVec N) := by
            rw [Matrix.mulVec_mulVec]; simp only [Matrix.mul_assoc]
      _ = (gramU N)ᵀ.mulVec ((gramMatrix N).mulVec (idVec N)) := by
            rw [hUUT, Matrix.mul_one, Matrix.mulVec_mulVec]
      _ = w := by rw [gramMatrix_mulVec_idVec]
  have hdw : (Matrix.diagonal d).mulVec w = w := by
    funext i
    have hi := congrFun hDw i
    simp only [Matrix.mulVec_diagonal] at hi ⊢
    by_cases h1 : gramEig N i = 1
    · simp [d, h1]
    · have hw0 : w i = 0 := by
        have hsub : (gramEig N i - 1) * w i = 0 := by linarith
        exact (mul_eq_zero.mp hsub).resolve_left (sub_ne_zero.mpr h1)
      simp [hw0]
  calc (invSqrtGram N).mulVec (idVec N)
      = (gramU N).mulVec ((Matrix.diagonal d).mulVec w) := by
          rw [invSqrtGram, Matrix.mul_assoc, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
    _ = (gramU N).mulVec w := by rw [hdw]
    _ = idVec N := by rw [Matrix.mulVec_mulVec, hUUT, Matrix.one_mulVec]

/-! ### All-Spin Stratonovich–Weyl System Construction -/

/-- The canonical all-spin Stratonovich–Weyl spherical Wigner function constructed by
symmetric orthonormalization (`G⁻¹/²`) of the coherent-state symbol map. -/
def canonicalWigner (N : ℕ) (ψ : Fin (N + 1) → ℂ) (u : S2) : ℝ :=
  matrixSymbol N ((invSqrtGram N).mulVec (hermCoords (pureProj ψ))) u

/-- Concrete `StratonovichWeylSystem N` for every spin `j = N / 2` (`N : ℕ`),
with complete proofs of polynomiality, normalization, `SU(2)`-covariance, and
all-state Moyal/tracial overlap. -/
def canonicalStratonovichWeyl (N : ℕ) : StratonovichWeylSystem N where
  W := canonicalWigner N
  poly ψ := matrixSymbol_poly N _
  norm_eq ψ := by
    unfold canonicalWigner
    rw [swIntegral_matrixSymbol, Matrix.dotProduct_mulVec,
      ← Matrix.mulVec_transpose, invSqrtGram_transpose, invSqrtGram_mulVec_idVec,
      dotProduct_idVec_pureProj]
  covariant g ψ u := by
    unfold canonicalWigner
    rw [← adMatrix_pureProj, Matrix.mulVec_mulVec,
      invSqrtGram_comm_of_gram_comm N (adMatrix N g) (gramMatrix_comm_adMatrix N g),
      ← Matrix.mulVec_mulVec, matrixSymbol_covariant]
  tracial φ ψ := by
    unfold canonicalWigner
    have hGt : (gramMatrix N)ᵀ = gramMatrix N := by
      simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using (gramMatrix_isHermitian N).eq
    rw [← dotProduct_gramMatrix, Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec,
      ← Matrix.mulVec_transpose, Matrix.transpose_mul, invSqrtGram_transpose, hGt,
      Matrix.mulVec_mulVec, invSqrtGram_mul_gram_mul_invSqrtGram, Matrix.one_mulVec,
      dotProduct_hermCoords_pureProj]

lemma canonicalStratonovichWeyl_continuous (N : ℕ) (u : S2) :
    Continuous (fun ψ : Fin (N + 1) → ℂ => (canonicalStratonovichWeyl N).W ψ u) := by
  change Continuous (fun ψ : Fin (N + 1) → ℂ =>
    ∑ p : HermIdx N, ((invSqrtGram N).mulVec (hermCoords (pureProj ψ))) p * basisSymbol N p u)
  apply continuous_finsetSum; intro p _
  refine Continuous.mul ?_ continuous_const
  change Continuous (fun ψ : Fin (N + 1) → ℂ =>
    ∑ q : HermIdx N, invSqrtGram N p q * hermCoords (pureProj ψ) q)
  apply continuous_finsetSum; intro q _
  have hc : Continuous (fun ψ : Fin (N + 1) → ℂ => hermCoords (pureProj ψ) q) := by
    unfold hermCoords pureProj
    split_ifs <;> fun_prop
  exact continuous_const.mul hc

/-- Unconditional universal Wigner negativity for every spin `j = N / 2 ≥ 1/2` (`N ≥ 1`)
using the explicitly constructed all-spin Stratonovich–Weyl system. -/
theorem canonical_universal_wigner_negativity {N : ℕ} (hN : 1 ≤ N)
    {ψ : Fin (N + 1) → ℂ} (hψ : innerC ψ ψ = 1) :
    ∃ u : S2, (canonicalStratonovichWeyl N).W ψ u < 0 :=
  universal_wigner_negativity hN (canonicalStratonovichWeyl N) hψ

/-- Unconditional uniform spin-dependent Wigner negativity bound for every `N ≥ 1`. -/
theorem canonical_uniform_wigner_negativity_bound {N : ℕ} (hN : 1 ≤ N) :
    ∃ c : ℝ, 0 < c ∧ ∀ ψ : Fin (N + 1) → ℂ, innerC ψ ψ = 1 →
      ∃ u : S2, (canonicalStratonovichWeyl N).W ψ u ≤ -c :=
  uniform_wigner_negativity_bound hN (canonicalStratonovichWeyl N)
    (canonicalStratonovichWeyl_continuous N)

end SU2Wigner
end
