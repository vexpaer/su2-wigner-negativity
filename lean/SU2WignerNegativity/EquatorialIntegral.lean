import SU2WignerNegativity.SpinRep
import SU2WignerNegativity.SphericalHarmonicZero
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Equatorial Integral Identity and Integer-Spin π-Rotation Orthogonality

We prove:
1. The spherical harmonic polynomial basis `Qcoeff j s θ φ = ((n(θ, φ) · Q)^j).coeff s`,
   where `Q = ((X² - 1)/2, -i(X² + 1)/2, X)` satisfies `Q_x² + Q_y² + Q_z² = 0`, is an
   eigenfunction of the spherical Laplacian with eigenvalue `-j(j + 1)`.
2. The middle-row amplitude `Y_ψ(θ, φ) = (D^{(j)}(R_z(φ) R_y(θ))⁻¹ ψ)_j` is a linear
   combination of `Qcoeff j s θ φ`, hence vanishes at some `(θ_*, φ_*)` by Lemma 2
   (`spherical_harmonic_has_zero`).
3. **Theorem 1 (Equatorial Integral Identity)**: For every integer spin `j ≥ 1`,
   `∫_0^{2π} ⟨ψ | D^{(j)}(g_π(R u_eq(φ))) | ψ⟩ dφ = 2π (-1)^j |Y_ψ(θ₀, φ₀)|²`.
4. **Theorem (Integer-Spin & Universal π-Rotation Orthogonality)**:
   Combining `pi_ortho_even` (from 2 + 3 + IVT) with `pi_ortho_odd` gives `pi_ortho_all`
   for EVERY spin `j = N / 2 ≥ 1/2` (`N ≥ 1`) and EVERY pure state `ψ`.
-/

open Complex Polynomial Finset BigOperators MeasureTheory intervalIntegral Real
open scoped Matrix

noncomputable section

namespace SU2Wigner

/-! ### Complex Spherical Laplacian Operator & Linearity -/

/-- Complex partial derivative with respect to `θ`. -/
def dThetaC (f : ℝ → ℝ → ℂ) (θ φ : ℝ) : ℂ :=
  deriv (fun t => f t φ) θ

/-- Complex partial derivative with respect to `φ`. -/
def dPhiC (f : ℝ → ℝ → ℂ) (θ φ : ℝ) : ℂ :=
  deriv (fun p => f θ p) φ

/-- Complex spherical Laplacian operator `∂_θ (sin θ ∂_θ f) + (sin θ)⁻¹ ∂_φ² f`. -/
def lapC (f : ℝ → ℝ → ℂ) (θ φ : ℝ) : ℂ :=
  dThetaC (fun t p => (Real.sin t : ℂ) * dThetaC f t p) θ φ +
    (((Real.sin θ)⁻¹ : ℝ) : ℂ) * dPhiC (dPhiC f) θ φ

private lemma hasDerivAt_thetaC {f : ℝ → ℝ → ℂ} (hf : ContDiff ℝ 2 (Function.uncurry f)) (θ φ : ℝ) :
    HasDerivAt (fun t => f t φ) (dThetaC f θ φ) θ := by
  have hF := hf.differentiable (by decide) (θ, φ)
  have hpair : HasDerivAt (fun t : ℝ => (t, φ)) ((1 : ℝ), (0 : ℝ)) θ :=
    (hasDerivAt_id θ).prodMk (hasDerivAt_const θ φ)
  have h := hF.hasFDerivAt.comp_hasDerivAt θ hpair
  change HasDerivAt (fun t => f t φ) _ θ at h
  rwa [dThetaC, h.deriv]

private lemma hasDerivAt_phiC {f : ℝ → ℝ → ℂ} (hf : ContDiff ℝ 2 (Function.uncurry f)) (θ φ : ℝ) :
    HasDerivAt (fun p => f θ p) (dPhiC f θ φ) φ := by
  have hF := hf.differentiable (by decide) (θ, φ)
  have hpair : HasDerivAt (fun p : ℝ => (θ, p)) ((0 : ℝ), (1 : ℝ)) φ :=
    (hasDerivAt_const φ θ).prodMk (hasDerivAt_id φ)
  have h := hF.hasFDerivAt.comp_hasDerivAt φ hpair
  change HasDerivAt (fun p => f θ p) _ φ at h
  rwa [dPhiC, h.deriv]

private lemma contDiff_dThetaC {f : ℝ → ℝ → ℂ} (hf : ContDiff ℝ 2 (Function.uncurry f)) :
    ContDiff ℝ 1 (Function.uncurry (dThetaC f)) := by
  have h_eq : Function.uncurry (dThetaC f) =
      fun x : ℝ × ℝ => fderiv ℝ (Function.uncurry f) x (1, 0) := by
    ext ⟨t, p⟩
    have hF := hf.differentiable (by decide) (t, p)
    have hpair : HasDerivAt (fun s : ℝ => (s, p)) ((1 : ℝ), (0 : ℝ)) t :=
      (hasDerivAt_id t).prodMk (hasDerivAt_const t p)
    have h := hF.hasFDerivAt.comp_hasDerivAt t hpair
    change HasDerivAt (fun s => f s p) _ t at h
    exact h.deriv
  rw [h_eq]
  exact (hf.fderiv_right (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ 2)).clm_apply contDiff_const

private lemma contDiff_dPhiC {f : ℝ → ℝ → ℂ} (hf : ContDiff ℝ 2 (Function.uncurry f)) :
    ContDiff ℝ 1 (Function.uncurry (dPhiC f)) := by
  have h_eq : Function.uncurry (dPhiC f) =
      fun x : ℝ × ℝ => fderiv ℝ (Function.uncurry f) x (0, 1) := by
    ext ⟨t, p⟩
    have hF := hf.differentiable (by decide) (t, p)
    have hpair : HasDerivAt (fun s : ℝ => (t, s)) ((0 : ℝ), (1 : ℝ)) p :=
      (hasDerivAt_const p t).prodMk (hasDerivAt_id p)
    have h := hF.hasFDerivAt.comp_hasDerivAt p hpair
    change HasDerivAt (fun s => f t s) _ p at h
    exact h.deriv
  rw [h_eq]
  exact (hf.fderiv_right (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ 2)).clm_apply contDiff_const

private lemma hasDerivAt_thetaC_of_c1 {g : ℝ → ℝ → ℂ}
    (hg : ContDiff ℝ 1 (Function.uncurry g)) (θ φ : ℝ) :
    HasDerivAt (fun t => g t φ) (dThetaC g θ φ) θ := by
  have hG := hg.differentiable (by decide) (θ, φ)
  have hpair : HasDerivAt (fun t : ℝ => (t, φ)) ((1 : ℝ), (0 : ℝ)) θ :=
    (hasDerivAt_id θ).prodMk (hasDerivAt_const θ φ)
  have h := hG.hasFDerivAt.comp_hasDerivAt θ hpair
  change HasDerivAt (fun t => g t φ) _ θ at h
  rwa [dThetaC, h.deriv]

private lemma hasDerivAt_phiC_of_c1 {g : ℝ → ℝ → ℂ}
    (hg : ContDiff ℝ 1 (Function.uncurry g)) (θ φ : ℝ) :
    HasDerivAt (fun p => g θ p) (dPhiC g θ φ) φ := by
  have hG := hg.differentiable (by decide) (θ, φ)
  have hpair : HasDerivAt (fun p : ℝ => (θ, p)) ((0 : ℝ), (1 : ℝ)) φ :=
    (hasDerivAt_const φ θ).prodMk (hasDerivAt_id φ)
  have h := hG.hasFDerivAt.comp_hasDerivAt φ hpair
  change HasDerivAt (fun p => g θ p) _ φ at h
  rwa [dPhiC, h.deriv]

private lemma contDiff_ofReal_sin : ContDiff ℝ 2 (fun x : ℝ × ℝ => (Real.sin x.1 : ℂ)) :=
  Complex.ofRealCLM.contDiff.comp (Real.contDiff_sin.comp contDiff_fst)

private lemma hasDerivAt_sin_dThetaC {f : ℝ → ℝ → ℂ}
    (hf : ContDiff ℝ 2 (Function.uncurry f)) (θ φ : ℝ) :
    HasDerivAt (fun t => (Real.sin t : ℂ) * dThetaC f t φ)
      (dThetaC (fun t p => (Real.sin t : ℂ) * dThetaC f t p) θ φ) θ := by
  have hc1 : ContDiff ℝ 1 (Function.uncurry (fun t p => (Real.sin t : ℂ) * dThetaC f t p)) :=
    (contDiff_ofReal_sin.of_le (by norm_num)).mul (contDiff_dThetaC hf)
  exact hasDerivAt_thetaC_of_c1 hc1 θ φ

/-- Real and imaginary parts of `lapC f` equal the real spherical Laplacian of `f.re` and `f.im`. -/
private lemma lapC_re {f : ℝ → ℝ → ℂ} (hf : ContDiff ℝ 2 (Function.uncurry f)) (θ φ : ℝ) :
    (lapC f θ φ).re =
      dTheta (fun t p => Real.sin t * dTheta (fun t' p' => (f t' p').re) t p) θ φ +
        (Real.sin θ)⁻¹ * dPhi (dPhi (fun t' p' => (f t' p').re)) θ φ := by
  have hdt : ∀ t p, dTheta (fun t' p' => (f t' p').re) t p = (dThetaC f t p).re := fun t p => by
    have h := Complex.reCLM.hasFDerivAt.comp_hasDerivAt t (hasDerivAt_thetaC hf t p)
    exact h.deriv
  have hdp : ∀ t p, dPhi (fun t' p' => (f t' p').re) t p = (dPhiC f t p).re := fun t p => by
    have h := Complex.reCLM.hasFDerivAt.comp_hasDerivAt p (hasDerivAt_phiC hf t p)
    exact h.deriv
  have h1 : dTheta (fun t p => Real.sin t * dTheta (fun t' p' => (f t' p').re) t p) θ φ =
      (dThetaC (fun t p => (Real.sin t : ℂ) * dThetaC f t p) θ φ).re := by
    have heq : (fun t => Real.sin t * dTheta (fun t' p' => (f t' p').re) t φ) =
        (fun t => Complex.reCLM ((Real.sin t : ℂ) * dThetaC f t φ)) := by
      funext t; rw [hdt]
      simp only [Complex.reCLM_apply, mul_re, ofReal_re, ofReal_im, zero_mul, sub_zero]
    rw [dTheta, heq]
    exact (Complex.reCLM.hasFDerivAt.comp_hasDerivAt θ (hasDerivAt_sin_dThetaC hf θ φ)).deriv
  have h2 : dPhi (dPhi (fun t' p' => (f t' p').re)) θ φ = (dPhiC (dPhiC f) θ φ).re := by
    have heq : (fun p => dPhi (fun t' p' => (f t' p').re) θ p) =
        (fun p => Complex.reCLM (dPhiC f θ p)) := by
      funext p; exact hdp θ p
    rw [dPhi, heq]
    exact (Complex.reCLM.hasFDerivAt.comp_hasDerivAt φ
      (hasDerivAt_phiC_of_c1 (contDiff_dPhiC hf) θ φ)).deriv
  rw [h1, h2]
  simp only [lapC, add_re, mul_re, ofReal_re, ofReal_im, zero_mul, sub_zero]

private lemma lapC_im {f : ℝ → ℝ → ℂ} (hf : ContDiff ℝ 2 (Function.uncurry f)) (θ φ : ℝ) :
    (lapC f θ φ).im =
      dTheta (fun t p => Real.sin t * dTheta (fun t' p' => (f t' p').im) t p) θ φ +
        (Real.sin θ)⁻¹ * dPhi (dPhi (fun t' p' => (f t' p').im)) θ φ := by
  have hdt : ∀ t p, dTheta (fun t' p' => (f t' p').im) t p = (dThetaC f t p).im := fun t p => by
    have h := Complex.imCLM.hasFDerivAt.comp_hasDerivAt t (hasDerivAt_thetaC hf t p)
    exact h.deriv
  have hdp : ∀ t p, dPhi (fun t' p' => (f t' p').im) t p = (dPhiC f t p).im := fun t p => by
    have h := Complex.imCLM.hasFDerivAt.comp_hasDerivAt p (hasDerivAt_phiC hf t p)
    exact h.deriv
  have h1 : dTheta (fun t p => Real.sin t * dTheta (fun t' p' => (f t' p').im) t p) θ φ =
      (dThetaC (fun t p => (Real.sin t : ℂ) * dThetaC f t p) θ φ).im := by
    have heq : (fun t => Real.sin t * dTheta (fun t' p' => (f t' p').im) t φ) =
        (fun t => Complex.imCLM ((Real.sin t : ℂ) * dThetaC f t φ)) := by
      funext t; rw [hdt]
      simp only [Complex.imCLM_apply, mul_im, ofReal_re, ofReal_im, zero_mul, add_zero]
    rw [dTheta, heq]
    exact (Complex.imCLM.hasFDerivAt.comp_hasDerivAt θ (hasDerivAt_sin_dThetaC hf θ φ)).deriv
  have h2 : dPhi (dPhi (fun t' p' => (f t' p').im)) θ φ = (dPhiC (dPhiC f) θ φ).im := by
    have heq : (fun p => dPhi (fun t' p' => (f t' p').im) θ p) =
        (fun p => Complex.imCLM (dPhiC f θ p)) := by
      funext p; exact hdp θ p
    rw [dPhi, heq]
    exact (Complex.imCLM.hasFDerivAt.comp_hasDerivAt φ
      (hasDerivAt_phiC_of_c1 (contDiff_dPhiC hf) θ φ)).deriv
  rw [h1, h2]
  simp only [lapC, add_im, mul_im, ofReal_re, ofReal_im, zero_mul, add_zero]

/-- `ℂ`-linearity of `lapC` over finite sums of `C²` functions. -/
private lemma lapC_finset_sum {ι : Type*} (S : Finset ι) (c : ι → ℂ) (f : ι → ℝ → ℝ → ℂ)
    (hf : ∀ i ∈ S, ContDiff ℝ 2 (Function.uncurry (f i))) (θ φ : ℝ) :
    lapC (fun t p => ∑ i ∈ S, c i * f i t p) θ φ = ∑ i ∈ S, c i * lapC (f i) θ φ := by
  have hdt_sum : ∀ t p, dThetaC (fun t' p' => ∑ i ∈ S, c i * f i t' p') t p =
      ∑ i ∈ S, c i * dThetaC (f i) t p := by
    intro t p
    have h := HasDerivAt.sum fun i hi => (hasDerivAt_thetaC (hf i hi) t p).const_mul (c i)
    have hfun : (∑ i ∈ S, fun y => c i * f i y p) = (fun s => ∑ i ∈ S, c i * f i s p) := by
      funext s; simp [Finset.sum_apply]
    rw [hfun] at h
    exact h.deriv
  have hdp_sum : ∀ t p, dPhiC (fun t' p' => ∑ i ∈ S, c i * f i t' p') t p =
      ∑ i ∈ S, c i * dPhiC (f i) t p := by
    intro t p
    have h := HasDerivAt.sum fun i hi => (hasDerivAt_phiC (hf i hi) t p).const_mul (c i)
    have hfun : (∑ i ∈ S, fun y => c i * f i t y) = (fun q => ∑ i ∈ S, c i * f i t q) := by
      funext q; simp [Finset.sum_apply]
    rw [hfun] at h
    exact h.deriv
  have h1 : dThetaC (fun t p => (Real.sin t : ℂ) * dThetaC (fun t' p' => ∑ i ∈ S, c i * f i t' p') t p) θ φ =
      ∑ i ∈ S, c i * dThetaC (fun t p => (Real.sin t : ℂ) * dThetaC (f i) t p) θ φ := by
    have heq : (fun t => (Real.sin t : ℂ) * dThetaC (fun t' p' => ∑ i ∈ S, c i * f i t' p') t φ) =
        (∑ i ∈ S, fun t => c i * ((Real.sin t : ℂ) * dThetaC (f i) t φ)) := by
      funext t; rw [hdt_sum, Finset.mul_sum, Finset.sum_apply]
      apply Finset.sum_congr rfl; intro i _; ring
    rw [dThetaC, heq]
    exact (HasDerivAt.sum fun i hi => (hasDerivAt_sin_dThetaC (hf i hi) θ φ).const_mul (c i)).deriv
  have h2 : dPhiC (dPhiC (fun t' p' => ∑ i ∈ S, c i * f i t' p')) θ φ =
      ∑ i ∈ S, c i * dPhiC (dPhiC (f i)) θ φ := by
    have heq : (fun p => dPhiC (fun t' p' => ∑ i ∈ S, c i * f i t' p') θ p) =
        (∑ i ∈ S, fun p => c i * dPhiC (f i) θ p) := by
      funext p; rw [hdp_sum, Finset.sum_apply]
    rw [dPhiC, heq]
    exact (HasDerivAt.sum fun i hi =>
      (hasDerivAt_phiC_of_c1 (contDiff_dPhiC (hf i hi)) θ φ).const_mul (c i)).deriv
  simp only [lapC, h1, h2, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-! ### Isotropic Harmonic Polynomial Generators `Qx, Qy, Qz` and Spherical Harmonics `Qcoeff` -/

def Qx : Polynomial ℂ := C (1 / 2 : ℂ) * (X ^ 2 - 1)
def Qy : Polynomial ℂ := C (-I / 2 : ℂ) * (X ^ 2 + 1)
def Qz : Polynomial ℂ := X

def Qpoly (θ φ : ℝ) : Polynomial ℂ :=
  C ((Real.sin θ * Real.cos φ : ℝ) : ℂ) * Qx +
  C ((Real.sin θ * Real.sin φ : ℝ) : ℂ) * Qy +
  C ((Real.cos θ : ℝ) : ℂ) * Qz

def Qcoeff (j s : ℕ) (θ φ : ℝ) : ℂ :=
  (Qpoly θ φ ^ j).coeff s

private lemma Qpoly_natDegree_le (θ φ : ℝ) : (Qpoly θ φ).natDegree ≤ 2 := by
  have hdeg_C_mul : ∀ (c : ℂ) (P : Polynomial ℂ), P.natDegree ≤ 2 → (C c * P).natDegree ≤ 2 := by
    intro c P hP
    calc (C c * P).natDegree ≤ (C c).natDegree + P.natDegree := natDegree_mul_le
      _ ≤ 0 + 2 := by simp [hP]
      _ = 2 := by norm_num
  have hQx : Qx.natDegree ≤ 2 := by
    apply hdeg_C_mul
    calc (X ^ 2 - 1 : Polynomial ℂ).natDegree
        ≤ max (X ^ 2 : Polynomial ℂ).natDegree (1 : Polynomial ℂ).natDegree := natDegree_sub_le _ _
      _ ≤ 2 := by simp
  have hQy : Qy.natDegree ≤ 2 := by
    apply hdeg_C_mul
    calc (X ^ 2 + 1 : Polynomial ℂ).natDegree
        ≤ max (X ^ 2 : Polynomial ℂ).natDegree (1 : Polynomial ℂ).natDegree := natDegree_add_le _ _
      _ ≤ 2 := by simp
  have hQz : Qz.natDegree ≤ 2 := by simp [Qz]
  calc (Qpoly θ φ).natDegree
      ≤ max (C ((Real.sin θ * Real.cos φ : ℝ) : ℂ) * Qx +
             C ((Real.sin θ * Real.sin φ : ℝ) : ℂ) * Qy).natDegree
            (C ((Real.cos θ : ℝ) : ℂ) * Qz).natDegree := natDegree_add_le _ _
    _ ≤ max (max (C ((Real.sin θ * Real.cos φ : ℝ) : ℂ) * Qx).natDegree
                 (C ((Real.sin θ * Real.sin φ : ℝ) : ℂ) * Qy).natDegree)
            (C ((Real.cos θ : ℝ) : ℂ) * Qz).natDegree :=
        max_le_max (natDegree_add_le _ _) le_rfl
    _ ≤ 2 := by
        exact max_le (max_le (hdeg_C_mul _ _ hQx) (hdeg_C_mul _ _ hQy)) (hdeg_C_mul _ _ hQz)

private lemma Qpoly_pow_natDegree_le (j : ℕ) (θ φ : ℝ) : (Qpoly θ φ ^ j).natDegree ≤ 2 * j := by
  calc (Qpoly θ φ ^ j).natDegree
      ≤ j * (Qpoly θ φ).natDegree := natDegree_pow_le
    _ ≤ j * 2 := Nat.mul_le_mul_left j (Qpoly_natDegree_le θ φ)
    _ = 2 * j := mul_comm j 2

private lemma contDiff_Qpoly_coeff (k : ℕ) :
    ContDiff ℝ 2 (fun x : ℝ × ℝ => (Qpoly x.1 x.2).coeff k) := by
  have hcoeff : ∀ x : ℝ × ℝ, (Qpoly x.1 x.2).coeff k =
      ((Real.sin x.1 * Real.cos x.2 : ℝ) : ℂ) * Qx.coeff k +
      ((Real.sin x.1 * Real.sin x.2 : ℝ) : ℂ) * Qy.coeff k +
      ((Real.cos x.1 : ℝ) : ℂ) * Qz.coeff k := by
    intro x
    simp only [Qpoly, coeff_add, coeff_C_mul]
  simp_rw [hcoeff]
  have h1 : ContDiff ℝ 2 (fun x : ℝ × ℝ => ((Real.sin x.1 * Real.cos x.2 : ℝ) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp
      ((Real.contDiff_sin.comp contDiff_fst).mul (Real.contDiff_cos.comp contDiff_snd))
  have h2 : ContDiff ℝ 2 (fun x : ℝ × ℝ => ((Real.sin x.1 * Real.sin x.2 : ℝ) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp
      ((Real.contDiff_sin.comp contDiff_fst).mul (Real.contDiff_sin.comp contDiff_snd))
  have h3 : ContDiff ℝ 2 (fun x : ℝ × ℝ => ((Real.cos x.1 : ℝ) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp (Real.contDiff_cos.comp contDiff_fst)
  exact ((h1.mul contDiff_const).add (h2.mul contDiff_const)).add (h3.mul contDiff_const)

private lemma contDiff_Qcoeff (j s : ℕ) :
    ContDiff ℝ 2 (Function.uncurry (Qcoeff j s)) := by
  induction j generalizing s with
  | zero =>
    have : Function.uncurry (Qcoeff 0 s) = fun _ => (1 : Polynomial ℂ).coeff s := by
      ext ⟨θ, φ⟩; simp [Qcoeff]
    rw [this]; exact contDiff_const
  | succ j ih =>
    have hmul : Function.uncurry (Qcoeff (j + 1) s) =
        fun x : ℝ × ℝ => ∑ p ∈ Finset.antidiagonal s,
          (Qpoly x.1 x.2).coeff p.1 * Function.uncurry (Qcoeff j p.2) x := by
      ext ⟨θ, φ⟩
      simp only [Function.uncurry, Qcoeff, pow_succ', coeff_mul]
    rw [hmul]
    exact ContDiff.sum fun p _ => (contDiff_Qpoly_coeff p.1).mul (ih p.2)

private lemma Qpoly_per (θ φ : ℝ) : Qpoly θ (φ + 2 * Real.pi) = Qpoly θ φ := by
  simp [Qpoly, Real.sin_add_two_pi, Real.cos_add_two_pi]

private lemma Qpoly_pole (φ : ℝ) : Qpoly 0 φ = Qpoly 0 0 := by
  simp [Qpoly]

/-- Core scalar calculus identity: for every fixed `z : ℂ`, `L(θ, φ)^j = (Qpoly θ φ ^ j).eval z`
satisfies `lapC (L^j) = -j(j+1) sin θ · L^j` on `(0, π) × ℝ`. -/
private lemma lapC_eval_Qpoly_pow (j : ℕ) (z : ℂ) (θ : ℝ) (hθ : θ ∈ Set.Ioo (0 : ℝ) Real.pi) (φ : ℝ) :
    lapC (fun t p => (Qpoly t p ^ j).eval z) θ φ =
      -((j * (j + 1) : ℕ) : ℂ) * (Real.sin θ : ℂ) * (Qpoly θ φ ^ j).eval z := by
  set qx : ℂ := (z ^ 2 - 1) / 2
  set qy : ℂ := -I * (z ^ 2 + 1) / 2
  set qz : ℂ := z
  have hiso : qx ^ 2 + qy ^ 2 + qz ^ 2 = 0 := by
    simp only [qx, qy, qz]
    have hcalc : ((z ^ 2 - 1) / 2) ^ 2 + (-I * (z ^ 2 + 1) / 2) ^ 2 + z ^ 2 =
        ((z ^ 2 - 1) ^ 2 + I ^ 2 * (z ^ 2 + 1) ^ 2 + 4 * z ^ 2) / 4 := by ring
    rw [hcalc, I_sq]; ring
  let L : ℝ → ℝ → ℂ := fun t p =>
    ((Real.sin t * Real.cos p : ℝ) : ℂ) * qx + ((Real.sin t * Real.sin p : ℝ) : ℂ) * qy +
    ((Real.cos t : ℝ) : ℂ) * qz
  let Lt : ℝ → ℝ → ℂ := fun t p =>
    ((Real.cos t * Real.cos p : ℝ) : ℂ) * qx + ((Real.cos t * Real.sin p : ℝ) : ℂ) * qy -
    ((Real.sin t : ℝ) : ℂ) * qz
  let Lp : ℝ → ℝ → ℂ := fun t p =>
    ((-Real.sin t * Real.sin p : ℝ) : ℂ) * qx + ((Real.sin t * Real.cos p : ℝ) : ℂ) * qy
  have hLeval : ∀ t p, (Qpoly t p ^ j).eval z = L t p ^ j := by
    intro t p
    rw [eval_pow]
    congr 1
    simp only [Qpoly, Qx, Qy, Qz, L, qx, qy, qz, eval_add, eval_mul, eval_sub, eval_pow,
      eval_C, eval_X, eval_one]
    ring
  have hLeval_fun : (fun t p => (Qpoly t p ^ j).eval z) = fun t p => L t p ^ j := by
    funext t p; exact hLeval t p
  rw [hLeval_fun, hLeval]
  -- Derivatives of `L`, `Lt`, `Lp`
  have hcos_d : ∀ t : ℝ, HasDerivAt (fun s : ℝ => (Real.cos s : ℂ)) (-(Real.sin t : ℂ)) t := fun t => by
    have h := Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt t (Real.hasDerivAt_cos t)
    change HasDerivAt (fun s : ℝ => (Real.cos s : ℂ)) (((-Real.sin t) : ℝ) : ℂ) t at h
    rwa [ofReal_neg] at h
  have hsin_d : ∀ t : ℝ, HasDerivAt (fun s : ℝ => (Real.sin s : ℂ)) (Real.cos t : ℂ) t := fun t =>
    Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt t (Real.hasDerivAt_sin t)
  have hLt : ∀ t p, HasDerivAt (fun s => L s p) (Lt t p) t := by
    intro t p
    have h1 := ((hsin_d t).mul_const ((Real.cos p : ℂ) * qx))
    have h2 := ((hsin_d t).mul_const ((Real.sin p : ℂ) * qy))
    have h3 := ((hcos_d t).mul_const qz)
    have hsum := (h1.add h2).add h3
    change HasDerivAt (fun s => (Real.sin s : ℂ) * ((Real.cos p : ℂ) * qx) +
        (Real.sin s : ℂ) * ((Real.sin p : ℂ) * qy) + (Real.cos s : ℂ) * qz) _ t at hsum
    have heq : (fun s => (Real.sin s : ℂ) * ((Real.cos p : ℂ) * qx) +
        (Real.sin s : ℂ) * ((Real.sin p : ℂ) * qy) + (Real.cos s : ℂ) * qz) = fun s => L s p := by
      funext s; simp only [L, ofReal_mul]; ring
    rw [heq] at hsum
    have hval : (Real.cos t : ℂ) * ((Real.cos p : ℂ) * qx) +
        (Real.cos t : ℂ) * ((Real.sin p : ℂ) * qy) + -(Real.sin t : ℂ) * qz = Lt t p := by
      simp only [Lt, ofReal_mul]; ring
    rwa [hval] at hsum
  have hLp : ∀ t p, HasDerivAt (fun q => L t q) (Lp t p) p := by
    intro t p
    have h1 := ((hcos_d p).const_mul ((Real.sin t : ℂ) * qx))
    have h2 := ((hsin_d p).const_mul ((Real.sin t : ℂ) * qy))
    have h3 := hasDerivAt_const p ((Real.cos t : ℂ) * qz)
    have hsum := (h1.add h2).add h3
    change HasDerivAt (fun q => (Real.sin t : ℂ) * qx * (Real.cos q : ℂ) +
        (Real.sin t : ℂ) * qy * (Real.sin q : ℂ) + (Real.cos t : ℂ) * qz) _ p at hsum
    have heq : (fun q => (Real.sin t : ℂ) * qx * (Real.cos q : ℂ) +
        (Real.sin t : ℂ) * qy * (Real.sin q : ℂ) + (Real.cos t : ℂ) * qz) = fun q => L t q := by
      funext q; simp only [L, ofReal_mul]; ring
    rw [heq] at hsum
    have hval : (Real.sin t : ℂ) * qx * -(Real.sin p : ℂ) +
        (Real.sin t : ℂ) * qy * (Real.cos p : ℂ) + 0 = Lp t p := by
      simp only [Lp, ofReal_mul, ofReal_neg]; ring
    rwa [hval] at hsum
  have hLtt : ∀ t p, HasDerivAt (fun s => Lt s p) (-L t p) t := by
    intro t p
    have h1 := ((hcos_d t).mul_const ((Real.cos p : ℂ) * qx))
    have h2 := ((hcos_d t).mul_const ((Real.sin p : ℂ) * qy))
    have h3 := ((hsin_d t).mul_const qz)
    have hsub := (h1.add h2).sub h3
    change HasDerivAt (fun s => (Real.cos s : ℂ) * ((Real.cos p : ℂ) * qx) +
        (Real.cos s : ℂ) * ((Real.sin p : ℂ) * qy) - (Real.sin s : ℂ) * qz) _ t at hsub
    have heq : (fun s => (Real.cos s : ℂ) * ((Real.cos p : ℂ) * qx) +
        (Real.cos s : ℂ) * ((Real.sin p : ℂ) * qy) - (Real.sin s : ℂ) * qz) = fun s => Lt s p := by
      funext s; simp only [Lt, ofReal_mul]; ring
    rw [heq] at hsub
    have hval : -(Real.sin t : ℂ) * ((Real.cos p : ℂ) * qx) +
        -(Real.sin t : ℂ) * ((Real.sin p : ℂ) * qy) - (Real.cos t : ℂ) * qz = -L t p := by
      simp only [L, ofReal_mul]; ring
    rwa [hval] at hsub
  have hLpp : ∀ t p, HasDerivAt (fun q => Lp t q)
      (-((Real.sin t * Real.cos p : ℝ) : ℂ) * qx - ((Real.sin t * Real.sin p : ℝ) : ℂ) * qy) p := by
    intro t p
    have h1 := ((hsin_d p).const_mul (-(Real.sin t : ℂ) * qx))
    have h2 := ((hcos_d p).const_mul ((Real.sin t : ℂ) * qy))
    have hadd := h1.add h2
    change HasDerivAt (fun q => -(Real.sin t : ℂ) * qx * (Real.sin q : ℂ) +
        (Real.sin t : ℂ) * qy * (Real.cos q : ℂ)) _ p at hadd
    have heq : (fun q => -(Real.sin t : ℂ) * qx * (Real.sin q : ℂ) +
        (Real.sin t : ℂ) * qy * (Real.cos q : ℂ)) = fun q => Lp t q := by
      funext q; simp only [Lp, ofReal_mul, ofReal_neg]; ring
    rw [heq] at hadd
    have hval : -(Real.sin t : ℂ) * qx * (Real.cos p : ℂ) +
        (Real.sin t : ℂ) * qy * -(Real.sin p : ℂ) =
        -((Real.sin t * Real.cos p : ℝ) : ℂ) * qx - ((Real.sin t * Real.sin p : ℝ) : ℂ) * qy := by
      simp only [ofReal_mul]; ring
    rwa [hval] at hadd
  -- Two exact trigonometric / isotropic identities at `(θ, φ)`!
  have hs_ne : (Real.sin θ : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sin_pos_of_pos_of_lt_pi hθ.1 hθ.2).ne'
  have hcs_t : (Real.cos θ : ℂ) ^ 2 + (Real.sin θ : ℂ) ^ 2 = 1 := by
    exact_mod_cast Real.cos_sq_add_sin_sq θ
  have hcs_p : (Real.cos φ : ℂ) ^ 2 + (Real.sin φ : ℂ) ^ 2 = 1 := by
    exact_mod_cast Real.cos_sq_add_sin_sq φ
  have hid1 : ((Real.cos θ : ℂ) * Lt θ φ + (Real.sin θ : ℂ) * (-L θ φ)) +
      (((Real.sin θ)⁻¹ : ℝ) : ℂ) * (-((Real.sin θ * Real.cos φ : ℝ) : ℂ) * qx -
        ((Real.sin θ * Real.sin φ : ℝ) : ℂ) * qy) = -2 * (Real.sin θ : ℂ) * L θ φ := by
    simp only [L, Lt, ofReal_mul, ofReal_inv]
    field_simp [hs_ne]
    linear_combination ((Real.cos φ : ℂ) * qx + (Real.sin φ : ℂ) * qy) * hcs_t
  have hid2 : (Real.sin θ : ℂ) * Lt θ φ ^ 2 + (((Real.sin θ)⁻¹ : ℝ) : ℂ) * Lp θ φ ^ 2 =
      -(Real.sin θ : ℂ) * L θ φ ^ 2 := by
    let U : ℂ := (Real.cos φ : ℂ) * qx + (Real.sin φ : ℂ) * qy
    let V : ℂ := -(Real.sin φ : ℂ) * qx + (Real.cos φ : ℂ) * qy
    have hL_eq : L θ φ = (Real.sin θ : ℂ) * U + (Real.cos θ : ℂ) * qz := by
      simp only [L, U, ofReal_mul]; ring
    have hLt_eq : Lt θ φ = (Real.cos θ : ℂ) * U - (Real.sin θ : ℂ) * qz := by
      simp only [Lt, U, ofReal_mul]; ring
    have hLp_eq : Lp θ φ = (Real.sin θ : ℂ) * V := by
      simp only [Lp, V, ofReal_mul, ofReal_neg]; ring
    have hL_Lt : L θ φ ^ 2 + Lt θ φ ^ 2 = U ^ 2 + qz ^ 2 := by
      rw [hL_eq, hLt_eq]
      linear_combination (U ^ 2 + qz ^ 2) * hcs_t
    have hU_V : U ^ 2 + V ^ 2 = qx ^ 2 + qy ^ 2 := by
      simp only [U, V]
      linear_combination (qx ^ 2 + qy ^ 2) * hcs_p
    rw [ofReal_inv, hLp_eq]
    have hterm : (Real.sin θ : ℂ)⁻¹ * ((Real.sin θ : ℂ) * V) ^ 2 = (Real.sin θ : ℂ) * V ^ 2 := by
      field_simp [hs_ne]
    rw [hterm]
    linear_combination (Real.sin θ : ℂ) * hL_Lt + (Real.sin θ : ℂ) * hU_V +
      (Real.sin θ : ℂ) * hiso
  -- Case split `j = 0`, `j = 1`, `j = k + 2`!
  cases j with
  | zero =>
    simp [lapC, dThetaC, dPhiC]
  | succ j' =>
    cases j' with
    | zero =>
      have hpow1 : (fun t p => L t p ^ (0 + 1)) = L := by funext t p; simp
      rw [hpow1]
      simp only [Nat.zero_add, pow_one]
      have h1 : ∀ t, dThetaC L t φ = Lt t φ := fun t => (hLt t φ).deriv
      have h2 : ∀ p, dPhiC L θ p = Lp θ p := fun p => (hLp θ p).deriv
      have hd1 : dThetaC (fun t p => (Real.sin t : ℂ) * dThetaC L t p) θ φ =
          (Real.cos θ : ℂ) * Lt θ φ + (Real.sin θ : ℂ) * (-L θ φ) := by
        have heq : (fun t => (Real.sin t : ℂ) * dThetaC L t φ) = fun t => (Real.sin t : ℂ) * Lt t φ := by
          funext t; rw [h1]
        rw [dThetaC, heq]
        exact ((hsin_d θ).mul (hLtt θ φ)).deriv
      have hd2 : dPhiC (dPhiC L) θ φ =
          -((Real.sin θ * Real.cos φ : ℝ) : ℂ) * qx - ((Real.sin θ * Real.sin φ : ℝ) : ℂ) * qy := by
        have heq : (fun p => dPhiC L θ p) = fun p => Lp θ p := funext h2
        rw [dPhiC, heq]
        exact (hLpp θ φ).deriv
      simp only [lapC, hd1, hd2]
      rw [hid1]
      push_cast; ring
    | succ k =>
      let n : ℕ := k + 2
      have hdt_pow : ∀ t p, dThetaC (fun s q => L s q ^ n) t p =
          (n : ℂ) * L t p ^ (k + 1) * Lt t p := by
        intro t p
        exact ((hLt t p).pow n).deriv
      have hdp_pow : ∀ t p, dPhiC (fun s q => L s q ^ n) t p =
          (n : ℂ) * L t p ^ (k + 1) * Lp t p := by
        intro t p
        exact ((hLp t p).pow n).deriv
      have hd1 : dThetaC (fun t p => (Real.sin t : ℂ) * dThetaC (fun s q => L s q ^ n) t p) θ φ =
          (n : ℂ) * ((k + 1 : ℕ) : ℂ) * (Real.sin θ : ℂ) * L θ φ ^ k * Lt θ φ ^ 2 +
          (n : ℂ) * L θ φ ^ (k + 1) * ((Real.cos θ : ℂ) * Lt θ φ + (Real.sin θ : ℂ) * (-L θ φ)) := by
        have heq : (fun t => (Real.sin t : ℂ) * dThetaC (fun s q => L s q ^ n) t φ) =
            fun t => ((n : ℂ) * L t φ ^ (k + 1)) * ((Real.sin t : ℂ) * Lt t φ) := by
          funext t; rw [hdt_pow]; ring
        rw [dThetaC, heq]
        have hA : HasDerivAt (fun t => (n : ℂ) * L t φ ^ (k + 1))
            ((n : ℂ) * (((k + 1 : ℕ) : ℂ) * L θ φ ^ k * Lt θ φ)) θ :=
          ((hLt θ φ).pow (k + 1)).const_mul (n : ℂ)
        have hB : HasDerivAt (fun t => (Real.sin t : ℂ) * Lt t φ)
            ((Real.cos θ : ℂ) * Lt θ φ + (Real.sin θ : ℂ) * (-L θ φ)) θ :=
          (hsin_d θ).mul (hLtt θ φ)
        have hmul := hA.mul hB
        change HasDerivAt (fun t => ((n : ℂ) * L t φ ^ (k + 1)) * ((Real.sin t : ℂ) * Lt t φ)) _ θ at hmul
        rw [hmul.deriv]
        ring
      have hd2 : dPhiC (dPhiC (fun s q => L s q ^ n)) θ φ =
          (n : ℂ) * ((k + 1 : ℕ) : ℂ) * L θ φ ^ k * Lp θ φ ^ 2 +
          (n : ℂ) * L θ φ ^ (k + 1) *
            (-((Real.sin θ * Real.cos φ : ℝ) : ℂ) * qx - ((Real.sin θ * Real.sin φ : ℝ) : ℂ) * qy) := by
        have heq : (fun p => dPhiC (fun s q => L s q ^ n) θ p) =
            fun p => ((n : ℂ) * L θ p ^ (k + 1)) * Lp θ p := by
          funext p; rw [hdp_pow]
        rw [dPhiC, heq]
        have hA : HasDerivAt (fun p => (n : ℂ) * L θ p ^ (k + 1))
            ((n : ℂ) * (((k + 1 : ℕ) : ℂ) * L θ φ ^ k * Lp θ φ)) φ :=
          ((hLp θ φ).pow (k + 1)).const_mul (n : ℂ)
        have hmul := hA.mul (hLpp θ φ)
        change HasDerivAt (fun p => ((n : ℂ) * L θ p ^ (k + 1)) * Lp θ p) _ φ at hmul
        rw [hmul.deriv]
        ring
      change lapC (fun t p => L t p ^ n) θ φ = -((n * (n + 1) : ℕ) : ℂ) * (Real.sin θ : ℂ) * L θ φ ^ n
      simp only [lapC, hd1, hd2]
      have hpow1 : L θ φ ^ n = L θ φ ^ (k + 1) * L θ φ := by
        simp only [n, pow_succ]
      have hpow2 : L θ φ ^ n = L θ φ ^ k * L θ φ ^ 2 := by
        simp only [n, pow_add]
      have hn_cast : ((n * (n + 1) : ℕ) : ℂ) = (n : ℂ) * ((k + 1 : ℕ) : ℂ) + 2 * (n : ℂ) := by
        simp only [n]; push_cast; ring
      rw [hn_cast]
      linear_combination (n : ℂ) * ((k + 1 : ℕ) : ℂ) * L θ φ ^ k * hid2 +
        (n : ℂ) * L θ φ ^ (k + 1) * hid1 +
        ((n : ℂ) * ((k + 1 : ℕ) : ℂ) * (Real.sin θ : ℂ)) * hpow2 +
        (2 * (n : ℂ) * (Real.sin θ : ℂ)) * hpow1

/-- Therefore EVERY basis coefficient `Qcoeff j s` is a spherical harmonic of degree `j`! -/
private lemma lapC_Qcoeff (j s : ℕ) (hs : s < 2 * j + 1)
    (θ : ℝ) (hθ : θ ∈ Set.Ioo (0 : ℝ) Real.pi) (φ : ℝ) :
    lapC (Qcoeff j s) θ φ = -((j * (j + 1) : ℕ) : ℂ) * (Real.sin θ : ℂ) * Qcoeff j s θ φ := by
  let R : Polynomial ℂ :=
    ∑ i ∈ range (2 * j + 1),
      C (lapC (Qcoeff j i) θ φ + ((j * (j + 1) : ℕ) : ℂ) * (Real.sin θ : ℂ) * Qcoeff j i θ φ) * X ^ i
  have hR_eval : ∀ z : ℂ, R.eval z = 0 := by
    intro z
    have hsum_eq : (fun t p => (Qpoly t p ^ j).eval z) =
        fun t p => ∑ i ∈ range (2 * j + 1), z ^ i * Qcoeff j i t p := by
      funext t p
      rw [Polynomial.eval_eq_sum_range' (Nat.lt_succ_of_le (Qpoly_pow_natDegree_le j t p))]
      apply Finset.sum_congr rfl; intro i _; simp only [Qcoeff]; ring
    have hlap := lapC_eval_Qpoly_pow j z θ hθ φ
    have hsum_val : (Qpoly θ φ ^ j).eval z = ∑ i ∈ range (2 * j + 1), z ^ i * Qcoeff j i θ φ :=
      congrFun (congrFun hsum_eq θ) φ
    rw [hsum_eq, lapC_finset_sum (range (2 * j + 1)) (fun i => z ^ i) (fun i => Qcoeff j i)
      (fun i _ => contDiff_Qcoeff j i) θ φ, hsum_val] at hlap
    have hR_val : R.eval z =
        ∑ i ∈ range (2 * j + 1),
          (lapC (Qcoeff j i) θ φ + ((j * (j + 1) : ℕ) : ℂ) * (Real.sin θ : ℂ) * Qcoeff j i θ φ) * z ^ i := by
      have hmap : R.eval z = (Polynomial.evalRingHom z) R := rfl
      rw [hmap, map_sum]
      apply Finset.sum_congr rfl; intro i _
      simp only [Polynomial.coe_evalRingHom, eval_mul, eval_C, eval_pow, eval_X]
    rw [hR_val]
    have hsplit :
        ∑ i ∈ range (2 * j + 1),
          (lapC (Qcoeff j i) θ φ + ((j * (j + 1) : ℕ) : ℂ) * (Real.sin θ : ℂ) * Qcoeff j i θ φ) * z ^ i =
        (∑ i ∈ range (2 * j + 1), z ^ i * lapC (Qcoeff j i) θ φ) +
        ((j * (j + 1) : ℕ) : ℂ) * (Real.sin θ : ℂ) *
          (∑ i ∈ range (2 * j + 1), z ^ i * Qcoeff j i θ φ) := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl; intro i _; ring
    rw [hsplit, hlap]
    ring
  have hR_zero : R = 0 := Polynomial.funext fun z => by rw [hR_eval z, eval_zero]
  have hcoeff_z : R.coeff s = 0 := by rw [hR_zero, coeff_zero]
  have hR_coeff : R.coeff s =
      lapC (Qcoeff j s) θ φ + ((j * (j + 1) : ℕ) : ℂ) * (Real.sin θ : ℂ) * Qcoeff j s θ φ := by
    simp only [R, finsetSum_coeff, coeff_C_mul_X_pow]
    rw [Finset.sum_eq_single s]
    · simp
    · intro i _ hne; simp [Ne.symm hne]
    · intro hnot; exfalso; exact hnot (Finset.mem_range.mpr hs)
  rw [hR_coeff] at hcoeff_z
  linear_combination hcoeff_z

/-! ### Row-`j` Amplitude `Ypsi` Equals a Complex Spherical Harmonic of Degree `j` -/

/-- Middle-row (`m = 0`, index `j`) rotated amplitude
`Y_ψ(θ, φ) = (D^{(j)}((R_z(φ) R_y(θ))⁻¹) ψ)_j`. -/
def Ypsi (j : ℕ) (ψ : Fin (2 * j + 1) → ℂ) (θ φ : ℝ) : ℂ :=
  ((spinRep (2 * j) (SU2.rotZ φ * SU2.rotY θ)⁻¹).mulVec ψ) ⟨j, by omega⟩

/-- Key algebraic identity: row `j` of `polyStep (2*j) (R_z(φ) R_y(θ))⁻¹` equals `Qpoly θ φ ^ j`. -/
lemma polyStep_rot_inv_mid (j : ℕ) (θ φ : ℝ) :
    polyStep (2 * j) (SU2.rotZ φ * SU2.rotY θ)⁻¹ ⟨j, by omega⟩ = Qpoly θ φ ^ j := by
  set g : SU2 := (SU2.rotZ φ * SU2.rotY θ)⁻¹
  have hsub : 2 * j - j = j := by omega
  unfold polyStep
  simp only [hsub, ← mul_pow]
  congr 1
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
  have he2 : e * e = (Real.cos φ : ℂ) - I * (Real.sin φ : ℂ) := by
    have h1 : e * e = Complex.exp (-I * (φ : ℂ)) := by
      simp only [e, ← Complex.exp_add]; congr 1; ring
    rw [h1]
    have h := Complex.exp_mul_I (-φ)
    rw [show (-↑φ : ℂ) * I = -I * ↑φ by ring] at h
    rw [h]
    simp [Complex.cos_neg, Complex.sin_neg, Complex.ofReal_cos, Complex.ofReal_sin]; ring
  have he_star2 : star e * star e = (Real.cos φ : ℂ) + I * (Real.sin φ : ℂ) := by
    have h1 : star e * star e = Complex.exp (I * (φ : ℂ)) := by
      rw [he_star, ← Complex.exp_add]; congr 1; ring
    rw [h1]
    have h := Complex.exp_mul_I (φ : ℂ)
    rw [show (↑φ : ℂ) * I = I * ↑φ by ring] at h
    rw [h]
    simp [Complex.ofReal_cos, Complex.ofReal_sin]; ring
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
  have hga : g.a = star e * c := by
    simp only [g, SU2.inv_a, SU2.mul_a, SU2.rotZ_a, SU2.rotZ_b, SU2.rotY_a, SU2.rotY_b,
      zero_mul, sub_zero, star_mul', RCLike.star_def, conj_ofReal]
    change star e * c = star e * c; rfl
  have hgb : g.b = e * s := by
    simp only [g, SU2.inv_b, SU2.mul_b, SU2.rotZ_a, SU2.rotZ_b, SU2.rotY_a, SU2.rotY_b,
      zero_mul, add_zero]
    change -(e * -s) = e * s; ring
  have hstar_ga : star g.a = e * c := by
    rw [hga, star_mul', star_star]
    simp only [c, RCLike.star_def, conj_ofReal]
  have hstar_gb : star g.b = star e * s := by
    rw [hgb, star_mul']
    simp only [s, RCLike.star_def, conj_ofReal]
  have hc0 : g.a * (-star g.b) =
      -((Real.sin θ * Real.cos φ : ℝ) : ℂ) * (1 / 2 : ℂ) +
      ((Real.sin θ * Real.sin φ : ℝ) : ℂ) * (-I / 2 : ℂ) := by
    rw [hstar_gb, hga]
    have h1 : (star e * c) * -(star e * s) = -(1 / 2 : ℂ) * (2 * s * c) * (star e * star e) := by ring
    rw [h1, hsin, he_star2]
    simp only [ofReal_mul]; ring
  have hc1 : g.a * star g.a + g.b * (-star g.b) = (Real.cos θ : ℂ) := by
    rw [hstar_ga, hstar_gb, hga, hgb]
    linear_combination (c ^ 2 - s ^ 2) * he_mul + hcos
  have hc2 : g.b * star g.a =
      ((Real.sin θ * Real.cos φ : ℝ) : ℂ) * (1 / 2 : ℂ) +
      ((Real.sin θ * Real.sin φ : ℝ) : ℂ) * (-I / 2 : ℂ) := by
    rw [hstar_ga, hgb]
    have h1 : (e * s) * (e * c) = (1 / 2 : ℂ) * (2 * s * c) * (e * e) := by ring
    rw [h1, hsin, he2]
    simp only [ofReal_mul]; ring
  have hLHS : (C g.a + C g.b * X) * (C (-star g.b) + C (star g.a) * X) =
      C (g.a * (-star g.b)) + C (g.a * star g.a + g.b * (-star g.b)) * X +
      C (g.b * star g.a) * X ^ 2 := by
    simp only [map_add, map_mul]; ring
  have hRHS : Qpoly θ φ =
      C (-((Real.sin θ * Real.cos φ : ℝ) : ℂ) * (1 / 2 : ℂ) +
         ((Real.sin θ * Real.sin φ : ℝ) : ℂ) * (-I / 2 : ℂ)) +
      C (Real.cos θ : ℂ) * X +
      C (((Real.sin θ * Real.cos φ : ℝ) : ℂ) * (1 / 2 : ℂ) +
         ((Real.sin θ * Real.sin φ : ℝ) : ℂ) * (-I / 2 : ℂ)) * X ^ 2 := by
    simp only [Qpoly, Qx, Qy, Qz, map_add, map_mul, map_neg]; ring
  rw [hLHS, hRHS, hc0, hc1, hc2]

lemma Ypsi_eq_sum_Qcoeff (j : ℕ) (ψ : Fin (2 * j + 1) → ℂ) (θ φ : ℝ) :
    Ypsi j ψ θ φ = ∑ s : Fin (2 * j + 1),
      (((binomWeight (2 * j) ⟨j, by omega⟩ : ℂ) / (binomWeight (2 * j) s : ℂ)) * ψ s) *
        Qcoeff j s.val θ φ := by
  simp only [Ypsi, Matrix.mulVec, dotProduct, spinRep, rawRep, polyStep_rot_inv_mid, Qcoeff]
  apply Finset.sum_congr rfl; intro s _; ring

/-- **Zeros of `Y_ψ`**: For every integer spin `j ≥ 1` and every state `ψ`, the complex spherical
harmonic `Y_ψ` vanishes at some `(θ_*, φ_*) ∈ [0, π] × [0, 2π]`. -/
theorem Ypsi_has_zero {j : ℕ} (hj : 1 ≤ j) (ψ : Fin (2 * j + 1) → ℂ) :
    ∃ θ ∈ Set.Icc (0 : ℝ) Real.pi, ∃ φ ∈ Set.Icc (0 : ℝ) (2 * Real.pi),
      Ypsi j ψ θ φ = 0 := by
  let c : Fin (2 * j + 1) → ℂ := fun s =>
    ((binomWeight (2 * j) ⟨j, by omega⟩ : ℂ) / (binomWeight (2 * j) s : ℂ)) * ψ s
  have hY_eq : ∀ θ φ, Ypsi j ψ θ φ = ∑ s : Fin (2 * j + 1), c s * Qcoeff j s.val θ φ :=
    fun θ φ => Ypsi_eq_sum_Qcoeff j ψ θ φ
  have hY_c2 : ContDiff ℝ 2 (Function.uncurry (Ypsi j ψ)) := by
    have : Function.uncurry (Ypsi j ψ) =
        fun x : ℝ × ℝ => ∑ s : Fin (2 * j + 1), c s * Function.uncurry (Qcoeff j s.val) x := by
      ext ⟨θ, φ⟩; exact hY_eq θ φ
    rw [this]
    exact ContDiff.sum fun s _ => contDiff_const.mul (contDiff_Qcoeff j s.val)
  have hY_lap : ∀ θ ∈ Set.Ioo (0 : ℝ) Real.pi, ∀ φ : ℝ,
      lapC (Ypsi j ψ) θ φ = -((j * (j + 1) : ℕ) : ℂ) * (Real.sin θ : ℂ) * Ypsi j ψ θ φ := by
    intro θ hθ φ
    have hf_eq : Ypsi j ψ = fun t p => ∑ s : Fin (2 * j + 1), c s * Qcoeff j s.val t p := by
      funext t p; exact hY_eq t p
    rw [hf_eq, lapC_finset_sum Finset.univ c (fun s => Qcoeff j s.val)
      (fun s _ => contDiff_Qcoeff j s.val) θ φ, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro s _
    rw [lapC_Qcoeff j s.val s.isLt θ hθ φ]
    ring
  have hY_per : ∀ θ φ, Ypsi j ψ θ (φ + 2 * Real.pi) = Ypsi j ψ θ φ := by
    intro θ φ; simp only [hY_eq, Qcoeff, Qpoly_per]
  have hY_pole : ∀ φ, Ypsi j ψ 0 φ = Ypsi j ψ 0 0 := by
    intro φ; simp only [hY_eq, Qcoeff, Qpoly_pole]
  let u : ℝ → ℝ → ℝ := fun θ φ => (Ypsi j ψ θ φ).re
  let v : ℝ → ℝ → ℝ := fun θ φ => (Ypsi j ψ θ φ).im
  have hlam : (0 : ℝ) < (j * (j + 1) : ℕ) := by
    have : 0 < j * (j + 1) := by positivity
    exact_mod_cast this
  have hu_c2 : ContDiff ℝ 2 (Function.uncurry u) := Complex.reCLM.contDiff.comp hY_c2
  have hv_c2 : ContDiff ℝ 2 (Function.uncurry v) := Complex.imCLM.contDiff.comp hY_c2
  have hu_lap : ∀ θ ∈ Set.Ioo (0 : ℝ) Real.pi, ∀ φ : ℝ,
      dTheta (fun t p => Real.sin t * dTheta u t p) θ φ +
        (Real.sin θ)⁻¹ * dPhi (dPhi u) θ φ = -((j * (j + 1) : ℕ) : ℝ) * Real.sin θ * u θ φ := by
    intro θ hθ φ
    rw [← lapC_re hY_c2 θ φ, hY_lap θ hθ φ]
    simp only [u, mul_re, mul_im, neg_re, neg_im, ofReal_re, ofReal_im, natCast_re, natCast_im,
      zero_mul, mul_zero, add_zero, sub_zero, neg_zero]
  have hv_lap : ∀ θ ∈ Set.Ioo (0 : ℝ) Real.pi, ∀ φ : ℝ,
      dTheta (fun t p => Real.sin t * dTheta v t p) θ φ +
        (Real.sin θ)⁻¹ * dPhi (dPhi v) θ φ = -((j * (j + 1) : ℕ) : ℝ) * Real.sin θ * v θ φ := by
    intro θ hθ φ
    rw [← lapC_im hY_c2 θ φ, hY_lap θ hθ φ]
    simp only [v, mul_im, mul_re, neg_re, neg_im, ofReal_re, ofReal_im, natCast_re, natCast_im,
      zero_mul, mul_zero, add_zero, sub_zero, neg_zero]
  obtain ⟨θ, hθ, φ, hφ, hu0, hv0⟩ := spherical_harmonic_has_zero hlam hu_c2 hv_c2
    (fun t p => congrArg Complex.re (hY_per t p))
    (fun t p => congrArg Complex.im (hY_per t p))
    (fun p => congrArg Complex.re (hY_pole p))
    (fun p => congrArg Complex.im (hY_pole p))
    hu_lap hv_lap
  exact ⟨θ, hθ, φ, hφ, Complex.ext hu0 hv0⟩

/-! ### Equatorial Integral Identity & Integer-Spin π-Rotation Orthogonality -/

/-- Exact closed form of `spinRep (2 * j)` on equatorial π-rotations `u_eq(φ) = (cos φ, sin φ, 0)`. -/
lemma spinRep_piRot_equator (j : ℕ) (φ : ℝ) (k s : Fin (2 * j + 1)) :
    spinRep (2 * j) (SU2.piRot (SU2.sphVec (Real.pi / 2) φ)) k s =
      if s.val = 2 * j - k.val then
        (-1 : ℂ) ^ j * Complex.exp (I * (2 * ((k.val : ℤ) - (j : ℤ)) : ℂ) * (φ : ℂ))
      else 0 := by
  have hexp_m : (Real.cos φ : ℂ) - I * (Real.sin φ : ℂ) = Complex.exp (-I * (φ : ℂ)) := by
    have h := Complex.exp_mul_I (-φ)
    rw [show (-↑φ : ℂ) * I = -I * ↑φ by ring] at h
    rw [h]
    simp [Complex.cos_neg, Complex.sin_neg, Complex.ofReal_cos, Complex.ofReal_sin]; ring
  have ha0 : (SU2.piRot (SU2.sphVec (Real.pi / 2) φ)).a = 0 := by
    simp [SU2.piRot_a, SU2.sphVec]
  have hb_eq : (SU2.piRot (SU2.sphVec (Real.pi / 2) φ)).b = -I * Complex.exp (-I * (φ : ℂ)) := by
    simp only [SU2.piRot_b, SU2.sphVec, Matrix.cons_val_zero, Matrix.cons_val_one,
      Real.sin_pi_div_two, one_mul, hexp_m]
  have hstar_b : -star (SU2.piRot (SU2.sphVec (Real.pi / 2) φ)).b =
      -I * Complex.exp (I * (φ : ℂ)) := by
    rw [hb_eq]
    simp only [star_mul', star_neg, RCLike.star_def, conj_I, ← Complex.exp_conj,
      map_mul, map_neg, conj_ofReal, neg_neg]
    ring
  have hpoly : polyStep (2 * j) (SU2.piRot (SU2.sphVec (Real.pi / 2) φ)) k =
      C ((-1 : ℂ) ^ j * Complex.exp (I * (2 * ((k.val : ℤ) - (j : ℤ)) : ℂ) * (φ : ℂ))) *
        X ^ (2 * j - k.val) := by
    unfold polyStep
    rw [ha0, hstar_b, hb_eq]
    simp only [map_zero, zero_add, star_zero, zero_mul, add_zero, mul_pow]
    have hcoeff :
        ((-I * Complex.exp (-I * (φ : ℂ))) ^ (2 * j - k.val)) *
          ((-I * Complex.exp (I * (φ : ℂ))) ^ k.val) =
        (-1 : ℂ) ^ j * Complex.exp (I * (2 * ((k.val : ℤ) - (j : ℤ)) : ℂ) * (φ : ℂ)) := by
      rw [mul_pow, mul_pow]
      have hk : (2 * j - k.val) + k.val = 2 * j := Nat.sub_add_cancel (Nat.le_of_lt_succ k.isLt)
      have hIpow : (-I) ^ (2 * j - k.val) * (-I) ^ k.val = (-1 : ℂ) ^ j := by
        rw [← pow_add, hk, pow_mul]
        congr 1; ring_nf; exact I_sq
      have hexp : Complex.exp (-I * (φ : ℂ)) ^ (2 * j - k.val) *
          Complex.exp (I * (φ : ℂ)) ^ k.val =
          Complex.exp (I * (2 * ((k.val : ℤ) - (j : ℤ)) : ℂ) * (φ : ℂ)) := by
        rw [← Complex.exp_nat_mul, ← Complex.exp_nat_mul, ← Complex.exp_add]
        congr 1
        have hle : k.val ≤ 2 * j := Nat.le_of_lt_succ k.isLt
        rw [Nat.cast_sub hle]
        push_cast
        ring
      calc (-I) ^ (2 * j - k.val) * Complex.exp (-I * ↑φ) ^ (2 * j - k.val) *
            ((-I) ^ k.val * Complex.exp (I * ↑φ) ^ k.val)
          = ((-I) ^ (2 * j - k.val) * (-I) ^ k.val) *
            (Complex.exp (-I * ↑φ) ^ (2 * j - k.val) * Complex.exp (I * ↑φ) ^ k.val) := by ring
        _ = _ := by rw [hIpow, hexp]
    rw [← hcoeff]
    simp only [map_mul, map_pow, map_neg]
    ring
  simp only [spinRep, rawRep, hpoly, coeff_C_mul_X_pow]
  split_ifs with h
  · have hwk : binomWeight (2 * j) k = binomWeight (2 * j) s := by
      unfold binomWeight
      rw [h, Nat.choose_symm (Nat.le_of_lt_succ k.isLt)]
    have hne : (binomWeight (2 * j) s : ℂ) ≠ 0 := by
      exact_mod_cast (binomWeight_pos (2 * j) s).ne'
    rw [hwk, div_self hne, one_mul]
  · simp

/-- Fourier orthogonality: `∫_0^{2π} e^{i m φ} dφ = 0` for every nonzero integer `m : ℤ`. -/
lemma integral_exp_int_mul_I (m : ℤ) (hm : m ≠ 0) :
    ∫ φ in (0 : ℝ)..(2 * Real.pi), Complex.exp (I * (m : ℂ) * (φ : ℂ)) = 0 := by
  have hmR : (m : ℝ) ≠ 0 := Int.cast_ne_zero.mpr hm
  have h2pi : Complex.exp ((((m : ℝ) * (2 * Real.pi) : ℝ) : ℂ) * I) = 1 := by
    have : ((((m : ℝ) * (2 * Real.pi) : ℝ) : ℂ) * I) = (m : ℂ) * (2 * Real.pi * I) := by
      push_cast; ring
    rw [this]
    exact Complex.exp_int_mul_two_pi_mul_I m
  have hcos2pi : Real.cos ((m : ℝ) * (2 * Real.pi)) = 1 := by
    have h := congrArg Complex.re h2pi
    rw [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin] at h
    simp only [add_re, mul_re, ofReal_re, ofReal_im, I_re, I_im, mul_zero, mul_one,
      sub_zero, add_zero, one_re] at h
    exact h
  have hsin2pi : Real.sin ((m : ℝ) * (2 * Real.pi)) = 0 := by
    have h := congrArg Complex.im h2pi
    rw [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin] at h
    simp only [add_im, mul_im, ofReal_re, ofReal_im, I_re, I_im, mul_zero, mul_one,
      zero_add, add_zero, one_im] at h
    exact h
  have hcos_int : ∫ φ in (0 : ℝ)..(2 * Real.pi), Real.cos ((m : ℝ) * φ) = 0 := by
    have hd : ∀ φ : ℝ, HasDerivAt (fun t : ℝ => Real.sin ((m : ℝ) * t) / (m : ℝ))
        (Real.cos ((m : ℝ) * φ)) φ := by
      intro φ
      have h1 : HasDerivAt (fun t : ℝ => (m : ℝ) * t) ((m : ℝ) * 1) φ :=
        (hasDerivAt_id φ).const_mul (m : ℝ)
      have h2 := (Real.hasDerivAt_sin ((m : ℝ) * φ)).comp φ h1
      change HasDerivAt (fun t : ℝ => Real.sin ((m : ℝ) * t)) _ φ at h2
      have h3 := h2.div_const (m : ℝ)
      have hval : Real.cos ((m : ℝ) * φ) * ((m : ℝ) * 1) / (m : ℝ) = Real.cos ((m : ℝ) * φ) := by
        field_simp [hmR]
      rwa [hval] at h3
    have hint : IntervalIntegrable (fun φ : ℝ => Real.cos ((m : ℝ) * φ)) volume 0 (2 * Real.pi) :=
      (Continuous.intervalIntegrable (by fun_prop) 0 (2 * Real.pi))
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (a := (0 : ℝ)) (b := 2 * Real.pi)
      (fun φ _ => hd φ) hint, hsin2pi]
    simp
  have hsin_int : ∫ φ in (0 : ℝ)..(2 * Real.pi), Real.sin ((m : ℝ) * φ) = 0 := by
    have hd : ∀ φ : ℝ, HasDerivAt (fun t : ℝ => -(Real.cos ((m : ℝ) * t) / (m : ℝ)))
        (Real.sin ((m : ℝ) * φ)) φ := by
      intro φ
      have h1 : HasDerivAt (fun t : ℝ => (m : ℝ) * t) ((m : ℝ) * 1) φ :=
        (hasDerivAt_id φ).const_mul (m : ℝ)
      have h2 := (Real.hasDerivAt_cos ((m : ℝ) * φ)).comp φ h1
      change HasDerivAt (fun t : ℝ => Real.cos ((m : ℝ) * t)) _ φ at h2
      have h3 := (h2.div_const (m : ℝ)).neg
      have hval : -(-Real.sin ((m : ℝ) * φ) * ((m : ℝ) * 1) / (m : ℝ)) = Real.sin ((m : ℝ) * φ) := by
        field_simp [hmR]
      rwa [hval] at h3
    have hint : IntervalIntegrable (fun φ : ℝ => Real.sin ((m : ℝ) * φ)) volume 0 (2 * Real.pi) :=
      (Continuous.intervalIntegrable (by fun_prop) 0 (2 * Real.pi))
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (a := (0 : ℝ)) (b := 2 * Real.pi)
      (fun φ _ => hd φ) hint, hcos2pi]
    simp
  have hexp_eq : (fun φ : ℝ => Complex.exp (I * (m : ℂ) * (φ : ℂ))) =
      fun φ : ℝ => (Real.cos ((m : ℝ) * φ) : ℂ) + (Real.sin ((m : ℝ) * φ) : ℂ) * I := by
    funext φ
    rw [show I * (m : ℂ) * (φ : ℂ) = (((m : ℝ) * φ : ℝ) : ℂ) * I by push_cast; ring]
    rw [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
  rw [hexp_eq]
  have ic : IntervalIntegrable (fun φ : ℝ => (Real.cos ((m : ℝ) * φ) : ℂ)) volume 0 (2 * Real.pi) :=
    (Continuous.intervalIntegrable (by fun_prop) 0 (2 * Real.pi))
  have is_ : IntervalIntegrable (fun φ : ℝ => (Real.sin ((m : ℝ) * φ) : ℂ) * I) volume 0 (2 * Real.pi) :=
    (Continuous.intervalIntegrable (by fun_prop) 0 (2 * Real.pi))
  rw [intervalIntegral.integral_add ic is_, intervalIntegral.integral_mul_const]
  have h1 := Complex.ofRealCLM.intervalIntegral_comp_comm (μ := volume) (a := (0 : ℝ)) (b := 2 * Real.pi)
    (f := fun φ : ℝ => Real.cos ((m : ℝ) * φ))
    (Continuous.intervalIntegrable (μ := volume) (by fun_prop) 0 (2 * Real.pi))
  have h2 := Complex.ofRealCLM.intervalIntegral_comp_comm (μ := volume) (a := (0 : ℝ)) (b := 2 * Real.pi)
    (f := fun φ : ℝ => Real.sin ((m : ℝ) * φ))
    (Continuous.intervalIntegrable (μ := volume) (by fun_prop) 0 (2 * Real.pi))
  change ∫ φ in (0 : ℝ)..(2 * Real.pi), (Real.cos ((m : ℝ) * φ) : ℂ) =
      ((∫ φ in (0 : ℝ)..(2 * Real.pi), Real.cos ((m : ℝ) * φ) : ℝ) : ℂ) at h1
  change ∫ φ in (0 : ℝ)..(2 * Real.pi), (Real.sin ((m : ℝ) * φ) : ℂ) =
      ((∫ φ in (0 : ℝ)..(2 * Real.pi), Real.sin ((m : ℝ) * φ) : ℝ) : ℂ) at h2
  rw [h1, h2, hcos_int, hsin_int]
  simp

/-- **Equatorial Integral Identity**:
For every integer spin `j`, every state `ψ : Fin (2 * j + 1) → ℂ`, and every spherical axis
`n(θ₀, φ₀)`, integrating the π-rotation matrix element along the equator orthogonal to `n(θ₀, φ₀)`
yields `2π (-1)^j |Y_ψ(θ₀, φ₀)|²`. -/
theorem equatorial_integral_identity (j : ℕ) (ψ : Fin (2 * j + 1) → ℂ) (θ₀ φ₀ : ℝ) :
    ∫ φ in (0 : ℝ)..(2 * Real.pi),
      innerC ψ ((spinRep (2 * j) (SU2.piRot (SU2.actS2 (SU2.rotZ φ₀ * SU2.rotY θ₀)
        (SU2.sphVec (Real.pi / 2) φ)))).mulVec ψ) =
      ((2 * Real.pi : ℝ) : ℂ) * (-1 : ℂ) ^ j * (star (Ypsi j ψ θ₀ φ₀) * Ypsi j ψ θ₀ φ₀) := by
  let R : SU2 := SU2.rotZ φ₀ * SU2.rotY θ₀
  let χ : Fin (2 * j + 1) → ℂ := (spinRep (2 * j) R⁻¹).mulVec ψ
  have hconj : ∀ φ : ℝ,
      innerC ψ ((spinRep (2 * j) (SU2.piRot (SU2.actS2 R (SU2.sphVec (Real.pi / 2) φ)))).mulVec ψ) =
      innerC χ ((spinRep (2 * j) (SU2.piRot (SU2.sphVec (Real.pi / 2) φ))).mulVec χ) := by
    intro φ
    rw [spinRep_piRot_actS2, ← spinRep_inv]
    simp only [χ, innerC_mulVec_left, ← spinRep_inv, Matrix.mulVec_mulVec, Matrix.mul_assoc]
    have hinv : R⁻¹⁻¹ = R := SU2.ext (star_star R.a) (neg_neg R.b)
    rw [hinv]
  have hconj_fun :
      (fun φ : ℝ => innerC ψ ((spinRep (2 * j) (SU2.piRot (SU2.actS2 (SU2.rotZ φ₀ * SU2.rotY θ₀)
        (SU2.sphVec (Real.pi / 2) φ)))).mulVec ψ)) =
      fun φ : ℝ => innerC χ ((spinRep (2 * j) (SU2.piRot (SU2.sphVec (Real.pi / 2) φ))).mulVec χ) :=
    funext hconj
  rw [hconj_fun]
  have hexpand : ∀ φ : ℝ,
      innerC χ ((spinRep (2 * j) (SU2.piRot (SU2.sphVec (Real.pi / 2) φ))).mulVec χ) =
      ∑ k : Fin (2 * j + 1),
        (star (χ k) * ((-1 : ℂ) ^ j * χ ⟨2 * j - k.val, by omega⟩)) *
          Complex.exp (I * (((2 * ((k.val : ℤ) - (j : ℤ))) : ℤ) : ℂ) * (φ : ℂ)) := by
    intro φ
    simp only [innerC, Matrix.mulVec, dotProduct]
    apply Finset.sum_congr rfl
    intro k _
    have hrow : ∑ s : Fin (2 * j + 1),
        spinRep (2 * j) (SU2.piRot (SU2.sphVec (Real.pi / 2) φ)) k s * χ s =
        ((-1 : ℂ) ^ j * Complex.exp (I * (2 * ((k.val : ℤ) - (j : ℤ)) : ℂ) * (φ : ℂ))) *
          χ ⟨2 * j - k.val, by omega⟩ := by
      simp_rw [spinRep_piRot_equator]
      rw [Finset.sum_eq_single (⟨2 * j - k.val, by omega⟩ : Fin (2 * j + 1))]
      · simp
      · intro s _ hne
        have hval : s.val ≠ 2 * j - k.val := fun heq => hne (Fin.ext heq)
        simp [hval]
      · intro hnot; exact absurd (Finset.mem_univ _) hnot
    rw [hrow]
    push_cast
    ring
  simp_rw [hexpand]
  rw [intervalIntegral.integral_finsetSum]
  · rw [Finset.sum_eq_single (⟨j, by omega⟩ : Fin (2 * j + 1))]
    · have hsub : (⟨2 * j - j, by omega⟩ : Fin (2 * j + 1)) = ⟨j, by omega⟩ := by ext; dsimp; omega
      simp only [sub_self, mul_zero, Int.cast_zero, zero_mul, Complex.exp_zero, mul_one,
        intervalIntegral.integral_const, sub_zero, Complex.real_smul, hsub]
      change ((2 * Real.pi : ℝ) : ℂ) * (star (Ypsi j ψ θ₀ φ₀) * ((-1 : ℂ) ^ j * Ypsi j ψ θ₀ φ₀)) = _
      ring
    · intro k _ hne
      have hm : (2 * ((k.val : ℤ) - (j : ℤ)) : ℤ) ≠ 0 := by
        intro h0
        apply hne; ext; dsimp; omega
      rw [intervalIntegral.integral_const_mul, integral_exp_int_mul_I _ hm, mul_zero]
    · intro hnot; exact absurd (Finset.mem_univ _) hnot
  · intro k _
    exact (Continuous.intervalIntegrable (by fun_prop) 0 (2 * Real.pi))

/-- **Theorem (Integer-Spin π-Rotation Orthogonality)**:
For every integer spin `j ≥ 1` (`N = 2 * j`) and every state `ψ : Fin (2 * j + 1) → ℂ`,
there exists an axis `u_* ∈ S²` such that `⟨ψ | D^{(j)}(g_π(u_*)) | ψ⟩ = 0`. -/
theorem pi_ortho_even {j : ℕ} (hj : 1 ≤ j) (ψ : Fin (2 * j + 1) → ℂ) :
    ∃ u : S2, innerC ψ ((spinRep (2 * j) (SU2.piRot u)).mulVec ψ) = 0 := by
  obtain ⟨θ₀, _, φ₀, _, hY0⟩ := Ypsi_has_zero hj ψ
  let R : SU2 := SU2.rotZ φ₀ * SU2.rotY θ₀
  let u : ℝ → S2 := fun φ => SU2.actS2 R (SU2.sphVec (Real.pi / 2) φ)
  let F : ℝ → ℂ := fun φ => innerC ψ ((spinRep (2 * j) (SU2.piRot (u φ))).mulVec ψ)
  have hreal : ∀ φ : ℝ, star (F φ) = F φ := by
    intro φ
    simp only [F]
    rw [innerC_conj_symm, innerC_mulVec_left, spinRep_piRot_conjTranspose]
    have hsign : (-1 : ℂ) ^ (2 * j) = 1 := by
      rw [pow_mul]; norm_num
    rw [hsign, one_smul]
  have hFim : ∀ φ : ℝ, (F φ).im = 0 := by
    intro φ
    have h := congrArg Complex.im (hreal φ)
    simp only [RCLike.star_def, conj_im] at h
    linarith
  have hint_F : ∫ φ in (0 : ℝ)..(2 * Real.pi), F φ = 0 := by
    have h := equatorial_integral_identity j ψ θ₀ φ₀
    rw [hY0] at h
    simpa [F, u, R] using h
  have hF_cont : Continuous F := by
    let χ : Fin (2 * j + 1) → ℂ := (spinRep (2 * j) R⁻¹).mulVec ψ
    have hF_eq : ∀ φ, F φ =
        ∑ k : Fin (2 * j + 1),
          (star (χ k) * ((-1 : ℂ) ^ j * χ ⟨2 * j - k.val, by omega⟩)) *
            Complex.exp (I * (2 * ((k.val : ℤ) - (j : ℤ)) : ℂ) * (φ : ℂ)) := by
      intro φ
      have hconj : F φ = innerC χ ((spinRep (2 * j) (SU2.piRot (SU2.sphVec (Real.pi / 2) φ))).mulVec χ) := by
        simp only [F, u, χ, spinRep_piRot_actS2, ← spinRep_inv, innerC_mulVec_left,
          Matrix.mulVec_mulVec, Matrix.mul_assoc]
        have hinv : R⁻¹⁻¹ = R := SU2.ext (star_star R.a) (neg_neg R.b)
        rw [hinv]
      rw [hconj]
      simp only [innerC, Matrix.mulVec, dotProduct]
      apply Finset.sum_congr rfl; intro k _
      have hrow : ∑ s : Fin (2 * j + 1),
          spinRep (2 * j) (SU2.piRot (SU2.sphVec (Real.pi / 2) φ)) k s * χ s =
          ((-1 : ℂ) ^ j * Complex.exp (I * (2 * ((k.val : ℤ) - (j : ℤ)) : ℂ) * (φ : ℂ))) *
            χ ⟨2 * j - k.val, by omega⟩ := by
        simp_rw [spinRep_piRot_equator]
        rw [Finset.sum_eq_single (⟨2 * j - k.val, by omega⟩ : Fin (2 * j + 1))]
        · simp
        · intro s _ hne
          have hval : s.val ≠ 2 * j - k.val := fun heq => hne (Fin.ext heq)
          simp [hval]
        · intro hnot; exact absurd (Finset.mem_univ _) hnot
      rw [hrow]; ring
    have hF_fun : F = fun φ : ℝ =>
        ∑ k : Fin (2 * j + 1),
          (star (χ k) * ((-1 : ℂ) ^ j * χ ⟨2 * j - k.val, by omega⟩)) *
            Complex.exp (I * (2 * ((k.val : ℤ) - (j : ℤ)) : ℂ) * (φ : ℂ)) :=
      funext hF_eq
    rw [hF_fun]
    apply continuous_finsetSum
    intro k _
    fun_prop
  let f : ℝ → ℝ := fun φ => (F φ).re
  have hf_cont : Continuous f := Complex.continuous_re.comp hF_cont
  have hf_int : ∫ φ in (0 : ℝ)..(2 * Real.pi), f φ = 0 := by
    have hcomm := Complex.reCLM.intervalIntegral_comp_comm (μ := volume)
      (a := (0 : ℝ)) (b := 2 * Real.pi) (f := F) (hF_cont.intervalIntegrable (μ := volume) 0 (2 * Real.pi))
    change ∫ φ in (0 : ℝ)..(2 * Real.pi), f φ = (∫ φ in (0 : ℝ)..(2 * Real.pi), F φ).re at hcomm
    rw [hcomm, hint_F, zero_re]
  by_cases hex : ∃ φ ∈ Set.Icc (0 : ℝ) (2 * Real.pi), f φ = 0
  · obtain ⟨φ1, _, hφ1⟩ := hex
    exact ⟨u φ1, Complex.ext hφ1 (hFim φ1)⟩
  · exfalso
    push Not at hex
    have h2pi_pos : (0 : ℝ) < 2 * Real.pi := by positivity
    by_cases h0 : 0 < f 0
    · have hall_pos : ∀ φ ∈ Set.Icc (0 : ℝ) (2 * Real.pi), 0 < f φ := by
        intro φ hφ
        by_contra hle
        push Not at hle
        have hmem : (0 : ℝ) ∈ Set.uIcc (f 0) (f φ) := by
          rw [Set.uIcc_of_ge (by linarith)]; exact ⟨hle, h0.le⟩
        have hIVT : Set.uIcc (f 0) (f φ) ⊆ f '' Set.Icc 0 φ := by
          rw [← Set.uIcc_of_le hφ.1]
          exact intermediate_value_uIcc hf_cont.continuousOn
        obtain ⟨c, hc, hfc⟩ := hIVT hmem
        exact hex c ⟨hc.1, hc.2.trans hφ.2⟩ hfc
      have hpos_int : 0 < ∫ φ in (0 : ℝ)..(2 * Real.pi), f φ :=
        intervalIntegral.integral_pos h2pi_pos hf_cont.continuousOn
          (fun φ hφ => (hall_pos φ ⟨hφ.1.le, hφ.2⟩).le) ⟨0, ⟨le_rfl, h2pi_pos.le⟩, h0⟩
      linarith
    · have h0_lt : f 0 < 0 := lt_of_le_of_ne (not_lt.mp h0) (hex 0 ⟨le_rfl, h2pi_pos.le⟩)
      have hall_neg : ∀ φ ∈ Set.Icc (0 : ℝ) (2 * Real.pi), f φ < 0 := by
        intro φ hφ
        by_contra hge
        push Not at hge
        have hmem : (0 : ℝ) ∈ Set.uIcc (f 0) (f φ) := by
          rw [Set.uIcc_of_le (by linarith)]; exact ⟨h0_lt.le, hge⟩
        have hIVT : Set.uIcc (f 0) (f φ) ⊆ f '' Set.Icc 0 φ := by
          rw [← Set.uIcc_of_le hφ.1]
          exact intermediate_value_uIcc hf_cont.continuousOn
        obtain ⟨c, hc, hfc⟩ := hIVT hmem
        exact hex c ⟨hc.1, hc.2.trans hφ.2⟩ hfc
      have hpos_int : 0 < ∫ φ in (0 : ℝ)..(2 * Real.pi), (-f φ) :=
        intervalIntegral.integral_pos h2pi_pos hf_cont.neg.continuousOn
          (fun φ hφ => by linarith [hall_neg φ ⟨hφ.1.le, hφ.2⟩])
          ⟨0, ⟨le_rfl, h2pi_pos.le⟩, by linarith⟩
      rw [intervalIntegral.integral_neg, hf_int, neg_zero] at hpos_int
      linarith

/-- **Theorem 1 (Universal π-Rotation Orthogonality for All Spins `j = N / 2 ≥ 1/2`)**:
For every positive integer `N ≥ 1` (covering every half-integer and integer spin `j = 1/2, 1, 3/2, ...`)
and every state `ψ : Fin (N + 1) → ℂ`, there exists an axis `u_* ∈ S²` such that
`⟨ψ | D^{(N/2)}(g_π(u_*)) | ψ⟩ = 0`. -/
theorem pi_ortho_all {N : ℕ} (hN : 1 ≤ N) (ψ : Fin (N + 1) → ℂ) :
    ∃ u : S2, innerC ψ ((spinRep N (SU2.piRot u)).mulVec ψ) = 0 := by
  rcases Nat.even_or_odd N with ⟨j, hj_eq⟩ | hodd
  · have hN2 : N = 2 * j := by omega
    subst hN2
    have hj : 1 ≤ j := by omega
    exact pi_ortho_even hj ψ
  · exact pi_ortho_odd hodd ψ

end SU2Wigner

end
