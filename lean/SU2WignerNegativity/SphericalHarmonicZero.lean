import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity

/-!
# Zeros of Complex Spherical Harmonics via 1D Calculus in Spherical Coordinates

We prove Lemma 2 of the paper without any Riemannian-manifold or cohomology machinery:
every smooth complex-valued eigenfunction `Y = u + i v` of the spherical Laplacian
with eigenvalue `λ > 0` on `S²` must vanish at some point `(θ_*, φ_*) ∈ [0, π] × [0, 2π]`.

The proof constructs the global phase `Φ(θ, φ) = ∫_0^θ ((u ∂_s v - v ∂_s u)/(u² + v²)) ds`
explicitly by integrating along meridians from the north pole, differentiates under the
integral sign using Clairaut/Schwarz symmetry of mixed partials, and applies 1D
integration by parts (FTC) + Fubini on `[ε, π - ε] × [0, 2π]` as `ε → 0⁺`.
-/

open MeasureTheory intervalIntegral Filter Topology Real

noncomputable section

namespace SU2Wigner

/-- Partial derivative with respect to the first coordinate `θ`. -/
def dTheta (f : ℝ → ℝ → ℝ) (θ φ : ℝ) : ℝ :=
  deriv (fun t => f t φ) θ

/-- Partial derivative with respect to the second coordinate `φ`. -/
def dPhi (f : ℝ → ℝ → ℝ) (θ φ : ℝ) : ℝ :=
  deriv (fun p => f θ p) φ

/-- Symmetry of mixed partial derivatives for a `C²` function `f : ℝ × ℝ → ℝ`,
obtained from Mathlib's Schwarz theorem `ContDiffAt.isSymmSndFDerivAt`. -/
lemma mixed_partials_eq {f : ℝ → ℝ → ℝ}
    (hf : ContDiff ℝ 2 (Function.uncurry f)) (θ φ : ℝ) :
    dPhi (dTheta f) θ φ = dTheta (dPhi f) θ φ := by
  set F : ℝ × ℝ → ℝ := Function.uncurry f
  have hsymm := (hf.contDiffAt (x := (θ, φ))).isSymmSndFDerivAt (by simp)
  have hF_diff : ∀ x : ℝ × ℝ, DifferentiableAt ℝ F x :=
    fun x => hf.differentiable (by decide) x
  have hdT : ∀ t p, dTheta f t p = fderiv ℝ F (t, p) (1, 0) := by
    intro t p
    have hcomp : HasDerivAt (fun s => F (s, p)) (fderiv ℝ F (t, p) (1, 0)) t := by
      have hpair : HasDerivAt (fun s : ℝ => (s, p)) ((1 : ℝ), (0 : ℝ)) t :=
        (hasDerivAt_id t).prodMk (hasDerivAt_const t p)
      exact (hF_diff (t, p)).hasFDerivAt.comp_hasDerivAt t hpair
    exact hcomp.deriv
  have hdP : ∀ t p, dPhi f t p = fderiv ℝ F (t, p) (0, 1) := by
    intro t p
    have hcomp : HasDerivAt (fun s => F (t, s)) (fderiv ℝ F (t, p) (0, 1)) p := by
      have hpair : HasDerivAt (fun s : ℝ => (t, s)) ((0 : ℝ), (1 : ℝ)) p :=
        (hasDerivAt_const p t).prodMk (hasDerivAt_id p)
      exact (hF_diff (t, p)).hasFDerivAt.comp_hasDerivAt p hpair
    exact hcomp.deriv
  have hDF_diff : DifferentiableAt ℝ (fderiv ℝ F) (θ, φ) :=
    (hf.contDiffAt.fderiv_right (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ 2)).differentiableAt
      (by simp)
  have h1 : HasDerivAt (fun p => dTheta f θ p)
      ((fderiv ℝ (fderiv ℝ F) (θ, φ) (0, 1)) (1, 0)) φ := by
    simp_rw [hdT]
    have hpair : HasDerivAt (fun p : ℝ => (θ, p)) ((0 : ℝ), (1 : ℝ)) φ :=
      (hasDerivAt_const φ θ).prodMk (hasDerivAt_id φ)
    have hfd : HasDerivAt (fun p => fderiv ℝ F (θ, p)) (fderiv ℝ (fderiv ℝ F) (θ, φ) (0, 1)) φ :=
      hDF_diff.hasFDerivAt.comp_hasDerivAt φ hpair
    simpa using hfd.clm_apply (hasDerivAt_const φ ((1 : ℝ), (0 : ℝ)))
  have h2 : HasDerivAt (fun t => dPhi f t φ)
      ((fderiv ℝ (fderiv ℝ F) (θ, φ) (1, 0)) (0, 1)) θ := by
    simp_rw [hdP]
    have hpair : HasDerivAt (fun t : ℝ => (t, φ)) ((1 : ℝ), (0 : ℝ)) θ :=
      (hasDerivAt_id θ).prodMk (hasDerivAt_const θ φ)
    have hfd : HasDerivAt (fun t => fderiv ℝ F (t, φ)) (fderiv ℝ (fderiv ℝ F) (θ, φ) (1, 0)) θ :=
      hDF_diff.hasFDerivAt.comp_hasDerivAt θ hpair
    simpa using hfd.clm_apply (hasDerivAt_const θ ((0 : ℝ), (1 : ℝ)))
  rw [dPhi, h1.deriv, dTheta, h2.deriv]
  exact hsymm.eq (0, 1) (1, 0)

/-- Differentiability of `t ↦ f t φ` from `ContDiff ℝ 2 (uncurry f)`. -/
lemma hasDerivAt_theta {f : ℝ → ℝ → ℝ} (hf : ContDiff ℝ 2 (Function.uncurry f)) (θ φ : ℝ) :
    HasDerivAt (fun t => f t φ) (dTheta f θ φ) θ := by
  have hF := hf.differentiable (by decide) (θ, φ)
  have hpair : HasDerivAt (fun t : ℝ => (t, φ)) ((1 : ℝ), (0 : ℝ)) θ :=
    (hasDerivAt_id θ).prodMk (hasDerivAt_const θ φ)
  have h := hF.hasFDerivAt.comp_hasDerivAt θ hpair
  change HasDerivAt (fun t => f t φ) _ θ at h
  rwa [dTheta, h.deriv]

/-- Differentiability of `p ↦ f θ p` from `ContDiff ℝ 2 (uncurry f)`. -/
lemma hasDerivAt_phi {f : ℝ → ℝ → ℝ} (hf : ContDiff ℝ 2 (Function.uncurry f)) (θ φ : ℝ) :
    HasDerivAt (fun p => f θ p) (dPhi f θ φ) φ := by
  have hF := hf.differentiable (by decide) (θ, φ)
  have hpair : HasDerivAt (fun p : ℝ => (θ, p)) ((0 : ℝ), (1 : ℝ)) φ :=
    (hasDerivAt_const φ θ).prodMk (hasDerivAt_id φ)
  have h := hF.hasFDerivAt.comp_hasDerivAt φ hpair
  change HasDerivAt (fun p => f θ p) _ φ at h
  rwa [dPhi, h.deriv]

/-- `dTheta f` is `C¹` when `f` is `C²`. -/
lemma contDiff_dTheta {f : ℝ → ℝ → ℝ} (hf : ContDiff ℝ 2 (Function.uncurry f)) :
    ContDiff ℝ 1 (Function.uncurry (dTheta f)) := by
  have h_eq : Function.uncurry (dTheta f) =
      fun x : ℝ × ℝ => fderiv ℝ (Function.uncurry f) x (1, 0) := by
    ext ⟨t, p⟩
    have hF := hf.differentiable (by decide) (t, p)
    have hpair : HasDerivAt (fun s : ℝ => (s, p)) ((1 : ℝ), (0 : ℝ)) t :=
      (hasDerivAt_id t).prodMk (hasDerivAt_const t p)
    have h := hF.hasFDerivAt.comp_hasDerivAt t hpair
    change HasDerivAt (fun s => f s p) _ t at h
    exact h.deriv
  rw [h_eq]
  have hfd : ContDiff ℝ 1 (fderiv ℝ (Function.uncurry f)) :=
    hf.fderiv_right (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ 2)
  exact hfd.clm_apply contDiff_const

/-- `dPhi f` is `C¹` when `f` is `C²`. -/
lemma contDiff_dPhi {f : ℝ → ℝ → ℝ} (hf : ContDiff ℝ 2 (Function.uncurry f)) :
    ContDiff ℝ 1 (Function.uncurry (dPhi f)) := by
  have h_eq : Function.uncurry (dPhi f) =
      fun x : ℝ × ℝ => fderiv ℝ (Function.uncurry f) x (0, 1) := by
    ext ⟨t, p⟩
    have hF := hf.differentiable (by decide) (t, p)
    have hpair : HasDerivAt (fun s : ℝ => (t, s)) ((0 : ℝ), (1 : ℝ)) p :=
      (hasDerivAt_const p t).prodMk (hasDerivAt_id p)
    have h := hF.hasFDerivAt.comp_hasDerivAt p hpair
    change HasDerivAt (fun s => f t s) _ p at h
    exact h.deriv
  rw [h_eq]
  have hfd : ContDiff ℝ 1 (fderiv ℝ (Function.uncurry f)) :=
    hf.fderiv_right (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ 2)
  exact hfd.clm_apply contDiff_const

lemma hasDerivAt_theta_of_c1 {g : ℝ → ℝ → ℝ} (hg : ContDiff ℝ 1 (Function.uncurry g)) (θ φ : ℝ) :
    HasDerivAt (fun t => g t φ) (dTheta g θ φ) θ := by
  have hG := hg.differentiable (by decide) (θ, φ)
  have hpair : HasDerivAt (fun t : ℝ => (t, φ)) ((1 : ℝ), (0 : ℝ)) θ :=
    (hasDerivAt_id θ).prodMk (hasDerivAt_const θ φ)
  have h := hG.hasFDerivAt.comp_hasDerivAt θ hpair
  change HasDerivAt (fun t => g t φ) _ θ at h
  rwa [dTheta, h.deriv]

lemma hasDerivAt_phi_of_c1 {g : ℝ → ℝ → ℝ} (hg : ContDiff ℝ 1 (Function.uncurry g)) (θ φ : ℝ) :
    HasDerivAt (fun p => g θ p) (dPhi g θ φ) φ := by
  have hG := hg.differentiable (by decide) (θ, φ)
  have hpair : HasDerivAt (fun p : ℝ => (θ, p)) ((0 : ℝ), (1 : ℝ)) φ :=
    (hasDerivAt_const φ θ).prodMk (hasDerivAt_id φ)
  have h := hG.hasFDerivAt.comp_hasDerivAt φ hpair
  change HasDerivAt (fun p => g θ p) _ φ at h
  rwa [dPhi, h.deriv]

private lemma continuous_dTheta_of_c1 {g : ℝ → ℝ → ℝ} (hg : ContDiff ℝ 1 (Function.uncurry g)) :
    Continuous (Function.uncurry (dTheta g)) := by
  have h_eq : Function.uncurry (dTheta g) =
      fun x : ℝ × ℝ => fderiv ℝ (Function.uncurry g) x (1, 0) := by
    ext ⟨t, p⟩
    have hG := hg.differentiable (by decide) (t, p)
    have hpair : HasDerivAt (fun s : ℝ => (s, p)) ((1 : ℝ), (0 : ℝ)) t :=
      (hasDerivAt_id t).prodMk (hasDerivAt_const t p)
    have h := hG.hasFDerivAt.comp_hasDerivAt t hpair
    change HasDerivAt (fun s => g s p) _ t at h
    exact h.deriv
  rw [h_eq]
  exact (hg.continuous_fderiv (by simp)).clm_apply continuous_const

private lemma continuous_dPhi_of_c1 {g : ℝ → ℝ → ℝ} (hg : ContDiff ℝ 1 (Function.uncurry g)) :
    Continuous (Function.uncurry (dPhi g)) := by
  have h_eq : Function.uncurry (dPhi g) =
      fun x : ℝ × ℝ => fderiv ℝ (Function.uncurry g) x (0, 1) := by
    ext ⟨t, p⟩
    have hG := hg.differentiable (by decide) (t, p)
    have hpair : HasDerivAt (fun s : ℝ => (t, s)) ((0 : ℝ), (1 : ℝ)) p :=
      (hasDerivAt_const p t).prodMk (hasDerivAt_id p)
    have h := hG.hasFDerivAt.comp_hasDerivAt p hpair
    change HasDerivAt (fun s => g t s) _ p at h
    exact h.deriv
  rw [h_eq]
  exact (hg.continuous_fderiv (by simp)).clm_apply continuous_const

private lemma per_2pi_int {w : ℝ → ℝ → ℝ} (hw : ∀ θ φ, w θ (φ + 2 * Real.pi) = w θ φ) :
    ∀ (k : ℤ) (θ φ : ℝ), w θ (φ + (k : ℝ) * (2 * Real.pi)) = w θ φ := by
  intro k θ φ
  induction k using Int.induction_on with
  | zero => simp
  | succ n ih =>
    have h1 : φ + (((n : ℤ) + 1 : ℤ) : ℝ) * (2 * Real.pi) =
        (φ + ((n : ℤ) : ℝ) * (2 * Real.pi)) + 2 * Real.pi := by push_cast; ring
    rw [h1, hw, ih]
  | pred n ih =>
    have h1 : (φ + ((-(n : ℤ) - 1 : ℤ) : ℝ) * (2 * Real.pi)) + 2 * Real.pi =
        φ + ((-(n : ℤ) : ℤ) : ℝ) * (2 * Real.pi) := by push_cast; ring
    rw [← hw, h1, ih]

private lemma dTheta_per_2pi {w : ℝ → ℝ → ℝ} (hw : ∀ θ φ, w θ (φ + 2 * Real.pi) = w θ φ)
    (θ φ : ℝ) : dTheta w θ (φ + 2 * Real.pi) = dTheta w θ φ := by
  simp only [dTheta]
  congr 1; funext t; exact hw t φ

private lemma dPhi_per_2pi {w : ℝ → ℝ → ℝ} (hw : ∀ θ φ, w θ (φ + 2 * Real.pi) = w θ φ)
    (θ φ : ℝ) : dPhi w θ (φ + 2 * Real.pi) = dPhi w θ φ := by
  simp only [dPhi]
  have hcomp : (fun p => w θ (p + 2 * Real.pi)) = (fun p => w θ p) := funext (hw θ)
  have h := deriv_comp_add_const (fun p => w θ p) (2 * Real.pi) φ
  rw [← h, hcomp]

private lemma continuousOn_slice_theta {g : ℝ → ℝ → ℝ} {s t : Set ℝ} {φ : ℝ}
    (hg : ContinuousOn (Function.uncurry g) (s ×ˢ t)) (hφ : φ ∈ t) :
    ContinuousOn (fun θ => g θ φ) s :=
  hg.comp (f := fun θ => (θ, φ)) (continuous_id.prodMk continuous_const).continuousOn
    (fun _ hθ => ⟨hθ, hφ⟩)

private lemma continuousOn_slice_phi {g : ℝ → ℝ → ℝ} {s t : Set ℝ} {θ : ℝ}
    (hg : ContinuousOn (Function.uncurry g) (s ×ˢ t)) (hθ : θ ∈ s) :
    ContinuousOn (fun φ => g θ φ) t :=
  hg.comp (f := fun φ => (θ, φ)) (continuous_const.prodMk continuous_id).continuousOn
    (fun _ hφ => ⟨hθ, hφ⟩)

private lemma hasDerivAt_div_sqrt_sum_sq {a b : ℝ → ℝ} {a' b' t : ℝ}
    (ha : HasDerivAt a a' t) (hb : HasDerivAt b b' t)
    (hpos : 0 < a t ^ 2 + b t ^ 2) (hcur : a t * b' - b t * a' = 0) :
    HasDerivAt (fun x => a x / Real.sqrt (a x ^ 2 + b x ^ 2)) 0 t := by
  have hsq_pos : 0 < Real.sqrt (a t ^ 2 + b t ^ 2) := Real.sqrt_pos.mpr hpos
  have hr2 : HasDerivAt (fun x => a x ^ 2 + b x ^ 2) (2 * a t * a' + 2 * b t * b') t := by
    have h1 := (ha.pow 2).add (hb.pow 2)
    have hval : 2 * a t ^ (2 - 1) * a' + 2 * b t ^ (2 - 1) * b' = 2 * a t * a' + 2 * b t * b' := by
      simp [pow_one]
    exact hval ▸ h1
  have hsqrt : HasDerivAt (fun x => Real.sqrt (a x ^ 2 + b x ^ 2))
      ((1 / (2 * Real.sqrt (a t ^ 2 + b t ^ 2))) * (2 * a t * a' + 2 * b t * b')) t := by
    have h := (Real.hasDerivAt_sqrt hpos.ne').comp t hr2
    exact h
  have hdiv := ha.div hsqrt hsq_pos.ne'
  have hzero :
      (a' * Real.sqrt (a t ^ 2 + b t ^ 2) -
        a t * (1 / (2 * Real.sqrt (a t ^ 2 + b t ^ 2)) * (2 * a t * a' + 2 * b t * b'))) /
        Real.sqrt (a t ^ 2 + b t ^ 2) ^ 2 = 0 := by
    have hsq : Real.sqrt (a t ^ 2 + b t ^ 2) ^ 2 = a t ^ 2 + b t ^ 2 := Real.sq_sqrt hpos.le
    field_simp [hsq_pos.ne']
    rw [hsq]
    linear_combination -b t * hcur
  exact hzero ▸ hdiv

/-- Continuous functions on `[a, b] × [c, d]` are `IntegrableOn` `uIoc a b ×ˢ uIoc c d`. -/
private lemma integrableOn_uIoc_prod_of_continuousOn {F : ℝ → ℝ → ℝ} {a b c d : ℝ}
    (hab : a ≤ b) (hcd : c ≤ d)
    (hF : ContinuousOn (Function.uncurry F) (Set.Icc a b ×ˢ Set.Icc c d)) :
    IntegrableOn (Function.uncurry F) (Set.uIoc a b ×ˢ Set.uIoc c d) := by
  rw [Set.uIoc_of_le hab, Set.uIoc_of_le hcd]
  exact (hF.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)).mono_set
    (Set.prod_mono Set.Ioc_subset_Icc_self Set.Ioc_subset_Icc_self)

/-- The outer slice integral of a continuous function on `[a, b] × [c, d]` is interval-integrable. -/
private lemma intervalIntegrable_integral_of_continuousOn {F : ℝ → ℝ → ℝ} {a b c d : ℝ}
    (hab : a ≤ b) (hcd : c ≤ d)
    (hF : ContinuousOn (Function.uncurry F) (Set.Icc a b ×ˢ Set.Icc c d)) :
    IntervalIntegrable (fun x => ∫ y in c..d, F x y) volume a b := by
  have hint := integrableOn_uIoc_prod_of_continuousOn hab hcd hF
  rw [Set.uIoc_of_le hab, Set.uIoc_of_le hcd] at hint
  have hprod : Integrable (Function.uncurry F)
      ((volume.restrict (Set.Ioc a b)).prod (volume.restrict (Set.Ioc c d))) := by
    rwa [Measure.prod_restrict, ← Measure.volume_eq_prod]
  have hleft := hprod.integral_prod_left
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hab]
  have heq : (fun x => ∫ y in c..d, F x y) = (fun x => ∫ y, F x y ∂volume.restrict (Set.Ioc c d)) := by
    funext x
    rw [intervalIntegral.integral_of_le hcd]
  rw [heq]
  exact hleft

/-- Elementary vanishing criterion: if `F ≥ 0` is continuous on `(0, π) × [0, 2π]` and its
integral over `[ε, π - ε] × [0, 2π]` is `≤ C * sin ε` for all `ε ∈ (0, π / 2)`,
then `F = 0` everywhere on `(0, π) × [0, 2π]`. -/
private lemma eq_zero_of_integral_le_mul_sin
    {F : ℝ → ℝ → ℝ}
    (hF_cont : ContinuousOn (Function.uncurry F)
      (Set.Ioo (0 : ℝ) Real.pi ×ˢ Set.Icc (0 : ℝ) (2 * Real.pi)))
    (hF_nonneg : ∀ θ ∈ Set.Ioo (0 : ℝ) Real.pi, ∀ φ ∈ Set.Icc (0 : ℝ) (2 * Real.pi), 0 ≤ F θ φ)
    {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ ε : ℝ, 0 < ε → ε < Real.pi / 2 →
      ∫ θ in ε..(Real.pi - ε), ∫ φ in (0 : ℝ)..(2 * Real.pi), F θ φ ≤ C * Real.sin ε) :
    ∀ θ ∈ Set.Ioo (0 : ℝ) Real.pi, ∀ φ ∈ Set.Icc (0 : ℝ) (2 * Real.pi), F θ φ = 0 := by
  intro θ₀ hθ₀ φ₀ hφ₀
  by_contra hne
  have hpos : 0 < F θ₀ φ₀ := lt_of_le_of_ne (hF_nonneg θ₀ hθ₀ φ₀ hφ₀) (Ne.symm hne)
  have hcont_at := Metric.continuousOn_iff.mp hF_cont (θ₀, φ₀) ⟨hθ₀, hφ₀⟩ (F θ₀ φ₀ / 2) (by linarith)
  obtain ⟨δ, hδ_pos, hδ⟩ := hcont_at
  set r : ℝ := min (min (δ / 2) (Real.pi / 4)) (min (θ₀ / 2) ((Real.pi - θ₀) / 2))
  have hr_pos : 0 < r := by
    have h1 : 0 < θ₀ := hθ₀.1
    have h2 : 0 < Real.pi - θ₀ := sub_pos.mpr hθ₀.2
    positivity
  have hr_lt_δ : r < δ := by
    have : r ≤ δ / 2 := le_trans (min_le_left _ _) (min_le_left _ _)
    linarith
  have hr_le_pi4 : r ≤ Real.pi / 4 := le_trans (min_le_left _ _) (min_le_right _ _)
  have hr_le_t0 : r ≤ θ₀ / 2 := le_trans (min_le_right _ _) (min_le_left _ _)
  have hr_le_pit0 : r ≤ (Real.pi - θ₀) / 2 := le_trans (min_le_right _ _) (min_le_right _ _)
  set t₁ : ℝ := θ₀ - r
  set t₂ : ℝ := θ₀ + r
  have ht₁_pos : 0 < t₁ := by linarith [hθ₀.1]
  have ht₂_lt : t₂ < Real.pi := by linarith [hθ₀.2]
  have ht₁_le_t₂ : t₁ ≤ t₂ := by linarith
  have hp_ex : ∃ p₁ p₂ : ℝ, 0 ≤ p₁ ∧ p₁ < p₂ ∧ p₂ ≤ 2 * Real.pi ∧ p₂ - p₁ = r ∧
      ∀ p ∈ Set.Icc p₁ p₂, |p - φ₀| ≤ r := by
    by_cases hφ : φ₀ ≤ Real.pi
    · refine ⟨φ₀, φ₀ + r, hφ₀.1, by linarith, by linarith, by ring, ?_⟩
      intro p hp
      rw [abs_le]; constructor <;> linarith [hp.1, hp.2]
    · refine ⟨φ₀ - r, φ₀, by linarith, by linarith, hφ₀.2, by ring, ?_⟩
      intro p hp
      rw [abs_le]; constructor <;> linarith [hp.1, hp.2]
  obtain ⟨p₁, p₂, hp₁_nn, hp₁_lt_p₂, hp₂_le, hp_len, hp_dist⟩ := hp_ex
  let m : ℝ := F θ₀ φ₀ / 2
  have hm_pos : 0 < m := by simp only [m]; linarith
  have hF_ge : ∀ t ∈ Set.Icc t₁ t₂, ∀ p ∈ Set.Icc p₁ p₂, m ≤ F t p := by
    intro t ht p hp
    have ht_mem : t ∈ Set.Ioo (0 : ℝ) Real.pi := ⟨by linarith [ht.1], by linarith [ht.2]⟩
    have hp_mem : p ∈ Set.Icc (0 : ℝ) (2 * Real.pi) := ⟨by linarith [hp.1], by linarith [hp.2]⟩
    have hdist : dist (t, p) (θ₀, φ₀) < δ := by
      rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq]
      apply max_lt
      · have : |t - θ₀| ≤ r := by rw [abs_le]; constructor <;> linarith [ht.1, ht.2]
        linarith
      · exact lt_of_le_of_lt (hp_dist p hp) hr_lt_δ
    have hsub := hδ (t, p) ⟨ht_mem, hp_mem⟩ hdist
    simp only [Function.uncurry, Real.dist_eq, abs_lt] at hsub
    simp only [m]
    linarith [hsub.1]
  set I₀ : ℝ := (t₂ - t₁) * (p₂ - p₁) * m
  have hI₀_pos : 0 < I₀ := by
    have : 0 < t₂ - t₁ := by linarith
    have : 0 < p₂ - p₁ := by linarith
    positivity
  set ε : ℝ := min (min t₁ (Real.pi - t₂) / 2) (I₀ / (2 * (C + 1)))
  have hε_pos : 0 < ε := by
    have h1 : 0 < min t₁ (Real.pi - t₂) := lt_min ht₁_pos (sub_pos.mpr ht₂_lt)
    have h2 : 0 < 2 * (C + 1) := by linarith
    positivity
  have hε_lt_t1 : ε < t₁ := by
    have : ε ≤ min t₁ (Real.pi - t₂) / 2 := min_le_left _ _
    have : min t₁ (Real.pi - t₂) ≤ t₁ := min_le_left _ _
    linarith
  have hε_lt_pit2 : ε < Real.pi - t₂ := by
    have : ε ≤ min t₁ (Real.pi - t₂) / 2 := min_le_left _ _
    have : min t₁ (Real.pi - t₂) ≤ Real.pi - t₂ := min_le_right _ _
    linarith
  have hε_lt_pi2 : ε < Real.pi / 2 := by linarith
  have hε_le_pie : ε ≤ Real.pi - ε := by linarith
  have hCε_lt : C * Real.sin ε < I₀ := by
    have hsin : Real.sin ε ≤ ε := Real.sin_le hε_pos.le
    have hε_le : ε ≤ I₀ / (2 * (C + 1)) := min_le_right _ _
    have h1 : C * Real.sin ε ≤ C * ε := mul_le_mul_of_nonneg_left hsin hC
    have h2 : C * ε ≤ C * (I₀ / (2 * (C + 1))) := mul_le_mul_of_nonneg_left hε_le hC
    have h3 : C * (I₀ / (2 * (C + 1))) < I₀ := by
      rw [mul_div_assoc', div_lt_iff₀ (by linarith : (0 : ℝ) < 2 * (C + 1))]
      nlinarith
    linarith
  have hbox_sub : Set.Icc ε (Real.pi - ε) ×ˢ Set.Icc (0 : ℝ) (2 * Real.pi) ⊆
      Set.Ioo (0 : ℝ) Real.pi ×ˢ Set.Icc (0 : ℝ) (2 * Real.pi) :=
    Set.prod_mono (fun t ht => ⟨lt_of_lt_of_le hε_pos ht.1, by linarith [ht.2]⟩) Set.Subset.rfl
  have hF_box_cont : ContinuousOn (Function.uncurry F)
      (Set.Icc ε (Real.pi - ε) ×ˢ Set.Icc (0 : ℝ) (2 * Real.pi)) := hF_cont.mono hbox_sub
  have hinner_ge : ∀ t ∈ Set.Icc t₁ t₂, (p₂ - p₁) * m ≤ ∫ φ in (0 : ℝ)..(2 * Real.pi), F t φ := by
    intro t ht
    have ht_eps : t ∈ Set.Icc ε (Real.pi - ε) := ⟨by linarith [ht.1], by linarith [ht.2]⟩
    have hFt_cont : ContinuousOn (fun φ => F t φ) (Set.Icc (0 : ℝ) (2 * Real.pi)) :=
      hF_box_cont.comp (continuous_const.prodMk continuous_id).continuousOn
        (fun p hp => ⟨ht_eps, hp⟩)
    have hFt_int : IntervalIntegrable (fun φ => F t φ) volume 0 (2 * Real.pi) :=
      (hFt_cont.mono (by rw [Set.uIcc_of_le (by positivity)])).intervalIntegrable
    have hFt_int_sub : IntervalIntegrable (fun φ => F t φ) volume p₁ p₂ :=
      (hFt_cont.mono (by
        rw [Set.uIcc_of_le hp₁_lt_p₂.le]
        exact fun p hp => ⟨by linarith [hp.1], by linarith [hp.2]⟩)).intervalIntegrable
    have h1 : (p₂ - p₁) * m ≤ ∫ φ in p₁..p₂, F t φ := by
      have hconst : ∫ _ in p₁..p₂, m = (p₂ - p₁) * m := by simp
      rw [← hconst]
      exact intervalIntegral.integral_mono_on hp₁_lt_p₂.le intervalIntegrable_const hFt_int_sub
        (fun p hp => hF_ge t ht p hp)
    have h2 : ∫ φ in p₁..p₂, F t φ ≤ ∫ φ in (0 : ℝ)..(2 * Real.pi), F t φ := by
      apply intervalIntegral.integral_mono_interval hp₁_nn hp₁_lt_p₂.le hp₂_le
      · exact (ae_restrict_iff' measurableSet_Ioc).mpr
          (ae_of_all _ (fun p hp => hF_nonneg t ⟨by linarith [ht.1], by linarith [ht.2]⟩ p
            ⟨hp.1.le, hp.2⟩))
      · exact hFt_int
    linarith
  have houter_int : IntervalIntegrable (fun t => ∫ φ in (0 : ℝ)..(2 * Real.pi), F t φ)
      volume ε (Real.pi - ε) :=
    intervalIntegrable_integral_of_continuousOn hε_le_pie (by positivity) hF_box_cont
  have houter_int_sub : IntervalIntegrable (fun t => ∫ φ in (0 : ℝ)..(2 * Real.pi), F t φ)
      volume t₁ t₂ :=
    houter_int.mono_set (by
      rw [Set.uIcc_of_le ht₁_le_t₂, Set.uIcc_of_le hε_le_pie]
      exact fun t ht => ⟨by linarith [ht.1], by linarith [ht.2]⟩)
  have hI₀_le : I₀ ≤ ∫ t in ε..(Real.pi - ε), ∫ φ in (0 : ℝ)..(2 * Real.pi), F t φ := by
    have h1 : I₀ ≤ ∫ t in t₁..t₂, ∫ φ in (0 : ℝ)..(2 * Real.pi), F t φ := by
      have hconst : ∫ _ in t₁..t₂, ((p₂ - p₁) * m) = I₀ := by
        simp [I₀]; ring
      rw [← hconst]
      exact intervalIntegral.integral_mono_on ht₁_le_t₂ intervalIntegrable_const houter_int_sub
        hinner_ge
    have h2 : ∫ t in t₁..t₂, ∫ φ in (0 : ℝ)..(2 * Real.pi), F t φ ≤
        ∫ t in ε..(Real.pi - ε), ∫ φ in (0 : ℝ)..(2 * Real.pi), F t φ := by
      apply intervalIntegral.integral_mono_interval hε_lt_t1.le ht₁_le_t₂ (by linarith)
      · exact (ae_restrict_iff' measurableSet_Ioc).mpr (ae_of_all _ fun t ht =>
          intervalIntegral.integral_nonneg (by positivity) fun p hp =>
            hF_nonneg t ⟨lt_of_lt_of_le hε_pos ht.1.le, by linarith [ht.2]⟩ p hp)
      · exact houter_int
    linarith
  have hup := hbound ε hε_pos hε_lt_pi2
  linarith

/-- Step 1–2 helper: for a nonvanishing `C²` complex eigenfunction `u + i v` on `S²`,
the probability current `(u ∂_θ v - v ∂_θ u, u ∂_φ v - v ∂_φ u)` vanishes identically on `(0, π) × ℝ`. -/
private lemma current_eq_zero_of_nonvanishing
    {u v : ℝ → ℝ → ℝ} {lam : ℝ}
    (hu : ContDiff ℝ 2 (Function.uncurry u))
    (hv : ContDiff ℝ 2 (Function.uncurry v))
    (hu_per : ∀ θ φ, u θ (φ + 2 * Real.pi) = u θ φ)
    (hv_per : ∀ θ φ, v θ (φ + 2 * Real.pi) = v θ φ)
    (hu_pole : ∀ φ, u 0 φ = u 0 0)
    (hv_pole : ∀ φ, v 0 φ = v 0 0)
    (hu_lap : ∀ θ ∈ Set.Ioo (0 : ℝ) Real.pi, ∀ φ : ℝ,
      dTheta (fun t p => Real.sin t * dTheta u t p) θ φ +
        (Real.sin θ)⁻¹ * dPhi (dPhi u) θ φ = -lam * Real.sin θ * u θ φ)
    (hv_lap : ∀ θ ∈ Set.Ioo (0 : ℝ) Real.pi, ∀ φ : ℝ,
      dTheta (fun t p => Real.sin t * dTheta v t p) θ φ +
        (Real.sin θ)⁻¹ * dPhi (dPhi v) θ φ = -lam * Real.sin θ * v θ φ)
    (hr2_pos : ∀ θ ∈ Set.Icc (0 : ℝ) Real.pi, ∀ φ : ℝ, 0 < u θ φ ^ 2 + v θ φ ^ 2) :
    ∀ θ ∈ Set.Ioo (0 : ℝ) Real.pi, ∀ φ : ℝ,
      u θ φ * dTheta v θ φ - v θ φ * dTheta u θ φ = 0 ∧
      u θ φ * dPhi v θ φ - v θ φ * dPhi u θ φ = 0 := by
  let r2 : ℝ → ℝ → ℝ := fun θ φ => u θ φ ^ 2 + v θ φ ^ 2
  let A : ℝ → ℝ → ℝ := fun θ φ => (u θ φ * dTheta v θ φ - v θ φ * dTheta u θ φ) / r2 θ φ
  let B : ℝ → ℝ → ℝ := fun θ φ => (u θ φ * dPhi v θ φ - v θ φ * dPhi u θ φ) / r2 θ φ
  let Φ : ℝ → ℝ → ℝ := fun θ φ => ∫ s in (0 : ℝ)..θ, A s φ

  have hu_t_c1 : ContDiff ℝ 1 (Function.uncurry (dTheta u)) := contDiff_dTheta hu
  have hv_t_c1 : ContDiff ℝ 1 (Function.uncurry (dTheta v)) := contDiff_dTheta hv
  have hu_p_c1 : ContDiff ℝ 1 (Function.uncurry (dPhi u)) := contDiff_dPhi hu
  have hv_p_c1 : ContDiff ℝ 1 (Function.uncurry (dPhi v)) := contDiff_dPhi hv
  have hr2_c2 : ContDiff ℝ 2 (Function.uncurry r2) := (hu.pow 2).add (hv.pow 2)

  have hA_c1_at : ∀ θ ∈ Set.Icc (0 : ℝ) Real.pi, ∀ φ : ℝ,
      ContDiffAt ℝ 1 (Function.uncurry A) (θ, φ) := by
    intro θ hθ φ
    have hnum : ContDiffAt ℝ 1 (fun x => Function.uncurry u x * Function.uncurry (dTheta v) x -
        Function.uncurry v x * Function.uncurry (dTheta u) x) (θ, φ) :=
      ((hu.of_le (by norm_num)).contDiffAt.mul hv_t_c1.contDiffAt).sub
        ((hv.of_le (by norm_num)).contDiffAt.mul hu_t_c1.contDiffAt)
    exact hnum.div (hr2_c2.of_le (by norm_num)).contDiffAt (hr2_pos θ hθ φ).ne'

  have hB_c1_at : ∀ θ ∈ Set.Icc (0 : ℝ) Real.pi, ∀ φ : ℝ,
      ContDiffAt ℝ 1 (Function.uncurry B) (θ, φ) := by
    intro θ hθ φ
    have hnum : ContDiffAt ℝ 1 (fun x => Function.uncurry u x * Function.uncurry (dPhi v) x -
        Function.uncurry v x * Function.uncurry (dPhi u) x) (θ, φ) :=
      ((hu.of_le (by norm_num)).contDiffAt.mul hv_p_c1.contDiffAt).sub
        ((hv.of_le (by norm_num)).contDiffAt.mul hu_p_c1.contDiffAt)
    exact hnum.div (hr2_c2.of_le (by norm_num)).contDiffAt (hr2_pos θ hθ φ).ne'

  -- Exact closedness identity `∂_φ A = ∂_θ B` on `[0, π] × ℝ`.
  have hclosed : ∀ θ ∈ Set.Icc (0 : ℝ) Real.pi, ∀ φ : ℝ,
      HasDerivAt (fun p => A θ p) (dTheta B θ φ) φ ∧
      HasDerivAt (fun t => B t φ) (dTheta B θ φ) θ := by
    intro θ hθ φ
    have hpos : r2 θ φ ≠ 0 := (hr2_pos θ hθ φ).ne'
    have hup := hasDerivAt_phi hu θ φ
    have hvp := hasDerivAt_phi hv θ φ
    have hutp := hasDerivAt_phi_of_c1 hu_t_c1 θ φ
    have hvtp := hasDerivAt_phi_of_c1 hv_t_c1 θ φ
    have hr2p : HasDerivAt (fun p => r2 θ p) (2 * u θ φ * dPhi u θ φ + 2 * v θ φ * dPhi v θ φ) φ := by
      convert (hup.pow 2).add (hvp.pow 2) using 1; ring
    have hAp : HasDerivAt (fun p => A θ p)
        ((((dPhi u θ φ * dTheta v θ φ + u θ φ * dPhi (dTheta v) θ φ) -
           (dPhi v θ φ * dTheta u θ φ + v θ φ * dPhi (dTheta u) θ φ)) * r2 θ φ -
          (u θ φ * dTheta v θ φ - v θ φ * dTheta u θ φ) *
           (2 * u θ φ * dPhi u θ φ + 2 * v θ φ * dPhi v θ φ)) / r2 θ φ ^ 2) φ :=
      ((hup.mul hvtp).sub (hvp.mul hutp)).div hr2p hpos
    have hut := hasDerivAt_theta hu θ φ
    have hvt := hasDerivAt_theta hv θ φ
    have hupt := hasDerivAt_theta_of_c1 hu_p_c1 θ φ
    have hvpt := hasDerivAt_theta_of_c1 hv_p_c1 θ φ
    have hr2t : HasDerivAt (fun t => r2 t φ) (2 * u θ φ * dTheta u θ φ + 2 * v θ φ * dTheta v θ φ) θ := by
      convert (hut.pow 2).add (hvt.pow 2) using 1; ring
    have hBt : HasDerivAt (fun t => B t φ)
        ((((dTheta u θ φ * dPhi v θ φ + u θ φ * dTheta (dPhi v) θ φ) -
           (dTheta v θ φ * dPhi u θ φ + v θ φ * dTheta (dPhi u) θ φ)) * r2 θ φ -
          (u θ φ * dPhi v θ φ - v θ φ * dPhi u θ φ) *
           (2 * u θ φ * dTheta u θ φ + 2 * v θ φ * dTheta v θ φ)) / r2 θ φ ^ 2) θ :=
      ((hut.mul hvpt).sub (hvt.mul hupt)).div hr2t hpos
    have hsym_u := mixed_partials_eq hu θ φ
    have hsym_v := mixed_partials_eq hv θ φ
    have hval_eq :
        (((dPhi u θ φ * dTheta v θ φ + u θ φ * dPhi (dTheta v) θ φ) -
          (dPhi v θ φ * dTheta u θ φ + v θ φ * dPhi (dTheta u) θ φ)) * r2 θ φ -
         (u θ φ * dTheta v θ φ - v θ φ * dTheta u θ φ) *
          (2 * u θ φ * dPhi u θ φ + 2 * v θ φ * dPhi v θ φ)) / r2 θ φ ^ 2 =
        (((dTheta u θ φ * dPhi v θ φ + u θ φ * dTheta (dPhi v) θ φ) -
          (dTheta v θ φ * dPhi u θ φ + v θ φ * dTheta (dPhi u) θ φ)) * r2 θ φ -
         (u θ φ * dPhi v θ φ - v θ φ * dPhi u θ φ) *
          (2 * u θ φ * dTheta u θ φ + 2 * v θ φ * dTheta v θ φ)) / r2 θ φ ^ 2 := by
      rw [hsym_u, hsym_v]
      simp only [r2]
      field_simp [hpos]
      ring
    have hdB : dTheta B θ φ =
        (((dTheta u θ φ * dPhi v θ φ + u θ φ * dTheta (dPhi v) θ φ) -
          (dTheta v θ φ * dPhi u θ φ + v θ φ * dTheta (dPhi u) θ φ)) * r2 θ φ -
         (u θ φ * dPhi v θ φ - v θ φ * dPhi u θ φ) *
          (2 * u θ φ * dTheta u θ φ + 2 * v θ φ * dTheta v θ φ)) / r2 θ φ ^ 2 :=
      hBt.deriv
    rw [hdB]
    exact ⟨hval_eq ▸ hAp, hBt⟩

  -- North-pole vanishing: `B(0, φ) = 0`.
  have hB_pole : ∀ φ : ℝ, B 0 φ = 0 := by
    intro φ
    have hu0 : dPhi u 0 φ = 0 := by
      have : (fun p => u 0 p) = fun _ => u 0 0 := funext hu_pole
      rw [dPhi, this, deriv_const]
    have hv0 : dPhi v 0 φ = 0 := by
      have : (fun p => v 0 p) = fun _ => v 0 0 := funext hv_pole
      rw [dPhi, this, deriv_const]
    simp [B, hu0, hv0]

  -- Periodicity in `φ`.
  have hA_per : ∀ θ φ, A θ (φ + 2 * Real.pi) = A θ φ := by
    intro θ φ; simp [A, r2, hu_per, hv_per, dTheta_per_2pi hu_per, dTheta_per_2pi hv_per]
  have hB_per : ∀ θ φ, B θ (φ + 2 * Real.pi) = B θ φ := by
    intro θ φ; simp [B, r2, hu_per, hv_per, dPhi_per_2pi hu_per, dPhi_per_2pi hv_per]
  have hΦ_per : ∀ θ φ, Φ θ (φ + 2 * Real.pi) = Φ θ φ := by
    intro θ φ; simp only [Φ, hA_per]

  have hA_meas : ∀ φ, StronglyMeasurable (fun s => A s φ) := by
    intro φ
    have hnum : Continuous (fun s => u s φ * dTheta v s φ - v s φ * dTheta u s φ) :=
      ((hu.continuous.comp (continuous_id.prodMk continuous_const)).mul
        (hv_t_c1.continuous.comp (continuous_id.prodMk continuous_const))).sub
      ((hv.continuous.comp (continuous_id.prodMk continuous_const)).mul
        (hu_t_c1.continuous.comp (continuous_id.prodMk continuous_const)))
    have hden : Continuous (fun s => r2 s φ) :=
      hr2_c2.continuous.comp (continuous_id.prodMk continuous_const)
    exact (hnum.measurable.div hden.measurable).stronglyMeasurable

  have hA_contAt_theta : ∀ θ ∈ Set.Icc (0 : ℝ) Real.pi, ∀ φ : ℝ,
      ContinuousAt (fun s => A s φ) θ := by
    intro θ hθ φ
    exact ContinuousAt.comp (g := Function.uncurry A) (f := fun s => (s, φ))
      (hA_c1_at θ hθ φ).continuousAt (continuous_id.prodMk continuous_const).continuousAt

  have hA_contOn : ∀ φ, ContinuousOn (fun s => A s φ) (Set.Icc 0 Real.pi) :=
    fun φ s hs => (hA_contAt_theta s hs φ).continuousWithinAt

  have hdTB_contOn : ContinuousOn (Function.uncurry (dTheta B))
      (Set.Icc (0 : ℝ) Real.pi ×ˢ Set.univ) := by
    have hfd_cont : ContinuousOn (fun x : ℝ × ℝ => fderiv ℝ (Function.uncurry B) x (1, 0))
        (Set.Icc (0 : ℝ) Real.pi ×ˢ Set.univ) := fun x hx =>
      (((hB_c1_at x.1 hx.1 x.2).continuousAt_fderiv (by simp)).clm_apply
        continuousAt_const).continuousWithinAt
    refine hfd_cont.congr (fun x hx => ?_)
    have hB_diff := (hB_c1_at x.1 hx.1 x.2).differentiableAt (by simp)
    have hpair : HasDerivAt (fun s : ℝ => (s, x.2)) ((1 : ℝ), (0 : ℝ)) x.1 :=
      (hasDerivAt_id x.1).prodMk (hasDerivAt_const x.1 x.2)
    exact (hB_diff.hasFDerivAt.comp_hasDerivAt x.1 hpair).deriv

  have hΦ_dTheta : ∀ θ ∈ Set.Icc (0 : ℝ) Real.pi, ∀ φ : ℝ,
      HasDerivAt (fun t => Φ t φ) (A θ φ) θ := by
    intro θ hθ φ
    have hint : IntervalIntegrable (fun s => A s φ) volume 0 θ :=
      ((hA_contOn φ).mono (Set.uIcc_subset_Icc (Set.left_mem_Icc.mpr Real.pi_pos.le) hθ)).intervalIntegrable
    exact intervalIntegral.integral_hasDerivAt_right hint (hA_meas φ).stronglyMeasurableAtFilter
      (hA_contAt_theta θ hθ φ)

  have hΦ_dPhi : ∀ θ ∈ Set.Icc (0 : ℝ) Real.pi, ∀ φ : ℝ,
      HasDerivAt (fun p => Φ θ p) (B θ φ) φ := by
    intro θ hθ φ
    obtain ⟨M, hM⟩ := (isCompact_Icc.prod isCompact_Icc).exists_bound_of_continuousOn
      (hdTB_contOn.mono (Set.prod_mono Set.Subset.rfl (Set.subset_univ _)) :
        ContinuousOn (Function.uncurry (dTheta B))
          (Set.Icc (0 : ℝ) Real.pi ×ˢ Set.Icc (φ - 1) (φ + 1)))
    have hle : (0 : ℝ) ≤ θ := hθ.1
    have hF_int : IntervalIntegrable (fun t => A t φ) volume 0 θ :=
      ((hA_contOn φ).mono (Set.uIcc_subset_Icc (Set.left_mem_Icc.mpr Real.pi_pos.le) hθ)).intervalIntegrable
    have hF'_cont : ContinuousOn (fun t => dTheta B t φ) (Set.Icc 0 θ) :=
      (continuousOn_slice_theta hdTB_contOn trivial).mono (fun t ht => ⟨ht.1, ht.2.trans hθ.2⟩)
    have hF'_meas : AEStronglyMeasurable (fun t => dTheta B t φ) (volume.restrict (Set.uIoc 0 θ)) := by
      rw [Set.uIoc_of_le hle]
      exact (hF'_cont.mono Set.Ioc_subset_Icc_self).aestronglyMeasurable measurableSet_Ioc
    have hparam := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (F := fun p t => A t p) (F' := fun p t => dTheta B t p) (bound := fun _ => M)
      (s := Set.Icc (φ - 1) (φ + 1)) (x₀ := φ) (a := 0) (b := θ) (μ := volume)
      (Icc_mem_nhds (by linarith) (by linarith))
      (Eventually.of_forall fun p => (hA_meas p).aestronglyMeasurable)
      hF_int
      hF'_meas
      (ae_of_all _ fun t ht p hp => by
        rw [Set.uIoc_of_le hle] at ht
        exact hM (t, p) ⟨⟨ht.1.le, ht.2.trans hθ.2⟩, hp⟩)
      intervalIntegrable_const
      (ae_of_all _ fun t ht p _ => by
        rw [Set.uIoc_of_le hle] at ht
        exact (hclosed t ⟨ht.1.le, ht.2.trans hθ.2⟩ p).1)
    have hftc : ∫ t in (0 : ℝ)..θ, dTheta B t φ = B θ φ - B 0 φ := by
      apply intervalIntegral.integral_eq_sub_of_hasDerivAt
      · intro t ht
        rw [Set.uIcc_of_le hle] at ht
        exact (hclosed t ⟨ht.1, ht.2.trans hθ.2⟩ φ).2
      · exact (hF'_cont.mono (by rw [Set.uIcc_of_le hle])).intervalIntegrable
    rw [hftc, hB_pole φ, sub_zero] at hparam
    exact hparam.2

  -- Joint continuity of `Φ` on `[0, π] × [0, 2π]`
  have hA_K_cont : ContinuousOn (Function.uncurry A)
      (Set.Icc (0 : ℝ) Real.pi ×ˢ Set.Icc (0 : ℝ) (2 * Real.pi)) :=
    fun x hx => (hA_c1_at x.1 hx.1 x.2).continuousAt.continuousWithinAt
  have hB_K_cont : ContinuousOn (Function.uncurry B)
      (Set.Icc (0 : ℝ) Real.pi ×ˢ Set.Icc (0 : ℝ) (2 * Real.pi)) :=
    fun x hx => (hB_c1_at x.1 hx.1 x.2).continuousAt.continuousWithinAt
  obtain ⟨MA, hMA⟩ := (isCompact_Icc.prod isCompact_Icc).exists_bound_of_continuousOn hA_K_cont
  obtain ⟨MB, hMB⟩ := (isCompact_Icc.prod isCompact_Icc).exists_bound_of_continuousOn hB_K_cont
  have hMA_nn : 0 ≤ MA :=
    le_trans (norm_nonneg _) (hMA (0, 0) ⟨⟨le_rfl, Real.pi_pos.le⟩, ⟨le_rfl, by positivity⟩⟩)
  have hMB_nn : 0 ≤ MB :=
    le_trans (norm_nonneg _) (hMB (0, 0) ⟨⟨le_rfl, Real.pi_pos.le⟩, ⟨le_rfl, by positivity⟩⟩)

  have hΦ_contOn : ContinuousOn (Function.uncurry Φ)
      (Set.Icc (0 : ℝ) Real.pi ×ˢ Set.Icc (0 : ℝ) (2 * Real.pi)) := by
    rw [Metric.continuousOn_iff]
    intro x hx ε' hε'
    let L : ℝ := MA + MB + 1
    have hL_pos : 0 < L := by simp only [L]; linarith
    refine ⟨ε' / L, by positivity, ?_⟩
    intro y hy hdist
    rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq] at hdist
    have h1 : |Φ y.1 y.2 - Φ x.1 y.2| ≤ MA * |y.1 - x.1| := by
      have hsub : Φ y.1 y.2 - Φ x.1 y.2 = ∫ s in x.1..y.1, A s y.2 := by
        simp only [Φ]
        have hint1 : IntervalIntegrable (fun s => A s y.2) volume 0 x.1 :=
          ((hA_contOn y.2).mono (Set.uIcc_subset_Icc (Set.left_mem_Icc.mpr Real.pi_pos.le) hx.1)).intervalIntegrable
        have hint2 : IntervalIntegrable (fun s => A s y.2) volume x.1 y.1 :=
          ((hA_contOn y.2).mono (Set.uIcc_subset_Icc hx.1 hy.1)).intervalIntegrable
        linarith [intervalIntegral.integral_add_adjacent_intervals hint1 hint2]
      rw [hsub]
      have hnorm := intervalIntegral.norm_integral_le_of_norm_le_const (C := MA)
        (a := x.1) (b := y.1) (f := fun s => A s y.2) (fun s hs =>
          hMA (s, y.2) ⟨Set.uIcc_subset_Icc hx.1 hy.1 (Set.uIoc_subset_uIcc hs), hy.2⟩)
      simpa [Real.norm_eq_abs, abs_sub_comm] using hnorm
    have h2 : |Φ x.1 y.2 - Φ x.1 x.2| ≤ MB * |y.2 - x.2| := by
      have hsub : Φ x.1 y.2 - Φ x.1 x.2 = ∫ p in x.2..y.2, B x.1 p := by
        symm
        apply intervalIntegral.integral_eq_sub_of_hasDerivAt
        · intro p _; exact hΦ_dPhi x.1 hx.1 p
        · exact ((continuousOn_slice_phi hB_K_cont hx.1).mono
            (Set.uIcc_subset_Icc hx.2 hy.2)).intervalIntegrable
      rw [hsub]
      have hnorm := intervalIntegral.norm_integral_le_of_norm_le_const (C := MB)
        (a := x.2) (b := y.2) (f := fun p => B x.1 p) (fun p hp =>
          hMB (x.1, p) ⟨hx.1, Set.uIcc_subset_Icc hx.2 hy.2 (Set.uIoc_subset_uIcc hp)⟩)
      simpa [Real.norm_eq_abs, abs_sub_comm] using hnorm
    simp only [Function.uncurry, Real.dist_eq]
    have htri : |Φ y.1 y.2 - Φ x.1 x.2| ≤ |Φ y.1 y.2 - Φ x.1 y.2| + |Φ x.1 y.2 - Φ x.1 x.2| := by
      simpa [sub_add_sub_cancel] using abs_add_le (Φ y.1 y.2 - Φ x.1 y.2) (Φ x.1 y.2 - Φ x.1 x.2)
    have hx1 : |y.1 - x.1| < ε' / L := lt_of_le_of_lt (le_max_left _ _) hdist
    have hx2 : |y.2 - x.2| < ε' / L := lt_of_le_of_lt (le_max_right _ _) hdist
    have hbound1 : MA * |y.1 - x.1| ≤ MA * (ε' / L) := mul_le_mul_of_nonneg_left hx1.le hMA_nn
    have hbound2 : MB * |y.2 - x.2| ≤ MB * (ε' / L) := mul_le_mul_of_nonneg_left hx2.le hMB_nn
    have hfinal : (MA + MB) * (ε' / L) < ε' := by
      rw [mul_div_assoc', div_lt_iff₀ hL_pos]
      simp only [L]; nlinarith
    linarith

  -- Divergence / energy identity on `[ε, π - ε] × [0, 2π]`
  let Jt : ℝ → ℝ → ℝ := fun θ φ => Real.sin θ * (u θ φ * dTheta v θ φ - v θ φ * dTheta u θ φ)
  let Jp : ℝ → ℝ → ℝ := fun θ φ => (Real.sin θ)⁻¹ * (u θ φ * dPhi v θ φ - v θ φ * dPhi u θ φ)
  let P : ℝ → ℝ → ℝ := fun θ φ => Φ θ φ * Jt θ φ
  let Q : ℝ → ℝ → ℝ := fun θ φ => Φ θ φ * Jp θ φ
  let E : ℝ → ℝ → ℝ := fun θ φ =>
    Real.sin θ * r2 θ φ * A θ φ ^ 2 + (Real.sin θ)⁻¹ * r2 θ φ * B θ φ ^ 2
  have hsin_ut_c1 : ContDiff ℝ 1 (Function.uncurry (fun t p => Real.sin t * dTheta u t p)) :=
    (Real.contDiff_sin.comp contDiff_fst).mul hu_t_c1
  have hsin_vt_c1 : ContDiff ℝ 1 (Function.uncurry (fun t p => Real.sin t * dTheta v t p)) :=
    (Real.contDiff_sin.comp contDiff_fst).mul hv_t_c1
  have hJt_deriv : ∀ θ φ,
      HasDerivAt (fun t => Jt t φ)
        (u θ φ * dTheta (fun t p => Real.sin t * dTheta v t p) θ φ -
         v θ φ * dTheta (fun t p => Real.sin t * dTheta u t p) θ φ) θ := by
    intro θ φ
    have h1 := (hasDerivAt_theta hu θ φ).mul (hasDerivAt_theta_of_c1 hsin_vt_c1 θ φ)
    have h2 := (hasDerivAt_theta hv θ φ).mul (hasDerivAt_theta_of_c1 hsin_ut_c1 θ φ)
    have heq : (fun t => Jt t φ) =
        (fun t => u t φ * (Real.sin t * dTheta v t φ) - v t φ * (Real.sin t * dTheta u t φ)) := by
      funext t; simp only [Jt]; ring
    rw [heq]; convert h1.sub h2 using 1; ring
  have hJp_deriv : ∀ θ φ,
      HasDerivAt (fun p => Jp θ p)
        ((Real.sin θ)⁻¹ * (u θ φ * dPhi (dPhi v) θ φ - v θ φ * dPhi (dPhi u) θ φ)) φ := by
    intro θ φ
    have h1 := (hasDerivAt_phi hu θ φ).mul (hasDerivAt_phi_of_c1 hv_p_c1 θ φ)
    have h2 := (hasDerivAt_phi hv θ φ).mul (hasDerivAt_phi_of_c1 hu_p_c1 θ φ)
    convert (h1.sub h2).const_mul (Real.sin θ)⁻¹ using 1; ring
  let dP : ℝ → ℝ → ℝ := fun θ φ =>
    A θ φ * Jt θ φ + Φ θ φ * (u θ φ * dTheta (fun t p => Real.sin t * dTheta v t p) θ φ -
      v θ φ * dTheta (fun t p => Real.sin t * dTheta u t p) θ φ)
  let dQ : ℝ → ℝ → ℝ := fun θ φ =>
    B θ φ * Jp θ φ + Φ θ φ * ((Real.sin θ)⁻¹ * (u θ φ * dPhi (dPhi v) θ φ -
      v θ φ * dPhi (dPhi u) θ φ))
  have hE_eq : ∀ θ ∈ Set.Ioo (0 : ℝ) Real.pi, ∀ φ : ℝ, E θ φ = dP θ φ + dQ θ φ := by
    intro θ hθ φ
    have hr : r2 θ φ ≠ 0 := (hr2_pos θ ⟨hθ.1.le, hθ.2.le⟩ φ).ne'
    have hdiv : (u θ φ * dTheta (fun t p => Real.sin t * dTheta v t p) θ φ -
        v θ φ * dTheta (fun t p => Real.sin t * dTheta u t p) θ φ) +
        (Real.sin θ)⁻¹ * (u θ φ * dPhi (dPhi v) θ φ - v θ φ * dPhi (dPhi u) θ φ) = 0 := by
      linear_combination u θ φ * hv_lap θ hθ φ - v θ φ * hu_lap θ hθ φ
    have hA_mul : r2 θ φ * A θ φ = u θ φ * dTheta v θ φ - v θ φ * dTheta u θ φ := by
      simp only [A]; field_simp [hr]
    have hB_mul : r2 θ φ * B θ φ = u θ φ * dPhi v θ φ - v θ φ * dPhi u θ φ := by
      simp only [B]; field_simp [hr]
    simp only [E, dP, dQ, Jt, Jp]
    rw [← hA_mul, ← hB_mul]
    linear_combination -Φ θ φ * hdiv

  have hdt_sin_u_cont := continuous_dTheta_of_c1 hsin_ut_c1
  have hdt_sin_v_cont := continuous_dTheta_of_c1 hsin_vt_c1
  have hdp2_u_cont := continuous_dPhi_of_c1 hu_p_c1
  have hdp2_v_cont := continuous_dPhi_of_c1 hv_p_c1
  have hJt_cont : Continuous (Function.uncurry Jt) :=
    (Real.continuous_sin.comp continuous_fst).mul
      ((hu.continuous.mul hv_t_c1.continuous).sub (hv.continuous.mul hu_t_c1.continuous))
  have hdP_contOn : ContinuousOn (Function.uncurry dP)
      (Set.Icc (0 : ℝ) Real.pi ×ˢ Set.Icc (0 : ℝ) (2 * Real.pi)) :=
    (hA_K_cont.mul hJt_cont.continuousOn).add
      (hΦ_contOn.mul ((hu.continuous.mul hdt_sin_v_cont).sub (hv.continuous.mul hdt_sin_u_cont)).continuousOn)
  have hE_contOn : ContinuousOn (Function.uncurry E)
      (Set.Ioo (0 : ℝ) Real.pi ×ˢ Set.Icc (0 : ℝ) (2 * Real.pi)) := by
    have hsin_inv : ContinuousOn (fun x : ℝ × ℝ => (Real.sin x.1)⁻¹)
        (Set.Ioo (0 : ℝ) Real.pi ×ˢ Set.Icc (0 : ℝ) (2 * Real.pi)) :=
      (Real.continuous_sin.comp continuous_fst).continuousOn.inv₀
        (fun x hx => (Real.sin_pos_of_pos_of_lt_pi hx.1.1 hx.1.2).ne')
    have hsub : Set.Ioo (0 : ℝ) Real.pi ×ˢ Set.Icc (0 : ℝ) (2 * Real.pi) ⊆
        Set.Icc (0 : ℝ) Real.pi ×ˢ Set.Icc (0 : ℝ) (2 * Real.pi) :=
      Set.prod_mono Set.Ioo_subset_Icc_self Set.Subset.rfl
    exact (((Real.continuous_sin.comp continuous_fst).continuousOn.mul hr2_c2.continuous.continuousOn).mul
      ((hA_K_cont.mono hsub).pow 2)).add
      ((hsin_inv.mul hr2_c2.continuous.continuousOn).mul ((hB_K_cont.mono hsub).pow 2))

  obtain ⟨MP, hMP⟩ := (isCompact_Icc.prod isCompact_Icc).exists_bound_of_continuousOn
    (hΦ_contOn.mul ((hu.continuous.mul hv_t_c1.continuous).sub
      (hv.continuous.mul hu_t_c1.continuous)).continuousOn)
  have hMP_nn : 0 ≤ MP :=
    le_trans (norm_nonneg _) (hMP (0, 0) ⟨⟨le_rfl, Real.pi_pos.le⟩, ⟨le_rfl, by positivity⟩⟩)

  have hE_bound : ∀ ε : ℝ, 0 < ε → ε < Real.pi / 2 →
      ∫ θ in ε..(Real.pi - ε), ∫ φ in (0 : ℝ)..(2 * Real.pi), E θ φ ≤
        (4 * Real.pi * MP) * Real.sin ε := by
    intro ε hε hε_lt
    have hε_le : ε ≤ Real.pi - ε := by linarith
    have h2pi_nn : (0 : ℝ) ≤ 2 * Real.pi := by positivity
    have hsub_oo : Set.Icc ε (Real.pi - ε) ⊆ Set.Ioo (0 : ℝ) Real.pi :=
      fun t ht => ⟨lt_of_lt_of_le hε ht.1, by linarith [ht.2]⟩
    have hsub_cc : Set.Icc ε (Real.pi - ε) ⊆ Set.Icc (0 : ℝ) Real.pi :=
      fun t ht => ⟨(lt_of_lt_of_le hε ht.1).le, by linarith [ht.2]⟩
    have hinner_eq : ∀ θ ∈ Set.Icc ε (Real.pi - ε),
        ∫ φ in (0 : ℝ)..(2 * Real.pi), E θ φ = ∫ φ in (0 : ℝ)..(2 * Real.pi), dP θ φ := by
      intro θ hθ
      have hθ_oo := hsub_oo hθ
      have hθ_cc := hsub_cc hθ
      have hdP_int : IntervalIntegrable (fun φ => dP θ φ) volume 0 (2 * Real.pi) :=
        ((continuousOn_slice_phi hdP_contOn hθ_cc).mono (by rw [Set.uIcc_of_le h2pi_nn])).intervalIntegrable
      have hdQ_cont : ContinuousOn (fun φ => dQ θ φ) (Set.Icc (0 : ℝ) (2 * Real.pi)) :=
        ((continuousOn_slice_phi hB_K_cont hθ_cc).mul
          (continuous_const.mul (((hu.continuous.comp (continuous_const.prodMk continuous_id)).mul
            (hv_p_c1.continuous.comp (continuous_const.prodMk continuous_id))).sub
            ((hv.continuous.comp (continuous_const.prodMk continuous_id)).mul
            (hu_p_c1.continuous.comp (continuous_const.prodMk continuous_id))))).continuousOn).add
        ((continuousOn_slice_phi hΦ_contOn hθ_cc).mul
          (continuous_const.mul (((hu.continuous.comp (continuous_const.prodMk continuous_id)).mul
            (hdp2_v_cont.comp (continuous_const.prodMk continuous_id))).sub
            ((hv.continuous.comp (continuous_const.prodMk continuous_id)).mul
            (hdp2_u_cont.comp (continuous_const.prodMk continuous_id))))).continuousOn)
      have hdQ_int : IntervalIntegrable (fun φ => dQ θ φ) volume 0 (2 * Real.pi) :=
        (hdQ_cont.mono (by rw [Set.uIcc_of_le h2pi_nn])).intervalIntegrable
      have hQ_zero : ∫ φ in (0 : ℝ)..(2 * Real.pi), dQ θ φ = 0 := by
        have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt
          (f := fun p => Q θ p) (a := (0 : ℝ)) (b := 2 * Real.pi)
          (fun p _ => (hΦ_dPhi θ hθ_cc p).mul (hJp_deriv θ p)) hdQ_int
        have hQ_per : Q θ (2 * Real.pi) = Q θ 0 := by
          have : (2 * Real.pi : ℝ) = 0 + 2 * Real.pi := by ring
          rw [this]
          simp only [Q, Jp, hΦ_per, hu_per, hv_per, dPhi_per_2pi hu_per, dPhi_per_2pi hv_per]
        linarith
      have hcongr : ∫ φ in (0 : ℝ)..(2 * Real.pi), E θ φ =
          ∫ φ in (0 : ℝ)..(2 * Real.pi), (dP θ φ + dQ θ φ) :=
        intervalIntegral.integral_congr (fun p _ => hE_eq θ hθ_oo p)
      rw [hcongr, intervalIntegral.integral_add hdP_int hdQ_int, hQ_zero, add_zero]
    rw [intervalIntegral.integral_congr (fun θ hθ => hinner_eq θ (by rwa [Set.uIcc_of_le hε_le] at hθ))]
    have hdP_box_cont : ContinuousOn (Function.uncurry dP)
        (Set.Icc ε (Real.pi - ε) ×ˢ Set.Icc (0 : ℝ) (2 * Real.pi)) :=
      hdP_contOn.mono (Set.prod_mono hsub_cc Set.Subset.rfl)
    rw [MeasureTheory.intervalIntegral_intervalIntegral_swap
      (integrableOn_uIoc_prod_of_continuousOn hε_le h2pi_nn hdP_box_cont)]
    have hftc_P : ∀ φ ∈ Set.Icc (0 : ℝ) (2 * Real.pi),
        ∫ θ in ε..(Real.pi - ε), dP θ φ = P (Real.pi - ε) φ - P ε φ := fun φ hφ =>
      intervalIntegral.integral_eq_sub_of_hasDerivAt
        (fun θ hθ => (hΦ_dTheta θ (hsub_cc (by rwa [Set.uIcc_of_le hε_le] at hθ)) φ).mul (hJt_deriv θ φ))
        (((continuousOn_slice_theta hdP_box_cont hφ).mono (by rw [Set.uIcc_of_le hε_le])).intervalIntegrable)
    rw [intervalIntegral.integral_congr (fun φ hφ => hftc_P φ (by rwa [Set.uIcc_of_le h2pi_nn] at hφ))]
    have hsin_pos : 0 ≤ Real.sin ε := (Real.sin_pos_of_pos_of_lt_pi hε (by linarith)).le
    have hP_le : ∀ φ ∈ Set.Icc (0 : ℝ) (2 * Real.pi),
        P (Real.pi - ε) φ - P ε φ ≤ 2 * MP * Real.sin ε := by
      intro φ hφ
      have h1 : |P (Real.pi - ε) φ| ≤ MP * Real.sin ε := by
        have hb := hMP (Real.pi - ε, φ) ⟨⟨by linarith, by linarith⟩, hφ⟩
        simp only [Real.norm_eq_abs, Pi.mul_apply, Pi.sub_apply, Function.uncurry] at hb
        have heq : P (Real.pi - ε) φ = Real.sin ε * (Φ (Real.pi - ε) φ *
            (u (Real.pi - ε) φ * dTheta v (Real.pi - ε) φ -
              v (Real.pi - ε) φ * dTheta u (Real.pi - ε) φ)) := by
          simp only [P, Jt, Real.sin_pi_sub]; ring
        rw [heq, abs_mul, abs_of_nonneg hsin_pos]; nlinarith
      have h2 : |P ε φ| ≤ MP * Real.sin ε := by
        have hb := hMP (ε, φ) ⟨⟨hε.le, by linarith⟩, hφ⟩
        simp only [Real.norm_eq_abs, Pi.mul_apply, Pi.sub_apply, Function.uncurry] at hb
        have heq : P ε φ = Real.sin ε * (Φ ε φ *
            (u ε φ * dTheta v ε φ - v ε φ * dTheta u ε φ)) := by
          simp only [P, Jt]; ring
        rw [heq, abs_mul, abs_of_nonneg hsin_pos]; nlinarith
      linarith [(abs_le.mp h1).2, (abs_le.mp h2).1]
    have hP_diff_int : IntervalIntegrable (fun φ => P (Real.pi - ε) φ - P ε φ) volume 0 (2 * Real.pi) :=
      ((((continuousOn_slice_phi hΦ_contOn ⟨by linarith, by linarith⟩).mul
          (hJt_cont.comp (continuous_const.prodMk continuous_id)).continuousOn).sub
        ((continuousOn_slice_phi hΦ_contOn ⟨hε.le, by linarith⟩).mul
          (hJt_cont.comp (continuous_const.prodMk continuous_id)).continuousOn)).mono
        (by rw [Set.uIcc_of_le h2pi_nn])).intervalIntegrable
    have hmono := intervalIntegral.integral_mono_on h2pi_nn hP_diff_int intervalIntegrable_const hP_le
    have hconst : ∫ _ in (0 : ℝ)..(2 * Real.pi), (2 * MP * Real.sin ε) =
        (4 * Real.pi * MP) * Real.sin ε := by simp; ring
    linarith

  have hE_nonneg : ∀ θ ∈ Set.Ioo (0 : ℝ) Real.pi, ∀ φ ∈ Set.Icc (0 : ℝ) (2 * Real.pi), 0 ≤ E θ φ := by
    intro θ hθ φ _
    have hs := Real.sin_pos_of_pos_of_lt_pi hθ.1 hθ.2
    have hr := hr2_pos θ ⟨hθ.1.le, hθ.2.le⟩ φ
    have h1 : 0 ≤ Real.sin θ * r2 θ φ * A θ φ ^ 2 := by positivity
    have h2 : 0 ≤ (Real.sin θ)⁻¹ * r2 θ φ * B θ φ ^ 2 := by positivity
    linarith

  have hE_zero := eq_zero_of_integral_le_mul_sin hE_contOn hE_nonneg
    (by positivity : 0 ≤ 4 * Real.pi * MP) hE_bound

  intro θ hθ φ
  have h2pi : 0 < 2 * Real.pi := by positivity
  let k : ℤ := ⌊φ / (2 * Real.pi)⌋
  let φ' : ℝ := φ - (k : ℝ) * (2 * Real.pi)
  have hφ'_mem : φ' ∈ Set.Icc (0 : ℝ) (2 * Real.pi) := by
    have hfl := Int.floor_le (φ / (2 * Real.pi))
    have hlt := Int.lt_floor_add_one (φ / (2 * Real.pi))
    constructor
    · have : (k : ℝ) * (2 * Real.pi) ≤ φ := (le_div_iff₀ h2pi).mp hfl
      linarith
    · have : φ < ((k : ℝ) + 1) * (2 * Real.pi) := (div_lt_iff₀ h2pi).mp hlt
      linarith
  have hEq := hE_zero θ hθ φ' hφ'_mem
  have hs := Real.sin_pos_of_pos_of_lt_pi hθ.1 hθ.2
  have hr := hr2_pos θ ⟨hθ.1.le, hθ.2.le⟩ φ'
  have h1_nn : 0 ≤ Real.sin θ * r2 θ φ' * A θ φ' ^ 2 := by positivity
  have h2_nn : 0 ≤ (Real.sin θ)⁻¹ * r2 θ φ' * B θ φ' ^ 2 := by positivity
  have hA' : A θ φ' = 0 := sq_eq_zero_iff.mp
    ((mul_eq_zero.mp (by linarith : Real.sin θ * r2 θ φ' * A θ φ' ^ 2 = 0)).resolve_left (mul_pos hs hr).ne')
  have hB' : B θ φ' = 0 := sq_eq_zero_iff.mp
    ((mul_eq_zero.mp (by linarith : (Real.sin θ)⁻¹ * r2 θ φ' * B θ φ' ^ 2 = 0)).resolve_left
      (mul_pos (inv_pos.mpr hs) hr).ne')
  have hφ_eq : φ = φ' + (k : ℝ) * (2 * Real.pi) := by ring
  have hA0 : A θ φ = 0 := by rw [hφ_eq, per_2pi_int hA_per]; exact hA'
  have hB0 : B θ φ = 0 := by rw [hφ_eq, per_2pi_int hB_per]; exact hB'
  have hr_phi : r2 θ φ ≠ 0 := (hr2_pos θ ⟨hθ.1.le, hθ.2.le⟩ φ).ne'
  simp only [A, B, div_eq_zero_iff] at hA0 hB0
  exact ⟨hA0.resolve_right hr_phi, hB0.resolve_right hr_phi⟩

/-- **Lemma 2 (Zeros of Complex Spherical Harmonics on `S²`)**:
Let `u, v : ℝ → ℝ → ℝ` be `C²` functions representing the real and imaginary parts of a
complex eigenfunction of the spherical Laplacian with eigenvalue `λ > 0`:
- `2π`-periodic in `φ`,
- constant in `φ` at the north pole `θ = 0`,
- satisfying `∂_θ (sin θ ∂_θ w) + (1 / sin θ) ∂_φ² w = -λ sin θ · w` on `(0, π) × ℝ` for `w = u, v`.

Then `u` and `v` must vanish simultaneously at some point `(θ_*, φ_*) ∈ [0, π] × [0, 2π]`. -/
theorem spherical_harmonic_has_zero
    {u v : ℝ → ℝ → ℝ} {lam : ℝ}
    (hlam : 0 < lam)
    (hu : ContDiff ℝ 2 (Function.uncurry u))
    (hv : ContDiff ℝ 2 (Function.uncurry v))
    (hu_per : ∀ θ φ, u θ (φ + 2 * Real.pi) = u θ φ)
    (hv_per : ∀ θ φ, v θ (φ + 2 * Real.pi) = v θ φ)
    (hu_pole : ∀ φ, u 0 φ = u 0 0)
    (hv_pole : ∀ φ, v 0 φ = v 0 0)
    (hu_lap : ∀ θ ∈ Set.Ioo (0 : ℝ) Real.pi, ∀ φ : ℝ,
      dTheta (fun t p => Real.sin t * dTheta u t p) θ φ +
        (Real.sin θ)⁻¹ * dPhi (dPhi u) θ φ = -lam * Real.sin θ * u θ φ)
    (hv_lap : ∀ θ ∈ Set.Ioo (0 : ℝ) Real.pi, ∀ φ : ℝ,
      dTheta (fun t p => Real.sin t * dTheta v t p) θ φ +
        (Real.sin θ)⁻¹ * dPhi (dPhi v) θ φ = -lam * Real.sin θ * v θ φ) :
    ∃ θ ∈ Set.Icc (0 : ℝ) Real.pi, ∃ φ ∈ Set.Icc (0 : ℝ) (2 * Real.pi),
      u θ φ = 0 ∧ v θ φ = 0 := by
  by_contra hno
  push Not at hno
  let r2 : ℝ → ℝ → ℝ := fun θ φ => u θ φ ^ 2 + v θ φ ^ 2
  have hr2_pos : ∀ θ ∈ Set.Icc (0 : ℝ) Real.pi, ∀ φ : ℝ, 0 < r2 θ φ := by
    intro θ hθ φ
    have h2pi : 0 < 2 * Real.pi := by positivity
    let k : ℤ := ⌊φ / (2 * Real.pi)⌋
    let φ' : ℝ := φ - (k : ℝ) * (2 * Real.pi)
    have hφ'_mem : φ' ∈ Set.Icc (0 : ℝ) (2 * Real.pi) := by
      have hfl := Int.floor_le (φ / (2 * Real.pi))
      have hlt := Int.lt_floor_add_one (φ / (2 * Real.pi))
      constructor
      · have : (k : ℝ) * (2 * Real.pi) ≤ φ := (le_div_iff₀ h2pi).mp hfl
        linarith
      · have : φ < ((k : ℝ) + 1) * (2 * Real.pi) := (div_lt_iff₀ h2pi).mp hlt
        linarith
    have hφ_eq : φ = φ' + (k : ℝ) * (2 * Real.pi) := by ring
    have hu_eq : u θ φ = u θ φ' := by rw [hφ_eq, per_2pi_int hu_per]
    have hv_eq : v θ φ = v θ φ' := by rw [hφ_eq, per_2pi_int hv_per]
    have hne := hno θ hθ φ' hφ'_mem
    simp only [r2, hu_eq, hv_eq]
    by_cases hu0 : u θ φ' = 0
    · have hv0 : v θ φ' ≠ 0 := hne hu0
      positivity
    · have : 0 < u θ φ' ^ 2 := sq_pos_of_ne_zero hu0
      have : 0 ≤ v θ φ' ^ 2 := sq_nonneg _
      linarith

  -- Step 1–2: Current vanishes everywhere on `(0, π) × ℝ`.
  have hcur := current_eq_zero_of_nonvanishing hu hv hu_per hv_per hu_pole hv_pole hu_lap hv_lap hr2_pos

  -- Step 3: Normalized phase `(u / √r2, v / √r2)` is constant `(c₁, c₂)` on `(0, π) × ℝ`.
  let cu : ℝ → ℝ → ℝ := fun θ φ => u θ φ / Real.sqrt (r2 θ φ)
  let cv : ℝ → ℝ → ℝ := fun θ φ => v θ φ / Real.sqrt (r2 θ φ)

  have hcu_dt : ∀ θ ∈ Set.Ioo (0 : ℝ) Real.pi, ∀ φ : ℝ, HasDerivAt (fun t => cu t φ) 0 θ :=
    fun θ hθ φ => hasDerivAt_div_sqrt_sum_sq (hasDerivAt_theta hu θ φ) (hasDerivAt_theta hv θ φ)
      (hr2_pos θ ⟨hθ.1.le, hθ.2.le⟩ φ) (hcur θ hθ φ).1

  have hcv_dt : ∀ θ ∈ Set.Ioo (0 : ℝ) Real.pi, ∀ φ : ℝ, HasDerivAt (fun t => cv t φ) 0 θ := by
    intro θ hθ φ
    have h := hasDerivAt_div_sqrt_sum_sq (hasDerivAt_theta hv θ φ) (hasDerivAt_theta hu θ φ)
      (by rw [add_comm]; exact hr2_pos θ ⟨hθ.1.le, hθ.2.le⟩ φ)
      (by linarith [(hcur θ hθ φ).1])
    have heq : (fun t => v t φ / Real.sqrt (v t φ ^ 2 + u t φ ^ 2)) = (fun t => cv t φ) := by
      funext t; simp only [cv, r2, add_comm]
    rwa [heq] at h

  have hcu_dp : ∀ θ ∈ Set.Ioo (0 : ℝ) Real.pi, ∀ φ : ℝ, HasDerivAt (fun p => cu θ p) 0 φ :=
    fun θ hθ φ => hasDerivAt_div_sqrt_sum_sq (hasDerivAt_phi hu θ φ) (hasDerivAt_phi hv θ φ)
      (hr2_pos θ ⟨hθ.1.le, hθ.2.le⟩ φ) (hcur θ hθ φ).2

  have hcv_dp : ∀ θ ∈ Set.Ioo (0 : ℝ) Real.pi, ∀ φ : ℝ, HasDerivAt (fun p => cv θ p) 0 φ := by
    intro θ hθ φ
    have h := hasDerivAt_div_sqrt_sum_sq (hasDerivAt_phi hv θ φ) (hasDerivAt_phi hu θ φ)
      (by rw [add_comm]; exact hr2_pos θ ⟨hθ.1.le, hθ.2.le⟩ φ)
      (by linarith [(hcur θ hθ φ).2])
    have heq : (fun p => v θ p / Real.sqrt (v θ p ^ 2 + u θ p ^ 2)) = (fun p => cv θ p) := by
      funext p; simp only [cv, r2, add_comm]
    rwa [heq] at h

  let c₁ : ℝ := cu (Real.pi / 2) 0
  let c₂ : ℝ := cv (Real.pi / 2) 0
  have hpi2_oo : Real.pi / 2 ∈ Set.Ioo (0 : ℝ) Real.pi := ⟨by positivity, by linarith [Real.pi_pos]⟩

  have hcu_const : ∀ θ ∈ Set.Ioo (0 : ℝ) Real.pi, ∀ φ : ℝ, cu θ φ = c₁ := by
    intro θ hθ φ
    have h1 : cu θ φ = cu (Real.pi / 2) φ := by
      have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt
        (f := fun t => cu t φ) (f' := fun _ => (0 : ℝ)) (a := Real.pi / 2) (b := θ)
        (fun t ht => hcu_dt t ⟨lt_of_lt_of_le (lt_min hpi2_oo.1 hθ.1) ht.1,
          lt_of_le_of_lt ht.2 (max_lt hpi2_oo.2 hθ.2)⟩ φ) intervalIntegrable_const
      simp at hftc; linarith
    have h2 : cu (Real.pi / 2) φ = cu (Real.pi / 2) 0 :=
      is_const_of_deriv_eq_zero (fun p => (hcu_dp _ hpi2_oo p).differentiableAt)
        (fun p => (hcu_dp _ hpi2_oo p).deriv) φ 0
    exact h1.trans h2

  have hcv_const : ∀ θ ∈ Set.Ioo (0 : ℝ) Real.pi, ∀ φ : ℝ, cv θ φ = c₂ := by
    intro θ hθ φ
    have h1 : cv θ φ = cv (Real.pi / 2) φ := by
      have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt
        (f := fun t => cv t φ) (f' := fun _ => (0 : ℝ)) (a := Real.pi / 2) (b := θ)
        (fun t ht => hcv_dt t ⟨lt_of_lt_of_le (lt_min hpi2_oo.1 hθ.1) ht.1,
          lt_of_le_of_lt ht.2 (max_lt hpi2_oo.2 hθ.2)⟩ φ) intervalIntegrable_const
      simp at hftc; linarith
    have h2 : cv (Real.pi / 2) φ = cv (Real.pi / 2) 0 :=
      is_const_of_deriv_eq_zero (fun p => (hcv_dp _ hpi2_oo p).differentiableAt)
        (fun p => (hcv_dp _ hpi2_oo p).deriv) φ 0
    exact h1.trans h2

  -- Step 4: Positive real eigenfunction `w = c₁ u + c₂ v = √r2 > 0` contradicts Laplacian integral!
  let w : ℝ → ℝ → ℝ := fun θ φ => c₁ * u θ φ + c₂ * v θ φ
  have hw_pos : ∀ θ ∈ Set.Ioo (0 : ℝ) Real.pi, ∀ φ : ℝ, 0 < w θ φ := by
    intro θ hθ φ
    have hr_pos := hr2_pos θ ⟨hθ.1.le, hθ.2.le⟩ φ
    have hsq_pos := Real.sqrt_pos.mpr hr_pos
    have hweq : w θ φ = Real.sqrt (r2 θ φ) := by
      simp only [w, ← hcu_const θ hθ φ, ← hcv_const θ hθ φ, cu, cv]
      have hsq : Real.sqrt (r2 θ φ) ^ 2 = r2 θ φ := Real.sq_sqrt hr_pos.le
      field_simp [hsq_pos.ne']; rw [hsq]
    rw [hweq]; exact hsq_pos

  have hu_t_c1 := contDiff_dTheta hu
  have hv_t_c1 := contDiff_dTheta hv
  have hu_p_c1 := contDiff_dPhi hu
  have hv_p_c1 := contDiff_dPhi hv
  have hsin_ut_c1 : ContDiff ℝ 1 (Function.uncurry (fun t p => Real.sin t * dTheta u t p)) :=
    (Real.contDiff_sin.comp contDiff_fst).mul hu_t_c1
  have hsin_vt_c1 : ContDiff ℝ 1 (Function.uncurry (fun t p => Real.sin t * dTheta v t p)) :=
    (Real.contDiff_sin.comp contDiff_fst).mul hv_t_c1

  have hw_c2 : ContDiff ℝ 2 (Function.uncurry w) :=
    (contDiff_const.mul hu).add (contDiff_const.mul hv)
  have hw_t_c1 : ContDiff ℝ 1 (Function.uncurry (dTheta w)) := contDiff_dTheta hw_c2
  have hw_p_c1 : ContDiff ℝ 1 (Function.uncurry (dPhi w)) := contDiff_dPhi hw_c2
  have hsin_wt_c1 : ContDiff ℝ 1 (Function.uncurry (fun t p => Real.sin t * dTheta w t p)) :=
    (Real.contDiff_sin.comp contDiff_fst).mul hw_t_c1
  have hw_per : ∀ θ φ, w θ (φ + 2 * Real.pi) = w θ φ := fun θ φ => by simp [w, hu_per, hv_per]

  have hdTheta_w : ∀ θ φ, dTheta w θ φ = c₁ * dTheta u θ φ + c₂ * dTheta v θ φ := fun θ φ =>
    (((hasDerivAt_theta hu θ φ).const_mul c₁).add ((hasDerivAt_theta hv θ φ).const_mul c₂)).deriv
  have hdPhi_w : ∀ θ φ, dPhi w θ φ = c₁ * dPhi u θ φ + c₂ * dPhi v θ φ := fun θ φ =>
    (((hasDerivAt_phi hu θ φ).const_mul c₁).add ((hasDerivAt_phi hv θ φ).const_mul c₂)).deriv

  have hw_lap : ∀ θ ∈ Set.Ioo (0 : ℝ) Real.pi, ∀ φ : ℝ,
      dTheta (fun t p => Real.sin t * dTheta w t p) θ φ +
        (Real.sin θ)⁻¹ * dPhi (dPhi w) θ φ = -lam * Real.sin θ * w θ φ := by
    intro θ hθ φ
    have h1 : dTheta (fun t p => Real.sin t * dTheta w t p) θ φ =
        c₁ * dTheta (fun t p => Real.sin t * dTheta u t p) θ φ +
        c₂ * dTheta (fun t p => Real.sin t * dTheta v t p) θ φ := by
      have heq : (fun t => Real.sin t * dTheta w t φ) =
          (fun t => c₁ * (Real.sin t * dTheta u t φ) + c₂ * (Real.sin t * dTheta v t φ)) := by
        funext t; rw [hdTheta_w]; ring
      rw [dTheta, heq]
      exact (((hasDerivAt_theta_of_c1 hsin_ut_c1 θ φ).const_mul c₁).add
        ((hasDerivAt_theta_of_c1 hsin_vt_c1 θ φ).const_mul c₂)).deriv
    have h2 : dPhi (dPhi w) θ φ = c₁ * dPhi (dPhi u) θ φ + c₂ * dPhi (dPhi v) θ φ := by
      have heq : (fun p => dPhi w θ p) = (fun p => c₁ * dPhi u θ p + c₂ * dPhi v θ p) := by
        funext p; exact hdPhi_w θ p
      rw [dPhi, heq]
      exact (((hasDerivAt_phi_of_c1 hu_p_c1 θ φ).const_mul c₁).add
        ((hasDerivAt_phi_of_c1 hv_p_c1 θ φ).const_mul c₂)).deriv
    rw [h1, h2]; simp only [w]
    linear_combination c₁ * hu_lap θ hθ φ + c₂ * hv_lap θ hθ φ

  have hdt_sin_w_cont := continuous_dTheta_of_c1 hsin_wt_c1
  have hdp2_w_cont := continuous_dPhi_of_c1 hw_p_c1

  obtain ⟨Mw, hMw⟩ := (isCompact_Icc.prod isCompact_Icc).exists_bound_of_continuousOn
    (hw_t_c1.continuous.continuousOn : ContinuousOn (Function.uncurry (dTheta w))
      (Set.Icc (0 : ℝ) Real.pi ×ˢ Set.Icc (0 : ℝ) (2 * Real.pi)))
  have hMw_nn : 0 ≤ Mw :=
    le_trans (norm_nonneg _) (hMw (0, 0) ⟨⟨le_rfl, Real.pi_pos.le⟩, ⟨le_rfl, by positivity⟩⟩)

  let Fw : ℝ → ℝ → ℝ := fun θ φ => lam * Real.sin θ * w θ φ
  have hFw_cont : ContinuousOn (Function.uncurry Fw)
      (Set.Ioo (0 : ℝ) Real.pi ×ˢ Set.Icc (0 : ℝ) (2 * Real.pi)) :=
    ((continuous_const.mul (Real.continuous_sin.comp continuous_fst)).mul hw_c2.continuous).continuousOn
  have hFw_nonneg : ∀ θ ∈ Set.Ioo (0 : ℝ) Real.pi, ∀ φ ∈ Set.Icc (0 : ℝ) (2 * Real.pi), 0 ≤ Fw θ φ := by
    intro θ hθ φ _
    have hs := Real.sin_pos_of_pos_of_lt_pi hθ.1 hθ.2
    have hw := hw_pos θ hθ φ
    simp only [Fw]; positivity

  have hFw_bound : ∀ ε : ℝ, 0 < ε → ε < Real.pi / 2 →
      ∫ θ in ε..(Real.pi - ε), ∫ φ in (0 : ℝ)..(2 * Real.pi), Fw θ φ ≤
        (4 * Real.pi * Mw) * Real.sin ε := by
    intro ε hε hε_lt
    have hε_le : ε ≤ Real.pi - ε := by linarith
    have h2pi_nn : (0 : ℝ) ≤ 2 * Real.pi := by positivity
    have hsub_oo : Set.Icc ε (Real.pi - ε) ⊆ Set.Ioo (0 : ℝ) Real.pi :=
      fun t ht => ⟨lt_of_lt_of_le hε ht.1, by linarith [ht.2]⟩
    have hinner_eq : ∀ θ ∈ Set.Icc ε (Real.pi - ε),
        ∫ φ in (0 : ℝ)..(2 * Real.pi), Fw θ φ =
        ∫ φ in (0 : ℝ)..(2 * Real.pi), (-dTheta (fun t p => Real.sin t * dTheta w t p) θ φ) := by
      intro θ hθ
      have hθ_oo := hsub_oo hθ
      have h1_int : IntervalIntegrable
          (fun φ => -dTheta (fun t p => Real.sin t * dTheta w t p) θ φ) volume 0 (2 * Real.pi) :=
        (hdt_sin_w_cont.comp (continuous_const.prodMk continuous_id)).neg.intervalIntegrable _ _
      have h2_int : IntervalIntegrable (fun φ => -((Real.sin θ)⁻¹ * dPhi (dPhi w) θ φ))
          volume 0 (2 * Real.pi) :=
        ((continuous_const.mul (hdp2_w_cont.comp (continuous_const.prodMk continuous_id))).neg).intervalIntegrable _ _
      have hdp2_zero : ∫ φ in (0 : ℝ)..(2 * Real.pi), dPhi (dPhi w) θ φ = 0 := by
        have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt
          (a := (0 : ℝ)) (b := 2 * Real.pi)
          (fun p _ => hasDerivAt_phi_of_c1 hw_p_c1 θ p)
          ((hdp2_w_cont.comp (continuous_const.prodMk continuous_id)).intervalIntegrable 0 (2 * Real.pi))
        have hper : dPhi w θ (2 * Real.pi) = dPhi w θ 0 := by
          have : (2 * Real.pi : ℝ) = 0 + 2 * Real.pi := by ring
          rw [this, dPhi_per_2pi hw_per]
        linarith
      have h2_zero : ∫ φ in (0 : ℝ)..(2 * Real.pi), -((Real.sin θ)⁻¹ * dPhi (dPhi w) θ φ) = 0 := by
        rw [intervalIntegral.integral_neg, intervalIntegral.integral_const_mul, hdp2_zero]; ring
      have hcongr : ∫ φ in (0 : ℝ)..(2 * Real.pi), Fw θ φ =
          ∫ φ in (0 : ℝ)..(2 * Real.pi),
            (-dTheta (fun t p => Real.sin t * dTheta w t p) θ φ +
             -((Real.sin θ)⁻¹ * dPhi (dPhi w) θ φ)) :=
        intervalIntegral.integral_congr fun φ _ => by
          have hl := hw_lap θ hθ_oo φ; simp only [Fw]; linarith
      rw [hcongr, intervalIntegral.integral_add h1_int h2_int, h2_zero, add_zero]
    rw [intervalIntegral.integral_congr (fun θ hθ => hinner_eq θ (by rwa [Set.uIcc_of_le hε_le] at hθ))]
    have hneg_cont : ContinuousOn
        (Function.uncurry (fun t p => -dTheta (fun t' p' => Real.sin t' * dTheta w t' p') t p))
        (Set.Icc ε (Real.pi - ε) ×ˢ Set.Icc (0 : ℝ) (2 * Real.pi)) :=
      hdt_sin_w_cont.neg.continuousOn
    rw [MeasureTheory.intervalIntegral_intervalIntegral_swap
      (integrableOn_uIoc_prod_of_continuousOn hε_le h2pi_nn hneg_cont)]
    have hftc_w : ∀ φ : ℝ,
        ∫ θ in ε..(Real.pi - ε), (-dTheta (fun t p => Real.sin t * dTheta w t p) θ φ) =
        Real.sin ε * dTheta w ε φ - Real.sin (Real.pi - ε) * dTheta w (Real.pi - ε) φ := by
      intro φ
      rw [intervalIntegral.integral_neg]
      have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt
        (a := ε) (b := Real.pi - ε)
        (fun θ _ => hasDerivAt_theta_of_c1 hsin_wt_c1 θ φ)
        ((hdt_sin_w_cont.comp (continuous_id.prodMk continuous_const)).intervalIntegrable ε (Real.pi - ε))
      linarith
    simp_rw [hftc_w]
    have hsin_pos : 0 ≤ Real.sin ε := (Real.sin_pos_of_pos_of_lt_pi hε (by linarith)).le
    have hle : ∀ φ ∈ Set.Icc (0 : ℝ) (2 * Real.pi),
        Real.sin ε * dTheta w ε φ - Real.sin (Real.pi - ε) * dTheta w (Real.pi - ε) φ ≤
          2 * Mw * Real.sin ε := by
      intro φ hφ
      have h1 : |dTheta w ε φ| ≤ Mw := by
        simpa [Real.norm_eq_abs] using hMw (ε, φ) ⟨⟨hε.le, by linarith⟩, hφ⟩
      have h2 : |dTheta w (Real.pi - ε) φ| ≤ Mw := by
        simpa [Real.norm_eq_abs] using hMw (Real.pi - ε, φ) ⟨⟨by linarith, by linarith⟩, hφ⟩
      rw [Real.sin_pi_sub]
      nlinarith [(abs_le.mp h1).2, (abs_le.mp h2).1]
    have hint_diff : IntervalIntegrable
        (fun φ => Real.sin ε * dTheta w ε φ - Real.sin (Real.pi - ε) * dTheta w (Real.pi - ε) φ)
        volume 0 (2 * Real.pi) :=
      ((continuous_const.mul (hw_t_c1.continuous.comp (continuous_const.prodMk continuous_id))).sub
        (continuous_const.mul (hw_t_c1.continuous.comp (continuous_const.prodMk continuous_id)))).intervalIntegrable _ _
    have hmono := intervalIntegral.integral_mono_on h2pi_nn hint_diff intervalIntegrable_const hle
    have hconst : ∫ _ in (0 : ℝ)..(2 * Real.pi), (2 * Mw * Real.sin ε) =
        (4 * Real.pi * Mw) * Real.sin ε := by simp; ring
    linarith

  have hFw_zero := eq_zero_of_integral_le_mul_sin hFw_cont hFw_nonneg
    (by positivity : 0 ≤ 4 * Real.pi * Mw) hFw_bound
  have hcontra := hFw_zero (Real.pi / 2) hpi2_oo 0 ⟨le_rfl, by positivity⟩
  have hpos_val : 0 < Fw (Real.pi / 2) 0 := by
    simp only [Fw, Real.sin_pi_div_two, mul_one]
    exact mul_pos hlam (hw_pos (Real.pi / 2) hpi2_oo 0)
  linarith

end SU2Wigner

end
