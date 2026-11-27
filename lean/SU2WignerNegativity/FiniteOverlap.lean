import SU2WignerNegativity.DiagonalKernel
import SU2WignerNegativity.SphereMoments

/-! # A finite overlap test for a diagonal kernel

Real polarization expands every pure-state expectation as a real linear
combination of expectations on basis vectors and two-term superpositions.
The same expansion applies to the target Hilbert-space overlap.
-/

open Complex Finset Matrix
noncomputable section
namespace SU2Wigner

private abbrev Component (N : ℕ) := Fin (N+1) × Bool
private def direction {N : ℕ} (i : Component N) : Fin (N+1) → ℂ :=
  Pi.single i.1 (if i.2 then I else 1)
private def coord {N : ℕ} (ψ : Fin (N+1) → ℂ) (i : Component N) : ℝ :=
  if i.2 then (ψ i.1).im else (ψ i.1).re

/-- An index for the finite list of unnormalized probe states. -/
abbrev Probe (N : ℕ) := (Fin (N+1) × Bool) × (Fin (N+1) × Bool) × Bool

def probeState {N : ℕ} (p : Probe N) : Fin (N+1) → ℂ :=
  if p.2.2 then direction p.1 + direction p.2.1 else direction p.1

private def weight {N : ℕ} (ψ : Fin (N+1) → ℂ) (p : Probe N) : ℝ :=
  (coord ψ p.1 * coord ψ p.2.1) * (if p.2.2 then 1/2 else -1)

private theorem dot_coords {N : ℕ} (v ψ : Fin (N+1) → ℂ) :
    dotProduct v ψ = ∑ i : Component N, (coord ψ i : ℂ) * dotProduct v (direction i) := by
  simp only [Fintype.sum_prod_type, Fintype.sum_bool, coord, direction, dotProduct_single]
  apply Finset.sum_congr rfl
  intro i _
  conv_lhs => rhs; rw [← Complex.re_add_im (ψ i)]
  simp only [ite_true, Bool.false_eq_true, ite_false, mul_one]
  ring

private theorem real_polarization {ι : Type*} [Fintype ι] (r : ι → ℝ) (z : ι → ℂ) :
    normSq (∑ i, (r i : ℂ)*z i) =
      ∑ i, ∑ j, r i*r j*(normSq (z i+z j)/2 - normSq (z i)) := by
  have h (i j : ι) : r i*r j*(normSq (z i+z j)/2 - normSq (z i)) =
      (r i*(z i).re)*(r j*(z j).re) + (r i*(z i).im)*(r j*(z j).im) +
      (r i*r j*normSq (z j) - r i*r j*normSq (z i))/2 := by
    simp [Complex.normSq_apply]; ring
  have hswap : (∑ i, ∑ j, r i*r j*normSq (z j)) = ∑ i, ∑ j, r i*r j*normSq (z i) := by
    rw [Finset.sum_comm]; simp [mul_comm (r _) (r _)]
  simp only [h, Complex.normSq_apply, Complex.re_sum, Complex.im_sum, Complex.mul_re,
    Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, add_zero,
    Finset.sum_add_distrib, ← Finset.sum_div, Finset.sum_sub_distrib] at *
  rw [hswap, sub_self, zero_div, add_zero]
  simp only [Finset.sum_mul, Finset.mul_sum]
  congr 1 <;> apply Finset.sum_congr rfl <;> intro i _ <;> apply Finset.sum_congr rfl <;> intro j _ <;> ring

private theorem expand_normSq {N : ℕ} (v ψ : Fin (N+1) → ℂ) :
    normSq (dotProduct v ψ) =
      ∑ p : Probe N, weight ψ p * normSq (dotProduct v (probeState p)) := by
  rw [dot_coords, real_polarization]
  conv_rhs => rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl; intro i _
  conv_rhs => rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl; intro j _
  simp only [Fintype.sum_bool, weight, probeState, Bool.false_eq_true,
    ite_false, ite_true, dotProduct_add]
  ring

private theorem symbol_expansion {N : ℕ} (d : Fin (N+1) → ℝ) (ψ : Fin (N+1) → ℂ) (u : S2) :
    diagonalSymbol N d ψ u = ∑ p : Probe N, weight ψ p * diagonalSymbol N d (probeState p) u := by
  obtain ⟨θ, _, φ, rfl⟩ := sphVec_surjective u
  rw [← SU2.actS2_rotZ_rotY_northPole]
  simp_rw [diagonalSymbol_rotated, Matrix.mulVec]
  conv_lhs => enter [2,k,2]; rw [expand_normSq]
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro p _
  apply Finset.sum_congr rfl; intro k _
  ring

private theorem overlap_expansion {N : ℕ} (φ ψ : Fin (N+1) → ℂ) :
    normSq (innerC φ ψ) = ∑ p : Probe N, weight ψ p * normSq (innerC φ (probeState p)) :=
  expand_normSq (fun i => star (φ i)) ψ

private theorem overlap_symm {N : ℕ} (φ ψ : Fin (N+1) → ℂ) :
    normSq (innerC φ ψ) = normSq (innerC ψ φ) := by
  rw [← innerC_conj_symm, RCLike.star_def, Complex.normSq_conj]

private theorem swIntegral_const_mul (N : ℕ) (a : ℝ) (f : S2 → ℝ) :
    swIntegral N (fun u => a * f u) = a * swIntegral N f := by
  unfold swIntegral sphereAvg
  simp_rw [mul_left_comm (Real.sin _) a, intervalIntegral.integral_const_mul]
  ring

/-- Exact self-duality on the finite probe list implies the overlap law on all states. -/
theorem tracial_of_probe_overlap {N : ℕ} (d : Fin (N+1) → ℝ)
    (h : ∀ p q : Probe N,
      swIntegral N (fun u => diagonalSymbol N d (probeState p) u * diagonalSymbol N d (probeState q) u) =
      normSq (innerC (probeState p) (probeState q))) (φ ψ : Fin (N+1) → ℂ) :
    swIntegral N (fun u => diagonalSymbol N d φ u * diagonalSymbol N d ψ u) = normSq (innerC φ ψ) := by
  let W := diagonalSymbol N d
  have hc (v : Fin (N+1) → ℂ) : Continuous (fun x : ℝ × ℝ => W v (SU2.sphVec x.1 x.2)) := by
    obtain ⟨P,hP⟩ := diagonalSymbol_poly N d v
    simp only [W, hP]; exact continuous_mvPolynomial_sphVec P
  have hlin (v w : Fin (N+1) → ℂ) :
      swIntegral N (fun u => W v u * W w u) = ∑ p : Probe N, weight w p *
        swIntegral N (fun u => W v u * W (probeState p) u) := by
    have he (u : S2) : W v u * W w u =
        ∑ p : Probe N, weight w p * (W v u * W (probeState p) u) := by
      conv_lhs => rhs; rw [show W w u = _ from symbol_expansion d w u]
      simp only [Finset.mul_sum, mul_left_comm (W v u)]
      rfl
    simp_rw [he]
    rw [swIntegral_sum]
    · simp only [swIntegral_const_mul]
    · intro i; exact continuous_const.mul ((hc v).mul (hc _))
  have firstProbe (p : Probe N) : swIntegral N (fun u => W (probeState p) u * W φ u) =
      normSq (innerC (probeState p) φ) := by
    rw [hlin, overlap_expansion]
    exact Finset.sum_congr rfl fun q _ => congrArg (weight φ q * ·) (h p q)
  change swIntegral N (fun u => W φ u * W ψ u) = _
  rw [hlin, overlap_expansion]
  apply Finset.sum_congr rfl; intro p _
  simp_rw [mul_comm (W φ _) (W (probeState p) _)]
  rw [firstProbe, overlap_symm]

/-- Construct the all-state SW system from a trace-one polar seed and finitely
many exact scalar identities for its explicit polynomial symbols. -/
def swOfProbeOverlap {N : ℕ} (d : Fin (N+1) → ℝ) (hd : ∑ k, d k = 1)
    (h : ∀ p q : Probe N,
      swIntegral N (fun u => diagonalSymbol N d (probeState p) u * diagonalSymbol N d (probeState q) u) =
      normSq (innerC (probeState p) (probeState q))) : StratonovichWeylSystem N :=
  diagonalStratonovichWeyl d hd (tracial_of_probe_overlap d h)

/-- Gram matrix of the probe symbols, evaluated by finite polynomial arithmetic. -/
def probeGram {N : ℕ} (d : Fin (N+1) → ℝ) (p q : Probe N) : ℝ :=
  ((N+1:ℕ):ℝ) * polynomialMoment
    (diagonalPolynomial N d (probeState p) * diagonalPolynomial N d (probeState q))

private theorem probeGram_eq_integral {N : ℕ} (d : Fin (N+1) → ℝ) (p q : Probe N) :
    probeGram d p q = swIntegral N (fun u =>
      diagonalSymbol N d (probeState p) u * diagonalSymbol N d (probeState q) u) := by
  simp only [probeGram, ← sphereAvg_eval, map_mul, diagonalPolynomial_eval, swIntegral]

/-- A trace-one seed defines a self-dual polar kernel exactly when its finite
polynomial Gram matrix agrees with the pure-state overlap matrix. -/
theorem probeGram_criterion {N : ℕ} (d : Fin (N+1) → ℝ) (hd : ∑ k, d k = 1) :
    (∃ sw : StratonovichWeylSystem N, sw.W = diagonalSymbol N d) ↔
    ∀ p q : Probe N, probeGram d p q = normSq (innerC (probeState p) (probeState q)) := by
  constructor
  · rintro ⟨sw,he⟩ p q
    rw [probeGram_eq_integral, ← he, sw.tracial]
  · intro h
    exact ⟨swOfProbeOverlap d hd (fun p q => (probeGram_eq_integral d p q).symm.trans (h p q)), rfl⟩

end SU2Wigner
end
