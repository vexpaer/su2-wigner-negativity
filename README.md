# Universal Wigner Negativity for Pure Spin States (`SU(2)`)

[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.24563264.svg)](https://doi.org/10.5281/zenodo.24563264)
[![Project Page](https://img.shields.io/badge/Project%20Page-GitHub%20Pages-0b4f6c)](https://vexpaer.github.io/su2-wigner-negativity/)
[![Lean 4](https://img.shields.io/badge/Lean%204-v4.36.0%20%7C%200%20sorry-2e7d32)](lean/SU2WignerNegativity.lean)
[![License: MIT](https://img.shields.io/badge/License-MIT-blue.svg)](LICENSE)

Proof, independent computational verification, and a **Lean 4** formalization of the following implication for every self-dual Stratonovich–Weyl system:

> **Theorem (Universal Spherical Wigner Negativity).** For every spin $j \in \frac{1}{2}\mathbb{N}$ ($j \ge \tfrac{1}{2}$, i.e., $N = 2j \ge 1$), every pure state $|\psi\rangle \in \mathbb{C}^{2j+1}$, and every $\mathrm{SU}(2)$-covariant, self-dual Stratonovich–Weyl spherical Wigner function $W_\psi : S^2 \to \mathbb{R}$, $W_\psi$ strictly attains negative values on $S^2$.

This settles the open conjecture of Davis, Kumari, Mann, and Ghose (2021) / Davis, Hennigar, Mann, and Ghose (2023) (Open Quantum Problem F18) and completes the constant-curvature trichotomy for pure-state Wigner positivity across $H^2$ ($\kappa < 0$), $\mathbb{R}^2$ ($\kappa = 0$), and $S^2$ ($\kappa > 0$).

- **Interactive Project Page:** https://vexpaer.github.io/su2-wigner-negativity/
- **Zenodo Archival Preprint (DOI):** https://doi.org/10.5281/zenodo.24563264

---

## Proof Outline

1. **Universal $\pi$-Rotation Orthogonality (Theorem 1):** Every pure spin-$j$ state ($j \ge \tfrac{1}{2}$) admits a unit axis $\mathbf{u}_* \in S^2$ such that $\langle \psi \mid e^{-i\pi \mathbf{u}_* \cdot \mathbf{J}} \mid \psi \rangle = 0$.
   - *Half-integer spins ($N = 2j$ odd):* $h(\mathbf{u}) := \langle \psi \mid i e^{-i\pi \mathbf{u}\cdot\mathbf{J}} \mid \psi \rangle$ is real-valued, continuous, and odd on $S^2$, hence vanishes by the intermediate value theorem.
   - *Integer spins ($N = 2j$ even, $j \ge 1$):* Every smooth complex spherical harmonic of eigenvalue $\lambda > 0$ on $S^2$ has a zero (Lemma 2). Applying this to $Y_\psi(\mathbf{n}) = \langle j, 0; \mathbf{n} \mid \psi \rangle$ and integrating along the equator orthogonal to its zero $\mathbf{n}_*$ via the exact **Equatorial Integral Identity**
     $$\frac{1}{2\pi}\int_0^{2\pi} e^{-i\pi \mathbf{u}(\varphi)\cdot\mathbf{J}}\,d\varphi = (-1)^j |j, 0; \mathbf{n}\rangle\langle j, 0; \mathbf{n}| \qquad (\mathbf{u}(\varphi) \perp \mathbf{n})$$
     yields a great circle on which $\langle \psi \mid e^{-i\pi \mathbf{u}\cdot\mathbf{J}} \mid \psi \rangle$ is real with mean $0$, hence has a zero $\mathbf{u}_* \perp \mathbf{n}_*$.
2. **Orthogonal Orbit Partner $\Rightarrow$ Strict Wigner Negativity (Lemma 1 & Theorem 2):** Traciality, $\mathrm{SU}(2)$-covariance, and polynomiality on $S^2$ rule out $W_\psi \ge 0$ globally whenever $|\psi\rangle$ has an orthogonal $\mathrm{SU}(2)$-rotated partner.
3. **Uniform Spin-Dependent Bound (Corollary 1):** Compactness of the unit sphere in $\mathbb{C}^{N+1}$ yields a constant $c_N > 0$ such that $\min_{S^2} W_\psi \le -c_N$ for every unit pure state $|\psi\rangle$.

---

## Repository Contents

| Path | Description |
| :--- | :--- |
| `paper.pdf` / `paper.tex` | Compiled preprint PDF and LaTeX manuscript (*Ximing Wang*, `vexpaer@gmail.com`) |
| `prl/` | *Physical Review Letters* submission package (`REVTeX 4.2` 4-page Letter + End Matter, 100-word justification, cover letter) |
| `docs/` | Interactive GitHub Pages project site with 3D spherical Wigner & $\pi$-rotation explorer |
| `verify_theorem.py` | Independent pure-Python / exact-Racah numerical verification script |
| `.zenodo.json` / `CITATION.cff` | Zenodo archival metadata (`DOI: 10.5281/zenodo.24563264`) and citation metadata |
| `LICENSE` | MIT License |
| `lean/SU2WignerNegativity.lean` | Root Lean 4 module importing the full formalization |
| `lean/SU2WignerNegativity/SpinRep.lean` | Explicit unitary spin-$N/2$ representation `spinRep`, group/unitarity laws, and half-integer orthogonality (`pi_ortho_odd`) |
| `lean/SU2WignerNegativity/SphericalHarmonicZero.lean` | Lemma 2 (`spherical_harmonic_has_zero`) via 1D calculus, Schwarz symmetry, and Fubini on $S^2$ |
| `lean/SU2WignerNegativity/EquatorialIntegral.lean` | Equatorial integral identity (`equatorial_integral_identity`), integer-spin (`pi_ortho_even`), and universal (`pi_ortho_all`) $\pi$-rotation orthogonality |
| `lean/SU2WignerNegativity/WignerNegativity.lean` | `StratonovichWeylSystem`, Lemma 1 (`wigner_neg_of_ortho_partner`), Theorem 2 (`universal_wigner_negativity`), Corollary 1 (`uniform_wigner_negativity_bound`), and concrete spin-$1/2$ witness (`spinHalfStratonovichWeyl`) |
| `lean/SU2WignerNegativity/SpinOne.lean` | All four spin-one sign choices, their polar spectra, and unconditional canonical negativity |
| `lean/SU2WignerNegativity/AxisKernel.lean` and `DiagonalKernel.lean` | Polynomial covariant spherical symbols from any real polar spectrum, for arbitrary spin |
| `lean/SU2WignerNegativity/SphereMoments.lean` and `FiniteOverlap.lean` | Exact spherical monomial moments and the finite Gram criterion for a trace-one polar spectrum |
| `lean/SU2WignerNegativity/CoherentSymbol.lean` and `CoherentNormalization.lean` | All-spin coherent-state informational completeness (`coherent_expectation_injective`) and resolution of the identity (`coherentSymbol_norm`) |
| `lean/SU2WignerNegativity/SphereInvariance.lean` | Full `SU(2)` rotation invariance of `sphereAvg` and `swIntegral` on Cartesian polynomials (`sphereAvg_actS2_poly`) |
| `lean/SU2WignerNegativity/CoherentGram.lean` | Coherent-state Gram operator `gramMatrix`, spectral inverse square root `invSqrtGram`, concrete all-spin `canonicalStratonovichWeyl N`, and unconditional all-spin negativity (`canonical_universal_wigner_negativity`, `canonical_uniform_wigner_negativity_bound`) |

---

## Building and Auditing the Lean 4 Formalization

The project pins Lean 4.36.0 and the Mathlib revision in the Lake manifest.
With Elan installed, run the same build and axiom audit as CI from the repository root.

```bash
bash lean/check.sh
```

The all-spin theorem `universal_wigner_negativity` holds for every `StratonovichWeylSystem N`
(`N = 2j ≥ 1`). Concrete constructions include:

- **All spins `N : ℕ` (`CoherentGram.lean`)**: `canonicalStratonovichWeyl N` constructs a
  concrete `StratonovichWeylSystem N` for every spin by symmetric orthonormalization (`G⁻¹/²`)
  of the coherent-state (Husimi) symbol map, using `coherent_expectation_injective`,
  `coherentSymbol_norm`, `sphereAvg_sq_pos`, and `sphereAvg_actS2_poly` (`SphereInvariance.lean`).
  This yields unconditional all-spin theorems `canonical_universal_wigner_negativity` and
  `canonical_uniform_wigner_negativity_bound` for every `N ≥ 1`.
- **Explicit low-spin closed forms**: `spinHalfStratonovichWeyl` (`N = 1`) and all four
  signed spin-one kernels `spinOneStratonovichWeyl` (`N = 2`, with `canonicalSpinOne_negativity`).
- **Diagonal polar-spectrum criterion (`DiagonalKernel.lean`, `FiniteOverlap.lean`)**: For any
  `N = 2j` and any trace-one real polar spectrum `d`, `probeGram_criterion` characterizes when
  the rotated diagonal kernel satisfies the SW laws via a finite polynomial Gram matrix.
  Explicit closed-form identification of the polar spectra of `canonicalStratonovichWeyl N`
  with the Brif–Mann / Varilly–Gracia-Bondia Racah multipole weights for `N ≥ 3` remains an
  optional refinement.

---

## Running the Numerical Verification Script

```bash
python3 verify_theorem.py
```
