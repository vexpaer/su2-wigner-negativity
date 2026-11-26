# Universal Wigner Negativity for Pure Spin States (`SU(2)`)

Proof, independent computational verification, and complete **Lean 4** formalization (zero `sorry`, zero custom axioms) of the theorem:

> **Theorem (Universal Spherical Wigner Negativity).** For every spin $j \in \frac{1}{2}\mathbb{N}$ ($j \ge \tfrac{1}{2}$, i.e., $N = 2j \ge 1$), every pure state $|\psi\rangle \in \mathbb{C}^{2j+1}$, and every $\mathrm{SU}(2)$-covariant, self-dual Stratonovich–Weyl spherical Wigner function $W_\psi : S^2 \to \mathbb{R}$, $W_\psi$ strictly attains negative values on $S^2$.

This settles the open conjecture of Davis, Kumari, Mann, and Ghose (2021) / Davis, Hennigar, Mann, and Ghose (2023) (Open Quantum Problem F18) and completes the constant-curvature trichotomy for pure-state Wigner positivity across $H^2$ ($\kappa < 0$), $\mathbb{R}^2$ ($\kappa = 0$), and $S^2$ ($\kappa > 0$).

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
| `verify_theorem.py` | Independent pure-Python / exact-Racah numerical verification script |
| `.zenodo.json` / `CITATION.cff` | Zenodo archival metadata and citation metadata |
| `LICENSE` | MIT License |
| `lean/SU2WignerNegativity.lean` | Root Lean 4 module importing the full formalization |
| `lean/SU2WignerNegativity/SpinRep.lean` | Explicit unitary spin-$N/2$ representation `spinRep`, group/unitarity laws, and half-integer orthogonality (`pi_ortho_odd`) |
| `lean/SU2WignerNegativity/SphericalHarmonicZero.lean` | Lemma 2 (`spherical_harmonic_has_zero`) via 1D calculus, Schwarz symmetry, and Fubini on $S^2$ |
| `lean/SU2WignerNegativity/EquatorialIntegral.lean` | Equatorial integral identity (`equatorial_integral_identity`), integer-spin (`pi_ortho_even`), and universal (`pi_ortho_all`) $\pi$-rotation orthogonality |
| `lean/SU2WignerNegativity/WignerNegativity.lean` | `StratonovichWeylSystem`, Lemma 1 (`wigner_neg_of_ortho_partner`), Theorem 2 (`universal_wigner_negativity`), Corollary 1 (`uniform_wigner_negativity_bound`), and concrete spin-$1/2$ witness (`spinHalfStratonovichWeyl`) |

---

## Building and Auditing the Lean 4 Formalization

Requires Lean `v4.36.0` (managed via `elan`, pinned in `lean/lean-toolchain`).

```bash
cd lean
lake exe cache get
lake build
```

### Axiom Audit

All main theorems and the explicit non-vacuity witness depend **only** on Lean's standard axioms `[propext, Classical.choice, Quot.sound]` (zero `sorry`, zero custom `axiom`s):

```bash
cd lean
lake env lean --stdin <<'EOF'
import SU2WignerNegativity
#print axioms SU2Wigner.spinRep_mul
#print axioms SU2Wigner.spinRep_conjTranspose_mul_self
#print axioms SU2Wigner.spherical_harmonic_has_zero
#print axioms SU2Wigner.equatorial_integral_identity
#print axioms SU2Wigner.pi_ortho_odd
#print axioms SU2Wigner.pi_ortho_even
#print axioms SU2Wigner.pi_ortho_all
#print axioms SU2Wigner.wigner_neg_of_ortho_partner
#print axioms SU2Wigner.universal_wigner_negativity
#print axioms SU2Wigner.uniform_wigner_negativity_bound
#print axioms SU2Wigner.spinHalfStratonovichWeyl
EOF
```

---

## Running the Numerical Verification Script

```bash
python3 verify_theorem.py
```
