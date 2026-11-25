# Conjecture 00000000441 — Resolution Package

## Verdict: **FALSE** (Disproved)

Conjecture `00000000441` asserts that in the ring of multisymmetric functions $\Lambda^{(r)}$ in $r$ sets of variables, the transition matrix of the multisymmetric monomial basis $\{m_\Lambda\}$ is triangular with determinant a power of two, and that the exponent is a function of $r$ alone.

We prove that this conjecture is **false** under every standard multiplicative basis of $\Lambda^{(r)}$—namely against the **elementary multisymmetric basis** $\{e_\Lambda\}$, the **complete homogeneous multisymmetric basis** $\{h_\Lambda\}$, the **power-sum multisymmetric basis** $\{p_\Lambda\}$, and the **augmented (divided-power) monomial basis** $\{\tilde{m}_\Lambda\}$—as well as for their inverse transition matrices $M(m, b) = M(b, m)^{-1}$, polarized scalings, and separate-symmetry tensor analogues $\Lambda^{\otimes r}$.

---

## Mathematical Summary

Let $\Lambda^{(r)} = \bigoplus_{\mathbf{d} \in \mathbb{N}^r} \Lambda^{(r)}_{\mathbf{d}}$ be the ring of diagonally symmetric functions in $r \ge 1$ sets of variables $\mathbf{x}^{(1)}, \dots, \mathbf{x}^{(r)}$, with multisymmetric monomial basis $\{m_\Lambda\}_{\Lambda \vdash \mathbf{d}}$ indexed by vector partitions $\Lambda$ of multidegree $\mathbf{d}$.

### 1. Elementary Basis $\{e_\Lambda\}$ and Complete Homogeneous Basis $\{h_\Lambda\}$
Generated multiplicatively by
$$\sum_{\mathbf{u} \in \mathbb{N}^r} e_{\mathbf{u}} \mathbf{t}^{\mathbf{u}} = \prod_{i \ge 0} \Bigl(1 + \sum_{j=1}^r t_j x_{i,j}\Bigr), \qquad \sum_{\mathbf{u} \in \mathbb{N}^r} h_{\mathbf{u}} \mathbf{t}^{\mathbf{u}} = \prod_{i \ge 0} \Bigl(1 - \sum_{j=1}^r t_j x_{i,j}\Bigr)^{-1},$$
these bases satisfy $|\det M(h, m)_{\mathbf{d}}| = |\det M(e, m)_{\mathbf{d}}|$ for all $r, \mathbf{d}$. Small multilinear degrees look deceptive ($|\det M(e, m)_{(1^r)}| = 1, 1, 2$ for $r = 1, 2, 3$), but all three claims of the conjecture fail:
- **Failure of triangularity:** Every entry of $M(h, m)_{\mathbf{d}}$ is strictly positive ($\ge 1$), failing permutation-triangularity already at $r = 2$, $\mathbf{d} = (1, 1)$ where $M(h, m)_{(1,1)} = \begin{pmatrix} 2 & 1 \\ 1 & 1 \end{pmatrix}$. For $\{e_\Lambda\}$ at $r = 3$, $\mathbf{d} = (1, 1, 1)$ ($5 \times 5$), every entry lies in $\{0, 1\}$ while $\det M(e, m)_{(1,1,1)} = -2$; since any permutation-triangular $\{0, 1\}$-matrix has determinant in $\{-1, 0, 1\}$, $M(e, m)_{(1,1,1)}$ is not triangular under any row and column orderings.
- **Failure of power-of-two determinant and pure $r$-dependence:** At $r = 2$, $\mathbf{d} = (2, 2)$ ($9 \times 9$),
  $$\det M(e, m)_{(2,2)} = \det M(h, m)_{(2,2)} = 3,$$
  which is divisible by $3$ (not $\pm 2^z$), not permutation-triangular, and differs from $|\det M(e, m)_{(1,1)}| = 1$ at the same $r = 2$.
- **Failure even in multilinear degree $\mathbf{d} = (1^r)$:** At $r = 4$, $\mathbf{d} = (1, 1, 1, 1)$ ($15 \times 15$, indexed by set partitions $\Pi_4$),
  $$\det M(e, m)_{(1,1,1,1)} = -96 = -2^5 \cdot 3, \qquad \det M(h, m)_{(1,1,1,1)} = 96 = 2^5 \cdot 3,$$
  refuting both triangularity and the power-of-two determinant property.

### 2. Power-Sum Basis $\{p_\Lambda\}$ and Augmented Monomial Basis $\{\tilde{m}_\Lambda\}$
Ordered by non-decreasing part count, $M(p, m)_{\mathbf{d}}$ *is* lower triangular for all $r, \mathbf{d}$, with diagonal entries $\mathrm{aut}(\Lambda) = \prod_{\mathbf{u}} m_\Lambda(\mathbf{u})!$ and determinant
$$\det M(p, m)_{\mathbf{d}} = \det M(\tilde{m}, m)_{\mathbf{d}} = \prod_{\Lambda \vdash \mathbf{d}} \mathrm{aut}(\Lambda).$$
- **Positive bounded-coordinate regime vs. failure of pure $r$-dependence:** Whenever $\mathbf{d} \in \{0, 1, 2\}^r$, $\det M(p, m)_{\mathbf{d}}$ is an exact power of two, but at fixed $r = 2$ it takes the distinct values $1 = 2^0$ at $\mathbf{d} = (1, 1)$, $2 = 2^1$ at $\mathbf{d} = (2, 1)$, and $32 = 2^5$ at $\mathbf{d} = (2, 2)$, so the exponent cannot be a function of $r$ alone.
- **Universal failure of power-of-two determinant for all $r \ge 1$:** For every $r \ge 1$, in the strictly positive multidegree $\mathbf{d}'_r = (3, 1, \dots, 1) \in \mathbb{N}^r$, the vector partition $\Lambda^*_r = \{\mathbf{e}_1, \mathbf{e}_1, \mathbf{e}_1, \mathbf{e}_2, \dots, \mathbf{e}_r\}$ has $\mathrm{aut}(\Lambda^*_r) = 3! = 6$, so $6 \mid \det M(p, m)_{\mathbf{d}'_r}$ (explicitly $\det M(p, m)_{(3)} = 6$ for $r = 1$ and $\det M(p, m)_{(3,1)} = 12$ for $r = 2$).

---

## Package Contents

- `SOURCE.md` — Original conjecture statement (unmodified).
- `main.tex` / `main.pdf` — Publication-grade mathematical paper proving the complete disproof and characterizing positive low-degree regimes.
- `verify.py` — Standalone Python 3 verification script (standard library only) cross-checking multivariate polynomial identities, exact determinants, permutation-triangularity, and inverse/polarized variants.
- `lean/` — Core Lean 4.19.0 formalization (`leanprover/lean4:v4.19.0`, zero external dependencies, `-DwarningAsError=true`, zero `sorry`, zero `native_decide`):
  - `Conjecture00000000441/LinearAlgebra.lean` — Recursive Laplace determinant, Hermite integer row operations, triangular determinant formulas, permutation-triangularity obstructions, and odd-divisor obstruction to $\pm 2^k$.
  - `Conjecture00000000441/Multisymmetric.lean` — First-principles sparse multivariate polynomial ring, $m_\Lambda, e_\Lambda, h_\Lambda, p_\Lambda$ constructors, dual-basis transition uniqueness, multilinear set-partition formula, and all-$r$ divisibility theorem `powerSum_all_r_not_power_of_two`.
  - `Conjecture00000000441/Counterexamples.lean` — Polynomial transition verifications and explicit counterexamples across $\mathbf{d} \in \{(1,1), (2,1), (1,1,1), (2,2), (3,1), (1,1,1,1)\}$.
  - `Conjecture00000000441.lean` — Top-level positive non-vacuity theorems and master disproof theorems (`disproof_elementary_basis`, `disproof_completeHomogeneous_basis`, `disproof_powerSum_basis`, `conjecture_00000000441_disproved`).
- `verification/` — Build and verification logs (`lake-build.log`, `lean-axioms.log`, `lean-version.log`, `pdf-build.log`, `python-verify.log`, `SELF_REVIEW.md`).
