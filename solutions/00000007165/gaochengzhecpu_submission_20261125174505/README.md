# Conjecture 00000007165 — Resolution Package

## Verdict: **FALSE** (Disproved)

Conjecture `00000007165` proposes that the extremal faces of the Rayleigh quotient determine contact manifolds whose dimension equals the multiplicity $m$ of the corresponding spectral index (*index-multiplicity Rayleigh contact manifolds* / 极值面的切触流形且形的维数为指标的重数).

We isolate the positive unnormalized linear-algebraic core behind the claim ($R_A(x) = \lambda_{\max} \iff A x = \lambda_{\max} x$ for $x \neq 0$, so adjoining $0 \notin \mathrm{dom}(R_A)$ yields $\dim_{\mathbb{F}} \ker(A - \lambda_{\max} I_n) = m$), and then prove that on **every canonical normalized state space** of the Rayleigh quotient—the real unit sphere $S^{n-1}$, real projective space $\mathbb{RP}^{n-1}$, the complex unit sphere $S^{2n-1}$, complex projective space $\mathbb{CP}^{n-1}$, and the density-matrix state spaces $\mathcal{D}_n(\mathbb{C})$ and $\mathcal{D}_n(\mathbb{R})$—as well as for non-normal matrices, multidimensional extremal faces of joint numerical ranges, interior spectral indices, and Morse/inertia indices, the conjecture is **false**.

---

## Mathematical Summary

Let $\mathbb{F} \in \{\mathbb{R}, \mathbb{C}\}$ and let $A \in \mathrm{Herm}_n(\mathbb{F})$ have ordered eigenvalues $\lambda_1 \ge \dots \ge \lambda_n$ where $\lambda_{\max} = \lambda_1$ has multiplicity $m \in \{1, \dots, n\}$. Because $R_A(t x) = \frac{\langle x, A x \rangle}{\|x\|^2} = R_A(x)$ for all $t \in \mathbb{F}^\times$ and $R_A(0)$ is undefined, variational and convex-geometric contact loci live on compact normalized manifolds:

| Normalized Domain | Contact Locus | Exact Dimension | Strict Contact? | Equals Multiplicity $m$? | Explicit Counterexample |
| :--- | :--- | :--- | :--- | :--- | :--- |
| **Real sphere** $S^{n-1}$ | $S^{m-1}$ | $m - 1$ (real) | Even $m$ only | **Never** ($m \ge 1$) | $m = 1$, $\mathrm{diag}(2,1)$: $S^0 = \{\pm e_1\}$, $\dim = 0 \neq 1$ |
| **Real projective** $\mathbb{RP}^{n-1}$ | $\mathbb{RP}^{m-1}$ | $m - 1$ (real) | Even $m \ge 2$ only | **Never** ($m \ge 1$) | $m = 1$, $\mathrm{diag}(2,1)$: $\{[e_1]\}$, $\dim = 0 \neq 1$ |
| **Complex sphere** $S^{2n-1}$ | $S^{2m-1}$ | $2m - 1$ (real) | **Yes** ($\alpha = \mathrm{Im}\langle z, dz \rangle$) | Only at $m = 1$; **fails for all $m \ge 2$** | $m = 2$, $\mathrm{diag}(2,2,1)$: $S^3$, $\dim_{\mathbb{R}} = 3 \neq 2$ |
| **Complex projective** $\mathbb{CP}^{n-1}$ | $\mathbb{CP}^{m-1}$ | $m - 1$ ($\mathbb{C}$); $2m - 2$ ($\mathbb{R}$) | Never ($\dim_{\mathbb{R}}$ even) | $\mathbb{C}$-dim: **Never**; $\mathbb{R}$-dim: **fails for all $m \neq 2$** | $m = 1$: $\{[e_1]\}$ ($\dim = 0 \neq 1$); $m = 3$: $\mathbb{CP}^2$ ($\dim_{\mathbb{R}} = 4 \neq 3$) |
| **Complex density states** $\mathcal{D}_n(\mathbb{C})$ | $\mathcal{D}_m(\mathbb{C})$ | $m^2 - 1$ (real) | Boundary for $m \ge 2$ | **Never** ($m^2 - m - 1 \neq 0$ on $\mathbb{Z}$) | $m = 1$: $\dim = 0 \neq 1$; $m = 2$: Bloch ball $B^3$, $\dim = 3 \neq 2$ |
| **Real density states** $\mathcal{D}_n(\mathbb{R})$ | $\mathcal{D}_m(\mathbb{R})$ | $\frac{m(m+1)}{2} - 1$ (real) | Boundary for $m \ge 2$ | Only at $m = 2$; **fails for $m = 1$ and all $m \ge 3$** | $m = 1$: $\dim = 0 \neq 1$; $m = 3$: $\dim = 5 \neq 3$ |

### Additional Structural Obstructions
1. **Strict Contact Topology Parity Obstruction:** Every strict contact manifold $\bigl(M, \alpha\bigr)$ in differential geometry has odd real dimension $2d + 1$, which can never equal an even multiplicity $m = 2k$. On $\bigl(S^{2n-1}, \mathrm{Im}\langle z, dz \rangle\bigr)$, $M_{\mathbb{C}, S}(A) \cong S^{2m-1}$ is a genuine strict contact submanifold with nondegenerate symplectic $d\alpha|_{\xi}$, and its dimension is $2m - 1 \neq m$ for all $m \ge 2$.
2. **Non-Normal Matrices:** For $A = \begin{pmatrix} 0 & 2 \\ 0 & 0 \end{pmatrix}$, $\chi_A(\mu) = \mu^2$ gives a unique eigenvalue $\lambda = 0$ of algebraic multiplicity $m_{\mathrm{alg}} = 2$ (geometric multiplicity $1$), whereas $\max_{\|x\|=1} R_A(x) = 1 \neq 0$ is attained on $\mathbb{RP}^1$ at the unique ray $[(1, 1)^\top]$ of dimension $0 \notin \{1, 2\}$.
3. **Multidimensional Extremal Faces of Joint Numerical Ranges:** For $A_1 = \mathrm{diag}(1, 1, 0, 0)$ and $A_2 = \mathrm{diag}(0, 0, 1, 0)$ ($A = A_1 + i A_2 = \mathrm{diag}(1, 1, i, 0)$), the $1$-dimensional hypotenuse extremal face $F = \{u + v = 1\} \subset W(A_1, A_2)$ has supporting operator $A_1 + A_2 = \mathrm{diag}(1, 1, 1, 0)$ of multiplicity $m_F = 3$, while its contact dimensions across $S^3$, $\mathbb{RP}^3$, $S^7$, $\mathbb{CP}^3$, $\mathcal{D}_4(\mathbb{C})$, and $\mathcal{D}_4(\mathbb{R})$ are $2, 2, 5, 2 \text{ (or } 4\text{)}, 8, 5 \neq 3$.
4. **Interior Eigenvalue Singularities & Morse Index:** For $A = \mathrm{diag}(1, 0, -1)$ on $S^2$, the interior eigenvalue $\lambda_2 = 0$ has multiplicity $m = 1$, yet $S^2 \cap R_A^{-1}(0) = \{x \in S^2 : x_1^2 = x_3^2\}$ is singular (not a smooth manifold): its Zariski tangent space jumps from dimension $1$ at $\bigl(\frac{2}{3}, \frac{1}{3}, \frac{2}{3}\bigr)^\top$ to dimension $2$ at $\bigl(0, 1, 0\bigr)^\top$. Meanwhile, the Morse index of $M_{\max}(A)$ on $S^{n-1}$ is $n - m$ (and $0$ at $M_{\min}(A)$), differing from $\dim M_{\max} = m - 1$.

---

## Package Contents

- `SOURCE.md` — Original conjecture statement (unmodified).
- `main.tex` / `main.pdf` — Complete mathematical paper proving the positive linear-cone theorem, exact dimension formulas across all five normalized domains, and non-normal, joint-face, and interior/Morse obstructions.
- `verify.py` — Standalone Python 3 exact verification suite (`fractions.Fraction` and exact $\mathbb{Q}[i]$ linear algebra; zero floating-point operations) testing non-diagonal orthogonal/unitary conjugates $B = U A U^*$ across $1 \le m \le n \le 6$.
- `lean/` — First-principles formalization in **Core Lean 4.19.0** (`leanprover/lean4:v4.19.0`, zero external dependencies, `-DwarningAsError=true`, zero `sorry`, zero `native_decide`):
  - `Conjecture00000007165/ModuleDim.lean` — Finite sums, Gaussian integers `GaussInt`, module rank/dimension predicates `HasDim`/`HasCDim`, trace-commutation rank uniqueness (`hasDim_unique`, `hasCDim_unique`), and direct-sum additivity (`hasDim_directSum`).
  - `Conjecture00000007165/RayleighSpectrum.lean` — Exact rational values `RatVal`, real/complex Rayleigh quotients, projective scale invariance, Hermitian quadratic form reality, and positive linear-eigenspace theorems.
  - `Conjecture00000007165/ContactDomains.lean` — Point-set characterizations, stereographic norm identity, strict Sasakian contact structure and symplectic nondegeneracy on $S^{2n-1}$, and universal dimension refutations on $S^{n-1}$, $\mathbb{RP}^{n-1}$, $S^{2n-1}$, and $\mathbb{CP}^{n-1}$.
  - `Conjecture00000007165/DensityAndObstructions.lean` — PSD density matrices, bilateral face-tangent equivalence at $\rho_0 = \frac{1}{m} P_m$, border-splitting inductions for $m^2 - 1$ and $\frac{1}{2}m(m+1) - 1$, and non-normal, joint-face, and interior-singularity theorems.
  - `Conjecture00000007165.lean` — Top-level non-vacuity theorem `positive_linear_cone_characterization` and master disproof theorem `conjecture_00000007165_disproved`.
- `verification/` — Build and verification logs (`lake-build.log`, `lean-axioms.log`, `lean-version.log`, `pdf-build.log`, `python-verify.log`, `SELF_REVIEW.md`).
