# Conjecture 00000007604 — Spinors as Elements of Minimal Left Ideals

## Problem Statement

> **English.** Definition: Spinors as elements of minimal left ideals. Conjecture: The realization dimension equals the half-dimension power of two and the spectrum is complete; the carrier of the realization is the minimal ideal; and the carrier of the minimal ideal is the matrix realization of the simple module. *(spinor half-dimension power of two)*
>
> **中文。** 定义：旋量为极小左理想的元素。猜想：实现维数等于二的半维幂且谱完全；且实现的载体为极小理想；且极小理想的载体为单纯模的矩阵实现。（旋量维数二半维幂）

---

## Verdict: **Refuted in General** (True Exactly in the Even-Dimensional Split / Complex Nondegenerate Regime)

For a quadratic vector space $\bigl(V, Q\bigr)$ of dimension $n = \dim_K V$ over a field $K$ with $\mathrm{char}\,K \neq 2$ and Clifford algebra $\mathrm{Cl}\bigl(V, Q\bigr)$ defined by $v^2 = Q(v)\cdot 1$, defining algebraic spinors as elements of a minimal nonzero left ideal $S \subset \mathrm{Cl}\bigl(V, Q\bigr)$ does **not** universally yield $\dim_K S = 2^{n/2}$, spectral completeness, or a faithful full-matrix simple module realization. Specifically, the conjecture fails across **three independent structural regimes**:

1. **Odd Dimensions ($n = 2m + 1$):**
   - **Arithmetic impossibility:** Since $n = 2m + 1$ is odd, $2^{n/2} = 2^m\sqrt{2} \notin \mathbb{Q}$; no vector space over any field has integer dimension $d$ satisfying $d^2 = 2^n$.
   - **Split center, non-faithfulness, and incomplete spectrum:** For $\mathbb{C}\mathrm{l}_{2m+1} \cong M_{2^m}(\mathbb{C}) \oplus M_{2^m}(\mathbb{C})$ and split $\mathrm{Cl}_{m+1,m}(K) \cong M_{2^m}(K) \oplus M_{2^m}(K)$, every minimal nonzero left ideal $S$ has $\dim_K S = 2^m = 2^{(n-1)/2} \neq 2^{n/2}$, annihilates a complementary $2^{2m}$-dimensional simple ideal ($\ker \rho_S \neq 0$), and realizes only one of the two eigenvalues $\{+1, -1\}$ of the signed central volume element $\omega$ (at $n = 1$, $\mathrm{Cl}_{1,0}(K) \cong K \times K$ has minimal left ideals $S_\pm = K(1 \pm e_1)$ of dimension $1$, with $1^2 \neq 2^1$).

2. **Even-Dimensional Division-Algebra Obstructions (Real / Rational Bott Periodicity):**
   - Even when $n = 2m$ is **even** and $Q$ is **nondegenerate**, if $\mathrm{Cl}\bigl(V, Q\bigr) \cong M_k(\mathbb{D})$ has a nontrivial central division $K$-algebra $\mathbb{D}$ with $\dim_K \mathbb{D} = d^2 \gt 1$, every minimal nonzero left ideal $S \cong \mathbb{D}^k$ has dimension $\dim_K S = d \cdot 2^{n/2} \gt 2^{n/2}$.
   - **Minimal even counterexample ($n = 2$):** For negative-definite $Q(x_1, x_2) = -x_1^2 - x_2^2$ over $K \in \{\mathbb{Q}, \mathbb{R}\}$, $\mathrm{Cl}_{0,2}(K) \cong \mathbb{H}_K$ is Hamilton's quaternion division ring. Every nonzero element is invertible, the only idempotents are $0$ and $1$, the **unique** minimal nonzero left ideal is $S = \mathbb{H}_K$ of dimension $\dim_K S = 4 \neq 2 = 2^{2/2}$, left multiplication embeds $\mathbb{H}_K$ as a proper $4$-dimensional subalgebra of $\mathrm{End}_K(S) \cong M_4(K)$ rather than $M_2(K)$, and $e_1, e_2$ admit no $K$-eigenvalues. Over $\mathbb{R}$ ($n = p + q \ge 1$), $\dim_{\mathbb{R}} S = 2^{n/2}$ holds **if and only if** $n$ is even and $p - q \equiv 0, 2 \pmod{8}$ (under $v^2 = +Q(v)\cdot 1$).

3. **Degenerate Quadratic Forms ($Q = 0$, Exterior Algebra $\Lambda(V)$):**
   - Over **every** field $K$ (including $\mathbb{C}$) and in even dimension $n = 2m \ge 2$, $\mathrm{Cl}(V, 0) = \Lambda(V)$ is a local Artinian non-semisimple algebra whose Jacobson radical $\bigoplus_{k=1}^n \Lambda^k(V)$ has dimension $2^n - 1$.
   - Every nonzero left ideal contains the top exterior line $S_{\mathrm{top}} = \Lambda^n(V)$, which is therefore the **unique** minimal nonzero left ideal: $\dim_K S_{\mathrm{top}} = 1 \lt 2^{n/2}$ (e.g., $\dim_K S_{\mathrm{top}} = 1 \neq 2$ at $n = 2$), $S_{\mathrm{top}}^2 = 0$ (no generating idempotent), and every vector $v \in V$ acts as $0$ on $S_{\mathrm{top}}$.

### Positive Non-Vacuity Theorem (Even-Dimensional Split / Complex Nondegenerate Case)

Under the Cartan–Chevalley reading of "minimal ideal" as "minimal left ideal," **all four clauses hold simultaneously** whenever $\bigl(V, Q\bigr)$ is a nondegenerate split (neutral) quadratic space of even dimension $n = 2m$ (including $\mathrm{Cl}_{m,m}(\mathbb{R})$, $\mathrm{Cl}_{m,m}(\mathbb{Q})$, and every nondegenerate even-dimensional complex Clifford algebra $\mathbb{C}\mathrm{l}_{2m}$): for a Witt primitive idempotent $e = f_1^* f_1 \cdots f_m^* f_m$, the minimal left ideal $S = \mathrm{Cl}\bigl(V, Q\bigr)e$ satisfies $\dim_K S = 2^m = 2^{n/2}$, $\mathrm{Cl}\bigl(V, Q\bigr) \xrightarrow{\sim} \mathrm{End}_K(S) \cong M_{2^m}(K)$, complete Cartan sign-weight spectrum $\{\pm 1\}^m$, and single-column matrix realization inside $M_{2^m}(K)$. (By contrast, if "minimal ideal" were read strictly as minimal *two-sided* ideal, simplicity of $M_{2^m}(K)$ forces dimension $4^m \neq 2^m$ for all $m \ge 1$.)

---

## Package Contents

- `SOURCE.md` — Original bilingual problem statement (unmodified).
- `main.tex` / `main.pdf` — Complete mathematical manuscript proving the positive split realization theorem, all three refutation regimes, and the full real Bott periodicity classification table.
- `lean/` — Self-contained **Core Lean 4.19.0** formalization (`SpinorMinimalIdeals`, zero external dependencies, `-DwarningAsError=true`, zero `sorry` / `admit` / `native_decide` / custom `axiom`):
  - `SpinorMinimalIdeals/PolyNorm.lean` — Verified sparse multivariate polynomial normalizer over $\mathbb{Z}$.
  - `SpinorMinimalIdeals/RatField.lean` — Quotient construction of $\mathbb{Q}$ (`RatQ`), field axioms, four-square anisotropy, and irrationality of $\sqrt{2^{2m+1}}$ for all $m \in \mathbb{N}$.
  - `SpinorMinimalIdeals/AlgebraicFramework.lean` — Unital associative $\mathbb{Q}$-algebras, minimal left/two-sided ideals, exact linear dimension `HasQDim`, and dimension invariance ($\dim 1 \neq \dim 2$, $\dim 4 \neq \dim 2$).
  - `SpinorMinimalIdeals/PositiveSplitCl11.lean` — Parametric Clifford algebras `Cl1` and `Cl2`, isomorphism $\mathrm{Cl}_{1,1}(\mathbb{Q}) \cong M_2(\mathbb{Q})$, and positive proof for $S_{1,1}$ ($\dim_{\mathbb{Q}} S_{1,1} = 2 = 2^{2/2}$, faithfulness, complete $\{+1, -1\}$ spectrum, and first-column matrix carrier).
  - `SpinorMinimalIdeals/Counterexamples.lean` — Complete classifications of all minimal nonzero left ideals and formal refutations for $\mathrm{Cl}_{1,0}(\mathbb{Q})$ ($n = 1$), $\mathrm{Cl}_{0,2}(\mathbb{Q}) \cong \mathbb{H}_{\mathbb{Q}}$ ($n = 2$), and $\Lambda(\mathbb{Q}^2)$ ($n = 2$).
  - `SpinorMinimalIdeals.lean` — Root module proving `conjecture_00000007604_complete_resolution`.
- `verify.py` — Standalone Python 3 exact rational verification script checking basis associativity across $24$ Clifford algebras, Dickson trace Jacobson radicals, positive split witnesses ($\mathrm{Cl}_{1,1}, \mathrm{Cl}_{2,2}$), counterexamples ($\mathrm{Cl}_{1,0}, \mathrm{Cl}_{0,1}, \mathrm{Cl}_{2,1}, \mathrm{Cl}_{0,2}, \mathrm{Cl}_{4,0}, \mathrm{Cl}_{0,4}, \Lambda(V_1\dots V_4), \mathrm{Cl}_{1,0,1}$), and all $44$ signatures $1 \le p + q \le 8$ in the real Bott periodicity table.
- `verification/` — Build, axiom-audit, version, PDF, and Python verification logs together with `SELF_REVIEW.md`.
