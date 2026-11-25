# Conjecture 00000007169 — Disproof and Formal Verification

## Verdict: **FALSE** (Ordering Correction Holds, but Antisymmetrization Optimality Is Refuted Across All Readings for All $n \ge 2$)

### Source Statement (`SOURCE.md`)

> **English.** Definition: Fiedler with the additive inequalities of eigenvalues. Conjecture: The ordering correction of additive inequalities holds, and the optimum of the correction is antisymmetrization. (antisymmetric Fiedler additive correction)
>
> **中文。** 定义：Fiedler：特征值的加性不等式。猜想：Fiedler 的加性：加性不等式的排序修正且正的最优为反对称化。（Fiedler 反对称化加性排序最优修正）

---

## Executive Summary

Let $A, B \in \mathcal{H}_n$ ($n \ge 2$) be $n \times n$ Hermitian (or real symmetric) matrices with eigenvalues ordered non-increasingly as $\alpha^\downarrow = (\alpha_1 \ge \dots \ge \alpha_n)$ and $\beta^\downarrow = (\beta_1 \ge \dots \ge \beta_n)$, let $\beta^\uparrow = (\beta_n, \dots, \beta_1)$ denote the reverse-ordered spectrum, and let $\gamma^\downarrow = (\gamma_1 \ge \dots \ge \gamma_n)$ denote the eigenvalues of $A + B$.

Conjecture `00000007169` consists of a conjunction $P \wedge Q$:

1. **Clause $P$ (*"The ordering correction of additive inequalities holds"*) — TRUE:**
   Naive unpermuted entrywise additivity $\gamma_k \le \alpha_k + \beta_k$ fails for every $n \ge 2$ (for example, $A = \mathrm{diag}(2, 0)$ and $B = \mathrm{diag}(0, 2)$ satisfy $\gamma_2 = 2 \gt 0 + 0$). Restoring validity requires classical index-ordering and majorization corrections:
   - **Lidskii–Wielandt–Ky Fan Two-Sided Majorization:**
     $$\bigl(\alpha^\downarrow + \beta^\uparrow\bigr)^\downarrow \prec \gamma^\downarrow \prec \alpha^\downarrow + \beta^\downarrow,$$
     meaning $\sum_{j=1}^n \gamma_j = \sum_{j=1}^n (\alpha_j + \beta_j)$ and $\sum_{j=1}^k \bigl(\alpha^\downarrow + \beta^\uparrow\bigr)^\downarrow_j \le \sum_{j=1}^k \gamma_j \le \sum_{j=1}^k (\alpha_j + \beta_j)$ for all $1 \le k \le n$.
   - **Weyl's Index-Shifted Inequalities (1912):** $\max_{i+j=k+n} (\alpha_i + \beta_j) \le \gamma_k \le \min_{i+j=k+1} (\alpha_i + \beta_j)$.
   - **Fiedler's Additive Determinant Bounds (1971):** For positive semidefinite $A, B \ge 0$,
     $$\prod_{i=1}^n (\alpha_i + \beta_i) \le \det(A + B) \le \prod_{i=1}^n (\alpha_i + \beta_{n+1-i}).$$

2. **Clause $Q$ (*"and the optimum of the correction is antisymmetrization"*) — FALSE:**
   Across the unitary/orthogonal orbit $\{(U A U^*, V B V^*) : U, V \in U(n)\}$, the ordering-corrected extremum $\bigl(\alpha^\downarrow + \beta^\uparrow\bigr)^\downarrow$ (which minimizes convex symmetric spreads and maximizes $\det(A + B)$ in Fiedler's 1971 theorem) is realized by **simultaneous diagonalization with anti-monotonic (reverse-order) permutation pairing** $w_0(i) = n + 1 - i$ — that is, by **commuting Hermitian / symmetric** matrices ($[A', B'] = 0$, $\bigl(A' + B'\bigr)^* = A' + B'$), **not** by antisymmetrization. Conflating *reverse eigenvalue ordering* ($\beta^\uparrow$) with *antisymmetrization* ($\mathcal{A}$) causes Clause $Q$ — and hence the conjunctive conjecture — to fail under **every** standard mathematical reading of antisymmetrization for all $n \ge 2$:

| Mathematical Reading of "Antisymmetrization" ($n \ge 2$) | Status of Clause $Q$ | Mechanism of Failure & Explicit Counterexample |
| :--- | :--- | :--- |
| **1A.** Matrix antisymmetrization $\mathcal{A}(M) = \frac{1}{2}(M - M^*)$ on Hermitian/symmetric domain | **False** | $\mathcal{A}(A) = \mathcal{A}(B) = \mathcal{A}(A+B) = 0$ identically (losing trace $\mathrm{tr}(A+B) \gt 0$), whereas true Fiedler optimum $A + B_{\mathrm{rev}}$ is purely symmetric ($\mathcal{A} = 0$, $\mathcal{S} = \mathrm{id}$) |
| **1B.** Non-Hermitian Cartesian decomposition $M_r = H_r + K_r$ ($K_r^* = -K_r$) | **False** | Nonzero skew parts destroy additive majorization: $M_1 = \bigl(\begin{smallmatrix}4&1\\-1&2\end{smallmatrix}\bigr)$, $M_2 = M_1^\top$ have $\lambda = (3,3)$ yet $\lambda(M_1+M_2) = (8,4)$ violates Weyl/Ky Fan ($8 \gt 6$) and Fiedler ($\det = 32 \lt 36$); $\mathrm{diag}(4,0) + \bigl(\begin{smallmatrix}0&3\\-3&0\end{smallmatrix}\bigr)$ has non-real eigenvalues $2 \pm i\sqrt{5}$ |
| **2A.** Real skew-symmetric orthogonal conjugation $A + K B K^\top$ ($K^\top = -K$, $K^\top K = I_n$) | **False** | For $n = 2$, $A = \mathrm{diag}(25,0)$ and $B = \bigl(\begin{smallmatrix}16&12\\12&9\end{smallmatrix}\bigr)$ give $\det(A + K B K^\top) = 400 \lt 625$ for every skew-symmetric orthogonal $K = \pm J_2$, while symmetric $Q = \frac{1}{5}\bigl(\begin{smallmatrix}-3&4\\4&3\end{smallmatrix}\bigr)$ attains $625$; for odd $n \ge 3$, $\det(K) = 0$ so no orthogonal skew-symmetric $K$ exists |
| **2B.** Complex skew-Hermitian unitary conjugation $A + U B U^*$ ($U^* = -U$, $U^* U = I_n$) | **False** | For $n \ge 3$, $A = \mathrm{diag}(3,2,1)$, $B = \mathrm{diag}(2,3,1)$ has Fiedler optimum $4 I_3$ realized by a $3$-cycle permutation $P$, while no $U$ with $U^* = -U$ can conjugate $B$ to $\mathrm{diag}(1,2,3)$ |
| **3.** Lie-algebraic product antisymmetrization $[A, B] = A B - B A$ | **False** | Both Lidskii–Fiedler extrema occur at $[A, B] = 0$; maximizing $\|[A, B]\|_F^2$ on traceless $2 \times 2$ pairs yields intermediate spread $2\sqrt{a^2+b^2}$ strictly between $2\lvert a-b\rvert$ and $2(a+b)$ |
| **4.** Young alternating permutation projector $\mathrm{Alt}(\beta) = \frac{1}{n!}\sum_{\sigma \in S_n} \mathrm{sgn}(\sigma)\sigma(\beta)$ | **False** | $\mathrm{Alt}(\beta) = 0$ identically for all $n \ge 3$, and has coordinate sum $0 \ne \mathrm{tr}(B)$ for $n = 2$; moreover $w_0$ has $\binom{n}{2}$ inversions and is an **even** permutation whenever $n \equiv 0, 1 \pmod{4}$ ($n = 4, 5, \dots$) |
| **5.** Fiedler algebraic connectivity $\lambda_2^\uparrow(L_1 + L_2)$ on graph Laplacians (Fiedler 1973) | **False** | Superadditivity $\lambda_2^\uparrow(L_1 + L_2) \ge \lambda_2^\uparrow(L_1) + \lambda_2^\uparrow(L_2)$ is realized by symmetric commuting Laplacians ($L_1 = L_2 = L_{K_3}$, $\mathcal{A} = 0$), whereas skew circulations $K_t$ yield complex spectra $6 \pm i\sqrt{3}\,t$ |

---

## Minimal Explicit Counterexamples (Extending to All $n \ge 2$)

1. **Destruction of Weyl/Ky Fan and Fiedler bounds by antisymmetric parts (Reading 1B):**
   $$M_1 = \begin{pmatrix} 4 & 1 \\ -1 & 2 \end{pmatrix}, \qquad M_2 = \begin{pmatrix} 4 & -1 \\ 1 & 2 \end{pmatrix}, \qquad M_1 + M_2 = \begin{pmatrix} 8 & 0 \\ 0 & 4 \end{pmatrix}.$$
   Since $\bigl(M_1 - 3 I_2\bigr)^2 = \bigl(M_2 - 3 I_2\bigr)^2 = 0$, both $M_1$ and $M_2$ have exact real spectrum $\bigl(3, 3\bigr)$, so every permutation sum of their eigenvalues equals $\bigl(6, 6\bigr)$. Yet $M_1 + M_2$ has eigenvalues $\bigl(8, 4\bigr)$: its largest eigenvalue $8 \gt 6$ violates Weyl/Ky Fan subadditivity, and $\det(M_1 + M_2) = 32 \lt 36$ violates Fiedler's determinant inequality.

2. **Failure of skew-symmetric orthogonal conjugation vs. symmetric reflection (Reading 2A):**
   $$A = \begin{pmatrix} 25 & 0 \\ 0 & 0 \end{pmatrix}, \qquad B = \begin{pmatrix} 16 & 12 \\ 12 & 9 \end{pmatrix}, \qquad Q = \frac{1}{5}\begin{pmatrix} -3 & 4 \\ 4 & 3 \end{pmatrix}, \qquad J_2 = \begin{pmatrix} 0 & 1 \\ -1 & 0 \end{pmatrix}.$$
   Both $A$ and $B$ are integer positive semidefinite symmetric matrices with spectrum $\bigl(25, 0\bigr)$. The **symmetric** orthogonal reflection $Q$ ($Q^\top = Q$, $Q^2 = I_2$) realizes the Fiedler reverse-order optimum $A + Q B Q^\top = 25 I_2$ ($\det = 625$, spread $0$), whereas **every** real orthogonal skew-symmetric matrix $K = \pm J_2$ ($K^\top = -K$, $K^\top K = I_2$) gives $A + K B K^\top = \bigl(\begin{smallmatrix}34 & -12 \\ -12 & 16\end{smallmatrix}\bigr)$ with eigenvalues $\bigl(40, 10\bigr)$ and $\det = 400 \lt 625$.

3. **Three-cycle obstruction to skew-Hermitian unitary conjugation (Reading 2B, $n \ge 3$):**
   For $A = \mathrm{diag}(3, 2, 1)$ and $B = \mathrm{diag}(2, 3, 1)$, the Fiedler optimum $4 I_3$ ($\det = 64$) is attained by $P B P^*$ where $P$ is the $3$-cycle permutation matrix mapping $\bigl(2, 3, 1\bigr) \mapsto \bigl(1, 2, 3\bigr)$. Because $B$ has distinct eigenvalues, every matrix $U \in M_3(\mathbb{C})$ satisfying $U B U^* = \mathrm{diag}(1, 2, 3)$ and $U U^* = I_3$ must have $U_{1,3} \ne 0$ and $U_{3,1} = 0$, making $U^* = -U$ impossible.

---

## Package Layout and Verification

- `SOURCE.md` — Original bilingual problem statement (unmodified).
- `main.tex` / `main.pdf` — Self-contained mathematical paper proving the positive ordering-corrected theorems (rearrangement, Fiedler's $n \times n$ permutation product bounds and reverse-order uniqueness, $n \times n$ Ky Fan majorization, $2 \times 2$ Lidskii–Wielandt–Fiedler and Bloch commutator identities, Bendixson's quadratic-form theorem) and refuting all five readings of antisymmetrization optimality.
- `lean/` — Standalone Core Lean 4 (`leanprover/lean4:v4.19.0`) formalization with zero external dependencies, compiled with `-DwarningAsError=true` and zero `sorry`s:
  - `lean/lean-toolchain`, `lean/lakefile.toml`, `lean/lake-manifest.json`
  - `lean/Main.lean` — Constructive `Int` and `QField` instances, Cartesian decomposition $M = \mathcal{S}(M) + \mathcal{A}(M)$ and uniqueness, Bendixson quadratic-form vanishing, all-$n$ rearrangement and Fiedler permutation product theorems with strict uniqueness of `revPerm n`, $n \times n$ Ky Fan additive majorization, $2 \times 2$ Lidskii–Wielandt–Fiedler and commutator theorems, all five refutation families, and the master resolution theorem `conjecture_00000007169_complete_resolution`.
- `verify.py` — Pure-Python verification suite checking exact rational counterexamples ($n = 2..6$), exhaustive $S_2..S_5$ permutation bounds, $300$ random Laplacian pairs, and $1{,}200$ random real symmetric and complex Hermitian matrix pairs.
- `verification/` — Complete build and audit logs (`lake-build.log`, `lean-axioms.log`, `lean-version.log`, `pdf-build.log`, `python-verify.log`, `SELF_REVIEW.md`).
