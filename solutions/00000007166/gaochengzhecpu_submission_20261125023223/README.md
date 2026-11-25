# Conjecture 00000007166 — Resolution Package

## Problem Statement

- **English:** *Definition: The Kantorovich inequality with the multiplicative bound of the quotient. Conjecture: The optimal constant is an explicit function of the condition ratio, and the minimum of the function is the harmonic mean. (harmonic-mean Kantorovich constant)*
- **Chinese:** *定义：Kantorovich 不等式：商的乘性界。猜想：Kanto 的最优常数：常数为条件比的显式函数且函数的极小为调和平均。（Kantorovich 调和平均条件比最优常数）*

## Verdict: **FALSE** (Clause 1 is **TRUE**; Clause 2 is **FALSE** across all readings)

Conjecture `00000007166` asserts a two-part conjunction $P_1 \land P_2$:
1. **Clause 1 ($P_1$ — TRUE):** For any $n \times n$ orthogonally diagonalizable symmetric positive-definite matrix $A = Q\,\mathrm{diag}(\lambda_1, \dots, \lambda_n)\,Q^\top$ over a linearly ordered field $\mathbb{F}$ (in particular over $\mathbb{Q}$ and $\mathbb{R}$) with eigenvalues bounded by $0 \lt m \le \lambda_i \le M$, condition ratio $\kappa = M / m \ge 1$, and any nonzero vector $x \in \mathbb{F}^n \setminus \{0\}$:
   $$1 \;\le\; \frac{\langle A x, x \rangle \langle A^{-1} x, x \rangle}{\|x\|^4} \;\le\; \frac{(M + m)^2}{4 M m} \;=\; \frac{(\kappa + 1)^2}{4\kappa} \;=\; K(\kappa).$$
   Moreover, for every dimension $n \ge 2$ and every $\kappa = M / m \ge 1$, the upper bound $K(\kappa) = \frac{\mathrm{AM}(M, m)}{\mathrm{HM}(M, m)}$ is **tight**, attained explicitly at the rational-coordinate superposition $x^* = q_{\min} + q_{\max}$ ($\|x^*\|^2 = 2$), where $\frac{\langle A x^*, x^* \rangle}{\|x^*\|^2} = \mathrm{AM}(M, m) = \frac{M + m}{2}$ and $\frac{\langle A^{-1} x^*, x^* \rangle}{\|x^*\|^2} = \mathrm{HM}(M, m)^{-1} = \frac{M + m}{2 M m}$.
2. **Clause 2 ($P_2$ — FALSE under every standard mathematical reading):** The claim *"and the minimum of the function is the harmonic mean"* fails across all four candidate interpretations:
   - **Reading A (Minimum of $K(\kappa) = \frac{(\kappa + 1)^2}{4\kappa}$ on $\kappa \ge 1$ or $\kappa \gt 0$):** Since $K(\kappa) - 1 = \frac{(\kappa - 1)^2}{4\kappa} \ge 0$, the unique global minimum of $K$ is the dimensionless constant $1$ (attained at $\kappa = 1$), **not** $\mathrm{HM}(M, m) = \frac{2 M m}{M + m}$ and **not** $\mathrm{HM}(\kappa, 1) = \frac{2\kappa}{\kappa + 1}$. For instance, at $m = 1, M = 3$ ($\kappa = 3$), $\min K = 1$ and $K(3) = 4/3$, whereas $\mathrm{HM}(3, 1) = 3/2 \notin \{1, 4/3\}$; at $m = M = 2$ ($\kappa = 1$), $\min K = K(1) = 1 \ne 2 = \mathrm{HM}(2, 2)$; and for every $\kappa \gt 1$, $\mathrm{HM}(\kappa, 1) \gt 1$.
   - **Reading B (Minimum of the Kantorovich quotient $Q_A(x)$ over $x \ne 0$ for fixed $A$):** By Cauchy–Schwarz, $\min_{x \ne 0} Q_A(x) = 1$ (attained on every eigenspace of $A$), which again disagrees with $\mathrm{HM}(M, m)$ and $\mathrm{HM}(\kappa, 1)$ (e.g. for $A = \mathrm{diag}(1, 3)$, $1 \ne 3/2$).
   - **Reading C (Reciprocal Wielandt–Kantorovich lower-bound function $R(\kappa) = \frac{4\kappa}{(\kappa + 1)^2}$):** Here $R(M / m) = \frac{\mathrm{HM}(M, m)}{\mathrm{AM}(M, m)}$ is the *ratio* of the harmonic mean to the arithmetic mean rather than $\mathrm{HM}(M, m)$ itself (at $m = 1, M = 3$, $R(3) = 3/4 \ne 3/2$). Furthermore, $R(1) = 1$ is the **maximum** of $R$ on $[1, \infty)$, $R$ is strictly decreasing on $[1, \infty)$ so it has **no minimum** on $[1, \infty)$, and $\inf_{\kappa \ge 1} R(\kappa) = 0 \ne \mathrm{HM}(M, m)$.
   - **Reading D (Rayleigh quotients at the minimum or at the Kantorovich extremizer):** Whenever $0 \lt m \lt M$, strict separation $m \lt \mathrm{HM}(M, m) \lt \mathrm{AM}(M, m)$ holds, so $\min_{x \ne 0} \frac{\langle A x, x \rangle}{\|x\|^2} = m \ne \mathrm{HM}(M, m)$, while at the extremizer $x^*$, $\frac{\langle A x^*, x^* \rangle}{\|x^*\|^2} = \mathrm{AM}(M, m) \ne \mathrm{HM}(M, m)$ and $\frac{\langle A^{-1} x^*, x^* \rangle}{\|x^*\|^2} = \mathrm{HM}(M, m)^{-1}$ (at $m = 1, M = 3$, equal to $2/3 \ne 3/2$).

## Origin of the Misconception

At the equal-weight Kantorovich extremizer ($w_{\min} = w_{\max} = 1/2$), the Rayleigh quotient of $A$ equals $\mathrm{AM}(M, m)$ while the harmonic Rayleigh quotient $\|x^*\|^2 / \langle A^{-1} x^*, x^* \rangle$ equals $\mathrm{HM}(M, m)$, yielding $K(M / m) = \frac{\mathrm{AM}(M, m)}{\mathrm{HM}(M, m)}$. Conflating the harmonic-mean denominator in this ratio with "the minimum of the function" (which is actually $1$) explains the false second clause.

## Package Structure

- `SOURCE.md` — Original bilingual problem statement (unmodified).
- `main.tex` / `main.pdf` — Self-contained mathematical paper proving Clause 1 from exact rational master identities and refuting Clause 2 across Readings A–D.
- `verify.py` — Standalone Python 3 verification suite using exact `fractions.Fraction` arithmetic (400 master-identity trials, 125 exact rational Householder orthogonal SPD matrices for $2 \le n \le 6$, Readings A–D counterexamples, and simplex equality checks).
- `lean/` — Zero-dependency **Core Lean 4.19.0** (`leanprover/lean4:v4.19.0`) formalization compiled with `-DwarningAsError=true` and zero `sorry`/`admit`/`native_decide`/custom axioms:
  - `Conjecture00000007166/OrderedField.lean`: Self-contained `LinearOrderedField` axiomatization, algebraic/inequality library, and constructive exact rational model `Q` (`instance : LinearOrderedField Q`).
  - `Conjecture00000007166/Kantorovich.lean`: Exact master identities, $n$-dimensional Kantorovich bounds, equality characterizations, $n \ge 2$ sharpness, and orthogonal invariance $A = Q\,\mathrm{diag}(\lambda)\,Q^\top$.
  - `Conjecture00000007166/Refutation.lean`: Formal refutations of Readings A, B, C, and D.
  - `Conjecture00000007166.lean`: Top-level summary theorems `conjecture_00000007166_clause1_true`, `conjecture_00000007166_clause2_false`, and `conjecture_00000007166_resolved_over_Q`.
- `verification/` — Build and audit logs (`lake-build.log`, `lean-axioms.log`, `lean-version.log`, `pdf-build.log`, `python-verify.log`, `SELF_REVIEW.md`).
