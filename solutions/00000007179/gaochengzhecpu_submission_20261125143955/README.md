# Conjecture 00000007179 — Resolution Package

## Problem Statement

- **English:** *Definition: The stability of perturbed spectra with Kato theory. Conjecture: Simple eigenvalues are analytically perturbable, and the coefficient of the perturbation is the residual projection. (residual-projection Kato analytic perturbation)*
- **Chinese:** *定义：摄动谱的稳定性：Kato 理论。猜想：Kato 的摄动：单重特征值的解析摄动且动的系数为残余投影。（Kato 残余投影解析摄动单重特征值）*

## Verdict: **FALSE** (Clause 1 is **TRUE**; Clause 2 is **FALSE** across all readings)

Conjecture `00000007179` asserts a two-part conjunction $P_1 \land P_2$ for perturbed linear operators $A(\varepsilon) = A_0 + \varepsilon A_1$ around an algebraically simple eigenvalue $\lambda_0$ of $A_0$:

1. **Clause 1 ($P_1$ — TRUE):** Around every algebraically simple root $\lambda_0$ of $\chi_{A_0}(x) = \bigl(x - \lambda_0\bigr) q(x)$ with $q(\lambda_0) \ne 0$, let $v_0, w_0$ be right and left eigenvectors ($A_0 v_0 = \lambda_0 v_0$, $A_0^\top w_0 = \lambda_0 w_0$, $w_0^\top v_0 \ne 0$), let $P = q(\lambda_0)^{-1} q(A_0) = \frac{v_0 w_0^\top}{w_0^\top v_0}$ be the rank-one **Riesz spectral eigenprojection** ($P^2 = P$, $\mathrm{tr}(P) = 1$, $A_0 P = P A_0 = \lambda_0 P$), let $Q = I - P$ be the **complementary (residual) projection** onto $\mathrm{im}(A_0 - \lambda_0 I)$, and let $S$ be the unique **Kato reduced resolvent** satisfying $\bigl(A_0 - \lambda_0 I\bigr) S = S \bigl(A_0 - \lambda_0 I\bigr) = Q$ and $P S = S P = 0$. Then there exists a **unique** normalized perturbation series $\lambda(\varepsilon) = \sum_{k=0}^\infty \lambda_k \varepsilon^k$, $v(\varepsilon) = \sum_{k=0}^\infty v_k \varepsilon^k$ ($w_0^\top v_k = 0$ for $k \ge 1$) satisfying $\bigl(A_0 + \varepsilon A_1\bigr) v(\varepsilon) = \lambda(\varepsilon) v(\varepsilon)$ with an explicit positive Cauchy–Kato radius of analytic convergence $R_0 = \rho^{-1} \gt 0$, whose exact leading coefficients are:
   $$\lambda_1 \;=\; \mathrm{tr}(P A_1) \;=\; \mathrm{tr}(P A_1 P) \;=\; \frac{w_0^\top A_1 v_0}{w_0^\top v_0}, \qquad v_1 \;=\; - S A_1 v_0, \qquad \lambda_2 \;=\; -\mathrm{tr}(P A_1 S A_1) \;=\; -\frac{w_0^\top A_1 S A_1 v_0}{w_0^\top v_0}.$$

2. **Clause 2 ($P_2$ — FALSE under every standard mathematical reading):** The claim *"and the coefficient of the perturbation is the residual projection"* ($Q = I - P$) fails across all four candidate interpretations:
   - **Reading A (First-order eigenvalue shift $\lambda_1$ via $Q = I - P$):** By trace duality, $P$ is the unique matrix representing $A_1 \mapsto \lambda_1(A_1) = \mathrm{tr}(M A_1)$, and $P \ne Q$ for every simple eigenvalue in every dimension $n \ge 1$ ($P v_0 = v_0 \ne 0 = Q v_0$), while $\frac{w_0^\top Q A_1 v_0}{w_0^\top v_0} = 0$ identically. Concretely, on $A_0 = \mathrm{diag}(2, 0)$ at $\lambda_0 = 2$ ($P = \mathrm{diag}(1, 0)$, $Q = \mathrm{diag}(0, 1)$):
     - For $A_1 = \mathrm{diag}(1, 0)$, $\lambda(\varepsilon) = 2 + \varepsilon$ gives $\lambda_1 = 1$, whereas $\mathrm{tr}(Q A_1) = 0 \ne 1$ and $\|Q A_1 v_0\|_1 = 0 \ne 1$.
     - For $A_1 = \mathrm{diag}(0, 5)$, $\lambda(\varepsilon) = 2$ gives $\lambda_1 = 0$, whereas $\mathrm{tr}(Q A_1) = 5 \ne 0$ ($\lambda_1 \ne \pm\mathrm{tr}(Q A_1)$).
     - For off-diagonal $A_1 = \begin{pmatrix} 0 & 1 \\ 1 & 0 \end{pmatrix}$, $\lambda(\varepsilon) = 1 + \sqrt{1 + \varepsilon^2}$ gives $\lambda_1 = 0$, whereas $Q A_1 v_0 = e_2$ has $\|Q A_1 v_0\|_1 = \|Q A_1 v_0\|_2^2 = 1 \ne 0$.
   - **Reading B (First-order eigenvector slope $v_1 = \pm Q A_1 v_0$):** On $A_0 = \mathrm{diag}(5, 1)$ at $\lambda_0 = 5$ with $A_1 = \begin{pmatrix} 0 & 1 \\ 1 & 0 \end{pmatrix}$, the reduced resolvent is $S = \mathrm{diag}(0, -1/4)$, so the exact Kato slope is $v_1 = - S A_1 e_1 = \frac{1}{4} e_2$ (weighted by the inverse spectral gap $\bigl(5 - 1\bigr)^{-1} = \frac{1}{4}$), whereas $\pm Q A_1 e_1 = \pm e_2 \ne \frac{1}{4} e_2$.
   - **Reading C (Second-order eigenvalue coefficient $\lambda_2 = \pm\mathrm{tr}(P A_1 Q A_1)$):** On the same $A_0 = \mathrm{diag}(5, 1)$ and $A_1 = \begin{pmatrix} 0 & 1 \\ 1 & 0 \end{pmatrix}$, $\lambda(\varepsilon) = 3 + \sqrt{4 + \varepsilon^2} = 5 + \frac{1}{4}\varepsilon^2 - \frac{1}{64}\varepsilon^4 + \cdots$ has $\lambda_2 = \frac{1}{4}$, whereas $\pm\mathrm{tr}(P A_1 Q A_1) = \pm 1 \ne \frac{1}{4}$.
   - **Reading D (First-order eigenprojection derivative $P_1$ via $Q$):** On the same $A_0 = \mathrm{diag}(5, 1)$ and $A_1 = \begin{pmatrix} 0 & 1 \\ 1 & 0 \end{pmatrix}$, $P_1 = - P A_1 S - S A_1 P = \frac{1}{4} A_1$, which disagrees with both $\pm Q$ and $\pm\bigl(P A_1 Q + Q A_1 P\bigr) = \pm A_1$.

*(Sharpness note: Algebraic simplicity in Clause 1 is indispensable — for the defective Jordan block perturbation $A(\varepsilon) = \begin{pmatrix} 0 & 1 \\ \varepsilon & 0 \end{pmatrix}$ at the double eigenvalue $\lambda_0 = 0$, $\chi_{A(\varepsilon)}(\lambda) = \lambda^2 - \varepsilon$ has fractional Puiseux branches $\pm\sqrt{\varepsilon}$ and admits no formal power series root or eigenvector over any field.)*

## Origin of the Misconception

In Kato's contour formalism, the eigenprojection $P = -\frac{1}{2\pi i}\oint_\Gamma \bigl(A_0 - \zeta I\bigr)^{-1}\,d\zeta = \mathrm{Res}_{\zeta = \lambda_0}\bigl(\zeta I - A_0\bigr)^{-1}$ is the **Cauchy residue** of the resolvent at $\lambda_0$, and $\lambda_1 = \mathrm{tr}(P A_1)$ is governed by this *residue projection* $P$. Conflating **residue projection** ($P$) with **residual projection** ($Q = I - P$, projecting onto $\mathrm{im}(A_0 - \lambda_0 I)$), or conflating the right-hand side $-Q A_1 v_0$ of $\bigl(A_0 - \lambda_0 I\bigr) v_1 = -Q A_1 v_0$ with its reduced-resolvent solution $v_1 = - S A_1 v_0$, produces the false second clause.

## Package Structure

- `SOURCE.md` — Original bilingual problem statement (unmodified).
- `main.tex` / `main.pdf` — Self-contained mathematical paper proving Clause 1 (including the Lagrange–Sylvester–Riesz polynomial decomposition, all-orders uniqueness, and explicit Cauchy–Kato convergence radius) and refuting Clause 2 across Readings A–D, plus sharpness of simplicity.
- `verify.py` — Standalone Python 3 exact `fractions.Fraction` verification suite (150 non-symmetric and Jordan-complement Riesz–Kato decompositions for $2 \le n \le 6$, 120 all-orders Kato series trials up to $k = 8$ with characteristic-polynomial congruences and Cauchy–Kato majorant bounds, Readings A–D counterexamples with Riesz contour quadrature cross-check, and defective Jordan obstruction).
- `lean/` — Zero-dependency **Core Lean 4.19.0** (`leanprover/lean4:v4.19.0`) formalization compiled with `-DwarningAsError=true` and zero `sorry`/`admit`/`native_decide`/custom axioms:
  - `Conjecture00000007179/OrderedField.lean`: Self-contained `LinearOrderedField` axiomatization, $\ell_1$/sum norms, finite sums, and constructive exact rational field `Q` (`instance : LinearOrderedField Q`).
  - `Conjecture00000007179/KatoPerturbation.lean`: Lagrange–Sylvester–Riesz polynomial construction, reduced-resolvent uniqueness, all-orders Kato formal power series existence & uniqueness, closed-form $\lambda_1, v_1, \lambda_2, P_1$, and explicit Cauchy–Kato convergence radius $R_0 \gt 0$ with $O(1/N)$ Cauchy tail bounds.
  - `Conjecture00000007179/Refutation.lean`: Universal $n \times n$ trace-duality refutation, concrete refutations of Readings A, B, C, and D, and defective Jordan Puiseux impossibility.
  - `Conjecture00000007179.lean`: Top-level resolution theorems `conjecture_00000007179_clause1_true`, `conjecture_00000007179_clause2_false`, and `conjecture_00000007179_resolved_over_Q`.
- `verification/` — Build and audit logs (`lake-build.log`, `lean-axioms.log`, `lean-version.log`, `pdf-build.log`, `python-verify.log`, `SELF_REVIEW.md`).
