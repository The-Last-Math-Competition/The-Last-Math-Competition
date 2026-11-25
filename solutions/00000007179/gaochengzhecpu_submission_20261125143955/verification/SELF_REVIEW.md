# Self-Review & Verification Audit — Conjecture 00000007179

## 1. Source Integrity & Bilingual Problem Alignment
- `SOURCE.md` was verified byte-identically untouched (473 bytes).
- Both the English statement (*"Definition: The stability of perturbed spectra with Kato theory. Conjecture: Simple eigenvalues are analytically perturbable, and the coefficient of the perturbation is the residual projection. (residual-projection Kato analytic perturbation)"*) and the parallel Chinese statement (*"定义：摄动谱的稳定性：Kato 理论。猜想：Kato 的摄动：单重特征值的解析摄动且动的系数为残余投影。（Kato 残余投影解析摄动单重特征值）"*) were analyzed side-by-side.
- The conjecture has the logical structure $P_1 \land P_2$:
  - **Clause 1 ($P_1$ — TRUE):** Simple eigenvalues are analytically perturbable around $\varepsilon = 0$ for $A(\varepsilon) = A_0 + \varepsilon A_1$.
  - **Clause 2 ($P_2$ — FALSE):** The coefficient of the perturbation is the residual projection $Q = I - P$.
  - **Compound Verdict:** **FALSE**.

## 2. Mathematical Completeness Audit
1. **Clause 1 (Positive Kato Analytic Perturbation Theorem):**
   - **Lagrange–Sylvester–Riesz Polynomial Decomposition:** Proved over any field that whenever $(A_0 - \lambda_0 I) q(A_0) = 0$ with $q(\lambda_0) \ne 0$, the explicit polynomials $P = q(\lambda_0)^{-1} q(A_0)$, $Q = I - P$, and $S = - q(\lambda_0)^{-1} r(A_0) Q$ (with $q(x) - q(\lambda_0) = (x - \lambda_0) r(x)$) satisfy all Riesz–Kato projection and reduced-resolvent identities (even when complementary eigenvalues $\mu_j \ne \lambda_0$ possess non-trivial Jordan blocks), and proved uniqueness of $S$.
   - **All-Orders Formal Power Series Existence & Uniqueness:** Constructed $(\lambda_k, v_k)_{k \ge 0}$ and proved normalization $w_0^\top v_k = 0$ ($k \ge 1$), exact formal power series satisfaction at every order $k \ge 0$, and strong-induction uniqueness.
   - **Exact Closed-Form Kato Formulas:**
     - $\lambda_1 = \mathrm{tr}(P A_1) = \mathrm{tr}(P A_1 P) = \frac{w_0^\top A_1 v_0}{w_0^\top v_0}$ (governed by the eigenprojection $P$),
     - $v_1 = - S A_1 v_0$ (governed by the reduced resolvent $S$),
     - $\lambda_2 = - \mathrm{tr}(P A_1 S A_1) = - \frac{w_0^\top A_1 S A_1 v_0}{w_0^\top v_0}$ (governed by $P$ and $S$),
     - $P_1 = - P A_1 S - S A_1 P$ (satisfying linearized idempotence and commutation).
   - **Explicit Positive Analytic Convergence Radius:** Proved via a discrete inverse-square convolution bound that $R_0 = \rho^{-1} \gt 0$ ($\rho = 4\beta + 8\alpha\sigma\|v_0\|_1 + 1$) satisfies $\|v_k\|_1 \le \frac{\|v_0\|_1}{(k + 1)^2} \rho^k$ and $|\lambda_k| \le \frac{\alpha\|v_0\|_1}{k^2} \rho^{k-1}$, yielding uniform $O(1/N)$ Cauchy tail bounds on $|\varepsilon| \le R_0$.
2. **Clause 2 (Exhaustive Refutation Across All Four Candidate Readings):**
   - **Reading A ($\lambda_1$ via $Q = I - P$):** Proved universal $n \times n$ trace-duality impossibility ($\neg \forall A_1,\; \lambda_1(A_1) = \mathrm{tr}(Q A_1)$ since $M = P \ne Q$), universal Rayleigh vanishing $\frac{w_0^\top Q A_1 v_0}{w_0^\top v_0} = 0$, and concrete counterexamples on $A_0 = \mathrm{diag}(2, 0)$ at $\lambda_0 = 2$ with $A_1 = \mathrm{diag}(1, 0)$ ($\lambda_1 = 1 \ne 0 = \mathrm{tr}(Q A_1)$), $A_1 = \mathrm{diag}(0, 5)$ ($\lambda_1 = 0 \ne \pm 5 = \pm\mathrm{tr}(Q A_1)$), and $A_1 = \begin{pmatrix} 0 & 1 \\ 1 & 0 \end{pmatrix}$ ($\lambda_1 = 0$, $\|Q A_1 v_0\|_1 = \|Q A_1 v_0\|_2^2 = 1$).
   - **Reading B ($v_1 = \pm Q A_1 v_0$):** Refuted on $A_0 = \mathrm{diag}(5, 1)$ at $\lambda_0 = 5$ with $A_1 = \begin{pmatrix} 0 & 1 \\ 1 & 0 \end{pmatrix}$ ($v_1 = \frac{1}{4} e_2 \ne \pm e_2$).
   - **Reading C ($\lambda_2 = \pm\mathrm{tr}(P A_1 Q A_1)$):** Refuted on $A_0 = \mathrm{diag}(5, 1)$ with $A_1 = \begin{pmatrix} 0 & 1 \\ 1 & 0 \end{pmatrix}$ ($\lambda_2 = \frac{1}{4} \ne \pm 1$).
   - **Reading D ($P_1$ via $Q$):** Refuted on $A_0 = \mathrm{diag}(5, 1)$ with $A_1 = \begin{pmatrix} 0 & 1 \\ 1 & 0 \end{pmatrix}$ ($P_1 = \frac{1}{4} A_1 \notin \{\pm Q, \pm(P A_1 Q + Q A_1 P)\}$).
3. **Sharpness of Simplicity:** Proved that the defective Jordan perturbation $A(\varepsilon) = \begin{pmatrix} 0 & 1 \\ \varepsilon & 0 \end{pmatrix}$ around the algebraically double eigenvalue $\lambda_0 = 0$ admits neither a formal power series eigenvalue root nor a formal power series eigenpair.

## 3. Core Lean 4.19.0 Formalization Audit
- Toolchain: `leanprover/lean4:v4.19.0`, zero external dependencies (Core Lean 4 only), compiled with `moreLeanArgs = ["-DwarningAsError=true"]`.
- Zero `sorry`, `admit`, `native_decide`, or custom `axiom` declarations across all four `.lean` modules; `.lake/` build cache deleted after capturing build and axiom logs.
- Constructive non-vacuity verified via `instance : LinearOrderedField Q` and unconditional theorem `conjecture_00000007179_resolved_over_Q`.
- `#print axioms` audited across all 19 core and top-level theorems (`lean-axioms.log`): depends exclusively on standard Lean kernel axioms (`propext`, `Classical.choice`, `Quot.sound`).

## 4. Independent Computational & Typesetting Audit
- `verify.py` uses exact `fractions.Fraction` arithmetic across 150 Riesz–Kato decompositions ($2 \le n \le 6$), 120 all-orders Kato series & majorant trials ($k \le 8$), Readings A–D counterexamples with Riesz contour quadrature cross-check, and the defective Puiseux obstruction; exits with code `0` (`python-verify.log`).
- `main.tex` compiled cleanly via `pdflatex` (`pdf-build.log`) with 0 errors and 0 overfull boxes, and `main.pdf` was visually inspected page by page.
- `README.md` and `pr_body.md` passed automated linting for all GitHub Markdown MathJax rules.
