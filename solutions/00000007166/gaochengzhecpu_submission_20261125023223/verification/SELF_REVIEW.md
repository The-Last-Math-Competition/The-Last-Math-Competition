# Self-Review & Verification Audit — Conjecture 00000007166

## 1. Source Integrity & Problem Alignment
- `SOURCE.md` was verified byte-identically untouched (506 bytes).
- Both the English statement (*"Definition: The Kantorovich inequality with the multiplicative bound of the quotient. Conjecture: The optimal constant is an explicit function of the condition ratio, and the minimum of the function is the harmonic mean. (harmonic-mean Kantorovich constant)"*) and the parallel Chinese statement (*"定义：Kantorovich 不等式：商的乘性界。猜想：Kanto 的最优常数：常数为条件比的显式函数且函数的极小为调和平均。（Kantorovich 调和平均条件比最优常数）"*) were analyzed side-by-side.
- The conjecture has the logical structure $P_1 \land P_2$:
  - **Clause 1 ($P_1$ — TRUE):** The optimal multiplicative constant in the Kantorovich inequality is an explicit function $K(\kappa) = \frac{(\kappa + 1)^2}{4\kappa}$ of the spectral condition ratio $\kappa = M / m \ge 1$.
  - **Clause 2 ($P_2$ — FALSE):** The minimum of the function is the harmonic mean.
  - **Compound Verdict:** **FALSE**.

## 2. Mathematical Completeness Audit
1. **Clause 1 (Positive Theorem over any Linearly Ordered Field $\mathbb{F}$):**
   - Proved from two exact single-sum rational identities without appealing to real-analytic calculus or square roots:
     - Lower-bound identity: $S(ST - 1) = \sum_{i=1}^n w_i \frac{(\lambda_i - S)^2}{\lambda_i} \ge 0$, establishing $1 \le Q_A(x)$ and exact equality iff all active weights lie on a single eigenvalue.
     - Upper-bound Kantorovich identity: $\frac{(M + m)^2}{4Mm} - ST = \frac{(2S - (M + m))^2}{4Mm} + S \sum_{i=1}^n w_i \frac{(M - \lambda_i)(\lambda_i - m)}{Mm\lambda_i} \ge 0$, establishing $Q_A(x) \le \frac{(M + m)^2}{4Mm} = K(M/m) = \frac{\mathrm{AM}(M, m)}{\mathrm{HM}(M, m)}$ and exact equality iff $S = \mathrm{AM}(M, m)$ and active weights are supported on $\{m, M\}$.
   - Proved square-root-free sharpness for all $n \ge 2$ and $\kappa \ge 1$ via $x^* = q_{\min} + q_{\max}$ ($\|x^*\|^2 = 2$), including full orthogonal invariance for non-diagonal SPD matrices $A = Q\,\mathrm{diag}(\lambda_1, \dots, \lambda_n)\,Q^\top$.
2. **Clause 2 (Exhaustive Refutation Across All Four Candidate Readings):**
   - **Reading A ($\min_{\kappa \ge 1} K(\kappa)$ or $\min_{\kappa \gt 0} K(\kappa)$):** Proved $K(\kappa) - 1 = \frac{(\kappa - 1)^2}{4\kappa} \ge 0$, so the unique global minimum is $1$, disagreeing with both $\mathrm{HM}(M, m)$ (e.g. $(m, M) = (1, 3) \implies \mathrm{HM} = 3/2 \notin \{1, 4/3\}$; $(m, M) = (2, 2) \implies \mathrm{HM} = 2 \ne 1$) and normalized $\mathrm{HM}(\kappa, 1) \gt 1$ for all $\kappa \gt 1$.
   - **Reading B ($\min_{x \ne 0} Q_A(x)$ for fixed $A$):** Proved $\min_{x \ne 0} Q_A(x) = 1$ (attained on eigenspaces), disagreeing with $\mathrm{HM}(3, 1) = 3/2$ for $A = \mathrm{diag}(1, 3)$.
   - **Reading C (Reciprocal Wielandt–Kantorovich lower bound $R(\kappa) = \frac{4\kappa}{(\kappa + 1)^2}$):** Proved $R(M/m) = \frac{\mathrm{HM}(M, m)}{\mathrm{AM}(M, m)}$ ($R(3) = 3/4 \ne 3/2$), strict decrease on $[1, \infty)$, non-existence of a minimum on $[1, \infty)$, and $\inf_{\kappa \ge 1} R(\kappa) = 0$ via $\kappa = 1 + 4/\varepsilon$.
   - **Reading D (Rayleigh quotients):** Proved $m \lt \mathrm{HM}(M, m) \lt \mathrm{AM}(M, m)$ for $0 \lt m \lt M$, and $\mathrm{HM}(3, 1)^{-1} = 2/3 \ne 3/2 = \mathrm{HM}(3, 1)$ at the Kantorovich extremizer.

## 3. Core Lean 4.19.0 Formalization Audit
- Toolchain: `leanprover/lean4:v4.19.0`, zero external dependencies (Core Lean 4 only), compiled with `moreLeanArgs = ["-DwarningAsError=true"]`.
- Zero `sorry`, `admit`, `native_decide`, or custom `axiom` declarations.
- Constructive non-vacuity verified: `OrderedField.lean` constructs exact rationals `Q` from Core `Int` and proves `instance : LinearOrderedField Q`, enabling the unconditional, hypothesis-free theorem `conjecture_00000007166_resolved_over_Q`.
- `#print axioms` audited across all core and top-level theorems (`lean-axioms.log`): depends exclusively on standard Lean kernel axioms (`propext`, `Classical.choice`, `Quot.sound`).

## 4. Independent Computational & Typesetting Audit
- `verify.py` uses exact `fractions.Fraction` arithmetic across 400 master-identity trials, 125 rational Householder orthogonal SPD matrices ($2 \le n \le 6$), Readings A–D counterexamples, and simplex grid uniqueness checks; exits with code `0` (`python-verify.log`).
- `main.tex` compiled cleanly via `pdflatex` (`pdf-build.log`) with 0 errors and 0 overfull boxes, and every page of `main.pdf` was visually inspected.
- `README.md` and `pr_body.md` passed automated linting for GitHub Markdown math rendering rules (no `\operatorname`, `\bowtie`, `\coloneqq`, `\DeclareMathOperator`, `\newcommand`, raw `<`/`>` in math, `$(`, or local file paths).
