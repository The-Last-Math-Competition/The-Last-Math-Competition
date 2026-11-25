# Adversarial Self-Review (`00000000472`)

## 1. Conjecture Fidelity & Bilingual Audit

- **`SOURCE.md` Integrity:** Verified byte-for-byte identical (matching SHA-256) to `conjectures/00000000472.md`.
- **Bilingual Terminology Check:**
  - The Chinese text states: *"定义：Bernoulli(分布) 的 Eulerian 多项式 A_n(t)。猜想：多重指标 Eulerian 多项式 A_α(t) 的根全为实数单根的充要条件是 α 为分段常数指标(显式判据,可编程验证小指标)。"*
  - Note the crucial phrase **多重指标 Eulerian 多项式 $A_\alpha(t)$**: "多重指标" = *multi-index* $\alpha = (\alpha_1, \dots, \alpha_m) \in \mathbb{Z}_{\ge 1}^m$, and the argument $(t)$ is explicitly univariate. The English rendering "multivariate Eulerian polynomial $A_\alpha(t)$" is a standard translation artifact for "multi-indexed Eulerian polynomial $A_\alpha(t)$".
  - Both the Bernoulli($p$) connection ($A_n(t)$ governing the higher cumulants $\kappa_{n+1}(\mathrm{Bernoulli}(p)) = p(1-p)^n A_n(-p/(1-p))$ and Geometric($1-p$) waiting-time moments) and every standard mathematical realization of $A_\alpha(t)$ are explicitly derived in `main.tex`, tested in `verify.py`, and formalized in `lean/Main.lean`.

## 2. Coverage of All Mathematical Conventions

To ensure no reviewer can object that an alternative standard convention was intended, we refute the conjecture under **all** standard candidates:

| Candidate Family $A_\alpha(t)$ | Behavior Across $\alpha \in \mathbb{Z}_{\ge 1}^m$ | Direction(s) Refuted | Lean 4 Theorem |
|---|---|---|---|
| MacMahon–Simion multiset $A_\alpha^{\mathrm{ms}}(t)$ | Simple negative real roots for **every** $\alpha$ | Necessity ("only if") fails for every proper criterion | `multiset_allRealSimple`, `disproof_conjecture472_multiset_anyProper` |
| $t$-shifted multiset $t A_\alpha^{\mathrm{ms}}(t)$ | Simple non-positive real roots for **every** $\alpha$ | Necessity ("only if") fails for every proper criterion | `multiset_allRealSimple`, `disproof_conjecture472_shifted_anyProper` |
| Strict MPL Eulerian $A_\alpha^{\mathrm{mpl}}(t)$ | Simple negative real roots for **every** $\alpha$ | Necessity ("only if") fails for every proper criterion | `mpl_allRealSimple`, `disproof_conjecture472_mpl_anyProper` |
| Star MPL Eulerian $A_\alpha^{\mathrm{mpl},\star}(t)$ | Simple negative real roots for **every** $\alpha$ | Necessity ("only if") fails for every proper criterion | `mplStar_allRealSimple`, `disproof_conjecture472_mplStar_anyProper` |
| Unstripped weak-descent $W_\alpha(t)$ | $W_{(1,2)}=2t+t^2$ simple; $W_{(3,3)}$ has $0^2$ | **Both** necessity and sufficiency fail | `weakDescent_bidirectional_failure` |
| Savage–Schuster $E_\alpha(t)$ | $E_{(1,2,3)}=1+4t+t^2$ simple; $E_{(2,2,1,1,2,2)}=(1+3t)^2$ | **Both** necessity and sufficiency fail | `savageSchuster_bidirectional_failure` |

Similarly, all standard nontrivial definitions of "piecewise-constant index" are formalized simultaneously:
1. `IsConstantIndex`: $\alpha_1 = \dots = \alpha_m$.
2. `IsBlockConstantGe2`: $\alpha$ decomposes into constant contiguous blocks each of length $\ge 2$.
3. `HasAdjacentEqual`: $\exists i,\, \alpha_i = \alpha_{i+1}$.
4. `IsProperCriterion`: any predicate $C$ excluding at least one valid $\alpha \in \mathbb{Z}_{\ge 1}^m$.

## 3. Core Lean 4.19.0 Soundness & Anti-Vacuity Audit

- **Zero External Dependencies / Zero Forbidden Constructs:**
  - `lean-toolchain` = `leanprover/lean4:v4.19.0`; `lakefile.toml` has `moreLeanArgs = ["-DwarningAsError=true"]` and zero packages.
  - Audited `lean/Main.lean` for forbidden keywords: zero `sorry`, zero `admit`, zero `native_decide`, zero custom `axiom`, zero `unsafe`, zero `@[extern]`, zero `@[implemented_by]`, zero `opaque`.
  - `#print axioms` verified on all 20 core theorems: every theorem depends solely on subsets of `{propext, Classical.choice, Quot.sound}`.
- **Semantic Non-Vacuity & Non-Tautology Checks:**
  - `R` is constructed genuinely as the Cauchy completion of `Q` with proven Archimedean ordered field laws, rational density `R.dense_ofQ`, and constructive bisection Polynomial Intermediate Value Theorem `Poly.poly_ivt`.
  - `Complex` is constructed genuinely as `R × R` and proved to be an integral domain (`Complex.mul_eq_zero`).
  - `Poly.HasAllRealSimpleRoots P` requires `(∃ k, coeff P k ≠ 0) ∧ ∀ z : Complex, evalC P z = 0 → z.im = 0 ∧ evalC (deriv P) z ≠ 0` — directly expressing that $P$ is nonzero and every complex root of $P$ is real and simple.
  - **Non-tautology proved in Lean:** `positive_witness_nonreal_roots` proves `¬ Poly.HasAllRealSimpleRoots [1, 0, 1]` ($1 + t^2$ has root $i \in \mathbb{C}$), and `positive_witness_multiple_real_root` proves `¬ Poly.HasAllRealSimpleRoots [1, 2, 1]` ($(1+t)^2$ has double root $-1$).
  - **Non-vacuity proved in Lean:** `positive_witness_constant_11` proves `[1, 1]` simultaneously satisfies `ValidMultiIndex`, `IsConstantIndex`, `IsBlockConstantGe2`, `HasAdjacentEqual`, and `HasAllRealSimpleRoots`.
  - **Combinatorial exactness of `eulerianPoly`:** `multisetPerms_and_eulerianPoly_master` proves both `ListNodup (multisetPerms α)` and `w ∈ multisetPerms α ↔ ∀ v, countNat v w = targetCount α v`, guaranteeing `eulerianPoly α` is the exact descent generating polynomial over $\mathfrak{S}(1^{\alpha_1}\cdots m^{\alpha_m})$ rather than merely a recursively defined sequence.

## 4. Computational & Typesetting Verification

- **Python (`verify.py`):** Zero external packages (Python 3.12 stdlib `fractions.Fraction`). Verified exact Sturm root counts on $511/511$ multiset Eulerian polynomials ($|\alpha| \le 9$), $255/255$ MPL Eulerian polynomials ($|\alpha| \le 8$), 3-way combinatorial/MacMahon/Simion agreement ($127/127$ for $|\alpha| \le 7$), and exact cubic discriminant $\Delta(1 + 17t + 33t^2 + 9t^3) = 82{,}800 > 0$.
- **LaTeX (`main.tex` -> `main.pdf`):** Compiled cleanly in two passes with zero errors, zero undefined references/citations, and zero overfull/underfull boxes. All auxiliary build artifacts (`.aux`, `.log`, `.out`, `.lake/`) removed from the final package.
