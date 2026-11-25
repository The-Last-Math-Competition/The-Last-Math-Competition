# Solution to Conjecture 00000000472

## Verdict: **DISPROVED** (False under all standard definitions of multi-indexed Eulerian polynomials $A_\alpha(t)$ and all nontrivial definitions of piecewise-constant multi-index $\alpha$)

### Conjecture Statement (`SOURCE.md`)

- **English:** *Definition: The Eulerian polynomial $A_n(t)$ of the Bernoulli distribution. Conjecture: The multivariate Eulerian polynomial $A_\alpha(t)$ has all real simple roots if and only if $\alpha$ is a piecewise-constant index (an explicit criterion, programmable for small indices).*
- **中文:** *定义：Bernoulli(分布) 的 Eulerian 多项式 $A_n(t)$。猜想：多重指标 Eulerian 多项式 $A_\alpha(t)$ 的根全为实数单根的充要条件是 $\alpha$ 为分段常数指标(显式判据,可编程验证小指标)。*

---

## Mathematical Summary

1. **Bilingual & Probabilistic Resolution:**
   - The classical Eulerian polynomial $A_n(t) = \sum_{w \in \mathfrak{S}_n} t^{\mathrm{des}(w)}$ governs the $\mathrm{Bernoulli}(p)$ distribution through its higher cumulants via Worpitzky's polylogarithm identity:
     $$\kappa_{n+1}(\mathrm{Bernoulli}(p)) = -\mathrm{Li}_{-n}\!\left(-\frac{p}{1-p}\right) = p(1-p)^n A_n\!\left(-\frac{p}{1-p}\right) \qquad (n \ge 1),$$
     as well as the raw moments $\mathbb{E}[G^n] = \frac{A_n(p)}{(1-p)^n}$ of the Bernoulli waiting-time $\mathrm{Geometric}(1-p)$ law.
   - In the original Chinese statement, **多重指标 Eulerian 多项式 $A_\alpha(t)$** literally denotes a **multi-indexed Eulerian polynomial** $A_\alpha(t)$ (univariate in $t$, indexed by a positive integer multi-index $\alpha = (\alpha_1, \dots, \alpha_m) \in \mathbb{Z}_{\ge 1}^m$).

2. **Universal Real-Simplicity Disproves Necessity ("Only If") Across All Canonical Families:**
   Using a single **Master Interlacing Operator** $\mathcal{T}_{r,s}(P)(t) = t(1-t)P'(t) + (r + st)P(t)$ and a direct combinatorial insertion–deletion reciprocity proof of Simion's recurrence, we prove that **every** nonempty positive integer multi-index $\alpha \in \mathbb{Z}_{\ge 1}^m$ produces a polynomial with **exclusively real simple roots**:
   - **MacMahon–Simion Multiset Eulerian Polynomials $A_\alpha^{\mathrm{ms}}(t)$:** Exact degree $|\alpha| - \max_i \alpha_i$, splitting over $\mathbb{R}$ into $|\alpha| - \max_i \alpha_i$ distinct strictly negative linear factors for *every* $\alpha \in \mathbb{Z}_{\ge 1}^m$.
   - **$t$-Shifted Multiset Eulerian Polynomials $\tilde{A}_\alpha^{\mathrm{ms}}(t) = t A_\alpha^{\mathrm{ms}}(t)$:** Exact degree $|\alpha| - \max_i \alpha_i + 1$, splitting into distinct real roots $\{0\} \cup \mathrm{Roots}(A_\alpha^{\mathrm{ms}})$ since $A_\alpha^{\mathrm{ms}}(0) = 1 \neq 0$.
   - **Multiple Polylogarithm Eulerian Polynomials $A_\alpha^{\mathrm{mpl}}(t)$ and $A_\alpha^{\mathrm{mpl},\star}(t)$:** Exact degree $|\alpha| - 1$, splitting into $|\alpha| - 1$ distinct strictly negative real roots for *every* $\alpha \in \mathbb{Z}_{\ge 1}^m$.
   - **Concrete Non-Piecewise-Constant Counterexamples:**
     - $\alpha = (1, 2)$: $A_{(1,2)}^{\mathrm{ms}}(t) = 1 + 2t$, unique simple real root $t = -1/2$.
     - $\alpha = (1, 2, 3)$ (strictly increasing, $60$ multiset permutations, zero equal adjacent entries): $A_{(1,2,3)}^{\mathrm{ms}}(t) = 1 + 17t + 33t^2 + 9t^3$, with strict rational sign alternation $A_{(1,2,3)}^{\mathrm{ms}}(-10) = -5869 \lt 0$, $A_{(1,2,3)}^{\mathrm{ms}}(-1) = 8 \gt 0$, $A_{(1,2,3)}^{\mathrm{ms}}(-1/3) = -4/3 \lt 0$, $A_{(1,2,3)}^{\mathrm{ms}}(0) = 1 \gt 0$, positive cubic discriminant $\Delta = 82{,}800 \gt 0$, and $3$ distinct simple real roots.
     - Infinite strictly increasing family $\alpha^{(m)} = (1, 2, \dots, m)$ ($m \ge 2$): pairwise distinct entries (all constant runs of length $1$), yet $\binom{m}{2}$ distinct negative simple real roots.

3. **Bidirectional Failure Under Alternative Multi-Index Conventions:**
   - **Unstripped Weak-Descent Polynomial $W_\alpha(t)$:** Non-piecewise-constant $\alpha = (1, 2)$ yields $W_{(1,2)}(t) = 2t + t^2$ (simple real roots $0, -2$), whereas constant $\alpha = (3, 3)$ yields $W_{(3,3)}(t) = t^2(1 + 9t + 9t^2 + t^3)$ (double root at $t = 0$).
   - **Savage–Schuster $\alpha$-Eulerian Polynomial $E_\alpha(t)$:** Strictly increasing $\alpha = (1, 2, 3)$ yields $E_{(1,2,3)}(t) = 1 + 4t + t^2$ (two simple real roots), whereas block-constant $\alpha = (2, 2, 1, 1, 2, 2)$ (all runs of length $2$) yields $E_{(2,2,1,1,2,2)}(t) = (1 + 3t)^2$ (double root at $t = -1/3$).

---

## Package Structure & Reproduction Commands

- `SOURCE.md` — Exact unmodified conjecture text (`conjectures/00000000472.md`).
- `main.tex`, `main.pdf` — Complete self-contained mathematical paper and compiled PDF.
- `verify.py` — Self-contained Python 3.12 verification suite (exact rational Sturm chains across $511$ multiset and $255$ multiple polylogarithm Eulerian polynomials, Bernoulli cumulant identity, and counterexample certificates).
- `lean/` — Self-contained Core Lean `v4.19.0` formalization (`Main.lean`, zero external dependencies, `-DwarningAsError=true`, zero `sorry`, zero `native_decide`, zero custom axioms):
  - Constructive $\mathbb{Q}$, Cauchy completion $\mathbb{R}$ (with polynomial Intermediate Value Theorem `Poly.poly_ivt`), and $\mathbb{C} = \mathbb{R}[i]$ (`Complex.mul_eq_zero`).
  - Master Interlacing Theorem (`Poly.interlaceOp_preserves_negSimpleRoots`), combinatorial multiset permutations (`multisetPerms`) and Simion's recurrence (`simion_recurrence`), universal theorems (`multiset_allRealSimple`, `mpl_allRealSimple`, `mplStar_allRealSimple`), concrete certificates (`counterexample_123_allRealSimple`, `strictIncFamily_counterexamples`), formal biconditional refutations (`disproof_conjecture472_*`), bidirectional failures (`weakDescent_bidirectional_failure`, `savageSchuster_bidirectional_failure`), and non-vacuity/non-tautology witnesses (`positive_witness_*`).
- `verification/` — Complete build, axiom, PDF, and Python verification logs plus `SELF_REVIEW.md`.

### How to Reproduce

```bash
# 1. Run exact rational Sturm & combinatorial Python verification
python verify.py

# 2. Build Core Lean 4.19.0 project and verify standard axioms only
cd lean
lake build
lake env lean -DwarningAsError=true Main.lean

# 3. Compile LaTeX manuscript (2 passes)
cd ..
pdflatex -interaction=nonstopmode -halt-on-error main.tex
pdflatex -interaction=nonstopmode -halt-on-error main.tex
```
