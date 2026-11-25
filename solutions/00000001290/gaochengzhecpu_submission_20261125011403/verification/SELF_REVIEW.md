# Self-Review Report — Conjecture 00000001290

## 1. Conjecture Statement & Fidelity Audit

* **Original Statement (`SOURCE.md`):**
  * **English:** *Conjecture: The generating function of Sprague–Grundy values is rational if and only if the game is short and local (a rationality criterion).*
  * **中文：** *猜想：sprague-grundy 值的生成函数为有理 ⟺ 博弈为短局部(rationality 判据)。*
* **`SOURCE.md` Integrity:** Verified byte-for-byte identical to the staged file (`286` bytes).
* **Resolution Verdict:** **FALSE** (both directions of the equivalence fail under general bounded-step / bounded-degree locality, and necessity fails unconditionally even under translation-invariant finite subtraction locality).

## 2. Coverage of Combinatorial Game Theory Conventions

To prevent any definitional loophole or vacuity, both the paper (`main.tex` / `main.pdf`) and the Core Lean `4.19.0` formalization (`lean/`) explicitly test all standard conventions:

1. **Shortness (`ImpartialGame.IsShort`):**
   * Defined faithfully as finite branching (`FinitelyBranching`) together with well-foundedness / absence of infinite plays (`NoInfinitePlay`).
   * Proved existence (`short_has_grundy`), uniqueness (`grundy_unique`), and the pigeonhole out-degree bound $\mathcal{G}(n) \le \lvert \mathrm{Opts}(n) \rvert$ (`grundy_le_outdegree`).
2. **Locality Notions:**
   * **Bounded-step / metric locality (`IsBoundedStepLocal`):** $\exists K,\ \forall m \in \mathrm{Opts}(n),\ \lvert n - m \rvert \le K$.
   * **Bounded out-degree locality (`IsBoundedOutDegree`):** $\exists B,\ \forall n,\ \lvert \mathrm{Opts}(n) \rvert \le B$.
   * **Translation-invariant finite subtraction locality (`IsFiniteSubtractionGame`):** $\mathrm{Opts}(n) = \{n - s : s \in S,\ s \le n\}$ for a finite list $S$ of positive integers.
   * Proved the hierarchy `IsFiniteSubtractionGame` $\Rightarrow$ `IsShort` $\land$ `IsBoundedStepLocal` $\land$ `IsBoundedOutDegree`.
3. **Generating Function Conventions:**
   * **Ordinary value generating function (`HasRationalGrundyOGF`):** $\sum_{n \ge 0} \mathcal{G}(n) x^n \in \mathbb{Q}(x)$, formalized both over $\mathbb{Z}[x]$ (`IsRationalOGF`) and directly over $\mathbb{Q}[x]$ (`IsRationalOGF_Q`), with formal equivalence proved by clearing denominators (`isRationalOGF_iff_Q`).
   * **All Grundy-fiber indicator series (`HasAllRationalGrundyFibers`):** $\sum_{\mathcal{G}(n)=v} x^n \in \mathbb{Q}(x)$ for every $v \in \mathbb{N}$ (and bivariate $\sum_{n \ge 0} x^n t^{\mathcal{G}(n)} \in \mathbb{Q}(x, t)$ in `main.tex`).
   * **$\mathcal{P}$-position indicator series (`HasRationalPPositionOGF`):** $\sum_{\mathcal{G}(n)=0} x^n \in \mathbb{Q}(x)$.

## 3. Verification of Counterexamples and Non-Vacuity

| Theorem / Witness | Lean Declaration | Verified Role |
| :--- | :--- | :--- |
| Single-pile Nim | `nimGame`, `nimGame_rational_ogf`, `nimGame_not_grundyEquiv_boundedOutDegree` | Short, rational OGF $\frac{x}{(1-x)^2}$ and fibers $x^v$; fails all locality notions and is not Grundy-equivalent to any bounded-degree game. |
| Odd-subtraction game $\mathrm{Sub}(\mathrm{Odd})$ | `oddSubGame`, `necessity_local_fails_bounded_periodic` | Short, translation-invariant subtraction game with bounded $2$-periodic $\mathcal{G}(n) = n \bmod 2$ and rational OGF $\frac{x}{1-x^2}$, yet non-local. |
| Step-$1$ loopy Smith game & $\infty$-branching game | `loopyStep1Game`, `infBranchGame`, `necessity_short_fails_even_when_local` | Step-$1$ local ($K = 1, B = 2$) loopy game with unique finite Sprague–Grundy/Smith valuation $\bigl(0, 1, 0, 1, 0, \dots\bigr)$ and polynomial OGF $x + x^3$; refutes necessity of shortness. |
| Lacunary step-$1$ short game $G_{\mathrm{pow2}}$ | `lacunaryLocalGame`, `sufficiency_fails_for_boundedStep_and_boundedOutDegree` | Short, step-$1$ local ($K = 1, B = 1$), yet both $\sum_{k \ge 2} x^{2^k}$ and $\sum_{\mathcal{G}(n)=0} x^n$ are formally proved irrational. |
| All $1$D finite subtraction games $\mathrm{Sub}(S)$ | `sufficiency_holds_for_finiteSubtraction` | Non-vacuity & positive sufficiency theorem: every finite subtraction game has eventually periodic Grundy values and rational value/fiber OGFs. |

## 4. Technical & Package Hygiene Checklist

* **Lean `4.19.0` Build:** `lake build` succeeds cleanly with `moreLeanArgs = ["-DwarningAsError=true"]` and zero external dependencies (`verification/lake-build.log`).
* **Axiom Audit:** Zero `sorry`, `admit`, `native_decide`, or custom `axiom` declarations. `#print axioms` (`verification/lean-axioms.log`) uses only standard Lean foundational axioms (`propext`, `Classical.choice`, `Quot.sound`).
* **Computational Verification:** `verify.py` passes all exact rational-arithmetic, Hankel-rank, Smith loopy valuation, $63$-game subtraction periodicity, and $2$D checks (`verification/python-verify.log`).
* **PDF Quality:** `main.pdf` compiled with `pdflatex` with `0` errors, `0` undefined references, and `0` overfull boxes (`verification/pdf-build.log`), and visually inspected page by page.
* **Cleanliness:** Removed `.lake/` build artifacts and LaTeX auxiliary files (`*.aux`, `*.out`, `*.toc`, root `*.log`). Checked `README.md` and `SELF_REVIEW.md` against all GitHub Markdown math formatting rules and path-hygiene rules.
