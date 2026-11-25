# Conjecture 00000001290 — Disproof and Formal Resolution

## Verdict: **FALSE**

Conjecture `00000001290` asserts:

> **English.** Conjecture: The generating function of Sprague–Grundy values is rational if and only if the game is short and local (a rationality criterion).
>
> **中文。** 猜想：sprague-grundy 值的生成函数为有理 ⟺ 博弈为短局部(rationality 判据)。

The equivalence is **false** under every standard combinatorial-game-theory convention for **short**, **local** (bounded move step $\lvert n - m \rvert \le K$, bounded out-degree $\lvert \mathrm{Opts}(n) \rvert \le B$, and translation-invariant finite subtraction rules), and **the generating function of Sprague–Grundy values** (the ordinary value generating function $\sum_{n \ge 0} \mathcal{G}(n) x^n \in \mathbb{Q}(x)$, all Grundy-fiber indicator series $\sum_{\mathcal{G}(n)=v} x^n \in \mathbb{Q}(x)$, the $\mathcal{P}$-position series $\sum_{\mathcal{G}(n)=0} x^n \in \mathbb{Q}(x)$, and the bivariate series $\sum_{n \ge 0} x^n t^{\mathcal{G}(n)} \in \mathbb{Q}(x, t)$).

---

## Mathematical Summary

### 1. Refutation of Necessity ($\Rightarrow$): Rational GF Does Not Imply Local or Short

* **Counterexample 1 (Single-Pile Nim — Short, Non-Local, Unbounded Grundy Values):**
  On $\mathbb{N}$ with $\mathrm{Opts}(n) = \{0, 1, \dots, n - 1\}$, Nim is short and has $\mathcal{G}(n) = n$. Its value OGF, bivariate GF, and fiber indicator GFs are all rational:
  $$F_{\mathcal{G}}(x) = \sum_{n=0}^{\infty} n x^n = \frac{x}{(1 - x)^2}, \qquad \Phi_{\mathcal{G}}(x, t) = \frac{1}{1 - x t}, \qquad F_{\mathcal{G}, v}(x) = x^v.$$
  Yet moves $n \to 0$ have unbounded step distance $n$ and unbounded out-degree $n$. Because every game with out-degree bounded by $B$ satisfies $\mathcal{G}(n) \le B$ for all $n$, Nim is not even Grundy-equivalent to any bounded-outdegree game.

* **Counterexample 2 (Odd-Subtraction Game $\mathrm{Sub}(\mathrm{Odd})$ — Short, Translation-Invariant, Bounded Periodic Grundy Values, Non-Local):**
  Define $\mathrm{Opts}(n) = \{n - s : s \le n,\ s \equiv 1 \pmod{2}\}$. This is a genuine translation-invariant subtraction game with bounded $2$-periodic Sprague–Grundy sequence $\mathcal{G}(n) = n \bmod 2 \in \{0, 1\}$, so
  $$F_{\mathcal{G}}(x) = \frac{x}{1 - x^2}, \qquad F_{\mathcal{P}}(x) = F_{\mathcal{G}, 0}(x) = \frac{1}{1 - x^2}, \qquad F_{\mathcal{G}, 1}(x) = \frac{x}{1 - x^2}$$
  are all rational, while the subtraction set $S = \{1, 3, 5, \dots\}$, maximum move step, and out-degree $\lceil n / 2 \rceil$ are all unbounded.

* **Counterexample 3 (Step-$1$ Stopper-Sided Loopy Game & Infinitely-Branching Game — Non-Short, Rational GF):**
  Let $G_{\mathrm{loopy}}$ have $\mathrm{Opts}(1) = \{0, 2\}$, $\mathrm{Opts}(2) = \{1, 3\}$, $\mathrm{Opts}(3) = \{4\}$, and $\mathrm{Opts}(n) = \emptyset$ otherwise. Every move has step distance $\lvert n - m \rvert = 1$ and out-degree at most $2$, and the cycle $1 \leftrightarrow 2$ makes $G_{\mathrm{loopy}}$ non-short; nevertheless, it admits a unique Sprague–Grundy (and Smith) valuation $\mathcal{G} = (0, 1, 0, 1, 0, 0, \dots)$ with polynomial OGF $F_{\mathcal{G}}(x) = x + x^3$. Likewise, $G_{\infty}$ with $\mathrm{Opts}(0) = \mathbb{N}_{\gt 0}$ and $\mathrm{Opts}(n) = \emptyset$ for $n \ge 1$ has no infinite plays, fails finite branching, and has constant OGF $F_{\mathcal{G}}(x) = 1$.

### 2. Refutation of Sufficiency ($\Leftarrow$) Under Bounded-Step & Bounded-Degree Locality

* **Counterexample 4 (Lacunary Step-$1$ Short Game $G_{\mathrm{pow2}}$):**
  Define $\mathrm{Opts}(n) = \{n - 1\}$ if $n = 2^k$ for some $k \ge 2$, and $\mathrm{Opts}(n) = \emptyset$ otherwise. Every play has length at most $1$, every move has step distance $\lvert n - m \rvert = 1$, and out-degree is at most $1$, so $G_{\mathrm{pow2}}$ is both short and metric/degree-local. Since $2^k - 1 \ge 3$ is odd, $\mathcal{G}(n) = 1$ iff $n = 2^k$ ($k \ge 2$) and $0$ otherwise. Because the open interval $\bigl(2^{k-1}, 2^k\bigr)$ contains no power of $2$, an elementary polynomial-gap argument shows that both
  $$F_{\mathcal{G}}(x) = F_{\mathcal{G}, 1}(x) = \sum_{k=2}^{\infty} x^{2^k} \notin \mathbb{Q}(x) \quad \text{and} \quad F_{\mathcal{P}}(x) = F_{\mathcal{G}, 0}(x) = \frac{1}{1 - x} - \sum_{k=2}^{\infty} x^{2^k} \notin \mathbb{Q}(x)$$
  are irrational.

### 3. Positive Theorem: Sufficiency Holds for $1$D Finite Subtraction Games

* **Theorem (`sufficiency_holds_for_finiteSubtraction`):**
  For every finite subtraction set $S \subset \mathbb{N}_{\gt 0}$, the game $\mathrm{Sub}(S)$ is short, bounded-step local, and bounded-outdegree local, and its Sprague–Grundy sequence is eventually periodic via sliding state windows of width $1 + \max S$ over $\{0, \dots, \lvert S \rvert\}$. Consequently, $F_{\mathcal{G}}(x)$, $F_{\mathcal{P}}(x)$, and all fiber series $F_{\mathcal{G}, v}(x)$ belong to $\mathbb{Q}(x)$.

---

## Repository Structure

* [`SOURCE.md`](SOURCE.md) — Original conjecture statement (untouched).
* [`main.tex`](main.tex) / [`main.pdf`](main.pdf) — Complete mathematical paper with self-contained proofs and truth-table analysis.
* [`verify.py`](verify.py) — Zero-dependency Python 3 verification suite using exact rational arithmetic (`fractions.Fraction`), Hankel-rank analysis, Smith's loopy game solver, and exhaustive checks over all $63$ non-empty finite subtraction sets $S \subseteq \{1, \dots, 6\}$.
* [`lean/`](lean/) — Complete formalization in Core Lean `4.19.0` (`-DwarningAsError=true`, zero external dependencies, zero `sorry`):
  * [`lean/Conjecture00000001290/Basic.lean`](lean/Conjecture00000001290/Basic.lean) — Impartial games, `IsShort`, locality predicates, constructive `listMex`, uniqueness, existence, and degree bounds.
  * [`lean/Conjecture00000001290/GeneratingFunction.lean`](lean/Conjecture00000001290/GeneratingFunction.lean) — Formal power series Cauchy products, rationality over $\mathbb{Z}[x]$ and $\mathbb{Q}[x]$ (`isRationalOGF_iff_Q`), and eventual-periodicity rationality theorems.
  * [`lean/Conjecture00000001290/PositiveSubtraction.lean`](lean/Conjecture00000001290/PositiveSubtraction.lean) — Infinite-to-finite pigeonhole principle and eventual periodicity / rationality for all finite subtraction games.
  * [`lean/Conjecture00000001290/Counterexamples.lean`](lean/Conjecture00000001290/Counterexamples.lean) — Formal counterexamples (`nimGame`, `oddSubGame`, `loopyStep1Game`, `infBranchGame`, `lacunaryLocalGame`) and lacunary irrationality proofs.
  * [`lean/Conjecture00000001290/Main.lean`](lean/Conjecture00000001290/Main.lean) — Formal statements of all conjecture interpretations and master disproof `conjecture_00000001290_false`.
  * [`lean/Conjecture00000001290/Axioms.lean`](lean/Conjecture00000001290/Axioms.lean) — `#print axioms` audit entrypoint.
* [`verification/`](verification/) — Reproducibility logs (`lake-build.log`, `lean-axioms.log`, `lean-version.log`, `pdf-build.log`, `python-verify.log`) and [`verification/SELF_REVIEW.md`](verification/SELF_REVIEW.md).

## Reproduction Commands

From inside `lean/`:
```bash
lake build
lake env lean Conjecture00000001290/Axioms.lean
```

From the package root:
```bash
python3 verify.py
pdflatex -interaction=nonstopmode main.tex
pdflatex -interaction=nonstopmode main.tex
```
