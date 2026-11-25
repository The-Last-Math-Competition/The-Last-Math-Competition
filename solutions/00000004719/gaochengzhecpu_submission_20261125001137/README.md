# Conjecture 00000004719 — Complete Disproof & Core Lean 4.19.0 Formalization

## Verdict: **DISPROVED (FALSE under every natural reading)**

### Official Conjecture (`SOURCE.md`)
- **English:** *Definition: A balanced word is a word where letter counts of same-length factors differ by at most one. Conjecture: The count of multiletter balanced words is finite with a rational generating function, and the denominator is given explicitly by Christoffel-type structures. (rational generating function of balanced word counts)*
- **中文:** *定义：平衡词指同长因子的字母计数差不超过一的词。猜想：多字母平衡词的计数有限且母函数为有理,分母由 Christoffel 型结构显式给出。（多字母平衡计数有理母函数）*

---

## Summary of Mathematical Results

Because the conjecture's phrasing admits several mathematical interpretations, we formalize and refute **all** reasonable readings:

1. **Reading 1 — Total-Count Finiteness (`not_finite_surjBalancedWords`, `not_finite_balancedWords`, `not_finite_atLeastBalancedWords`):**
   - For every alphabet size $k \ge 1$ (specifically $k = 2$, $k = 3$, and all $k \ge 3$) and every length $n \ge k$, the periodic word $w_{k,n}[i] = i \bmod k$ uses all $k$ letters and is balanced. Moreover, Hubert's cyclic-splitting construction (`hubertSplit_isBalanced`, `hubertSplit_usesAllLetters`) lifts arbitrary binary balanced words to non-periodic $k$-letter balanced words. Hence the set of multiletter balanced words (and of strictly $k$-letter surjective balanced words) is **infinite**.

2. **Reading 2A–2D — Per-Length Univariate Generating Function ($\sum_{n \ge 0} c_k(n) x^n \in \mathbb{Q}(x)$):**
   - **Universal Modular Periodicity (`isRationalGF_implies_eventuallyPeriodicMod`):** Every sequence $a : \mathbb{N} \to \mathbb{N}$ whose ordinary generating function is rational over $\mathbb{Q}$ is eventually periodic modulo every prime $p \ge 2$.
   - **Binary Case $k = 2$ (`balancedCount_two_eq_lipatov`, `not_isRationalGF_balancedCount_two`, `not_isRationalGF_surjBalancedCount_two`):** Proving Lipatov's exact formula $b_2(n) = 1 + \sum_{m=1}^n (n + 1 - m)\varphi(m)$ from first principles via mechanical Christoffel central words gives $\Delta^2 b_2(n) = \varphi(n + 2)$. For every odd prime $p$, $\bigl(\varphi(m) \bmod p\bigr)$ is **not** eventually periodic (`not_eventuallyPeriodicMod_totient`). Thus neither $\sum_{n \ge 0} b_2(n) x^n$ nor $\sum_{n \ge 0} \mathrm{surj}_2(n) x^n$ is rational over $\mathbb{Q}$.
   - **Strict Multiletter Case $k \ge 3$ (`balancedCount_mod_eq_two_of_prime_dvd_sub_two`, `not_isRationalGF_balancedCount_five`, `not_isRationalGF_atLeast2BalancedCount_five`):** Whenever an odd prime $p$ divides $k - 2$ ($k = 5, 7, 8, 9, 11, 12, \dots$), acting by disjoint $p$-cycles on $\{2, \dots, k-1\}$ while fixing $\{0, 1\}$ preserves balancedness and yields $b_k(n) \equiv b_2(n) \pmod p$ and $m_{k,\ge 2}(n) = b_k(n) - k \equiv b_2(n) - k \pmod p$ ($n \ge 1$). Consequently, neither $\sum_{n \ge 0} b_k(n) x^n$ nor $\sum_{n \ge 0} m_{k,\ge 2}(n) x^n$ is rational over $\mathbb{Q}$. In addition, Theorem 5.3 of `main.pdf` (verified up to $n = 110$ in `verify.py`) establishes the ternary even-length palindrome law $|\mathrm{Pal}_3(2m)| = \frac{\varphi(2m)}{2} + \tau(2m - 1) - 2$ ($m \ge 6$), proving univariate irrationality of $\sum_{n \ge 0} b_3(n) x^n$ and $\sum_{n \ge 0} \mathrm{surj}_3(n) x^n$ as well.

3. **Reading 2E — Multivariate (Parikh) Generating Function (`not_isRationalParikhGF`, `not_isRationalParikhGF_three`):**
   - For **every** alphabet size $k \ge 2$ (including $k = 3$ and $k = 4$), specializing the $k$-variate Parikh series $F_k(x_0, \dots, x_{k-1}) \in \mathbb{Q}[[x_0, \dots, x_{k-1}]]$ at $\bigl(x, x, 0, \dots, 0\bigr)$ recovers $\sum_{n \ge 0} b_2(n) x^n$ while preserving $Q(0, \dots, 0) \neq 0$. Hence $F_k$ is non-rational for every $k \ge 2$.

4. **Reading 3 — Explicit Christoffel-Denominator Clause (`disproof_Conjecture4719_FullWithChristoffel`):**
   - Parameterized over an arbitrary predicate `IsChristoffelDenominator : PolyQ → Prop`, the full conjecture is refuted uniformly because no nonzero polynomial denominator $Q \in \mathbb{Q}[x]$ exists at all.

---

## Package Structure

- `SOURCE.md` — Byte-identical copy of `conjectures/00000004719.md`.
- `README.md` — Package overview and build/reproduction instructions.
- `main.tex`, `main.pdf` — Self-contained mathematical manuscript and compiled PDF.
- `verify.py` — Independent Python 3.12 computational verification suite (6 test suites).
- `lean/` — Core Lean 4.19.0 formalization (`lean-toolchain`, `lakefile.toml`, `lake-manifest.json`, `Main.lean`), zero external dependencies, compiled with `-DwarningAsError=true`.
- `verification/` — Build and verification logs (`lean-version.log`, `lake-build.log`, `lean-axioms.log`, `pdf-build.log`, `python-verify.log`) and `SELF_REVIEW.md`.

## Reproduction Commands

```bash
# 1. Build Core Lean 4.19.0 formalization from scratch (zero external dependencies)
cd lean
lake build
lake env lean -DwarningAsError=true Main.lean

# 2. Run independent Python 3.12 verification suite
cd ..
python verify.py

# 3. Compile LaTeX manuscript (2 passes)
pdflatex -interaction=nonstopmode -halt-on-error main.tex
pdflatex -interaction=nonstopmode -halt-on-error main.tex
```
