# Conjecture 00000008539 — Resolution and Formal Verification

## Status: **DISPROVED (False under all natural sequence conventions)**

### Original Statement (`SOURCE.md`)

> **English.** Definition: The Mobius function is the inverse of zeta in the incidence algebra. Conjecture: The absolute values of the Mobius function of a geometric lattice form a log-concave sequence with first term 1; and equality holds globally only for Boolean lattices. (Mobius log-concavity)
>
> **中文。** 定义：Möbius 函数指关联代数中的逆 zeta。猜想：几何格的 Möbius 绝对值构成对数凹序列且首项为 1；等号仅在布尔格整体成立。（Möbius 对数凹）

---

## Mathematical Summary

Let $L$ be a finite geometric lattice of rank $n = \mathrm{rank}(L) \ge 0$ with minimum $\hat{0}$, maximum $\hat{1}$, rank function $\mathrm{rk} : L \to \{0, 1, \dots, n\}$, and Möbius function $\mu = \zeta^{-1}$ in the incidence algebra $I(L, \mathbb{Z})$, characterized by $\mu \ast \zeta = \delta = \zeta \ast \mu$.

Extracting a rank-indexed sequence $\bigl(a_0, a_1, \dots, a_n\bigr)$ from $|\mu(\hat{0}, x)|$ admits three natural mathematical conventions (plus rank-extremal variants). **Conjecture `00000008539` is false under every single one of them**, because its two clauses conflate two incompatible constructions: log-concavity belongs to the *rank-summed* unsigned Whitney numbers of the first kind $w_k^+(L)$, whereas global equality $a_k^2 = a_{k-1} a_{k+1}$ across Boolean lattices $B_n$ belongs to *elementwise or normalized* $|\mu|$ sequences (which fail log-concavity on non-Boolean geometric lattices).

| Convention | Sequence $a_k$ ($0 \le k \le n$) | $a_0 = 1$ | Log-Concave | Global Equality $\iff$ Boolean | Minimal Counterexample |
| :--- | :--- | :---: | :---: | :---: | :--- |
| **I. Unsigned Whitney** | $w_k^+(L) = \sum_{\mathrm{rk}(x)=k} \lvert\mu(\hat{0}, x)\rvert$ | Yes | Yes (Adiprasito–Huh–Katz) | **No** (fails for all $B_n$, $n \ge 2$) | $B_2$: $\bigl(1, 2, 1\bigr)$, $2^2 = 4 \neq 1$ |
| **IIA. Maximal Chain / Selector** | $\lvert\mu(\hat{0}, x_k)\rvert$ with $\mathrm{rk}(x_k) = k$ | Yes | **No** (fails for all non-Boolean $L$) | Yes on $B_n$ | $M_3$: $\bigl(1, 1, 2\bigr)$, $1^2 = 1 \lt 2$ |
| **IIB. Rank-Averaged** | $w_k^+(L) / W_k(L)$ | Yes | **No** (fails for all non-Boolean $L$) | Yes on $B_n$ | $M_3$: $\bigl(1, 1, 2\bigr)$, $1^2 = 1 \lt 2$ |
| **IIC. Rank-Min / Rank-Max** | $\min / \max_{\mathrm{rk}(x)=k} \lvert\mu(\hat{0}, x)\rvert$ | Yes | **No** (fails for all non-Boolean $L$) | Yes on $B_n$ | $M_3$: $\bigl(1, 1, 2\bigr)$, $1^2 = 1 \lt 2$ |
| **III. Binomial-Normalized** | $w_k^+(L) / \binom{n}{k}$ (ultra-log-concavity) | Yes | **No** | Yes on $B_n$ | $U_{3,4}$: $\bigl(1, \tfrac{4}{3}, 2, 3\bigr)$, $\tfrac{16}{9} \lt 2$ |

### Key Theorems Proved from First Principles

1. **Incidence Algebra Two-Sided Inverse and Uniqueness (`IncidenceAlg.mobius_is_mobius`, `IncidenceAlg.mobius_unique`):**
   For any finite poset $P$, convolution in $I(P, \mathbb{Z})$ is associative with identity $\delta$, and $\zeta$ possesses a unique two-sided inverse $\mu$.
2. **Weisner's Identity and Rota's Strict Sign Theorem (`weisner_thm`, `rota_sign_thm`):**
   For any finite geometric lattice $L$ and any $y \in L$,
   $$(-1)^{\mathrm{rk}(y)} \mu(\hat{0}, y) \ge 1, \qquad \text{so} \qquad \lvert\mu(\hat{0}, y)\rvert = (-1)^{\mathrm{rk}(y)} \mu(\hat{0}, y) \ge 1.$$
3. **Exact Möbius Characterization of Boolean Geometric Lattices (`isBoolean_iff_natAbs_mu_top_eq_one`):**
   A finite geometric lattice $L$ is Boolean (distributive and complemented) if and only if $\lvert\mu(\hat{0}, \hat{1})\rvert = 1$ (in which case $\lvert\mu(\hat{0}, y)\rvert = 1$ for every $y \in L$).
4. **Complete Classification of Global Equality for $w_k^+(L)$ (`whitney1Abs_no_global_eq_of_rank_ge_two`, `whitney1Abs_global_eq_iff_rank_le_one`, `disproof_convention_I_whitney_iff`):**
   - On the Boolean lattice $B_n$ ($n \ge 2$), $w_k^+(B_n) = \binom{n}{k}$ satisfies strict log-concavity $\binom{n}{k}^2 \gt \binom{n}{k-1}\binom{n}{k+1}$ for all $1 \le k \le n - 1$; already $B_2$ has $w^+(B_2) = \bigl(1, 2, 1\bigr)$ with $2^2 = 4 \gt 1 \cdot 1$.
   - More generally, for **every** finite geometric lattice $L$ of rank $n \ge 2$, global equality $\bigl(w_k^+(L)\bigr)^2 = w_{k-1}^+(L) w_{k+1}^+(L)$ ($1 \le k \le n - 1$) **never** holds: global equality with $w_0^+ = 1$ and $w_1^+ = a \ge 2$ forces $w_k^+ = a^k$, contradicting $0 = (1 + a)\sum_{k=0}^n (-1)^k w_k^+ = 1 - (-a)^{n+1}$. Thus global equality holds if and only if $\mathrm{rank}(L) \le 1$ (vacuously over an empty interior index set, where $L \cong B_0$ or $B_1$).
   - *(Note on the degenerate material implication `whitney1Abs_global_eq_imp_boolean`:)* If *"only for Boolean lattices"* were read strictly as the one-way implication $\mathrm{GlobalEq}\bigl(w^+(L)\bigr) \implies \mathrm{IsBoolean}(L)$ without requiring Boolean lattices of rank $\ge 2$ to achieve equality, that implication holds solely because its premise collapses to $\mathrm{rank}(L) \le 1$.
5. **Universal Failure of Elementwise and Rank-Averaged Log-Concavity on Non-Boolean Geometric Lattices (`nonBoolean_rankSelector_not_logConcave`, `rankSelector_logConcave_iff_boolean`, `nonBoolean_avg_not_logConcave`, `disproof_convention_IIA_chain`, `disproof_convention_IIB_avg`):**
   For every non-Boolean finite geometric lattice $L$, $\mathrm{rank}(L) \ge 2$, $a_0 = 1$, $a_1 = 1$, and $a_n = \lvert\mu(\hat{0}, \hat{1})\rvert \ge 2$, which is incompatible with positive log-concavity. In particular, on the $5$-element diamond geometric lattice $M_3$, $\mu(\hat{0}, \hat{1}) = 2$ and every maximal chain gives $\bigl(1, 1, 2\bigr)$ with $1^2 = 1 \lt 2 = 1 \cdot 2$.
6. **Disproof of Binomial-Normalized Ultra-Log-Concavity (`disproof_convention_III_ultra`):**
   On the $12$-element rank-$3$ uniform geometric lattice $U_{3,4}$, $w^+(U_{3,4}) = \bigl(1, 4, 6, 3\bigr)$ and $b_k = w_k^+ / \binom{3}{k} = \bigl(1, \frac{4}{3}, 2, 3\bigr)$, violating log-concavity at $k = 1$ since $\bigl(\frac{4}{3}\bigr)^2 = \frac{16}{9} \lt 2 = 1 \cdot 2$.

---

## Package Structure

- `SOURCE.md` — Unmodified original problem statement.
- `README.md` — Overview of results, conventions, and verification instructions.
- `main.tex` / `main.pdf` — Self-contained mathematical paper with complete proofs and Lean declaration mapping.
- `verify.py` — Independent Python 3.12 verification script checking $14$ finite geometric lattices ($B_0$–$B_4$, $M_3$–$M_5$, $U_{3,4}$, $U_{3,5}$, $U_{4,5}$, $\Pi_4$, $\mathrm{PG}(2,2)$, and $M_3 \times B_1$).
- `lean/` — Self-contained Core Lean 4 (`leanprover/lean4:v4.19.0`) formalization (`lean-toolchain`, `lakefile.toml`, `lake-manifest.json`, `Main.lean`), zero external dependencies, zero `sorry`, zero `native_decide`, zero custom axioms.
- `verification/` — Complete build and audit logs (`lake-build.log`, `lean-axioms.log`, `lean-version.log`, `pdf-build.log`, `python-verify.log`, `SELF_REVIEW.md`).
