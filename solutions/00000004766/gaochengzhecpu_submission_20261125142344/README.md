# Conjecture 00000004766 — Disproof and Formal Verification

## Verdict: **FALSE**

Conjecture `00000004766` (*two-dimensional Narayana polynomials*) is **false** across all four canonical mathematical readings of two-dimensional noncrossing structures in algebraic combinatorics and free probability.

---

## Original Statement (`SOURCE.md`)

> **English.** Definition: Two-dimensional noncrossing is the joint structure of two noncrossing conditions. Conjecture: Its low-dimensional counts are explicit two-dimensional Narayana-type polynomials, given by symmetric combinations of the two-dimensional parameters and closed. (two-dimensional Narayana polynomials)
>
> **中文。** 定义：二维非交叉指两组不交叉条件的联合结构。猜想：其低维计数为 Narayana 型二维显式多项式,由两维参数的对称组合给出且封闭。（二维 NC Narayana 多项式）

---

## Mathematical Summary

### 1. Why Small-Order and Boundary Cases Create a Mirage

- **Degenerate Boundary Grids ($m = 1$ or $n = 1$):** On the Cartesian grid $G_{m,n} = \{0, \dots, m-1\} \times \{0, \dots, n-1\}$, row-major lexicographic order $\lt _{\mathrm{row}}$ and column-major colexicographic order $\lt _{\mathrm{col}}$ coincide whenever $\min(m, n) = 1$, so $\mathrm{NC}_2(1, n) \cong \mathrm{NC}(n)$ and $\mathrm{NC}_2(m, 1) \cong \mathrm{NC}(m)$ yield the classical palindromic Narayana polynomials $N_n(t)$ and $N_m(t)$.
- **Four-Point Threshold ($n \le 3$):** Because a partition crossing $a \lt b \lt c \lt d$ requires four distinct elements, $\mathrm{NC}(V, \lt) = \Pi(V)$ whenever $|V| \le 3$. Consequently, for $n \in \{1, 2, 3\}$:
  - Joint $2$-poset noncrossing $\mathrm{NC}([n], \lt_{\mathrm{id}}) \cap \mathrm{NC}([n], \lt_\sigma)$ equals $\mathrm{NC}(n)$ for every $\sigma \in S_n$.
  - Both join-compatible pairs $\{(\pi_1, \pi_2) \in \mathrm{NC}(n)^2 : \pi_1 \vee_{\Pi(n)} \pi_2 \in \mathrm{NC}(n)\}$ and mutually block-noncrossing pairs have bivariate block polynomial equal to the symmetric Narayana product $P_n(u, v) = N_n(u) N_n(v)$, expressible purely in $e_1 = u + v$ and $e_2 = u v$.
- **Bi-Free Word Invariance:** In Voiculescu's bi-free probability, Charlesworth--Nelson--Skoufranis' reading permutation $s_\chi$ makes the channel-block polynomial $P_{\mathrm{BNC}(\chi)}(u, v)$ invariant under rearranging Left/Right letters for fixed $\bigl(m, n\bigr)$.

### 2. Complete Refutation Across All Four Canonical Readings

1. **Reading I — Cartesian Grid Noncrossing on $[m] \times [n]$ ($\mathrm{NC}( \lt _{\mathrm{row}}) \cap \mathrm{NC}( \lt _{\mathrm{col}})$ and Geometric Variants):**
   - **Failure of Narayana palindromicity at $\bigl(2, 2\bigr)$:** $|\mathrm{NC}_2(2, 2)| = 13$ with block polynomial $P_{2,2}(t) = t + 5t^2 + 6t^3 + t^4$, breaking Kreweras self-duality ($c_2 = 5 \ne 6 = c_3$); at $\bigl(2, 3\bigr)$, $P_{2,3}(t) = t + 7t^2 + 26t^3 + 38t^4 + 15t^5 + t^6$ ($7 \ne 15$, $26 \ne 38$).
   - **Universal $2$-block formula and algebraic non-polynomiality:** We prove for all $m, n \ge 1$ that
     $$c_2(m, n) = \begin{cases} \binom{n}{2}, & m = 1, \\ \binom{m}{2}, & n = 1, \\ mn + 1, & m \ge 2 \text{ and } n \ge 2. \end{cases}$$
     Fixing $m = 2$, any polynomial $Q(x, y) \in \mathbb{Q}[x, y]$ agreeing with $c_2(2, n) = 2n + 1$ for all $n \ge 2$ satisfies $Q(2, y) \equiv 2y + 1$, forcing $Q(2, 1) = 3 \ne 1 = c_2(2, 1)$. Thus **no bivariate polynomial over $\mathbb{Q}$ equals $c_2(m, n)$ on $\mathbb{Z}_{\ge 1}^2$**.
   - **Slice-wise, projection, and planar convex-hull variants:** Slice-wise and projection noncrossing collapse on $[2] \times [2]$ to the non-palindromic Stirling polynomial $t + 7t^2 + 6t^3 + t^4$, and planar convex-hull noncrossing on $[3] \times [3]$ ($2915$ partitions) breaks self-duality ($c_3 = 226 \ne 222 = c_7$, $c_4 = 708 \ne 692 = c_6$).

2. **Reading II — Bi-Ordered ($2$-Poset) Joint Noncrossing $\mathrm{NC}(\mathrm{id}) \cap \mathrm{NC}(\sigma)$ on $[n]$:**
   - **Order dependence & non-palindromicity at $n = 4, 5$:** At $n = 4$, $\sigma_1 = (0, 1, 2, 3)$ gives $t + 6t^2 + 6t^3 + t^4$ (total $14$), whereas $\sigma_2 = (0, 1, 3, 2)$ gives $t + 5t^2 + 6t^3 + t^4$ (total $13$, non-palindromic). At $n = 5$, four distinct polynomials arise across $S_5$ (totals $32, 35, 37, 42$).

3. **Reading III — Voiculescu's Bi-Free $\mathrm{BNC}(\chi)$ & Untwisted Two-Channel $\mathrm{NC}_2(\chi)$ on $[m] \sqcup [n]$:**
   - **Asymmetry for $m \ne n$:** At $\chi = LLR$ ($m = 2, n = 1$), $P_{\mathrm{BNC}(LLR)}(u, v) = 2uv + 3u^2v \ne P_{\mathrm{BNC}(LLR)}(v, u)$.
   - **Failure of Narayana biduality at $m = n = 2$:** $P_{\mathrm{BNC}(LLRR)}(u, v) = 2uv + 3uv^2 + 3u^2v + 6u^2v^2$ ($[uv] = 2 \ne 6 = [u^2v^2]$).
   - **Word dependence for untwisted $\mathrm{NC}_2(\chi)$ at $m = n = 2$:** $P_{\mathrm{NC}_2(LLRR)}(u, v) = 2uv + 3uv^2 + 3u^2v + 6u^2v^2 \ne uv + 3uv^2 + 3u^2v + 7u^2v^2 = P_{\mathrm{NC}_2(LRLR)}(u, v)$.

4. **Reading IV — Coupled Pairs $\bigl(\pi_1, \pi_2) \in \mathrm{NC}(n) \times \mathrm{NC}(n\bigr)$:**
   - **Join compatibility ($\pi_1 \vee_{\Pi(n)} \pi_2 \in \mathrm{NC}(n)$):** Fails at $n = 4$ ($P_4^{\vee}(u, v) = N_4(u) N_4(v) - 2u^3v^3$, total $194 \ne 196$, $[u^3v^3] = 34 \ne 36 = [u^2v^2]$) and $n = 5$ (total $1714 = 2 \times 857$).
   - **Mutual block noncrossing:** Fails at $n = 4$ (total $165$, $[uv] = 0 \ne 1 = [u^4v^4]$).
   - **Refinement $2$-chains ($\pi_1 \le \pi_2$):** Fails $\bigl(u, v\bigr)$-symmetry at $n = 2$ ($uv + u^2v + u^2v^2$).
   - **Bicolored circle interleaving ($\pi \sqcup \sigma \in \mathrm{NC}(\chi)$):** Fails $\bigl(u, v\bigr)$-symmetry for $m \ne n$, fails word-independence at $m = n = 2$ ($LLRR \to 4$ vs.\ $LRLR \to 3$), and fails Narayana biduality even on alternating $LRLR$ ($[uv] = 0 \ne 1 = [u^2v^2]$).

---

## Package Structure & Reproduction

- `SOURCE.md` — Unmodified competition problem statement.
- `main.tex` / `main.pdf` — Complete mathematical paper proving the positive small-order results, the universal $2$-block grid classification and non-polynomiality theorem, and refutations of all four canonical readings.
- `verify.py` — Standalone Python 3.12 combinatorial verification script (standard library only).
- `lean/` — Self-contained Core Lean 4.19.0 formalization (`TwoDimNarayana`, zero external dependencies, `-DwarningAsError=true`, zero `sorry` / `admit` / `native_decide` / custom axioms):
  - `TwoDimNarayana/Basic.lean` — Univariate & bivariate integer polynomials, Narayana predicates, and universal root-vanishing / non-polynomiality theorem `no_biv_poly_grid_slice`.
  - `TwoDimNarayana/Partitions.lean` — Restricted Growth Strings (`allRGS`) with proved completeness (`mem_allRGS_iff`) and duplicate-freeness (`nodup_allRGS`), noncrossing predicates, and partition joins.
  - `TwoDimNarayana/Grid2D.lean` — Grid bi-lexicographic & slice disproofs, order-convexity equivalence `noCrossing2_iff_convex`, universal theorem `c2Grid_eq_mul_add_one` ($\forall m, n \ge 2,\; c_2(m, n) = mn + 1$), and `grid2D_twoBlock_not_polynomial`.
  - `TwoDimNarayana/MainTheorems.lean` — Positive mirages (`poset2D_mirage_le3`, `bnc_word_invariance_2_2`, `coupled_pairs_mirage_le3`), complete reading disproofs, and master theorem `conjecture_00000004766_false`.
- `verification/` — Complete build, axiom-audit, and verification logs (`lake-build.log`, `lean-axioms.log`, `lean-version.log`, `pdf-build.log`, `python-verify.log`, `SELF_REVIEW.md`).

### Commands to Reproduce

```bash
python3 verify.py
cd lean && lake build
pdflatex -interaction=nonstopmode -halt-on-error main.tex
```
