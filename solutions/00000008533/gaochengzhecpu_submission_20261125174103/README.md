# Conjecture 00000008533 — Optimal LYM Inequalities and Möbius Weightings on Geometric Lattices

## Problem Statement

- **English:** *Definition: The LYM inequality is the weighted inequality for antichains in lattices. Conjecture: LYM type inequalities hold on all geometric lattices; the optimal weighting is the normalization of the absolute value of the Mobius function; and the weighting constant cannot be improved further. (optimal LYM on geometric lattices)*
- **Chinese:** *定义：LYM 不等式指格中反链的加权不等式。猜想：LYM 型不等式在一切几何格上成立；最优加权为 Möbius 函数的绝对值归一化；加权常数不可再改进。（几何格 LYM 最优）*

---

## Complete Resolution: Disproved (with Universal Positive LYM-Type Theorem)

We give a complete resolution of Conjecture `00000008533`, proving the positive universal LYM-type theorem on **all** finite geometric lattices via maximal-chain probability weightings while **refuting** the conjecture's claim that normalizing the absolute value of the Möbius function $\mu$ yields the optimal tight LYM weighting under **every** standard normalization convention.

### 1. Positive Theorem: Tight LYM-Type Inequalities Hold on All Geometric Lattices

For any finite geometric lattice $L$ of rank $R = \mathrm{rk}(\hat{1})$, let $\mathcal{C}(L)$ denote the set of maximal chains $\hat{0} = x_0 \lt x_1 \lt \dots \lt x_R = \hat{1}$, and let $c(x) = |\{C \in \mathcal{C}(L) : x \in C\}|$. Lubell's maximal-chain probability weighting

$$
w_{\mathrm{chain}}(x) = \frac{c(x)}{|\mathcal{C}(L)|}
$$

satisfies $|\mathcal{C}(L)| \ge 1$, the LYM inequality

$$
\sum_{x \in A} w_{\mathrm{chain}}(x) \le 1 \qquad \text{for every antichain } A \subseteq L,
$$

and exact rank-level equality $\sum_{x \in L_k} w_{\mathrm{chain}}(x) = 1$ on every rank level $L_k = \{x \in L : \mathrm{rk}(x) = k\}$ for $0 \le k \le R$. Consequently, tight LYM-type inequalities with unimprovable constant $1$ hold on all finite geometric lattices.

### 2. Failure of Classical Rank-Uniform LYM

Unlike on Boolean lattices, the classical rank-uniform weighting $w_{\mathrm{unif}}(x) = 1 / W_{\mathrm{rk}(x)}(L)$ (where $W_k(L) = |L_k|$) fails already in rank $3$: on the $34$-element geometric lattice $L_{34} = \mathcal{L}(U_{2,5} \oplus_{e_0} U_{2,6})$ with $W = (1, 10, 22, 1)$, the $21$-element antichain $A_{34} = \{\{e_0\}\} \cup \{\{u, v\} : u \in E_A, v \in E_B\}$ satisfies

$$
\sum_{x \in A_{34}} \frac{1}{W_{\mathrm{rk}(x)}(L_{34})} = \frac{1}{10} + \frac{20}{22} = \frac{111}{110} \gt 1.
$$

### 3. Complete Refutation Across All Normalizations of $|\mu|$

Write $|w_k(L)| = \sum_{y \in L_k} |\mu(\hat{0}, y)|$ and $L^\circ = L \setminus \{\hat{0}, \hat{1}\}$. Every canonical normalization of $|\mu|$ fails at least one clause of the conjecture:

| Normalization Convention | Formula $w(x)$ | LYM $\le 1$? | Tight ($C = 1$)? | Optimal? | Counterexample / Exact Bound |
| :--- | :--- | :---: | :---: | :---: | :--- |
| Chain-probability (Lubell) | $c(x) / \lvert\mathcal{C}(L)\rvert$ | **Yes** | **Yes** | Valid baseline | Holds on all geometric lattices |
| Classical rank-uniform | $1 / W_{\mathrm{rk}(x)}(L)$ | **No** | — | — | $L_{34}$ (rank $3$): $\frac{111}{110} \gt 1$ |
| Global lower $\|\mu\|$ | $\lvert\mu(\hat{0}, x)\rvert / \sum_{y \in L} \lvert\mu(\hat{0}, y)\rvert$ | Yes | **No** | No | $C \le \frac{S-1}{S} \lt 1$ for all $\mathrm{rk}(\hat{1}) \ge 1$ ($\frac{5}{12}$ on $L_{10}$) |
| Proper-flat global $\|\mu\|$ | $\lvert\mu(\hat{0}, x)\rvert / \sum_{y \in L^\circ} \lvert\mu(\hat{0}, y)\rvert$ | Yes | **No** | No | $C \le \frac{S^\circ-1}{S^\circ} \lt 1$ for all $\mathrm{rk}(\hat{1}) \ge 3$ ($\frac{5}{9}$ on $L_{10}$) |
| Rank-normalized two-sided $\|\mu\|$ | $\frac{\lvert\mu(\hat{0}, x)\mu(x, \hat{1})\rvert}{\sum_{y \in L_{\mathrm{rk}(x)}} \lvert\mu(\hat{0}, y)\mu(y, \hat{1})\rvert}$ | **No** | — | — | $L_{46} = \mathcal{L}(U_{1,1} \oplus U_{3,6})$ (rank $4$): $\frac{66}{65} \gt 1$ |
| Rank-normalized upper $\|\mu\|$ | $\frac{\lvert\mu(x, \hat{1})\rvert}{\sum_{y \in L_{\mathrm{rk}(x)}} \lvert\mu(y, \hat{1})\rvert}$ | **No** | — | — | $L_{922} = \mathcal{L}(U_{3,8} \oplus_{e_0} U_{3,8})$ (rank $5$): $\frac{23788}{23725} \gt 1$ |
| Rank-normalized lower $\|\mu\|$ | $\lvert\mu(\hat{0}, x)\rvert / \lvert w_{\mathrm{rk}(x)}(L)\rvert$ | Valid on $L_{10}$ | Yes on $L_k$ | **No** | $L_{10} = B_1 \times M_3$ (rank $3$): $\min_{L_{10}^\circ} = \frac{1}{5} \lt \frac{2}{9} \lt \frac{1}{4}$ |

In particular, on the $10$-element modular geometric lattice $L_{10} = B_1 \times M_3 = \mathcal{L}(U_{1,1} \oplus U_{2,3})$, both $w_{\mathrm{unif}}$ (realized via an explicit $4$-chain symmetric chain decomposition) and $w_{\mathrm{chain}}$ are valid tight LYM weightings, yet

$$
\min_{x \in L_{10}^\circ} w_{\mathrm{low}}(x) = \frac{1}{5} \lt \min_{x \in L_{10}^\circ} w_{\mathrm{chain}}(x) = \frac{2}{9} \lt \min_{x \in L_{10}^\circ} w_{\mathrm{unif}}(x) = \frac{1}{4},
$$

so $w_{\mathrm{low}}$ yields only the loose cardinality bound $|A| \le 5$ instead of the sharp Sperner width $4$, while also failing pointwise dominance and $L^1$ uniqueness.

---

## Package Structure

- `SOURCE.md` — Original conjecture statement (English and Chinese, unmodified).
- `main.tex`, `main.pdf` — Self-contained mathematical paper with complete proofs, parametric matroid constructions, and verification mapping.
- `verify.py` — Standalone exact-arithmetic Python 3 verification suite (`fractions.Fraction` + Dinic max-flow / min-cut).
- `lean/` — Core Lean 4.19.0 formalization (`leanprover/lean4:v4.19.0`, zero external dependencies, `-DwarningAsError=true`, zero `sorry`/`admit`/`native_decide`/custom axioms):
  - `Conjecture00000008533/Basic.lean` — Exact positive-denominator rationals `QRat`, `GeometricLattice` axioms, and incidence-algebra `mobius` with left and right inversion laws (`mobius_sum_left`, `mobius_sum_right`).
  - `Conjecture00000008533/LubellLYM.lean` — Universal Lubell chain-probability LYM inequality (`lubell_lym_qrat`), rank-level tightness (`lubell_rankLevel_tight`), and global/proper-global constant-improvability theorems (`global_mobius_constant_improvable`, `proper_global_mobius_constant_improvable`).
  - `Conjecture00000008533/SimpleMatroid.lean` — General bridge theorem `SimpleMatroid.toGeometricLattice` constructing a verified `GeometricLattice` from any finite simple matroid.
  - `Conjecture00000008533/Counterexamples.lean` — Corank-$1$ and corank-$2$ upper Möbius formulas, parametric matroid families `directSumColoop` and `parallelConnUniform`, and machine-checked counterexample theorems `classical_lym_fails_on_L34`, `two_sided_mobius_lym_fails_on_L46`, `upper_mobius_lym_fails_on_L922`, and `lower_mobius_suboptimal_on_L10`.
  - `Conjecture00000008533.lean` — Top-level positive theorem `lubell_lym_holds_on_all_geometric_lattices` and master disproof `optimal_mobius_lym_conjecture_false`.
- `verification/` — Build, axiom, toolchain, PDF compilation, Python verification logs, and `SELF_REVIEW.md`.

## Reproducing Verification

```bash
# 1. Exact Python verification
python3 verify.py

# 2. Core Lean 4.19.0 formalization (from lean/)
cd lean && lake build

# 3. Compile LaTeX paper
pdflatex -interaction=nonstopmode -halt-on-error main.tex
pdflatex -interaction=nonstopmode -halt-on-error main.tex
```
