# Conjecture 00000007178 — Cycle-Parity Minimum-Rank Completion Obstruction

## Problem Statement

From `SOURCE.md`:

> **English.** Definition: Minimum-rank completion with the rank side of spectra. Conjecture: The combinatorial characterization of minimum-rank completion holds, and the obstruction of the characterization is the parity of cycles. (cycle-parity minimum-rank completion obstruction)
>
> **中文。** 定义：极小秩完备：谱的秩侧影。猜想：低秩可完备判据：矩阵的极小秩完备的组合刻画且画的障碍为圈的奇偶。（极小秩圈奇偶障碍组合完备刻画）

---

## Final Verdict: Refuted Across All Standard Formulations

The conjecture makes two coupled claims regarding minimum-rank matrix completion (where $\mathrm{rank}\bigl(B\bigr) = n - \mathrm{mult}_{0}\bigl(B\bigr)$ projects the eigenvalue spectrum onto its rank/nullity side):
1. **Claim I (Combinatorial Characterization):** Minimum-rank completion is characterized purely by the combinatorics of the specification pattern/graph.
2. **Claim II (Cycle-Parity Obstruction):** The obstruction to low-rank completability is governed by the parity (odd vs. even length) of cycles.

We analyze **all four canonical mathematical formulations** in linear algebra and spectral graph theory. While non-trivial positive theorems hold in restricted regimes (confirming non-vacuity of all definitions), **both Claim I and Claim II are false under every formulation**:

| Formulation | Claim I (Combinatorial?) | Claim II (Cycle Parity?) | True Mathematical Obstruction | Minimal Counterexample / Separation |
| :--- | :---: | :---: | :--- | :--- |
| **1. Rectangular / Bipartite Partial Matrix** $\mathrm{mr}_{\mathbb{F}}\bigl(E, a\bigr)$ | **False** | **False** | Multiplicative cocycle mismatch on chordless even cycles $C_{2k}$ ($k \ge 3$) | $3 \times 3$ chordless even $C_{6}$ ($|\mathbb{F}| \ge 3$): $\mathrm{mr}\bigl(A^{+}\bigr) = 1 \neq 2 = \mathrm{mr}\bigl(A^{\alpha}\bigr)$ |
| **2A. Symmetric Partial Matrix (Unit Diagonal)** $\mathrm{mr}_{\mathbb{F}}, \mathrm{smr}_{\mathbb{F}}$ | **False** | **False** | Clique $2$-complex homology $H_{1}\bigl(\Delta_{2}(G)\bigr) \neq 0$ / non-chordality ($k \ge 4$) | Even $C_{4}$: $\mathrm{mr} = 2$, $\mathrm{smr} = 3$ vs. $1$; both odd $C_{5}$ and even $C_{6}$ obstruct |
| **2B. Symmetric Partial Matrix (Free Diagonal)** $\mathrm{mr}_{\mathbb{F}}, \mathrm{smr}_{\mathbb{F}}$ | **False** | **False** | Even closed walks / bipartite double cover $\beta_{1}\bigl(G \times K_{2}\bigr) \gt 0$ | Even $C_{4}$ ($\mathrm{mr} = \mathrm{smr} = 2$) **and** odd-only butterfly $B_{2}$ ($\mathrm{mr} = \mathrm{smr} = 2$) |
| **3. Spectral Graph** $\mathrm{mr}_{\mathbb{F}}\bigl(G\bigr)$ **& Fano** $\mathrm{mr}_{\mathbb{F}}^{\mathrm{znz}}\bigl(Z\bigr)$ | **False** | **False** | Field size & characteristic ($\mathrm{char}\bigl(\mathbb{F}\bigr) = 2$ vs. $\neq 2$); acyclic $\bigl(P_{3}, 2K_{2}\bigr)$ at $r = 1$ | Chordal $G_{5} = K_{5} \setminus P_{3}$: $\mathrm{mr}_{\mathbb{F}_{2}} = 3 \neq 2$; $7 \times 7$ Fano $Z_{\mathrm{Fano}}$: $3$ vs. $4$ |
| **4. Haemers' Minrank** $\mathrm{minrank}_{\mathbb{F}}\bigl(G\bigr)$ | **False** | **False** | Orthogonal representations & field dependence at $r \ge 3$ | Bipartite even $C_{6}$ ($\mathrm{minrank} = 3$) vs. $\overline{C_{6}}$ with odd $C_{3}$'s ($\mathrm{minrank} = 2$) |

---

## Key Mathematical Results

### 1. Pillar I — Bipartite Partial Matrix Completion (`BipartiteCompletion.lean`)

Associate to $E \subseteq \{1,\dots,m\} \times \{1,\dots,n\}$ its bipartite specification graph $B\bigl(E\bigr)$ on $R \sqcup C$. Every cycle in $B\bigl(E\bigr)$ has **even** length; odd cycles do not exist.

- **Positive Non-Vacuity Theorem (`forest_partial_matrix_minRank_one`):** Over every field $\mathbb{F}$, every everywhere-nonzero partial matrix ($E \neq \emptyset$) on an acyclic forest pattern—such as the $5$-edge spanning tree $T_{5} = \{\bigl(0,0\bigr),\bigl(0,1\bigr),\bigl(1,1\bigr),\bigl(1,2\bigr),\bigl(2,2\bigr)\}$ (`spec_T5_isForest`)—has exact minimum completion rank $\mathrm{mr}_{\mathbb{F}}\bigl(P\bigr) = 1$.
- **Refutation on the Incomplete Chordless Even $6$-Cycle $E_{C_{6}}$ (`even_C6_refutes_combinatorial_and_parity`):** Adding the single closing edge $\bigl(2,0\bigr)$ yields $E_{C_{6}} = T_{5} \cup \{\bigl(2,0\bigr)\}$, whose bipartite graph $B\bigl(E_{C_{6}}\bigr) \cong C_{6}$ is an **even** $6$-cycle with zero odd cycles and no $2 \times 2$ specified submatrix. Over **every** field $\mathbb{F}$ with $|\mathbb{F}| \ge 3$ ($\alpha \in \mathbb{F} \setminus \{0, 1\}$, e.g., $\alpha = -1$ when $\mathrm{char}\bigl(\mathbb{F}\bigr) \neq 2$ and $\alpha = \omega \in \mathbb{F}_{4}$ when $\mathrm{char}\bigl(\mathbb{F}\bigr) = 2$), both $A^{+}$ and $A^{\alpha}$ are everywhere nonzero and satisfy `LocallyRankAtMost F 1` across *all* fully specified submatrices of every size, yet
  $$\mathrm{mr}_{\mathbb{F}}\bigl(E_{C_{6}}, A^{+}\bigr) = 1 \quad \neq \quad 2 = \mathrm{mr}_{\mathbb{F}}\bigl(E_{C_{6}}, A^{\alpha}\bigr).$$
  Across all $512$ specification patterns on $3 \times 3$, local rank $\le 1$ fails to imply global rank $\le 1$ on **exact**ly the $6$ induced even $C_{6}$ patterns, while succeeding on all $506$ chordal-bipartite patterns (including even $C_{4} = K_{2,2}$).

### 2. Pillar II — Symmetric Partial Matrices on Undirected Graphs (`SymmetricCycles.lean`)

- **Variant 2A — Fixed Nonzero Diagonal (Chordality & Clique Homology vs. Cycle Parity):**
  - **Positive Simplicial Chordal Extension (`chordal_simplicial_sym_rank_one_step`):** Simplicial vertex extension preserves symmetric rank-$1$ completability; hence odd $3$-cycles ($C_{3}$) and chordal graphs never obstruct. Across all $52$ non-isomorphic simple graphs on $1 \le n \le 5$, local clique-rank-$1 \implies$ global rank-$1$ holds on **exact**ly the $45$ graphs with $H_{1}\bigl(\Delta_{2}(G); \mathbb{F}_{2}\bigr) = 0$: all $44$ chordal graphs plus the wheel $W_{4} = C_{4} \vee K_{1}$ (where four *odd* triangles cone off and eliminate the obstruction of the *even* $4$-cycle $C_{4}$).
  - **Three-Way Split on Even $C_{4}$ (`S_C4_minus_minRank_two`, `S_C4_minus_minSymRank_three`):** Over every field with $\mathrm{char}\bigl(\mathbb{F}\bigr) \neq 2$, $S_{C_{4}}^{-}$ has all clique blocks symmetric of rank $1$, yet $\mathrm{mr}_{\mathbb{F}}\bigl(S_{C_{4}}^{+}\bigr) = \mathrm{smr}_{\mathbb{F}}\bigl(S_{C_{4}}^{+}\bigr) = 1$ whereas $\mathrm{mr}_{\mathbb{F}}\bigl(S_{C_{4}}^{-}\bigr) = 2$ and $\mathrm{smr}_{\mathbb{F}}\bigl(S_{C_{4}}^{-}\bigr) = 3$.
  - **Both Odd $C_{5}$ and Even $C_{6}$ Obstruct (`S_C5_minus_locallyRankOne`, `S_C6_minus_locallyRankOne`):** Both $S_{C_{5}}^{-}$ (odd cycle) and $S_{C_{6}}^{-}$ (even cycle) have rank $\le 1$ on *every* fully specified submatrix (principal or non-principal), yet neither admits a rank-$1$ completion.
- **Variant 2B — Free Diagonal (Exposing & Refuting the Single-Cycle Parity Illusion):**
  - **Positive Single-Odd-Cycle Theorem (`freeDiag_odd_C3_always_rank_one`):** On $C_{3}$ with free diagonal, *every* everywhere-nonzero symmetric edge assignment satisfies $\mathrm{mr}_{\mathbb{F}} = \mathrm{smr}_{\mathbb{F}} = 1$ over every field $\mathbb{F}$.
  - **Double Refutation (`freeDiag_even_C4_obstruction`, `freeDiag_butterfly_odd_cycles_obstruct`):** Over $\mathrm{char}\bigl(\mathbb{F}\bigr) \neq 2$, free-diagonal rank-$1$ completion fails **both** on the even cycle $C_{4}$ ($\mathrm{mr} = \mathrm{smr} = 1$ vs. $2$) **and** on the $5$-vertex butterfly $B_{2}$ (two odd $C_{3}$ triangles sharing one vertex—*every* simple cycle has odd length $3$, zero even cycles—where $\mathrm{mr} = \mathrm{smr} = 1$ for $a^{+}$ vs. $2$ for $a^{-}$).

### 3. Pillars III & IV — Spectral Graph $\mathrm{mr}_{\mathbb{F}}\bigl(G\bigr)$, Fano Pattern, and Haemers Minrank (`SpectralGraphMinRank.lean`)

- **Universal $\mathrm{mr}_{\mathbb{F}}\bigl(G\bigr) = 1$ Criterion (`graph_minRank_one_iff_activeClique`):** For $E\bigl(G\bigr) \neq \emptyset$, $\mathrm{mr}_{\mathbb{F}}\bigl(G\bigr) = 1 \iff G$ is $\bigl(P_{3}, 2K_{2}\bigr)$-free (acyclic forest obstructions).
- **Unique Minimal $5$-Vertex Field Separation (`G5_minRank_F2_eq_three`, `G5_minRank_card_ge_three_eq_two`):** Across $1 \le n \le 4$ ($18$ graphs), $\mathrm{mr}_{\mathbb{F}}\bigl(G\bigr)$ is field-independent. At $n_{\min} = 5$, the chordal graph $G_{5} = K_{5} \setminus P_{3}$ uniquely satisfies $\mathrm{mr}_{\mathbb{F}_{2}}\bigl(G_{5}\bigr) = 3 \neq 2 = \mathrm{mr}_{\mathbb{F}}\bigl(G_{5}\bigr)$ for every field with $|\mathbb{F}| \ge 3$ (including both $\mathbb{F}_{3}$ and $\mathbb{F}_{4}$).
- **Characteristic Dependence Across Arbitrary Fields (`fano_znz_minRank_char_two`, `fano_znz_minRank_char_ne_two`):** On the $7 \times 7$ Fano inner-product pattern $Z_{\mathrm{Fano}}$, $\mathrm{mr}_{\mathbb{F}}^{\mathrm{znz}}\bigl(Z_{\mathrm{Fano}}\bigr) = 3$ for every field of $\mathrm{char}\bigl(\mathbb{F}\bigr) = 2$ (including $\overline{\mathbb{F}}_{2}$), whereas $\mathrm{mr}_{\mathbb{F}}^{\mathrm{znz}}\bigl(Z_{\mathrm{Fano}}\bigr) = 4$ for every field of $\mathrm{char}\bigl(\mathbb{F}\bigr) \neq 2$ (including $\mathbb{Q}, \mathbb{R}, \mathbb{C}$).
- **Haemers Minrank Cycle-Parity Reversal (`haemers_C6_vs_complement`):** Over every field $\mathbb{F}$, bipartite even $C_{6}$ has $\mathrm{minrank}_{\mathbb{F}}\bigl(C_{6}\bigr) = 3 \gt 2 = \mathrm{minrank}_{\mathbb{F}}\bigl(\overline{C_{6}}\bigr)$.

---

## Package Structure & Verification

- `SOURCE.md` — Original unmodified problem statement.
- `main.tex` / `main.pdf` — Self-contained research paper with full proofs, tables, and Lean correspondence.
- `verify.py` — Standalone Python 3.12 verification suite (standard library only) checking all $512$ $3 \times 3$ bipartite patterns, all $52$ simple graphs of order $1 \le n \le 5$, the $7 \times 7$ Fano pattern, and Haemers minrank on $C_{6}$ vs. $\overline{C_{6}}$.
- `lean/` — Core Lean 4.19.0 (`leanprover/lean4:v4.19.0`) formalization with `-DwarningAsError=true`, zero external dependencies, zero `sorry`/`admit`, zero `native_decide`, and zero custom axioms:
  - `Conjecture00000007178.lean` — Top-level master theorems (`conjecture_00000007178_positive_nonvacuity`, `conjecture_00000007178_complete_refutation`, `conjecture_00000007178_field_separation`).
  - `Conjecture00000007178/Algebra.lean` — Self-contained `CommRingR` and `FieldR` hierarchy with concrete instances `F2`, `F3`, `F4`.
  - `Conjecture00000007178/MatrixRank.lean` — Rank factorization `HasRankAtMost`, $2 \times 2$ and $3 \times 3$ determinantal minor obstructions, and partial matrix completion definitions.
  - `Conjecture00000007178/BipartiteCompletion.lean` — Cycle-product identities, universal forest completion theorem, and chordless even $C_{6}$ refutation.
  - `Conjecture00000007178/SymmetricCycles.lean` — Chordal simplicial extension, unit-diagonal $C_{4}/C_{5}/C_{6}$ separations, and free-diagonal $C_{3}$ vs. $C_{4}$ and butterfly $B_{2}$ theorems.
  - `Conjecture00000007178/SpectralGraphMinRank.lean` — Universal $\mathrm{mr}_{\mathbb{F}}\bigl(G\bigr) = 1$ theorem, minimal $5$-vertex $G_{5}$ separation, $7 \times 7$ Fano characteristic separation, and Haemers minrank reversal.
- `verification/` — Complete verification logs (`lake-build.log`, `lean-axioms.log`, `lean-version.log`, `pdf-build.log`, `python-verify.log`) and `SELF_REVIEW.md`.

### Reproduction Commands

```bash
# 1. Run standalone Python verification
python3 verify.py

# 2. Build Core Lean 4.19.0 formalization
cd lean && lake build

# 3. Compile LaTeX paper
pdflatex -interaction=nonstopmode main.tex
pdflatex -interaction=nonstopmode main.tex
```
