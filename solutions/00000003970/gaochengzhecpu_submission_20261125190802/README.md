# Conjecture 00000003970 — Minimal Subgraph-Count Spectrum Separation

## Problem Statement

From `SOURCE.md`:

> **English.** Definition: The subgraph count vector is the sequence of the numbers of subgraphs of each order. Conjecture: There exist two graphs whose counts of all connected subgraphs coincide while their adjacency spectra differ; the minimal vertex number for such a separation is 6 or 7, and all cases can be completely enumerated. (minimal subgraph-count spectrum separation)
>
> **中文。** 定义：子图计数向量指各阶子图的个数序列。猜想：存在两个图其全部连通子图计数相同但邻接谱相异;此类分离的最小顶点数为 6 或 7,且可完全枚举。（子图计数-谱分离最小例）

---

## Final Verdict: Conjectured Threshold "6 or 7" Refuted Across All Readings

Because the first sentence defines the **subgraph count vector** (sequence of subgraph counts indexed by vertex order $k$) while the second sentence requires that **counts of all connected subgraphs coincide**, we analyze **all three standard mathematical interpretations** and establish a sharp **Grand Trichotomy**. Under **every** reading of connected subgraph counts, the conjectured minimal vertex number "$6$ or $7$" is **false** ($n_{\min} \notin \{6, 7\}$):

| Reading / Invariant | Existence of Separation | Exact $n_{\min}$ (All Graphs) | Exact $n_{\min}$ (Connected Graphs) | Minimal Separating Pairs at $n_{\min}$ |
| :--- | :---: | :---: | :---: | :--- |
| **I. Connected induced order-vector** $c^{\mathrm{ind}}(G)$ | **True** | **$5$** | **$5$** | **$4$ pairs** ($1$ disconnected, $3$ connected) |
| **II. Connected edge-subset order-vector** $c^{\mathrm{sub}}(G)$ | **True** | **$8$** | **$8$** | **$11$ pairs** ($2$ disconnected, $9$ connected) |
| **IIIa. Connected induced iso-counts** $\{N_{\mathrm{ind}}(H, G)\}_{H\text{ conn.}}$ | **False** | $\infty$ | $\infty$ | **$0$ for all $n$** ($G_1 \cong G_2$) |
| **IIIb. Connected general iso-counts** $\{N_{\mathrm{sub}}(H, G)\}_{H\text{ conn.}}$ | **False** | $\infty$ | $\infty$ | **$0$ for all $n$** ($G_1 \cong G_2$) |
| *Diagnostic A:* Degree-matched $\bigl(c^{\mathrm{ind}}(G),\, \mathrm{deg}(G)\bigr)$ | True | $6$ | $6$ | $7$ pairs (all connected) |
| *Diagnostic B:* Unrestricted subgraph vector $s^{\mathrm{sub}}(G)$ | True | $7$ | $7$ | $20$ pairs (all connected) |

Here the adjacency spectrum of an $n$-vertex simple graph $G$ is uniquely determined by its characteristic polynomial $\chi_G(x) = \det(xI_n - A_G) \in \mathbb{Z}[x]$.

---

## Key Mathematical Results

### 1. Reading I: Connected Induced Subgraph Order-Vector ($n_{\min} = 5$)

Let $c^{\mathrm{ind}}_k(G)$ be the number of $k$-vertex subsets $S \subseteq V(G)$ such that the induced subgraph $G[S]$ is connected, and $c^{\mathrm{ind}}(G) = \bigl(c^{\mathrm{ind}}_1(G), \dots, c^{\mathrm{ind}}_n(G)\bigr)$.

- **Lower bound ($n \le 4$):** Across all simple graphs of order $0 \le n \le 4$ ($1, 1, 2, 4, 11$ non-isomorphic graphs), $c^{\mathrm{ind}}(G)$ is strictly injective up to isomorphism, so $c^{\mathrm{ind}}(G_1) = c^{\mathrm{ind}}(G_2)$ forces $G_1 \cong G_2$ and $\chi_{G_1}(x) = \chi_{G_2}(x)$.
- **Exact minimality and complete enumeration at $n = 5$:** Separation already occurs at **$n = 5 \lt 6$**, both for general simple graphs and for connected simple graphs. Up to isomorphism and pair-swapping, there are **exactly $4$ separating pairs** on $5$ vertices:
  1. **Pair 1 (Disconnected, $|E| = 3$, $c^{\mathrm{ind}} = \bigl(5, 3, 1, 0, 0\bigr)$):** $K_3 \sqcup 2K_1$ vs. $P_3 \sqcup K_2$, with $\chi(x) = x^5 - 3x^3 - 2x^2$ vs. $x^5 - 3x^3 + 2x$.
  2. **Pair 2 (Connected, $|E| = 5$, $c^{\mathrm{ind}} = \bigl(5, 5, 6, 4, 1\bigr)$):** $K_{1,4} + e$ vs. $\mathrm{Banner}$ ($C_4$ with a pendant leaf), with $\chi(x) = x^5 - 5x^3 - 2x^2 + 2x$ vs. $x^5 - 5x^3 + 2x$.
  3. **Pair 3 (Connected, $|E| = 6$, $c^{\mathrm{ind}} = \bigl(5, 6, 6, 4, 1\bigr)$):** $\mathrm{Diamond} + \text{leaf}$ vs. $\mathrm{Butterfly}$ ($2K_3$ sharing a vertex), with $\chi(x) = x^5 - 6x^3 - 4x^2 + 3x + 2$ vs. $x^5 - 6x^3 - 4x^2 + 5x + 4$.
  4. **Pair 4 (Connected, $|E| = 7$, $c^{\mathrm{ind}} = \bigl(5, 7, 9, 5, 1\bigr)$):** $\mathrm{Book}\ B_3$ vs. $K_{2,3} + e$, with $\chi(x) = x^5 - 7x^3 - 6x^2$ vs. $x^5 - 7x^3 - 4x^2 + 2x$.

### 2. Reading II: Connected Edge-Subset Subgraph Order-Vector ($n_{\min} = 8$)

Let $c^{\mathrm{sub}}_k(G)$ be the number of connected (not-necessarily-induced) subgraphs $\bigl(S, F\bigr)$ of $G$ with $|S| = k$ and $F \subseteq E(G[S])$, and $c^{\mathrm{sub}}(G) = \bigl(c^{\mathrm{sub}}_1(G), \dots, c^{\mathrm{sub}}_n(G)\bigr)$.

- **Lower bound ($n \le 7$, refuting $6$ and $7$):** Across all $1 + 2 + 4 + 11 + 34 + 156 + 1044 = 1252$ non-isomorphic simple graphs of order $1 \le n \le 7$, $c^{\mathrm{sub}}(G)$ takes $1252$ pairwise distinct values. Thus no separating pair exists for any $n \le 7$.
- **Exact minimality at $n = 8 \gt 7$:** At $n = 8$ there are **$11$ separating pairs** ($2$ disconnected pairs and $9$ connected pairs). The simplest witness is the $5$-edge forest pair $G_1 = K_{1,3} \sqcup 2K_2$ vs. $G_2 = P_4 \sqcup P_3 \sqcup K_1$, both having $c^{\mathrm{sub}} = \bigl(8, 5, 3, 1, 0, 0, 0, 0\bigr)$ while $\chi_{G_1}(x) = x^8 - 5x^6 + 7x^4 - 3x^2 \ne x^8 - 5x^6 + 7x^4 - 2x^2 = \chi_{G_2}(x)$. Moreover, the connected $12$-edge pair `G8_Conn_A` vs. `G8_Conn_B` simultaneously shares $c^{\mathrm{sub}}(G)$, $c^{\mathrm{ind}}(G)$, $s^{\mathrm{sub}}(G)$, and degree sequence while differing in $\chi_G(x)$.

### 3. Reading III: Isomorphism-Class Connected Subgraph Counts (Impossible for All $n$)

For all $n_1, n_2 \in \mathbb{N}$ and all simple graphs $G_1, G_2$ (connected or disconnected), if $N_{\mathrm{ind}}(H, G_1) = N_{\mathrm{ind}}(H, G_2)$ (or $N_{\mathrm{sub}}(H, G_1) = N_{\mathrm{sub}}(H, G_2)$) holds for every connected simple graph $H$, then $n_1 = n_2$, $G_1 \cong G_2$, and $\chi_{G_1}(x) = \chi_{G_2}(x)$. This is proved constructively via automorphism scaling, connected supergraph expansion, a one-edge inequality contraction recurrence on constrained homomorphisms, multiplicative component peeling of $\mathrm{Hom}(F, G)$, and Lovasz's edge-counting bijection argument.

---

## Package Structure & Verification

- `SOURCE.md` — Original unmodified problem statement.
- `main.tex` / `main.pdf` — Self-contained research paper with full proofs and complete enumeration tables.
- `verify.py` — Standalone Python 3.12 computational verification suite (zero external dependencies) checking all $13{,}598$ non-isomorphic simple graphs up to $n = 8$ and cross-validating DP vs. brute-force subgraph counts and Faddeev–LeVerrier vs. Laplace characteristic polynomials.
- `lean/` — Complete Core Lean 4.19.0 (`leanprover/lean4:v4.19.0`) formalization with `-DwarningAsError=true`, zero external dependencies, zero `sorry`/`admit`, zero `native_decide`, and zero custom axioms:
  - `Conjecture00000003970.lean` — Master top-level resolution theorems:
    - `resolution_reading_I_induced_order_vector`
    - `resolution_reading_II_edge_subgraph_order_vector`
    - `resolution_reading_III_isomorphism_class_counts`
  - `Conjecture00000003970/CountList.lean` — Duplicate-free finite counting & bijection combinators.
  - `Conjecture00000003970/Graph.lean` — `SimpleGraphN`, `GraphIso`, walk reachability `ReachableIn`, and verified fixed-point decidability.
  - `Conjecture00000003970/CharPoly.lean` — Univariate polynomials over $\mathbb{Z}$, Laplace determinant `detPoly`, `charPoly`, and `GraphIso.charPoly_eq`.
  - `Conjecture00000003970/SubgraphCounts.lean`, `FastSubgraphEval.lean` & `FastPackedEval.lean` — Induced and edge-subset subgraph count vectors, verified $O(3^n - 2^n)$ binary-trie subset-convolution evaluator, 32-bit/40-bit SWAR GMP evaluator, and concrete Laplace point evaluator.
  - `Conjecture00000003970/CanonCertsData.lean` & `CanonGraphs.lean` — Minimum-degree canonical reduction ($1 \le n \le 7$) and verified tree-map injectivity checker.
  - `Conjecture00000003970/InducedOrderSeparation.lean` — Complete proof of Reading I ($n_{\min} = 5$ and complete $4$-pair enumeration).
  - `Conjecture00000003970/EdgeSubgraphOrderSeparation.lean` — Complete proof of Reading II ($n_{\min} = 8$) and Diagnostic B ($n_{\min}(s^{\mathrm{sub}}) = 7$).
  - `Conjecture00000003970/IsoCountReconstruction.lean` — Universal constructive proof of Reading III for all $n \in \mathbb{N}$.
- `verification/` — Build and verification logs (`lake-build.log`, `lean-axioms.log`, `lean-version.log`, `pdf-build.log`, `python-verify.log`) and `SELF_REVIEW.md`.

### Reproduction Commands

```bash
# 1. Run exhaustive Python verification
python3 verify.py

# 2. Build Core Lean 4.19.0 formalization
cd lean && lake build

# 3. Compile LaTeX paper
pdflatex -interaction=nonstopmode main.tex
pdflatex -interaction=nonstopmode main.tex
```
