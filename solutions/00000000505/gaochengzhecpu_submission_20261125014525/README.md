# Conjecture 00000000505: Arithmetical Rank and Projective Dimension of Edge Ideals

## Verdict: **DISPROVED (FALSE)**

Conjecture `00000000505` states (see `SOURCE.md`):

> **English.** Definition: The arithmetical rank ara(I) of an edge ideal. Conjecture: For any graph, ara(I(G)) ≤ pd + 1, with equality for Cohen–Macaulay graphs.
>
> **中文。** 定义：edge ideal 的 arithmetical rank ara(I)。猜想：对任何图 ara(I(G)) ≤ pd + 1 且对 Cohen–Macaulay 图取等。

Let $k$ be any field, $G = (V, E)$ a finite simple graph on $n = |V|$ vertices, $R = k[x_0, \dots, x_{n-1}]$, and $I(G) = \bigl(x_u x_v : \{u, v\} \in E\bigr) \subseteq R$ the edge ideal of $G$. The arithmetical rank is
$$\mathrm{ara}\bigl(I(G)\bigr) = \min\Bigl\{ r \in \mathbb{N} : \exists\, f_1, \dots, f_r \in R,\; \sqrt{(f_1, \dots, f_r)} = \sqrt{I(G)} \Bigr\}.$$

In combinatorial commutative algebra there are two standard conventions for the projective dimension $\mathrm{pd}$ associated with $I(G)$:

1. **Convention (C1) — Quotient convention:** $\mathrm{pd} = \mathrm{pd}_R\bigl(R / I(G)\bigr)$ (standard in Lyubeznik, Barile, Kimura–Terai, and Villarreal).
2. **Convention (C2) — Ideal-module convention:** $\mathrm{pd} = \mathrm{pd}_R\bigl(I(G)\bigr)$ (used in Herzog–Hibi and `Macaulay2`'s `pdim(I)`), satisfying $\mathrm{pd}_R\bigl(I(G)\bigr) + 1 = \mathrm{pd}_R\bigl(R / I(G)\bigr)$ whenever $E(G) \neq \emptyset$.

We prove that Conjecture `00000000505` is **false over every field $k$ under both conventions**, and even when restricted to non-empty Cohen–Macaulay graphs:

- **Elementary disproof of Convention (C1) on $G = K_2$:** Over every field $k$, the single-edge graph $K_2$ has $I(K_2) = \bigl(x_0 x_1\bigr) \subseteq k[x_0, x_1]$. Its quotient $R / I(K_2)$ has Krull dimension $1$ and $\mathfrak{m}$-depth $1$ (witnessed by the regular element $x_1 - x_0$), so $K_2$ is Cohen–Macaulay over $k$, with $\mathrm{ara}\bigl(I(K_2)\bigr) = 1$ and $\mathrm{pd}_R\bigl(R / I(K_2)\bigr) = 1$. Thus $\mathrm{ara}\bigl(I(K_2)\bigr) = 1 \neq 2 = \mathrm{pd}_R\bigl(R / I(K_2)\bigr) + 1$. More generally, every complete graph $K_n$ ($n \ge 2$) is Cohen–Macaulay with $\mathrm{ara}\bigl(I(K_n)\bigr) = \mathrm{pd}_R\bigl(R / I(K_n)\bigr) = n - 1 \neq n$.
- **Elementary disproof of Convention (C2) on edgeless graphs $\overline{K_n}$ ($n \ge 1$):** Over every field $k$, $I(\overline{K_n}) = (0)$ has $\mathrm{ara}\bigl((0)\bigr) = 0$ and $\mathrm{pd}_R\bigl((0)\bigr) = 0$, while $R / (0) = R$ is Cohen–Macaulay, violating $0 = 0 + 1$.
- **Non-empty Cohen–Macaulay counterexamples violating BOTH the inequality and equality under BOTH conventions:**
  - For $\mathrm{char}(k) \neq 2$, let $G_{11}$ ($11$ vertices, $25$ edges) be Katzman's complement graph of a minimal $11$-vertex flag triangulation $\Delta_{11}$ of $\mathbb{RP}^2$. By Reisner's criterion, $G_{11}$ is Cohen–Macaulay over $k$ of dimension $3$, so $\mathrm{pd}_R\bigl(I(G_{11})\bigr) + 1 = \mathrm{pd}_R\bigl(R / I(G_{11})\bigr) = 8$. Since $\widetilde{H}_1(\Delta_{11}; \mathbb{F}_2) \cong \mathbb{F}_2 \neq 0$, the Bruns–Schwänzl / Yan étale Goresky–MacPherson bound ($\ell = 2 \neq \mathrm{char}(k)$) gives $\mathrm{ara}_R\bigl(I(G_{11})\bigr) \ge 9 \gt 8 = \mathrm{pd}_R\bigl(I(G_{11})\bigr) + 1$ (and an explicit Schmitt–Vogel partition gives $\mathrm{ara}_R\bigl(I(G_{11})\bigr) \le 10$). Taking the disjoint union $G_{22} = G_{11} \sqcup G_{11}$ ($22$ vertices, $50$ edges), $G_{22}$ is Cohen–Macaulay over $k$ with $\mathrm{pd}_R\bigl(I(G_{22})\bigr) + 1 = 16$, $\mathrm{pd}_R\bigl(R / I(G_{22})\bigr) + 1 = 17$, and $\mathrm{ara}_R\bigl(I(G_{22})\bigr) \ge 18 \gt 17 \gt 16$.
  - For $\mathrm{char}(k) = 2$ (and every field with $\mathrm{char}(k) \neq 3$), the complement $G_{(3)}$ ($17$ vertices, $84$ edges) of an explicit $17$-vertex flag triangulation $\Delta_{(3)}$ of the mod-$3$ Moore space $M(\mathbb{Z}/3\mathbb{Z}, 1)$ satisfies Reisner's criterion over $k$ with $\mathrm{pd}_R\bigl(I(G_{(3)})\bigr) + 1 = 14 \lt 15 \le \mathrm{ara}_R\bigl(I(G_{(3)})\bigr)$, and $G_{(3)} \sqcup G_{(3)}$ ($34$ vertices) is Cohen–Macaulay with $\mathrm{ara}_R(I) \ge 30 \gt 29 = \mathrm{pd}_R(R / I) + 1 \gt 28 = \mathrm{pd}_R(I) + 1$.

---

## Summary Table of Counterexamples

| Graph $G$ | Base field $k$ | $\bigl(\lvert V\rvert, \lvert E\rvert\bigr)$ | $\mathrm{ara}\bigl(I(G)\bigr)$ | $\mathrm{pd}_R(R/I) + 1$ | $\mathrm{pd}_R(I) + 1$ | Violated clauses |
| :--- | :--- | :---: | :---: | :---: | :---: | :--- |
| $\overline{K_n}$ ($n \ge 1$) | any field $k$ | $\bigl(n, 0\bigr)$ | $0$ | $1$ | $1$ | CM equality in **(C1)** and **(C2)** |
| $K_2$ | any field $k$ | $\bigl(2, 1\bigr)$ | $1$ | $2$ | $1$ | CM equality in **(C1)** |
| $K_n$ ($n \ge 2$) | any field $k$ | $\bigl(n, \binom{n}{2}\bigr)$ | $n - 1$ | $n$ | $n - 1$ | CM equality in **(C1)** |
| $G_{11}$ (flag $\mathbb{RP}^2$) | $\mathrm{char}(k) \neq 2$ | $\bigl(11, 25\bigr)$ | $9$ or $10$ | $9$ | $8$ | Inequality and CM equality in **(C2)** |
| $G_{11} \sqcup G_{11}$ | $\mathrm{char}(k) \neq 2$ | $\bigl(22, 50\bigr)$ | $\ge 18$ | $17$ | $16$ | Inequality and CM equality in **(C1)** and **(C2)** |
| $G_{(3)}$ (flag $M_3$) | $\mathrm{char}(k) \neq 3$ | $\bigl(17, 84\bigr)$ | $\ge 15$ | $15$ | $14$ | Inequality and CM equality in **(C2)** |
| $G_{(3)} \sqcup G_{(3)}$ | $\mathrm{char}(k) \neq 3$ | $\bigl(34, 168\bigr)$ | $\ge 30$ | $29$ | $28$ | Inequality and CM equality in **(C1)** and **(C2)** |

---

## Package Contents

- `SOURCE.md` — Unmodified problem statement in English and Chinese.
- `main.tex`, `main.pdf` — Self-contained mathematical paper proving the complete refutation across all conventions and characteristics.
- `verify.py` — Independent Python 3 verification suite computing exact simplicial boundary ranks, Reisner link homology, full Hochster multigraded Betti tables across all $2^{11} - 1 = 2047$ vertex subsets of $\Delta_{11}$, Schmitt–Vogel radical partitions, and symbolic polynomial identities.
- `lean/` — Core Lean `v4.19.0` formalization (`Conjecture00000000505`) with zero external dependencies, `-DwarningAsError=true`, zero `sorry`/`admit`/`native_decide`, and clean `#print axioms`:
  - `Conjecture00000000505/Ring.lean`: Commutative rings, integral domains, fields, ideals, finite spans, radicals, and arithmetical rank (`IsArithmeticalRank`).
  - `Conjecture00000000505/Module.lean`: Modules, direct-summand projectivity (`IsProjective`), finite projective resolutions (`HasProjResolution`), projective dimension (`IsProjDim`), ideal modules, and quotient modules.
  - `Conjecture00000000505/Poly.lean`: Univariate polynomials with Euclidean division, PID theorem, prime-chain dimension bound (`Poly.no_prime_chain_len_two`), and iterated multivariate polynomial rings `MPoly n K`.
  - `Conjecture00000000505/DimensionDepth.lean`: Prime-chain Krull dimension (`IsKrullDimQuot`), $\mathfrak{m}$-regular-sequence depth (`IsDepthQuot`), and graded Cohen–Macaulayness (`IsCohenMacaulayQuot`).
  - `Conjecture00000000505/EdgeIdeal.lean`: Simple graphs, edge ideals, `disproof_conjecture505_quotientPD_nonEmpty` (via $K_2$ over any field $K$), `disproof_conjecture505_quotientPD`, `disproof_conjecture505_idealPD` (via $\overline{K_1}$ over any field $K$), and concrete $\mathbb{F}_2$ instantiation `disproof_over_F2`.
- `verification/` — Build and verification logs (`lake-build.log`, `lean-axioms.log`, `lean-version.log`, `pdf-build.log`, `python-verify.log`) and `SELF_REVIEW.md`.
