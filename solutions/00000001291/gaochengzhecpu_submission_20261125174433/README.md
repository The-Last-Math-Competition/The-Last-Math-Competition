# Conjecture 00000001291 — Disproof and Structural Dichotomy

## Problem Statement

From `SOURCE.md`:

> **English.** Conjecture: Under misère play, the height of the normalization partial order of Grundy values is at most n (misère layer height).
>
> **中文。** 猜想：misère 规则下 Grundy 值的规范化偏序的高度 ≤ n(misère 层高)。

## Resolution Summary: Disproved (False for $n \ge 4$ / $n \ge 5$)

Under normal play, the Sprague–Grundy theorem normalizes every impartial game of layer height (tree height / birthday) at most $n$ to a canonical Nim-heap in $\lbrace *0, *1, \dots, *n \rbrace$. Consequently, both the canonical option-inclusion poset ($*0 \subsetneq *1 \subsetneq \dots \subsetneq *n$, height $n$) and the equivalence-preserving option-normalization poset (height $\max(0, n-1)$) satisfy height $\le n$ for every $n \ge 0$.

Under **misère play**, Conway's canonical layer cardinalities $|\mathcal{M}_n|$ (OEIS A005130) begin $1, 2, 3, 5, 22, 4171780, \dots$. Because $|\mathcal{M}_0| = 1$, $|\mathcal{M}_1| = 2$, and $|\mathcal{M}_2| = 3$ match normal play on the first three layers, small-layer testing satisfies height $\le n$ up to $n = 3$ (and up to $n = 4$ for pre-normalized option reduction). However, **the conjecture is false** once non-Nim canonical proliferation begins:

1. **Convention A — Canonical Option-Inclusion Order on Misère Grundy Values $\bigl(\mathcal{M}_n, \subsetneq\bigr)$:**
   - Exact poset heights for $n = 0, 1, 2, 3$ are $0, 1, 2, 3$ ($\le n$).
   - **Refuted at $n = 4$ (poset height $5 \gt 4$, vertex cardinality $6 \gt 4$):** Defining $g_0 = \emptyset$, $g_1 = \lbrace g_0 \rbrace$, $g_2 = \lbrace g_0, g_1 \rbrace$, $g_{2b} = \lbrace g_2 \rbrace$, $g_3 = \lbrace g_0, g_1, g_2 \rbrace$, $g_4 = \lbrace g_0, g_1, g_2, g_3 \rbrace$, and $g_5 = \lbrace g_0, g_1, g_2, g_{2b}, g_3 \rbrace$, all six games belong to $\mathcal{M}_4$ (irreducible canonical misère forms of layer height $\le 4$) and satisfy
     $$
 g_0 \subsetneq g_1 \subsetneq g_2 \subsetneq g_3 \subsetneq g_4 \subsetneq g_5.
 $$

2. **Convention B — Conway Normalization Partial Order on Layer-$n$ Games $\bigl(\mathcal{P}(\mathcal{M}_{n-1}), \prec_{\mathrm{norm}}\bigr)$:**
   - Ordering games of layer height $\le n$ over distinct canonical options in $\mathcal{M}_{n-1}$ by equivalence-preserving option deletion ($H \prec_{\mathrm{norm}} G \iff H \subsetneq G \text{ and } H \equiv^- G$) yields exact heights $0, 1, 2, 3$ for $n = 1, 2, 3, 4$.
   - **Refuted at $n = 5$ (poset height $\ge 10 \gt 5$, vertex cardinality $11 \gt 5$):** By our **Universal Zero-Normalization Theorem**, any game $H$ containing $* = \lbrace 0 \rbrace$ whose options all contain $0$ is semantically misère-equivalent to $0$. Since $U_4 = \lbrace u \in \mathcal{M}_4 : 0 \in u \rbrace$ has $|U_4| = 10$ pairwise inequivalent canonical games of layer height $\le 4$, its prefixes $H_0 \prec_{\mathrm{norm}} H_1 \prec_{\mathrm{norm}} \dots \prec_{\mathrm{norm}} H_{10}$ all have layer height $\le 5$ and satisfy $H_k \equiv^- 0$. (On raw hereditary game trees without pre-normalizing options, height $\le n$ already fails at $n = 4$ with height $\ge 12 \gt 4$.)

3. **Positive Contrast Regimes (Boundary of Validity):**
   - **Normal-play Sprague–Grundy values:** Poset height $= n \le n$ for all $n \ge 0$.
   - **Conway's scalar misère Grundy function $\mathcal{G}^-(G)$:** Satisfies $\mathcal{G}^-(G) = 0 \iff o^-(G) = \mathcal{P}$, and the attained integer poset at layer height $\le n$ has height $0$ ($n = 0$) and $n$ ($n \ge 1$), hence $\le n$ for all $n \ge 0$.
   - **Global syntactic outcome order:** Collapses to an antichain ($G \le_{\mathcal{P}}^{\mathrm{glob}} H \iff G \equiv^- H$, height $0 \le n$), whereas restricting contexts to Plambeck–Siegel's finite non-tame misère quotient $\mathcal{R}_8$ yields strict syntactic comparabilities (height $1 \gt 0$).

## Package Structure

- `SOURCE.md` — Original bilingual problem statement (untouched).
- `main.tex` / `main.pdf` — Complete mathematical paper with self-contained proofs, exact layer tables, and theorem-to-Lean correspondence.
- `verify.py` — Standalone Python 3.12 computational verification suite (standard library only).
- `lean/` — Pure Core Lean 4.19.0 formalization (`lean-toolchain`, `lakefile.lean`, `Conjecture00000001291.lean`, and `Conjecture00000001291/{Basic,Poset,Counterexamples,Contrast}.lean`), compiled with `-DwarningAsError=true` and `-DautoImplicit=false` (zero `sorry`, zero `admit`, zero `native_decide`, zero custom `axiom`).
- `verification/` — Complete 6-log verification record covering Python execution, Lake build, Lean axiom/token audit, LaTeX compilation, PDF visual inspection, and package integrity.

## Reproduction Commands

```powershell
python verify.py
lake --dir lean build
pdflatex -interaction=nonstopmode -halt-on-error main.tex
```
