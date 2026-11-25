# Self-Review Report — Conjecture `00000000505`

## 1. Problem Analysis & Convention Coverage

- **`SOURCE.md` Integrity:** Verified byte-identically preserved (`325` bytes, untouched).
- **Both Language Formulations:** Analyzed both the English statement (*"Definition: The arithmetical rank ara(I) of an edge ideal. Conjecture: For any graph, ara(I(G)) ≤ pd + 1, with equality for Cohen–Macaulay graphs."*) and the Chinese statement (*"定义：edge ideal 的 arithmetical rank ara(I)。猜想：对任何图 ara(I(G)) ≤ pd + 1 且对 Cohen–Macaulay 图取等。"*).
- **Complete Resolution Across All Conventions and Characteristics:**
  1. **Convention (C1) (`pd = pd_R(R / I(G))`, standard quotient convention):**
     - Refuted on non-empty Cohen–Macaulay graphs over **every** field $k$ via $G = K_2$ ($\mathrm{ara}(I(K_2)) = 1 \neq 2 = \mathrm{pd}_R(R / I(K_2)) + 1$), and more generally on all $K_n$ ($n \ge 2$).
     - Even the inequality $\mathrm{ara}(I(G)) \le \mathrm{pd}_R(R / I(G)) + 1$ is refuted on non-empty Cohen–Macaulay graphs over **every** field $k$: via $G_{22} = G_{11} \sqcup G_{11}$ ($\mathrm{ara} \ge 18 > 17 = \mathrm{pd}_R(R / I) + 1$) when $\mathrm{char}(k) \neq 2$, and via $G_{(3)} \sqcup G_{(3)}$ ($\mathrm{ara} \ge 30 > 29 = \mathrm{pd}_R(R / I) + 1$) when $\mathrm{char}(k) = 2$.
  2. **Convention (C2) (`pd = pd_R(I(G))`, ideal-module convention):**
     - Refuted on edgeless graphs $\overline{K_n}$ ($n \ge 1$) over **every** field $k$ ($\mathrm{ara} = 0$, $\mathrm{pd}_R(I) = 0$, Cohen–Macaulay, $0 \neq 1$; or under $\mathrm{pd}_R(0) = -\infty$, $0 \not\le -\infty$).
     - Refuted on non-empty Cohen–Macaulay graphs over **every** field $k$ (violating both the inequality and equality): via Katzman's $11$-vertex flag-$\mathbb{RP}^2$ graph $G_{11}$ ($\mathrm{pd}_R(I) + 1 = 8 < 9 \le \mathrm{ara} \le 10$) for $\mathrm{char}(k) \neq 2$, and via the $17$-vertex flag mod-$3$ Moore graph $G_{(3)}$ ($\mathrm{pd}_R(I) + 1 = 14 < 15 \le \mathrm{ara}$) for $\mathrm{char}(k) = 2$.

## 2. Core Lean 4 Formalization Audit (`lean/`)

- **Toolchain & Flags:** `leanprover/lean4:v4.19.0` with `moreLeanArgs = ["-DwarningAsError=true"]` and zero external dependencies.
- **Zero Forbidden Constructs:** Audited all `.lean` files (`Ring.lean`, `Module.lean`, `Poly.lean`, `DimensionDepth.lean`, `EdgeIdeal.lean`, `Conjecture00000000505.lean`) for zero `sorry`, `admit`, `native_decide`, or custom `axiom` declarations.
- **Definition Faithfulness & Non-Vacuity:**
  - Multivariate polynomials `MPoly n K` are constructed from scratch by iterating finitely supported univariate polynomials `Poly R`, with full ring structure, evaluation, Euclidean division, and the PID theorem over any `CAlgField K`.
  - `IsArithmeticalRank` formalizes the exact minimum generator count up to radical (`√(f_1, ..., f_r) = √I`).
  - `IsProjDim` formalizes the exact minimum length of a finite resolution by direct-summand projective `R`-modules.
  - `IsCohenMacaulayQuot` formalizes properness (`1 ∉ I`) together with equality of prime-chain Krull dimension (`IsKrullDimQuot`) and `𝔪`-regular-sequence depth (`IsDepthQuot`).
  - Concrete instantiation `instF2Field : CAlgField Bool` and `disproof_over_F2` certify non-vacuity of the field axioms.
- **Axiom Footprint (`verification/lean-axioms.log`):** Only standard Lean kernel axioms (`propext`, `Classical.choice`, `Quot.sound`).

## 3. Paper, Computational Suite, and Package Hygiene

- **`main.pdf` Visual & Log Check:** Compiled cleanly via `pdflatex` with `0` errors, `0` LaTeX/hyperref warnings, and `0` overfull boxes; visually inspected all 9 pages.
- **`verify.py` Check:** Passed all assertions across edgeless graphs, 7 small benchmark graphs, the 2047-subset Hochster Betti table and Reisner checks for $G_{11}$, Schmitt–Vogel radical partitions, $G_{22}$, and $G_{(3)}$.
- **`README.md` Compliance:** Verified free of `\operatorname`, `\bowtie`, `\coloneqq`, `\DeclareMathOperator`, `\newcommand`, raw `<`/`>` inside math, `$(`, and local machine paths.
- **Clean Directory Tree:** Removed `.lake/` and all LaTeX temporary files (`*.aux`, `*.out`, `*.toc`, root `*.log`).
