# Solution Package for Conjecture 00000001242

## Verdict: **DISPROVED (FALSE)**

### Official Conjecture Statement (`SOURCE.md`)

- **English:** *Definition: The lamp lighting game (lit-only sigma-game). Conjecture: The graphs with min-lit number at most ⌈n/2⌉ are exactly those with an odd bipartition (a lit-only extremal characterization).*
- **中文:** *定义：lamp lighting game(lit-only σ-game)。猜想：min-lit 数 ≤ ⌈n/2⌉ 的图的结构为奇部二分(lit-only 极值)。*

---

## Summary of Mathematical Results

We formalize and analyze **all 24 standard convention combinations** across:
- **2 Move Rules:** Open-neighborhood lit-only rule $\sigma^-$ (`MoveRule.openNbr`, where pressing a lit vertex $v$ toggles $N(v)$ and keeps $v$ lit) and closed-neighborhood lit-only rule $\sigma^+$ (`MoveRule.closedNbr`, where pressing a lit vertex $v$ toggles $N[v] = \{v\} \cup N(v)$).
- **3 Extremal `min-lit` Objectives:** Minimum lit count reachable from the all-lit configuration $V$ (`MinLitMode.fromAllLit`), worst-case minimum over all initial configurations $S_0 \subseteq V$ (`MinLitMode.worstAll`), and worst-case minimum over all non-empty initial configurations $\emptyset \neq S_0 \subseteq V$ (`MinLitMode.worstNonempty`).
- **4 Odd-Bipartition Interpretations:** Existence of a bipartition with at least one odd part (`OddBipMode.existsSomeOdd`), existence of a bipartition with both parts odd (`OddBipMode.existsBothOdd`), bipartiteness with every bipartition having at least one odd part (`OddBipMode.everySomeOdd`), and bipartiteness with every bipartition having both parts odd (`OddBipMode.everyBothOdd`).

### Key Counterexample Theorems

1. **Connected Non-Bipartite Infinite Family (`K_n`, $n \ge 3$) — Refutes $\bigl(\implies\bigr)$ Across All 24 Conventions:**
   For every $n \ge 3$, the complete graph $K_n$ is connected and non-bipartite (containing a triangle, hence possessing no bipartition at all), yet reaches at most $\lceil n/2 \rceil$ lit vertices in at most one move from every initial configuration under both $\sigma^-$ and $\sigma^+$. Smallest connected instance: **$K_3$ ($n = 3$, $\lceil 3/2 \rceil = 2$)**.
2. **Connected Bipartite Infinite Family (`K_{2k,2k}`, $k \ge 1$) — Refutes $\bigl(\implies\bigr)$ Even on Connected Bipartite Graphs:**
   For every $k \ge 1$, $K_{2k,2k}$ ($n = 4k$, including $C_4 = K_{2,2}$ at $k = 1$) is connected and bipartite, and its unique bipartition has even part sizes $\bigl(2k, 2k\bigr)$ (hence no odd bipartition under any mode), yet reaches at most $2k = \lceil 4k/2 \rceil$ lit vertices in at most one move from every initial configuration under both $\sigma^-$ and $\sigma^+$.
3. **Tree Counterexample (`P_4`, $n = 4$) — Refutes $\bigl(\implies\bigr)$ Even on Trees:**
   The 4-vertex path $P_4$ ($0 - 1 - 2 - 3$) is a tree whose unique bipartition $\{0,2\} \sqcup \{1,3\}$ has even part sizes $\bigl(2, 2\bigr)$, yet satisfies $\mathrm{min-lit}(P_4) \le 1 \lt 2 = \lceil 4/2 \rceil$ under all six game conventions.
4. **Infinite Converse Counterexample Families (`Empty_{2m}` and `K_2 ⊔ Empty_{2m}`, $m \ge 1$) — Refutes $\bigl(\Longleftarrow\bigr)$ Under $\sigma^-$:**
   Both $\overline{K_{2m}}$ ($n = 2m$) and $K_2 \sqcup \overline{K_{2m}}$ ($n = 2m + 2$, which has a non-empty edge set) possess odd-odd bipartitions of sizes $\bigl(1, 2m-1\bigr)$ and $\bigl(1, 2m+1\bigr)$, yet satisfy $\mathrm{min-lit}^-(\overline{K_{2m}}) = 2m \gt m$ and $\mathrm{min-lit}^-(K_2 \sqcup \overline{K_{2m}}) = 2m + 1 \gt m + 1$.
5. **Positive Non-Vacuity & Non-Triviality Witnesses:**
   - $K_2$ ($n = 2$) is connected, satisfies all four odd-bipartition modes with sizes $\bigl(1, 1\bigr)$, and satisfies $\mathrm{min-lit}(K_2) \le 1 = \lceil 2/2 \rceil$ under all six game conventions.
   - $\overline{K_2}$ ($n = 2$) satisfies $\mathrm{min-lit}_{\mathbf{1}}^-(\overline{K_2}) = 2 \gt 1 = \lceil 2/2 \rceil$.
   - The connected octahedron graph $K_{2,2,2}$ ($n = 6$) satisfies $\mathrm{min-lit}_{\max}^-(K_{2,2,2}) = 4 \gt 3 = \lceil 6/2 \rceil$.

---

## Directory Layout

- `SOURCE.md` — Exact copy of `conjectures/00000001242.md`.
- `main.tex`, `main.pdf` — Self-contained LaTeX manuscript and compiled 7-page PDF.
- `verify.py` — Independent Python 3.12 script performing an exhaustive census of all labelled graphs on $1 \le n \le 5$ vertices, all $208$ non-isomorphic graphs on $1 \le n \le 6$ vertices (OEIS A000088 / A001349), and all infinite counterexample families across all 24 conventions.
- `lean/` — Self-contained Core Lean 4.19.0 formalization (`Main.lean`, `lakefile.toml`, `lean-toolchain`, `lake-manifest.json`), compiled with `-DwarningAsError=true` and zero external dependencies.
- `verification/` — Build and verification logs (`lean-version.log`, `lake-build.log`, `lean-axioms.log`, `pdf-build.log`, `python-verify.log`, and `SELF_REVIEW.md`).

## Reproduction Commands

```powershell
# 1. Python exhaustive verification
python verify.py

# 2. Core Lean 4.19.0 formal verification
cd lean
lake build

# 3. LaTeX PDF compilation
cd ..
pdflatex -interaction=nonstopmode -halt-on-error main.tex
pdflatex -interaction=nonstopmode -halt-on-error main.tex
```
