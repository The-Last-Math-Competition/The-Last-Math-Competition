# Self-Review Audit — Conjecture `00000007178`

## 1. Fidelity to `SOURCE.md` (Bilingual Verification)

- **Source untouched:** `SOURCE.md` is byte-identically preserved from the staged problem statement.
- **English & Chinese parity checked:**
  - *Definition:* Minimum-rank completion with the rank side of spectra (`极小秩完备：谱的秩侧影`, projecting the eigenvalue spectrum onto $\mathrm{rank}\bigl(B\bigr) = n - \mathrm{mult}_{0}\bigl(B\bigr)$).
  - *Clause I:* The combinatorial characterization of minimum-rank completion holds (`低秩可完备判据：矩阵的极小秩完备的组合刻画`).
  - *Clause II:* The obstruction of the characterization is the parity of cycles (`且[刻]画的障碍为圈的奇偶`, `极小秩圈奇偶障碍组合完备刻画`).
- **All four canonical mathematical interpretations analyzed:**
  1. Rectangular / bipartite partial matrix completion $\mathrm{mr}_{\mathbb{F}}\bigl(E, a\bigr)$ (Cohen–Johnson–Rodman–Woerdeman 1989),
  2. Symmetric partial matrix completion on undirected graphs with nonzero/unit diagonal specified $\mathrm{mr}_{\mathbb{F}}, \mathrm{smr}_{\mathbb{F}}$ (Grone–Johnson–Sá–Wolkowicz 1984; Laurent 2001),
  3. Symmetric partial matrix completion on undirected graphs with free/unspecified diagonal $\mathrm{mr}_{\mathbb{F}}, \mathrm{smr}_{\mathbb{F}}$ (isolating and refuting the single-cycle parity illusion),
  4. Pattern-level spectral graph minimum rank $\mathrm{mr}_{\mathbb{F}}\bigl(G\bigr)$ (Fallat–Hogben 2007; Barioli–Fallat 2004), zero-nonzero pattern minimum rank $\mathrm{mr}_{\mathbb{F}}^{\mathrm{znz}}\bigl(Z_{\mathrm{Fano}}\bigr)$ (Berman et al. 2008), and Haemers' orthogonal-representation minrank $\mathrm{minrank}_{\mathbb{F}}\bigl(G\bigr)$ (Haemers 1979; Peeters 1996).

## 2. Positive Non-Vacuity Witnesses & Sharp Refutations

- **Positive Non-Vacuity (`conjecture_00000007178_positive_nonvacuity`):**
  - Every everywhere-nonzero partial matrix on an acyclic bipartite forest pattern ($E \neq \emptyset$, e.g. `spec_T5`) satisfies $\mathrm{mr}_{\mathbb{F}}\bigl(P\bigr) = 1$ over every field $\mathbb{F}$.
  - Simplicial chordal vertex extension (`chordal_simplicial_sym_rank_one_step`) preserves symmetric rank-$1$ completability.
  - Every everywhere-nonzero symmetric edge assignment on the odd $3$-cycle $C_{3}$ with free diagonal satisfies $\mathrm{mr}_{\mathbb{F}} = \mathrm{smr}_{\mathbb{F}} = 1$ over every field $\mathbb{F}$.
  - $\mathrm{mr}_{\mathbb{F}}\bigl(G\bigr) = 1 \iff G$ satisfies `ActiveCliqueProp G` ($\bigl(P_{3}, 2K_{2}\bigr)$-freeness).
- **Polymorphic & Concrete Refutations (`conjecture_00000007178_complete_refutation`, `conjecture_00000007178_field_separation`):**
  - Incomplete chordless even $6$-cycle $E_{C_{6}}$ (zero odd cycles, locally rank $\le 1$ on all submatrices): $\mathrm{mr}_{\mathbb{F}}\bigl(A^{+}\bigr) = 1 \neq 2 = \mathrm{mr}_{\mathbb{F}}\bigl(A^{\alpha}\bigr)$ over every field with $|\mathbb{F}| \ge 3$ (instantiated on both $\mathbb{F}_{3}$ and $\mathbb{F}_{4}$).
  - Unit-diagonal symmetric even $C_{4}$: $1 = \mathrm{mr}_{\mathbb{F}}\bigl(S_{C_{4}}^{+}\bigr) \lt \mathrm{mr}_{\mathbb{F}}\bigl(S_{C_{4}}^{-}\bigr) = 2 \lt \mathrm{smr}_{\mathbb{F}}\bigl(S_{C_{4}}^{-}\bigr) = 3$, and both odd $C_{5}$ and even $C_{6}$ satisfy `LocallyRankAtMost F 1` while obstructing rank-$1$ completion.
  - Free-diagonal symmetric completion: both even $C_{4}$ and purely-odd-cycle butterfly $B_{2}$ ($2C_{3}$ sharing a vertex, zero even cycles) obstruct ($\mathrm{mr} = \mathrm{smr} = 2$).
  - Spectral graph minimum rank: unique minimal $5$-vertex chordal graph $G_{5} = K_{5} \setminus P_{3}$ has $\mathrm{mr}_{\mathbb{F}_{2}}\bigl(G_{5}\bigr) = 3 \neq 2 = \mathrm{mr}_{\mathbb{F}_{3}}\bigl(G_{5}\bigr) = \mathrm{mr}_{\mathbb{F}_{4}}\bigl(G_{5}\bigr)$; $7 \times 7$ Fano pattern $Z_{\mathrm{Fano}}$ has $\mathrm{mr}_{\mathbb{F}}^{\mathrm{znz}} = 3$ in $\mathrm{char}\bigl(\mathbb{F}\bigr) = 2$ vs. $4$ in $\mathrm{char}\bigl(\mathbb{F}\bigr) \neq 2$; Haemers minrank reverses parity on $C_{6}$ ($3$) vs. $\overline{C_{6}}$ ($2$).

## 3. Formalization, Code, & Typography Hygiene Checklist

- [x] **Core Lean 4.19.0:** `leanprover/lean4:v4.19.0`, `moreLeanArgs = ["-DwarningAsError=true"]`, zero external dependencies.
- [x] **Zero Forbidden Lean Constructs:** Audited for zero `sorry`, `admit`, `native_decide`, and custom `axiom` declarations; `#print axioms` recorded in `verification/lean-axioms.log` (every theorem depends solely on standard Lean kernel axioms `propext`, `Classical.choice`, `Quot.sound`).
- [x] **Standalone Python Verification (`verify.py`):** Uses only Python 3.12 standard library, exits `0`, logged in `verification/python-verify.log`.
- [x] **PDF Build & Visual Inspection (`main.pdf`):** Compiled cleanly via `pdflatex` with `0` errors, `0` overfull boxes, `0` unresolved references, and visually inspected page-by-page.
- [x] **Package Cleanliness & GitHub Markdown Math:** `.lake/` and LaTeX auxiliary files removed; `README.md` and `pr_body.md` audited for zero `\operatorname`, `\bowtie`, `\coloneqq`, `\DeclareMathOperator`, `\newcommand`, raw `<`/`>` inside `$...$`/`$$...$$`, leading `$(` in inline math, or local machine paths.
