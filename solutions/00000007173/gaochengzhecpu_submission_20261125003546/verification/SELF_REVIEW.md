# Self-Review Audit — Conjecture 00000007173

## 1. Verdict and Mathematical Completeness

- **Final Verdict:** **FALSE** (disproved across all standard mathematical interpretations).
- **Source Fidelity (`SOURCE.md`):** Preserved byte-identically (459 bytes, SHA-256 untouched). Both the English text (*"Definition: Majorization with the poset of spectra. Conjecture: The endpoints of the majorization chain are the ordered spectra, and the realization of the endpoints is permutation similarity."*) and the Chinese text (*"定义：优超：谱的偏序。猜想：优超的极值元素：优超链的端点为排序谱且点的实现为置换相似。"*) were analyzed word-by-word.
- **All Standard Interpretations Covered:**
  1. **Schur–Horn Diagonal-to-Spectrum Majorization ($\mathrm{diag}(A) \prec \lambda(A)$):**
     - *Lower endpoint:* Proved that for non-scalar $\lambda \in \mathbb{R}_\downarrow^n$ ($\lambda_1 > \lambda_n$), the lower endpoint is the uniform mean vector $\bar{\lambda}\mathbf{1} \precneqq \lambda$ (not an ordered spectrum), and exhibited exact $2 \times 2$ real symmetric integer witnesses $A_+ = \bigl(\begin{smallmatrix}1&1\\1&1\end{smallmatrix}\bigr)$ and $A_- = \bigl(\begin{smallmatrix}1&-1\\-1&1\end{smallmatrix}\bigr)$ (plus $3 \times 3$ witnesses $J_3, J_3'$ in `verify.py`) showing neither permutation similarity to $\mathrm{diag}(\lambda^\downarrow)$ nor mutual permutation similarity between realizations.
     - *Upper endpoint (general real-spectrum matrices):* Exhibited $B_1 = \bigl(\begin{smallmatrix}1&1\\0&0\end{smallmatrix}\bigr)$ ($GL_2(\mathbb{Z})$-diagonalizable, distinct spectrum $(1,0)$) and $B_2 = \bigl(\begin{smallmatrix}1&1\\0&1\end{smallmatrix}\bigr)$ (Jordan block, spectrum $(1,1)$) attaining $\mathrm{diag}(B_i) = \lambda^\downarrow(B_i)$ while failing permutation similarity.
  2. **Lidskii–Wielandt Eigenvalue Majorization of Sums ($\lambda(A + B)$):**
     - Exhibited the exact all-integer $2 \times 2$ symmetric pair $A = \mathrm{diag}(25, 0)$ and $B = \bigl(\begin{smallmatrix}9&12\\12&16\end{smallmatrix}\bigr)$ whose Lidskii endpoints $(50, 0)$ and $(25, 25)$ are realized over $O(2, \mathbb{Q})$ via $3$-$4$-$5$ rational orthogonal rotations, whereas all $P \in \mathcal{P}_2$ yield $(40, 10)$ or $(45, 5)$ strictly inside $(25, 25) \precneqq (40, 10) \precneqq (45, 5) \precneqq (50, 0)$, together with a $3 \times 3$ extension checked across all $3! = 6$ permutation matrices.
  3. **Fixed-Trace and PSD Spectral Poset Slices ($\mathcal{S}_{n,\tau}$ and $\mathcal{S}_{n,\tau}^+$):**
     - Proved upward unboundedness on $\mathcal{S}_{n,\tau}$ ($n \ge 2$) and rank/determinant incompatibility plus non-uniqueness up to permutation similarity at the endpoints $\frac{\tau}{n}\mathbf{1}$ and $(\tau, 0, \dots, 0)$ on $\mathcal{S}_{n,\tau}^+$.
- **Positive Non-Vacuity Witnesses Included:**
  - Collapse of opposite orderings $x^\downarrow$ and $x^\uparrow$ in the majorization preorder (`nonvacuity_ordering_equivalence`).
  - General $n \times n$ Schur Frobenius upper-endpoint theorem (`nonvacuity_schur_upper_endpoint_dim_n`) and exact $2 \times 2$ symmetric equivalence (`nonvacuity_schur_upper_endpoint_symm2`).
  - Already-diagonal Lidskii sum realization by permutation similarity (`nonvacuity_lidskii_diagonal_case`).

---

## 2. Core Lean 4.19.0 Formalization Audit (`lean/`)

- **Toolchain:** `leanprover/lean4:v4.19.0` (`lean-version.log`: `Lean (version 4.19.0, x86_64-w64-windows-gnu, commit 6caaee842e94, Release)`).
- **Dependencies:** Zero external packages (`lake-manifest.json` has `"packages": []`).
- **Compiler Flags:** `moreLeanArgs = ["-DwarningAsError=true"]` enabled in `lakefile.toml`; `lake build` exits with code `0` and zero warnings (`lake-build.log`).
- **Forbidden Constructs Check:** Zero occurrences of `sorry`, `admit`, `native_decide`, `axiom`, `unsafe`, `extern`, `implemented_by`, or `opaque` in code.
- **Axiom Audit (`lean-axioms.log`):** `#print axioms` on all nine main non-vacuity and refutation theorems uses exclusively standard Lean kernel axioms (`propext`, `Classical.choice`, `Quot.sound`).

---

## 3. Independent Computational, LaTeX/PDF, and Markdown Audits

- **Python Verification (`verify.py`):** Uses only the Python 3.12 standard library (`fractions.Fraction`, `itertools`, `math`, `random`); exits with code `0` (`python-verify.log`).
- **LaTeX & Visual PDF Audit (`main.tex` / `main.pdf`):** Compiled twice with `pdflatex -interaction=nonstopmode -halt-on-error main.tex`; zero errors, zero warnings, and zero `Overfull \hbox` messages (`pdf-build.log`). Visually inspected page-by-page across all 8 pages: all equations, matrices, tables, and references render cleanly within margins with no clipping.
- **GitHub Markdown Math Audit (`README.md`):** Verified zero occurrences of `\operatorname`, `\bowtie`, `\coloneqq`, `\DeclareMathOperator`, `\newcommand`, raw `<` or `>` inside `$...$` / `$$...$$`, inline `$(` openings, or local host paths.
- **Clean Package Layout:** Verified removal of `lean/.lake/` and all LaTeX temporary files (`*.aux`, `*.out`, `*.toc`, root `*.log`).
