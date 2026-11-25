# Self-Review Report — Conjecture `00000007161`

## 1. Verdict & Coverage Across All Readings

- **Verdict:** **DISPROVED**.
- **English and Chinese Alignment:** Checked both statements in `SOURCE.md` byte-for-byte. All three natural mathematical interpretations of *cyclic lists* (`循环列表`) and *rotation lattice* (`轮换格`) in the Nonnegative Inverse Eigenvalue Problem (NIEP) are analyzed and refuted:
  1. **Reading I (Scaled root-of-unity cyclic lists and disjoint multiset unions):**
     - *Positive non-vacuity:* Weighted cyclic shift matrices $C_n(r) = r P_n \in M_n(\mathbb{R}_{\ge 0})$ ($r \ge 0$) realize $\Lambda_{\mathrm{cyc}}(n, r)$ with $\det(tI_n - C_n(r)) = t^n - r^n$.
     - *Universal invariant:* Any multiset $\Lambda$ covered by cyclic root-of-unity pieces satisfies $\lambda \in \Lambda \implies |\lambda| \in \Lambda$ (`abs_mem_of_coveredByCyclicPieces`).
     - *Counterexamples and infinite families:* Even restricting to symmetric, zero-diagonal (trace-zero), irreducible $\{0,1\}$-matrices, $A_n = J_n - I_n$ ($n \ge 3$) realizes $\bigl(n-1, -1, \dots, -1\bigr)$ (at $n = 3$: $\bigl(2, -1, -1\bigr)$), violating $|-1| = 1 \in \Lambda(A_n)$. Furthermore, Suleimanova's theorem provides an infinite family of nonnegative Frobenius companion matrices realizing $\bigl(\lambda_1, -\mu_2, \dots, -\mu_n\bigr)$ whenever $\lambda_1 \ge \sum_{k=2}^n \mu_k$ ($\mu_k \ge 0$), including $n$ pairwise distinct zero-sum integers $\bigl(\binom{n}{2}, -1, -2, \dots, -(n-1)\bigr)$.
  2. **Reading II (Spectra of nonnegative circulant matrices, `循环矩阵`):**
     - By Gauss's identity $2\det\bigl(tI_3 - \mathrm{circ}(c_0, c_1, c_2)\bigr) = \bigl(t - (c_0 + c_1 + c_2)\bigr)\bigl((t - c_0 + c_1)^2 + (t - c_0 + c_2)^2 + (c_1 - c_2)^2\bigr)$, no real $3 \times 3$ circulant matrix can realize three pairwise distinct real eigenvalues (`no_circulant3_three_distinct_roots`).
     - Both the zero-diagonal primitive matrix $M_3$ with spectrum $\bigl(3, -1, -2\bigr)$ and the symmetric primitive matrix $S_3$ with spectrum $\bigl(3, 0, -2\bigr)$ realize three distinct integers, refuting Reading II alongside Reading I.
  3. **Reading III (Complex phase rotations and circular-shift lattices, `轮换格`):**
     - Every $A \in M_n(\mathbb{R}_{\ge 0})$ satisfies $\mathrm{tr}(A^k) \ge 0$ (`trace_pow_nonneg_of_nonneg`). Rotating $\bigl(r, -r\bigr)$ ($r \ge 1$) by $\pi/2$ produces $\bigl(ri, -ri\bigr)$ with $s_2 = -2r^2 \lt 0$, realized by no nonnegative $2 \times 2$ matrix (`no_nonneg2_realizes_rotated_cyclic`). More generally, for $n \ge 2$ and $r \gt 0$, $e^{i\theta}\Lambda_{\mathrm{cyc}}(n, r)$ is nonnegative realizable iff $e^{in\theta} = 1$.
     - Circular coordinate shifts preserve $\prod_{k=1}^n (t - \lambda_k)$ (`polyOfRoots_rotList_eq`), while componentwise lattice meets of circular shifts of $\bigl(1, -1\bigr)$ and $\bigl(2, -1, -1\bigr)$ yield $\bigl(-1, -1\bigr)$ and $\bigl(-1, -1, -1\bigr)$ with negative traces, which are not nonnegative realizable (`circular_shift_meet_unrealizable_dim2`, `circular_shift_meet_unrealizable_dim3`).

## 2. Formal Verification Audit (Core Lean 4.19.0)

- **Toolchain:** `leanprover/lean4:v4.19.0` with `moreLeanArgs = ["-DwarningAsError=true"]` and zero external dependencies.
- **Forbidden constructs:** Scanned `lean/Main.lean` — zero occurrences of `sorry`, `admit`, `native_decide`, or custom `axiom`.
- **Axiom footprint (`verification/lean-axioms.log`):** Checked all 22 exported theorems via `#print axioms`; only standard Lean core axioms (`propext`, `Classical.choice`, `Quot.sound`) appear, with `abs_mem_of_coveredByCyclicPieces` depending on zero axioms.
- **Artifact cleanup:** `.lake/` build cache removed after generating `lake-build.log` and `lean-axioms.log`.

## 3. Computational, Manuscript, and Formatting Audit

- **Python verification (`verify.py`):** Uses exact rational arithmetic (`fractions.Fraction`) from Python 3.12 stdlib; exits with code `0` (`verification/python-verify.log`).
- **LaTeX / PDF (`main.tex` & `main.pdf`):** Compiled twice with `pdflatex`; verified zero errors, zero warnings, and zero overfull/underfull boxes in `verification/pdf-build.log`, and visually inspected every page of `main.pdf`. Temporary LaTeX files (`*.aux`, `*.out`, `*.toc`, root `*.log`) removed.
- **Markdown Math & Path Hygiene:** Mechanically audited `README.md`, `SELF_REVIEW.md`, and `pr_body.md` for GitHub MathJax compatibility (zero disallowed operator macros, zero raw angle-bracket inequality characters inside math spans, and zero dollar-parenthesis inline openings) and confirmed zero local machine paths across all deliverables.
