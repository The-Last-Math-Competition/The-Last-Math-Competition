# Self-Review Audit — Conjecture 00000007171

## 1. Semantic Fidelity & Completeness Check

- **Official statement (`SOURCE.md`):** Untouched staged copy of Conjecture `00000007171` (*Definition: Constrained spectral extrema with fixed trace. Conjecture: The configuration of the maximal spectrum is the concentrated type, and the realization of the type is rank-one perturbation.*).
- **General spectral & matrix formalization (`lean/Main.lean`):**
  - Axiomatized linearly ordered fields (`OrderedField F`) covering $\mathbb{R}$ and $\mathbb{Q}$, and constructed the exact rational quotient model `RatField` with a verified instance `instOrderedFieldRat` (`orderedField_nonvacuous`) so that every polymorphic theorem is constructively inhabited within Core Lean 4.
  - Defined spectral simplices `LowerTraceSimplex n a c` ($\Delta_{n,c}(a)$), `PSDTraceSimplex n c` ($\Delta_{n,c}(0)$), and two-sided operator intervals `BoxTracePolytope n a b c` ($\mathcal{B}_{n,c}(a,b)$), Hardy–Littlewood–Pólya / Ky Fan majorization (`KyFanMajorizes`, `SortedMajorizes`, `kyFanMajorizes_implies_sortedMajorizes`), strict floor concentration (`IsConcentratedFloor`), weak single-spike concentration (`IsWeaklyConcentrated`), rank-at-most-one outer products (`IsRankAtMostOne`, `IsRankOne`), and orthogonal spectral realization (`IsOrthogonal`, `RealizesSpectrum`).
- **Positive non-vacuity regime (Section 2 of `main.tex` / Section 4 of `lean/Main.lean`):**
  - Proved `concSpec_majorizes_lowerTraceSimplex`: on $\Delta_{n,c}(a)$ ($n \ge 1$, $c > n a$), $\lambda^{\mathrm{conc}} = (c - (n-1)a, a, \dots, a)$ Ky-Fan-majorizes every feasible spectrum.
  - Proved `convex_sum_le_concSpec` (arbitrary interval-convex sum maximization) and `specSumSq_eq_concSpec_iff` (exact quadratic excess identity $\sum (\lambda_i^{\mathrm{conc}})^2 - \sum \lambda_i^2 = \sum_{i \neq j} (\lambda_i - a)(\lambda_j - a) \ge 0$ with strict uniqueness up to spike coordinate).
  - Proved `rankOnePerturb_realizes_concSpec`: for *every* unit vector $u \in F^n$ ($\|u\|_2^2 = 1$), the trace-changing rank-one perturbation $A(u) = a I_n + (c - n a) u u^\top$ satisfies $\mathrm{rank}(A(u) - a I_n) = 1$, $\mathrm{tr}(A(u)) = c$, and orthogonally realizes $\lambda^{\mathrm{conc}}$ over $F$ itself via a square-root-free Householder reflection.
- **Three independent refutations of the unqualified conjecture (Sections 3–5 of `main.tex` / Section 5 of `lean/Main.lean`):**
  - **Refutation R1 (`refutation_R1_det_and_elemSymm2`):** Proved Bernoulli's inequality (`bernoulli_ge`, `bernoulli_strict`) and the general $n$-variable AM–GM theorem with strict equality characterization (`am_gm_complete`), establishing that on $\Delta_{n,c}(0)$ ($n \ge 2$, $c > 0$) both $\det(\mathrm{diag}\,\lambda) = \prod_{i=1}^n \lambda_i$ and $2 e_2(\lambda) = \sum_{i \neq j} \lambda_i \lambda_j$ attain their unique global maximum at the uniform full-rank spectrum $(c/n, \dots, c/n)$, while every concentrated spectrum attains the global minimum $0$.
  - **Refutation R2 (`scalar_plus_rankAtMostOne_at_most_one_non_alpha`, `boxSpec_majorizes_boxTracePolytope`, `refutation_R2_box_interior`, `refutation_R2_n3_and_n4`):** Proved Weyl's rank-one multiplicity obstruction over orthonormal eigenbases, proved that $\lambda^{\mathrm{box}}$ majorizes $\mathcal{B}_{n,c}(a,b)$, and proved that whenever $(n-1)a + b < c < a + (n-1)b$, $\lambda^{\mathrm{box}}$ fails even weak single-spike concentration and satisfies $\mathrm{rank}(A - \alpha I_n) \ge 2$ for every symmetric realization $A$ and every scalar $\alpha \in F$ (instantiated at the sharp minimal dimension $n = 3$ on $\mathcal{B}_{3,3}(0,2) \to (2,1,0)$ and on the Ky Fan $2$-frame polytope $\mathcal{B}_{4,2}(0,1) \to (1,1,0,0)$).
  - **Refutation R3 (`symmetric_rankAtMostOne_frobSq_eq_trace_sq`, `no_trace_preserving_symmetric_rankOne_perturbation`, `traceless_rankAtMostOne_nilpotent`, `robinMuirhead_rankTwo_witness`):** Proved $\|R\|_F^2 = (\mathrm{tr}\, R)^2$ for every symmetric rank-$\le 1$ matrix $R$, whence $\mathrm{tr}(R) = 0 \implies R = 0$ (no nonzero trace-preserving symmetric rank-one perturbation exists; minimum rank is $2$), and $R^2 = 0$ for non-symmetric traceless rank-$\le 1$ matrices.
  - **Master synthesis (`conjecture_00000007171_disproved`):** Combines polymorphic refutations of all three readings with unconditional ground refutations and a ground Householder witness over `RatField`.

## 2. Lean 4 Formalization Audit

- **Toolchain:** `leanprover/lean4:v4.19.0` (Core Lean 4 only, zero external packages).
- **Compiler flags:** `-DwarningAsError=true` in `lakefile.toml` and standalone `lake env lean` check.
- **Forbidden constructs scan:** Confirmed zero occurrences of `sorry`, `admit`, `native_decide`, `Lean.ofReduceBool`, custom `axiom`, `unsafe`, `@[extern]`, or `@[implemented_by]` in `lean/Main.lean`.
- **Axiom printouts (`verification/lean-axioms.log`):** Every audited theorem depends solely on standard Lean foundational axioms (`propext`, `Classical.choice`, `Quot.sound`).
- **Cleanliness:** Verified `.lake/` and build artifacts are removed from `package/lean/` after log generation.

## 3. LaTeX Manuscript & Python Verification Audit

- **PDF quality (`main.pdf` & `verification/pdf-build.log`):** Compiled cleanly with TinyTeX `pdflatex` (2 passes), visually inspected page-by-page across all 10 pages, 0 errors, 0 `hyperref` warnings, 0 `Overfull \hbox` / `Overfull \vbox` messages, all cross-references and citations resolved. Auxiliary files (`.aux`, `.log`, `.out`) removed from `package/`.
- **Python verification (`verify.py` & `verification/python-verify.log`):** Deterministically verifies exact rational Householder diagonalizations across 2000 simplex spectra, Schur-concave optima ($\det$, $e_2$, von Neumann entropy) for $2 \le n \le 6$, 155 box-polytope parameter regimes matching the exact iff classification, the trace–Frobenius $1$-spike vs. $2$-spike majorization split, and 1000 rank-at-most-one trace-rigidity tests.
