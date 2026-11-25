# Self-Review Audit — Conjecture 00000008533

## 1. Source & Problem Statement Fidelity
- **File:** `SOURCE.md` verified untouched and byte-identical (599 bytes).
- **Statement Coverage:** Both the English and Chinese formulations of Conjecture `00000008533` (*LYM type inequalities hold on all geometric lattices; the optimal weighting is the normalization of the absolute value of the Mobius function; and the weighting constant cannot be improved further*) are analyzed and resolved completely without unstated assumptions.

## 2. Mathematical & Non-Vacuity Audit
- **Positive Universal Theorem (`lubell_lym_holds_on_all_geometric_lattices`):** Proves for every finite `GeometricLattice` `L` that `0 < L.maxChains.length` (explicit non-vacuity), that Lubell's maximal-chain probability weighting satisfies `∑_{x ∈ A} w_chain(x) ≤ 1` on every antichain `A`, and that every rank level `L_k` (`0 ≤ k ≤ rk ⊤`) is an antichain achieving exact equality `∑_{x ∈ L_k} w_chain(x) = 1` (unimprovable constant `1`).
- **Classical Rank-Uniform LYM Refutation (`classical_lym_fails_on_L34`):** Proves on the explicit 34-element rank-3 geometric lattice `L34 = L(U_{2,5} ⊕_{e_0} U_{2,6})` that a 21-element antichain achieves `1/10 + 20/22 = 111/110 > 1`.
- **Exhaustive Refutation of Normalized `|μ|` Weightings (`optimal_mobius_lym_conjecture_false`):** Rather than testing only a single normalization convention, we formalize and refute all five canonical normalizations of `|μ|`:
  1. `globalLower` (`|μ(⊥, x)| / ∑_{y ∈ L} |μ(⊥, y)|`): constant `1` strictly improvable (`≤ (S - 1)/S < 1`) on every geometric lattice of rank `≥ 1` (`5/12 < 1` on `L10`).
  2. `properGlobalLower` (`|μ(⊥, x)| / ∑_{y ∈ L^\circ} |μ(⊥, y)|`): constant `1` strictly improvable (`≤ (S^\circ - 1)/S^\circ < 1`) on every geometric lattice of rank `≥ 3` (`5/9 < 1` on `L10`).
  3. `rankTwoSided` (`|μ(⊥, x)μ(x, ⊤)| / ∑_{rk y = k} |μ(⊥, y)μ(y, ⊤)|`): violates `≤ 1` on `L46 = L(U_{1,1} ⊕ U_{3,6})` (`24/39 + 10/25 = 66/65 > 1`).
  4. `rankUpper` (`|μ(x, ⊤)| / ∑_{rk y = k} |μ(y, ⊤)|`): violates `≤ 1` on `L922 = L(U_{3,8} ⊕_{e_0} U_{3,8})` (`61/1825 + 441/455 = 23788/23725 > 1`).
  5. `rankLower` (`|μ(⊥, x)| / |w_{rk x}(L)|`): fails Sperner/maximin optimality already on the 10-element modular geometric lattice `L10 = B_1 × M_3` (`min_{L^\circ} w_low = 1/5 < 2/9 = min w_chain < 1/4 = min w_unif`), and also fails pointwise dominance and `L^1` uniqueness.
- **Definition Faithfulness:** `GeometricLattice` encodes bounded lattice axioms, Jordan–Dedekind grading, upper semimodularity, and atomisticity; `mobius` is proved to satisfy both left and right incidence-algebra inversion (`mobius_sum_left`, `mobius_sum_right`); and every concrete witness lattice (`L10`, `L34`, `L46`, `L922`) is constructed via the proved general theorem `SimpleMatroid.toGeometricLattice`.

## 3. Core Lean 4.19.0 Verification Audit
- **Toolchain:** `leanprover/lean4:v4.19.0` (`verification/lean-version.log`).
- **Build Flags & Dependencies:** `moreLeanArgs := #["-DwarningAsError=true"]`, zero external dependencies (`verification/lake-build.log`).
- **Forbidden Tokens Check:** Scanned all `.lean` files — zero `sorry`, zero `admit`, zero `native_decide`, zero custom `axiom`.
- **Kernel Axiom Audit (`verification/lean-axioms.log`):** `#print axioms` on all main theorems reports exclusively `[propext, Quot.sound]` and `[propext, Classical.choice, Quot.sound]`.

## 4. Independent Computational Verification (`verify.py`)
- Standalone Python 3 script using exact `fractions.Fraction` and Dinic max-flow / min-cut exited with code `0` (`verification/python-verify.log`), independently verifying all geometric-lattice axioms, full two-sided Möbius inversion, Rota sign alternation, and all exact rational values.

## 5. Paper Quality & Visual PDF Audit (`main.tex`, `main.pdf`)
- Compiled twice via `pdflatex` with `0` errors, `0` warnings, `0` Overfull boxes, and `0` Underfull boxes (`verification/pdf-build.log`).
- Visually inspected all 12 rendered pages of `main.pdf`: typography, equations, tables, margins, and bibliography render cleanly with no clipping or overlap.

## 6. Package Hygiene & Markdown Formatting Audit
- Removed `lean/.lake/` and all LaTeX temporary files (`*.aux`, `*.out`, `*.toc`, root `main.log`).
- Audited `README.md` and PR description for GitHub MathJax safety: zero `\operatorname`, `\bowtie`, `\coloneqq`, `\DeclareMathOperator`, `\newcommand`, raw `<`/`>` inside math, `$(` inline math openings, or local filesystem paths.
