# Self-Review Audit — Conjecture 00000007624

## 1. Statement Fidelity & Bilingual Verification

- **`SOURCE.md` integrity:** Byte-identical to the original problem statement (verified untouched).
- **Both English and Chinese statements analyzed:**
  - *English:* "Definition: The null-vector sum construction of nilpotent formulas. Conjecture: The construction domain is explicit and the sum of squares is the null vector; the existence of null vectors is the isotropic vector; and the existence of isotropic vectors is the signature condition. (isotropic null-vector sum construction)"
  - *Chinese:* "定义：幂零公式的零向量和构造。猜想：构造域显式且平方和为零向量；且零向量的存在为迷向向量；且迷向向量的存在为符号差条件。（零向量平方和迷向构造）"
- **Semantic & convention coverage:**
  - Addressed both meanings of "null vector / 零向量" (trivial zero vector $0 \in V$ vs. nonzero lightlike/isotropic vector $Q(v) = 0$).
  - Checked both Clifford algebra sign conventions ($v^2 = +Q(v)\cdot 1$ and $v^2 = -Q(v)\cdot 1$).
  - Checked both square-zero ($z^2 = 0$) and arbitrary-index nilpotency ($z^k = 0$, $k \ge 1$).
  - Checked both nondegenerate forms $\bigl(p, q\bigr)$ and degenerate forms $\bigl(p, q, r\bigr)$ ($r \ge 1$).
  - Checked $\mathbb{R}$, $\mathbb{Q}$, $\mathbb{Z}$, $\mathbb{C}$ / $\mathbb{Z}[i]$, and finite prime fields $\mathbb{F}_p$.

## 2. Non-Vacuity & Structural Audit of Lean 4.19.0 Formalization

- **Toolchain & build flags:** `leanprover/lean4:v4.19.0` with `moreLeanArgs = ["-DwarningAsError=true"]` and zero external dependencies.
- **Zero cheats:** Verified zero occurrences of `sorry`, `admit`, `native_decide`, or `axiom` across all `.lean` files in `lean/`.
- **Axiom audit (`verification/lean-axioms.log`):** `#print axioms` run on all 22 core declarations (`instAssocRingCl`, `embedVec_sq`, `embedVec_anticomm`, `grade1_nilpotent_iff`, `hasIsotropic_sigList_iff`, `hasIsotropic_inertiaList_iff`, `refutation_pos_def_plus_conv`, `refutation_pos_def_minus_conv`, `cl_has_nilpotent_iff`, `refutation_null_vector_sum`, `refutation_degenerate_semidefinite`, `refutation_complex_sum_of_squares`, `refutation_finite_fields_sum_of_squares`, `refutation_hasse_minkowski_indefinite`, and `Int` instantiations). Only standard Lean kernel axioms appear.
- **Non-vacuity check:**
  - `OrderedDomain R` is concretely instantiated on `Int` (`instance : OrderedDomain Int`), and the main polymorphic theorems are explicitly instantiated on `Int` (`nonvacuous_int_grade1_iff`, `nonvacuous_int_cl_classification`, `nonvacuous_int_pos_def_nilpotents`).
  - `IntegralDomain` is concretely instantiated on `Int`, `GaussInt`, `F3`, and `F5`.
  - Every counterexample witness (`nilpotentCl20`, `nilpotentCl04`, `nullVecPlus`, `nullVecMinus`, `(1, i)` in `GaussInt`, `(1, 2)` in `F5`, `(1, 1, 1)` in `F3`) is accompanied by an explicit proof of `≠ 0`.

## 3. Independent Computational & Typographical Audit

- **Python verification (`verify.py` / `verification/python-verify.log`):** Standalone Python 3.12 script independently builds $2^n \times 2^n$ bitmask blade multiplication tables (distinct from Lean's recursive graded-doubling representation), confirming every algebraic identity, bounded reducedness check, polar orthogonality test in $\mathrm{Cl}_{2,2}$, finite-field Chevalley–Warning witnesses across all 24 odd primes $p \lt 100$, and rational Hasse–Minkowski anisotropy; exits with code `0`.
- **LaTeX & PDF audit (`main.tex` / `main.pdf` / `verification/pdf-build.log`):** Compiled cleanly with `pdflatex` with zero errors, zero unresolved references, and zero overfull boxes; every page visually inspected.
- **GitHub Markdown Math & Path Hygiene:** `README.md` and `pr_body.md` mechanically linted to ensure strict GitHub MathJax compatibility (`\mathrm` operators, `\lt`/`\gt` in math, `\bigl(...\bigr)` openings, and zero local filesystem paths).
