# Self-Review & Audit Report — Conjecture 00000004719

## 1. Scope & Integrity Check
- **Single Conjecture Verified:** Only Conjecture `00000004719` is addressed.
- **`SOURCE.md` Byte Identity:** `SOURCE.md` is byte-for-byte identical to `conjectures/00000004719.md` (verified via SHA-256 hash).
- **Clean Directory Tree:** No `.lake/`, `__pycache__/`, `.aux`, `.log`, or `.out` build artifacts remain outside `verification/*.log`.

## 2. Semantic Completeness & Non-Vacuity Audit
Every plausible interpretation of the English and Chinese problem statements is formalized and refuted:
1. **Combinatorial Definition Faithfulness:**
   - `IsFactor u w` (`∃ p s, p ++ u ++ s = w`) and `IsBalanced w` (`∀ u v, IsFactor u w → IsFactor v w → u.length = v.length → ∀ a, natDist (letterCount a u) (letterCount a v) ≤ 1`) match the exact text *"A balanced word is a word where letter counts of same-length factors differ by at most one"*.
   - Decidable boolean reflections (`isBalancedBool_eq_true_iff`, `usesAllLettersBool_eq_true_iff`, `hasAtLeastLettersBool_eq_true_iff`) are proved equivalent to the propositional definitions, and `balancedCount_spec` / `surjBalancedCount_spec` / `atLeastBalancedCount_spec` prove exact duplicate-free finite cardinality (`HasCardinality`).
2. **Positive Non-Vacuity Witnesses (Ensuring No Vacuous Negations):**
   - `unary_balanced_isRationalGF` proves `IsRationalGF (balancedCount 1)` ($\sum_{n \ge 0} x^n = \frac{1}{1-x}$).
   - `arith_seq_isRationalGF` proves `IsRationalGF (fun n => n + 1)` ($\sum_{n \ge 0} (n+1)x^n = \frac{1}{(1-x)^2}$, Sturmian single-word complexity).
   - `unary_parikh_isRationalParikhGF` proves `IsRationalParikhGF 1` ($\frac{1}{1 - x_0}$).
   - `fraenkel7_balanced_surj_witness` proves Fraenkel's ternary word `[0, 1, 0, 2, 0, 1, 0]` satisfies `IsBalanced w ∧ UsesAllLetters 3 w`.
   - `word_0011_not_balanced_witness` proves `[0, 0, 1, 1]` satisfies `¬ IsBalanced w`.
3. **Complete Coverage of Readings:**
   - **Total-Count Finiteness (`disproof_Conjecture4719_TotalCountFinite_Multiletter`):** Refuted for all $k \ge 1$ ($k = 2, 3, \dots$) via periodic surjective balanced words $w_{k,n}$ and non-periodic Hubert cyclic-splitting words.
   - **Univariate Per-Length OGF ($k \ge 2$ and $k \ge 3$):** Refuted for `balancedCount 2` and `surjBalancedCount 2` (`disproof_Conjecture4719_UnivariateRational_Ge2`, `disproof_Conjecture4719_SurjUnivariateRational_Ge2`), and for strict multiletter $k \ge 3$ (`balancedCount 5` and `atLeastBalancedCount 5 2`, plus all $k$ with an odd prime divisor of $k - 2$: `disproof_Conjecture4719_UnivariateRational_Ge3`, `disproof_Conjecture4719_MultiletterAtLeast2Rational_Ge3`), supplemented by the exact ternary ($k = 3$) palindrome parity proof in `main.tex` / `verify.py`.
   - **Multivariate Parikh OGF ($\forall k \ge 2$, including $k = 3$):** Refuted for every $k \ge 2$ (`not_isRationalParikhGF`, `disproof_Conjecture4719_ParikhRational_Ge3`).
   - **Christoffel-Type Denominator Clause:** Refuted uniformly for any predicate `IsChristoffelDenominator : PolyQ → Prop` (`disproof_Conjecture4719_FullWithChristoffel`).

## 3. Lean 4.19.0 Soundness & Axiom Audit
- **Toolchain:** `leanprover/lean4:v4.19.0` (Core Lean 4 only; `packages = []` in `lake-manifest.json`).
- **Compiler Flags:** `moreLeanArgs = ["-DwarningAsError=true"]` in `lakefile.toml`; clean build exits with code `0` and zero warnings.
- **Forbidden Construct Scan:** Zero occurrences of `sorry`, `admit`, `native_decide`, custom `axiom`, `unsafe`, `extern`, `implemented_by`, or `opaque`.
- **`#print axioms` Verification (`verification/lean-axioms.log`):** All 27 audited theorems depend exclusively on subsets of standard Lean kernel axioms `{propext, Classical.choice, Quot.sound}`.

## 4. Computational & Typographical Verification
- **`verify.py` (`verification/python-verify.log`):** Exits with code `0`; independently cross-checks brute-force enumeration against canonical backtracking, Lipatov's formula, mechanical Christoffel central words, prime-cycle congruences ($k = 5, 7, 8$), ternary even-length palindrome formula ($6 \le m \le 55$), and nonsingularity of Hankel matrices up to order $18$ ($k = 2$) and $16$ ($k = 3$).
- **`main.pdf` (`verification/pdf-build.log`):** Compiled via 2-pass `pdflatex` with exit code `0`, zero errors, zero undefined references, zero `Overfull \hbox`, and zero warnings.
