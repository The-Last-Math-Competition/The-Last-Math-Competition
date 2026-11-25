# Self-Review Audit for Conjecture 00000008532

## 1. Problem Fidelity and Definitional Coverage

- **Source text (`SOURCE.md`):** Preserved byte-identically. Both the English and Chinese formulations define the Sperner number of a lattice as the size of its largest antichain and conjecture that for the free distributive lattice on $n$ generators, this number is an explicit central correction of $\binom{n}{\lfloor n/2 \rfloor}$ of logarithmic order with always positive sign.
- **Both standard lattice conventions covered:**
  1. `FD n` ($\mathrm{FD}(n)$, bounded free distributive lattice with $\bot, \top$, cardinality $M(n) = 2, 3, 6, 20, 168, 7581, \dots$): formalized in `SpernerFD/Lattice.lean` together with a machine-checked proof (`evalBounded_isHom`, `evalBounded_gen`, `evalBounded_unique`) of its categorical universal property over arbitrary bounded distributive lattices.
  2. `FD0 n` ($\mathrm{FD}_0(n)$, unbounded free distributive lattice without empty join/meet, cardinality $0, 1, 4, 18, 166, 7579, \dots$): formalized as monotone functions preserving `0...0 ↦ false` and `1...1 ↦ true`, with width invariance `spernerFD0_eq_spernerFD` proved for all $n \ge 1$.
- **Signed integer arithmetic (no `Nat` subtraction truncation):** Both `spernerCorrectionFD` and `spernerCorrectionFD0` are defined in `Int` (`(spernerFD n : Int) - (centralBinom n : Int)`), avoiding any natural-number subtraction truncation pitfall. Non-negativity `0 ≤ spernerCorrectionFD n` is proved separately via the elementary conjunction embedding `centralBinom_le_spernerFD`.

## 2. Verification of Both Independent Refutations and Non-Vacuity

1. **Failure of always-positive sign:**
   - Exact evaluations in `SpernerFD/SmallN.lean`: `spernerFD 0 = 1`, `spernerFD 1 = 1`, `spernerFD 2 = 2`, `spernerFD 3 = 4` (and `spernerFD0 0 = 0`, `spernerFD0 1 = 1`, `spernerFD0 2 = 2`, `spernerFD0 3 = 4`).
   - Thus $\Delta(1) = \Delta_0(1) = 0$ and $\Delta(2) = \Delta_0(2) = 0$ (and $\Delta(0) = 0$, $\Delta_0(0) = -1$), formalized in `not_always_positive_FD`, `not_always_positive_FD_pos_n`, `not_always_positive_FD0`, and `not_always_positive_FD0_pos_n`.
   - Complete sign classification `spernerCorrectionFD_pos_iff` proves `0 < spernerCorrectionFD n ↔ 3 ≤ n`.
2. **Failure of logarithmic order (doubly-exponential lower bound):**
   - `midSliceAntichain n` constructs an explicit duplicate-free list of pairwise incomparable monotone functions in `FD n` of length `centralBinom (centralBinom n)`.
   - `spernerFD_ge_iterated_centralBinom` and `spernerFD_ge_double_exp` establish $w(\mathrm{FD}(n)) \ge \binom{N_n}{\lfloor N_n/2 \rfloor} \ge 2^{2^{\lfloor n/2 \rfloor - 1}}$ for all $n \ge 2$.
   - `correction_exceeds_any_exponential` proves that for *every* threshold $n_0$, base $B$, and constants $C, D$, there exists $n \ge n_0$ with $\Delta(n) = \Delta_0(n) > C B^n + D$. In particular, `not_logarithmic_order_FD` and `not_logarithmic_order_FD0` refute any asymptotic $O(\log n)$ bound starting from any $n_0 \in \mathbb{N}$ (not merely $n_0 = 1$).

## 3. Lean 4 Toolchain, Build, and Axiom Audit

- **Toolchain:** `leanprover/lean4:v4.19.0` (Core Lean only; zero external dependencies in `lakefile.toml`).
- **Strict compiler flags:** `moreLeanArgs = ["-DwarningAsError=true"]` enabled; clean build from scratch passes with 0 errors and 0 warnings (`verification/lake-build.log`).
- **Forbidden constructs check:** Grep across all `lean/**/*.lean` confirms zero occurrences of `sorry`, `admit`, `native_decide`, or `axiom`.
- **Axiom audit (`verification/lean-axioms.log`):** `#print axioms` on all 31 core theorems reports exclusively the standard Lean 4 kernel axioms (`propext`, `Classical.choice`, `Quot.sound`), with zero custom axioms and zero `Lean.ofReduceBool`.

## 4. Computational and Typesetting Audit

- **Python suite (`verify.py`, `verification/python-verify.log`):** Pure Python 3.12 standard library; exits with code `0`; independently certifies exact Sperner numbers $w(\mathrm{FD}(0..5)) = [1, 1, 2, 4, 24, 621]$ via Hopcroft–Karp matching and König–Dilworth chain partitions, verifies DNF representations and Lean bitmask certificates, and checks doubly-exponential bounds through $n = 10$.
- **LaTeX & PDF inspection (`main.tex`, `main.pdf`, `verification/pdf-build.log`):** Compiled with two `pdflatex` passes; `pdf-build.log` has 0 errors, 0 undefined references/citations, and 0 overfull `\hbox`es. Visual page-by-page inspection of all pages confirmed clean equation layout, table alignment, and unbroken bibliography formatting.
