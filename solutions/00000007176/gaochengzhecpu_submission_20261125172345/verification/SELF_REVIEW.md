# Self-Review Audit — Conjecture 00000007176

## 1. Statement Fidelity & Bilingual Verification

- **`SOURCE.md` integrity:** Byte-identical to the original problem statement (verified untouched).
- **Both English and Chinese statements analyzed:**
  - *English:* "Definition: The extrema of tensor eigenvalues with higher-order spectra. Conjecture: The modulus upper bound of the spectra of symmetric tensors is the degree power, and the realization of the bound is the binomial type. (binomial-realized tensor spectral bound)"
  - *Chinese:* "定义：张量特征值的极值：高阶谱。猜想：张量谱的刚性：对称张量的谱的模的上界为度数的幂且界的实现为二项型。（张量谱二项型实现度数幂上界模）"
- **Comprehensive coverage of spectral definitions, normalizations, and terminological readings:**
  - Checked Qi's (2005) and Lim's (2005) $H$-eigenvalues (both real and complex eigenpairs), $Z$-eigenvalues ($\|x\|_2 = 1$), and complex $E$-eigenvalues ($x^\top x = 1$ in $\mathbb{C}^n$).
  - Checked all standard normalizations: unnormalized tensors, entrywise bounded ($|a_\alpha| \le 1$ and $\lbrace 0, 1 \rbrace$-entries), Frobenius-norm normalized ($\|\mathcal{A}\|_F \le 1$), entrywise $\ell_1$-normalized ($\|\mathcal{A}\|_1 \le 1$), polynomial-coefficient bounded ($|c_\alpha| \le 1$), and $k$-uniform hypergraph vertex-degree ($\Delta$) adjacency tensors.
  - Addressed both meanings of "binomial type" (support-$2$ binomial homogeneous forms $\bigl(x_1 + x_2\bigr)^m$ vs. literal binomial-entry tensors $\mathcal{B}_{m,2}$ with $a_{i_1 \dots i_m} = \binom{m}{\#\{r : i_r = 2\}}$) as well as the $n$-variable all-ones uniform tensor $\mathcal{J}_{m,n}$.

## 2. Non-Vacuity & Structural Audit of Lean 4.19.0 Formalization

- **Toolchain & build flags:** `leanprover/lean4:v4.19.0` with `moreLeanArgs = ["-DwarningAsError=true"]` and zero external dependencies.
- **Zero cheats:** Verified zero occurrences of `sorry`, `admit`, `native_decide`, or custom `axiom` across all `.lean` files in `lean/`.
- **Axiom audit (`verification/lean-axioms.log`):** `#print axioms` run across all 40 core declarations (`vandermonde`, `cauchy_schwarz_list`, `powSum_two_m_le`, `entrywise_H_bound_complex`, `entrywise_H_rigidity_complex`, `entrywise_H_rigidity_nonneg`, `entrywise_H_rigidity_odd_real`, `entrywise_H_rigidity_even_real`, `entrywise_Z_bound`, `frob_Z_bound`, `frob_Z_rigidity`, `frob_H_bound`, `binomialEntry_exact_H_radius`, all `refutation_*` theorems, and concrete `Int` / `RatField` instantiations). Only standard Lean kernel axioms (`propext`, `Classical.choice`, `Quot.sound`) appear.
- **Non-vacuity check:**
  - `OrderedDomain R` is concretely instantiated on both `Int` ($\mathbb{Z}$) and `RatField` ($\mathbb{Q}$, constructed from first principles via `Quot`), and its complexification `ComplexOver R` is proved to be an `IntegralDomain`.
  - Every `IsHEigenpair` witness carries a machine-checked `IsNonzeroVec` proof, and every `IsZEigenpair` / `IsComplexEEigenpair` witness over `RatField` / `ComplexOver RatField` satisfies the exact unit-norm equation $\sum x_i^2 = 1$ (no cleared-denominator proxies).

## 3. Independent Computational & Typographical Audit

- **Python verification (`verify.py` / `verification/python-verify.log`):** Standalone Python 3.12 script independently constructs full $n^m$ Cartesian index dictionaries and uses complex polynomial root-finding and exact `Fraction` arithmetic to verify every algebraic identity, exhaustive $\lbrace -1, 0, 1 \rbrace$ rigidity counts, Vandermonde radii, Frobenius bounds, and complex $E$-eigenvalue unboundedness; exits with code `0`.
- **LaTeX & PDF audit (`main.tex` / `main.pdf` / `verification/pdf-build.log`):** Compiled cleanly with `pdflatex` with zero errors, zero warnings, and zero overfull boxes; every page visually inspected.
- **GitHub Markdown Math & Path Hygiene:** `README.md`, `pr_body.md`, and `SELF_REVIEW.md` mechanically linted to ensure strict GitHub MathJax compatibility (`\mathrm` operators, `\lt`/`\gt` inside math, `\bigl(...\bigr)` delimiters, and zero local filesystem paths).
