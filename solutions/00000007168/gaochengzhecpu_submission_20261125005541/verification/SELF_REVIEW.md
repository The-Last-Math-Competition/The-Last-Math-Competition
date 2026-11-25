# Self-Review and Verification Audit — Conjecture 00000007168

## 1. Source Integrity & Scope Check
- `SOURCE.md` was read first and verified byte-identical to its staged original (482 bytes, untouched).
- Both the English statement (*"Definition: Schur's inequality with the spectral bounds of power sums. Conjecture: The upper bound of power sums is the sum of spectral-radius powers, and the realization of the bound is the normal matrix. (normal-realized Schur power-sum bound)"*) and the Chinese statement (*"定义：Schur 不等式：幂和的谱界。猜想：Schur 幂和的极值：幂和的上界为谱半径幂的和且界的实现为正规矩阵。（Schur 正常谱半径幂和上界极值）"*) were analyzed in full.

## 2. Exhaustive Mathematical Coverage ($M_n(\mathbb{C})$ and $M_n(\mathbb{R})$, $n \ge 2$)
Every natural reading of "power sums", "sum of spectral-radius powers", and "the realization of the bound is the normal matrix" is explicitly addressed in `main.tex`/`main.pdf`, `lean/Main.lean`, `verify.py`, and `README.md`:

1. **Reading 1A — Eigenvalue modulus power sums $\sum_{i=1}^n |\lambda_i(A)|^k \le n\,\rho(A)^k$ ($k \ge 1$):**
   - Upper bound **holds** (`eigModPowSum_le_spectralPowerBound`).
   - Exact equality condition proved (`eigModPowSum_eq_iff_equal_moduli`): $|\lambda_1| = \dots = |\lambda_n| = \rho(A)$ (equal-modulus spectrum, invariant under invertible similarity).
   - Normality **necessity fails**: non-normal $J_n = I_n + E_{12}$ ($n \ge 2$) attains $n = n\,\rho(J_n)^k$ for all $k \ge 1$ while $J_n J_n^* \ne J_n^* J_n$ (`jordanBlock_not_isNormal`, `jordanBlock_attains_eigModPowSum`); dense non-triangular rational-unitary conjugate $A_{\mathrm{dense}} = U J_2 U^* = \frac{1}{25}\begin{pmatrix} 13 & 9 \\ -16 & 37 \end{pmatrix}$ (`denseJordanQ_not_isNormal_yet_attains_bounds`) and diagonalizable non-normal involution $B = \begin{pmatrix} 1 & -2 \\ 0 & -1 \end{pmatrix}$ also attain equality.
   - Normality **sufficiency fails**: normal projection $D_n = \mathrm{diag}(1,0,\dots,0)$ satisfies $D_n D_n^* = D_n^* D_n$ (`diagProj_isNormal`) and Schur equality, yet gives $1 < n = n\,\rho(D_n)^k$ for all $k \ge 1$ (`diagProj_fails_eigModPowSum`).

2. **Reading 1B — Trace / Newton power sums $|\mathrm{tr}(A^k)| \le n\,\rho(A)^k$ ($k \ge 1$):**
   - Upper bound **holds** via $n$-variable complex Lagrange/Cauchy–Schwarz (`complex_lagrange`, `trace_normSq_le_spectralPowerBound`).
   - Both necessity and sufficiency of normality **fail** (`refute_reading1_trace_power_sum`) via $J_n$ and $D_n$ (and even unitary $\mathrm{diag}(1, i)$ fails at $k = 1$).

3. **Benchmark Contrast — Classical Schur's Inequality $\sum_{i=1}^n |\lambda_i(A)|^2 \le \|A\|_F^2 = \mathrm{tr}(A^* A)$:**
   - Proved in full generality for all $n \in \mathbb{N}$ in Core Lean 4 (`schur_inequality`, `schur_eq_iff_isNormal`), establishing that equality holds **if and only if** $A$ is normal ($A A^* = A^* A$), and bridging real and complex normality (`isRealNormal_iff_isNormal_toComplex`).

4. **Reading 2 — Frobenius, Singular-Value, Schatten, and Entrywise Power Sums ($\|A^k\|_F^2 \le n\,\rho(A)^{2k}$, $\mathrm{tr}((A^* A)^k) \le n\,\rho(A)^{2k}$, $\sum_{i=1}^n \sigma_i(A)^p \le n\,\rho(A)^p$):**
   - Proved valid *when restricted to normal matrices* (`normal_frobNormSq_matPow_le`), where equality still requires equal-modulus eigenvalues rather than general normality (`diagProj_fails_frobPowerBound`).
   - On general matrices, **the upper bound itself fails** (`refute_reading2_frobenius_and_schatten`):
     - Non-normal nilpotent family $N_{n,c} = c E_{12}$ ($c \ne 0$) has $\rho(N_{n,c}) = 0$ while $\|N_{n,c}\|_F^2 = |c|^2 > 0$ (`nilpotentBlock_exceeds_frobBound`) and $\mathrm{tr}((N_{n,c}^* N_{n,c})^k) = |c|^{2k} > 0$ for all $k \ge 1$ (`nilpotentBlock_exceeds_schattenBound`).
     - Shear powers $J_n^k = I_n + k E_{12}$ have $\rho(J_n) = 1$ while $\|J_n^k\|_F^2 = n + k^2 > n$ for all $k \ge 1$ (`jordanBlock_exceeds_frobPowerBound`), and $\sum_{i=1}^n \sigma_i(J_n^k)^p > n$ for all $p > 0$ by strict AM–GM.

5. **Reading 3 — Multi-exponent sums ($\sum_{k=1}^K P_k(A)$) and unscaled spectral-radius sums ($\le \rho(A)^k$ or $\sum_{k=1}^K \rho(A)^k$ without factor $n$):**
   - Both refuted for all $n \ge 2$ and $K \ge 1$ (`refute_reading3_multi_exponent_and_unscaled`), with the unscaled bound failing immediately on the normal identity matrix $I_n$ ($n > 1$, $K n > K$).

## 3. Lean 4.19.0 Formalization Audit
- **Toolchain:** `leanprover/lean4:v4.19.0` (verified in `verification/lean-version.log`).
- **Configuration:** Self-contained Core Lean 4 (`lakefile.toml` has zero external dependencies and `moreLeanArgs = ["-DwarningAsError=true"]`; clean `lake-manifest.json` included).
- **Soundness & Non-Vacuity:**
  - Zero `sorry`, zero `admit`, zero `native_decide`, zero `axiom`, zero `unsafe`, zero `extern`, zero `implemented_by`, zero `opaque`.
  - Both `LinearOrderedCommRing` and `LinearOrderedField` are constructively inhabited in `Main.lean` via `Int` and exact rational numbers `QField` (`Quotient RawRat.setoid`), preventing any vacuous-typeclass loophole.
  - `#print axioms` (`verification/lean-axioms.log`) confirms all main theorems depend solely on `[propext, Classical.choice, Quot.sound]` (with `schur_inequality` using only `[propext, Quot.sound]`).

## 4. Independent Python, PDF Visual, and GitHub Markdown Audits
- `verify.py` exits with code `0` (`verification/python-verify.log`), checking exact $\mathbb{Q}(i)$ counterexamples ($n = 2..6$, $k = 1..6$), dense/diagonalizable witnesses, singular-value AM–GM inequalities, and 2,000 randomized real and complex matrix tests.
- `main.pdf` compiled twice with `pdflatex -interaction=nonstopmode -halt-on-error main.tex`, achieving zero errors, zero overfull `\hbox`es, and clean page-by-page visual layout.
- `README.md` verified compliant with all GitHub Markdown math rules: no `\operatorname`, `\bowtie`, `\coloneqq`, `\DeclareMathOperator`, or `\newcommand`; no raw `<` or `>` inside math spans; no `$(` inline math openers; and no local filesystem paths.
- Temporary build artifacts (`lean/.lake/`, `*.aux`, `*.out`, `*.toc`, root `*.log`) cleaned from `package/`.
