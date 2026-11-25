# Conjecture 00000007168 — Disproof and Formal Verification

## Verdict: **FALSE** (Refuted Across All Natural Readings for All $n \ge 2$)

### Source Statement (`SOURCE.md`)

> **English.** Definition: Schur's inequality with the spectral bounds of power sums. Conjecture: The upper bound of power sums is the sum of spectral-radius powers, and the realization of the bound is the normal matrix. (normal-realized Schur power-sum bound)
>
> **中文。** 定义：Schur 不等式：幂和的谱界。猜想：Schur 幂和的极值：幂和的上界为谱半径幂的和且界的实现为正规矩阵。（Schur 正常谱半径幂和上界极值）

---

## Executive Summary

Let $\mathbb{F} \in \{\mathbb{R}, \mathbb{C}\}$ and let $A \in M_n(\mathbb{F})$ ($n \ge 2$) have complex eigenvalues $\lambda_1, \dots, \lambda_n \in \mathbb{C}$, singular values $\sigma_1 \ge \dots \ge \sigma_n \ge 0$, spectral radius $\rho(A) = \max_{1 \le i \le n} |\lambda_i|$, and squared Frobenius norm $\|A\|_F^2 = \mathrm{tr}(A^* A) = \sum_{i,j=1}^n |a_{ij}|^2$.

Conjecture `00000007168` conflates two distinct classical matrix inequalities:

1. **Classical Schur's Inequality (1909):**
   $$\sum_{i=1}^n |\lambda_i(A)|^2 \le \|A\|_F^2 = \mathrm{tr}(A^* A),$$
   where equality **is** characterized by normal matrices ($A A^* = A^* A$), because $\|A\|_F^2$ is unitarily invariant but sensitive to non-orthogonal eigenspaces and superdiagonal Schur entries.
2. **Spectral-Radius Power-Sum Inequality ($k \ge 1$):**
   $$\bigl|\mathrm{tr}(A^k)\bigr| \le \sum_{i=1}^n |\lambda_i(A)|^k \le \sum_{i=1}^n \rho(A)^k = n\,\rho(A)^k.$$
   Here both sides of $\sum_{i=1}^n |\lambda_i|^k \le n\,\rho(A)^k$ depend purely on the spectrum of $A$ (invariant under arbitrary similarity $S A S^{-1}$), so equality characterizes **equal-modulus spectra** ($|\lambda_1| = \dots = |\lambda_n| = \rho(A)$), **not** normality. Conversely, replacing the left-hand side by Frobenius or singular-value power sums $\|A^k\|_F^2$ or $\sum_{i=1}^n \sigma_i(A)^p$ causes the upper bound $n\,\rho(A)^{2k}$ or $n\,\rho(A)^p$ to **fail altogether** on non-normal matrices (such as nonzero nilpotent matrices where $\rho(A) = 0$).

Consequently, for every dimension $n \ge 2$ over both $M_n(\mathbb{R})$ and $M_n(\mathbb{C})$, **every natural mathematical reading of Conjecture `00000007168` is false**:

| Mathematical Reading ($n \ge 2$) | Upper Bound Status | Normality Realization Test | Counterexamples / Exact Characterization |
| :--- | :--- | :--- | :--- |
| **1A.** Eigenvalue modulus power sum $\sum_{i=1}^n |\lambda_i|^k \le n\,\rho(A)^k$ ($k \ge 1$) | **True** | **False** (both $\Rightarrow$ and $\Leftarrow$ fail) | Eq. $\iff |\lambda_1| = \dots = |\lambda_n| = \rho(A)$; non-normal $J_n = I_n + E_{12}$ attains $n = n\,\rho(J_n)^k$; normal $D_n = \mathrm{diag}(1,0,\dots,0)$ gives $1 \lt n$ |
| **1B.** Trace / Newton power sum $\lvert\mathrm{tr}(A^k)\rvert \le n\,\rho(A)^k$ ($k \ge 1$) | **True** | **False** (both $\Rightarrow$ and $\Leftarrow$ fail) | Eq. $\iff |\lambda_i| \equiv \rho(A)$ and $\lambda_1^k = \dots = \lambda_n^k$; non-normal $J_n$ attains $n$; normal $D_n$ gives $1 \lt n$ |
| **2A.** Frobenius power norm $\|A^k\|_F^2 \le n\,\rho(A)^{2k}$ ($k \ge 1$) | **False** | Upper bound itself fails | Nilpotent $N_{n,c} = c E_{12}$ ($c \ne 0$) has $\rho = 0$ and $\|N_{n,c}\|_F^2 = \lvert c\rvert^2 \gt 0$; shear $J_n$ has $\|J_n^k\|_F^2 = n + k^2 \gt n$ |
| **2B.** Singular-value / Schatten power sum $\sum_{i=1}^n \sigma_i(A)^p \le n\,\rho(A)^p$ ($p \gt 0$) | **False** | Upper bound itself fails | $\mathrm{tr}\bigl((N_{n,c}^* N_{n,c})^k\bigr) = \lvert c\rvert^{2k} \gt 0 = n\,\rho(N_{n,c})^{2k}$; $\sum_{i=1}^n \sigma_i(J_n^k)^p \gt n$ |
| **3A.** Scaled multi-exponent sum $\sum_{k=1}^K P_k(A) \le \sum_{k=1}^K n\,\rho(A)^k$ | **True** (for 1A/1B) | **False** (both $\Rightarrow$ and $\Leftarrow$ fail) | Non-normal $J_n$ attains $K n = K n$; normal $D_n$ gives $K \lt K n$ |
| **3B.** Unscaled sum $\le \rho(A)^k$ or $\sum_{k=1}^K \rho(A)^k$ (without factor $n$) | **False** | Upper bound itself fails | Normal $I_n$ has $\rho(I_n) = 1$ and gives $n \gt 1$ and $K n \gt K$ |
| **Benchmark:** Classical Schur $\sum_{i=1}^n |\lambda_i|^2 \le \|A\|_F^2$ | **True** | **True** ($\iff$ normal) | Upper bound is $\|A\|_F^2 = \mathrm{tr}(A^* A)$, **not** $n\,\rho(A)^2$ |

---

## Minimal Explicit $2 \times 2$ Counterexamples (Extending to All $n \ge 2$)

All three core counterexample families have entries in $\{0, 1\} \subset \mathbb{Z} \subset \mathbb{R} \subset \mathbb{C}$ (extending to any $n \ge 2$ via direct sum with $I_{n-2}$ or $0_{n-2}$):

1. **Non-normal matrix realizing the spectral-radius power-sum bound for all $k \ge 1$:**
   $$J_2 = \begin{pmatrix} 1 & 1 \\ 0 & 1 \end{pmatrix}, \qquad J_2^k = \begin{pmatrix} 1 & k \\ 0 & 1 \end{pmatrix}.$$
   Its eigenvalues are $\lambda_1 = \lambda_2 = 1$, so $\rho(J_2) = 1$ and $\mathrm{tr}(J_2^k) = |\lambda_1|^k + |\lambda_2|^k = 2 = 2\,\rho(J_2)^k$ for every $k \ge 1$. Yet $J_2 J_2^* = \begin{pmatrix} 2 & 1 \\ 1 & 1 \end{pmatrix} \ne \begin{pmatrix} 1 & 1 \\ 1 & 2 \end{pmatrix} = J_2^* J_2$, so $J_2$ is **not normal** (and $\|J_2^k\|_F^2 = 2 + k^2 \gt 2 = 2\,\rho(J_2)^{2k}$).
   *(Dense non-triangular unitary conjugate: $A_{\mathrm{dense}} = U J_2 U^* = \frac{1}{25}\begin{pmatrix} 13 & 9 \\ -16 & 37 \end{pmatrix}$ with $U = \frac{1}{5}\begin{pmatrix} 3 & -4 \\ 4 & 3 \end{pmatrix}$ is likewise non-normal and realizes $2 = 2\,\rho(A_{\mathrm{dense}})^k$ for all $k \ge 1$.)*

2. **Normal matrix failing to realize the spectral-radius power-sum bound for all $k \ge 1$:**
   $$D_2 = \begin{pmatrix} 1 & 0 \\ 0 & 0 \end{pmatrix}, \qquad D_2^k = D_2.$$
   $D_2$ is real symmetric, hence **normal** ($D_2 D_2^* = D_2^* D_2$), and achieves equality in classical Schur's inequality ($|\lambda_1|^2 + |\lambda_2|^2 = 1 = \|D_2\|_F^2$), with $\rho(D_2) = 1$. Yet for every $k \ge 1$, $|\mathrm{tr}(D_2^k)| = |\lambda_1|^k + |\lambda_2|^k = \|D_2^k\|_F^2 = 1 \lt 2 = 2\,\rho(D_2)^k$.

3. **Non-normal nilpotent matrix refuting Frobenius and singular-value spectral-radius bounds:**
   $$N_{2,c} = \begin{pmatrix} 0 & c \\ 0 & 0 \end{pmatrix} \quad (c \ne 0).$$
   Here $\lambda_1 = \lambda_2 = 0$ so $\rho(N_{2,c}) = 0$, whereas $\|N_{2,c}\|_F^2 = |c|^2 \gt 0 = 2\,\rho(N_{2,c})^2$ and $\mathrm{tr}\bigl((N_{2,c}^* N_{2,c})^k\bigr) = |c|^{2k} \gt 0 = 2\,\rho(N_{2,c})^{2k}$ for every $k \ge 1$.

---

## Package Layout and Verification

- `SOURCE.md` — Original bilingual problem statement (unmodified).
- `main.tex` / `main.pdf` — Self-contained mathematical paper proving the positive benchmark theorems (classical $n \times n$ Schur inequality and normality characterization, spectral-radius power-sum bounds, equal-modulus characterization, normal Frobenius bound) and refuting every reading of Conjecture `00000007168`.
- `lean/` — Standalone Core Lean 4 (`leanprover/lean4:v4.19.0`) formalization with zero external dependencies, compiled with `-DwarningAsError=true` and zero `sorry`s:
  - `lean/lean-toolchain`, `lean/lakefile.toml`, `lean/lake-manifest.json`
  - `lean/Main.lean` — Constructs `LinearOrderedCommRing`, `LinearOrderedField`, verified `Int` and exact rational `QField` instances, `Complex R`, finite sums and $n$-variable complex Lagrange/Cauchy–Schwarz, $n \times n$ Schur inequality and normality characterization (`schur_inequality`, `schur_eq_iff_isNormal`), spectral-radius characterizations (`eigModPowSum_eq_iff_equal_moduli`, `normal_frobNormSq_matPow_le`), all $n \times n$ counterexample families, the dense rational-unitary witness (`denseJordanQ_not_isNormal_yet_attains_bounds`), and master refutation theorems (`conjecture_00000007168_complete_resolution`).
- `verify.py` — Independent pure-Python verification suite checking exact $\mathbb{Q}(i)$ counterexample families for $n = 2,\dots,6$ and $k = 1,\dots,6$, dense and diagonalizable witnesses, singular-value AM–GM bounds, and $2{,}000$ random matrix stress tests over $M_n(\mathbb{R})$ and $M_n(\mathbb{C})$.
- `verification/` — Complete build and audit logs (`lake-build.log`, `lean-axioms.log`, `lean-version.log`, `pdf-build.log`, `python-verify.log`, `SELF_REVIEW.md`).
