# Conjecture 00000007173 — Disproof and Formal Verification

## Verdict: **FALSE** (Disproved Across All Standard Readings)

---

## 1. Original Statement

From `SOURCE.md`:

> **English.** Definition: Majorization with the poset of spectra. Conjecture: The endpoints of the majorization chain are the ordered spectra, and the realization of the endpoints is permutation similarity. (permutation-similar majorization endpoints)
>
> **中文。** 定义：优超：谱的偏序。猜想：优超的极值元素：优超链的端点为排序谱且点的实现为置换相似。（优超置换相似排序谱端点极值链）

---

## 2. Executive Summary

For vectors $x, y \in \mathbb{R}^n$, write $x^\downarrow$ and $x^\uparrow$ for the non-increasing and non-decreasing rearrangements of $x$. Recall that $x$ is **majorized** by $y$ ($x \prec y$) if

$$\sum_{i=1}^k x_i^\downarrow \le \sum_{i=1}^k y_i^\downarrow \quad (1 \le k \le n-1) \qquad \text{and} \qquad \sum_{i=1}^n x_i = \sum_{i=1}^n y_i.$$

Modulo coordinate permutations $\mathfrak{S}_n$, majorization restricts to a partial order (poset) on ordered real spectra $\mathbb{R}_\downarrow^n = \{ \lambda \in \mathbb{R}^n : \lambda_1 \ge \dots \ge \lambda_n \}$. Two $n \times n$ matrices $A, B$ are **permutation-similar** if $A = P B P^\top$ for some permutation matrix $P \in \mathcal{P}_n$.

Evaluating every standard interpretation of the conjecture in spectral theory and matrix analysis shows that the conjecture is **false in every case**:

1. **Reading I — Schur–Horn Diagonal Majorization ($\mathrm{diag}(A) \prec \lambda(A)$):**
   - **Lower endpoint failure (even for real symmetric matrices):** For any non-scalar spectrum $\lambda \in \mathbb{R}_\downarrow^n$ ($\lambda_1 \gt \lambda_n$) with mean $\bar{\lambda} = \frac{1}{n}\sum_{i=1}^n \lambda_i$, the minimum element of the Schur–Horn majorization interval $\{ d \in \mathbb{R}_\downarrow^n : d \prec \lambda \}$ is the uniform vector $\bar{\lambda}\mathbf{1}$, which satisfies $\bar{\lambda}\mathbf{1} \prec \lambda$ and $\lambda \not\prec \bar{\lambda}\mathbf{1}$ — hence is **not** an ordered rearrangement of $\lambda$. Furthermore, for $\lambda = (2, 0)$ and lower endpoint $\bar{\lambda}\mathbf{1} = (1, 1)$, the real symmetric integer matrices

     $$A_+ = \begin{pmatrix} 1 & 1 \\ 1 & 1 \end{pmatrix}, \qquad A_- = \begin{pmatrix} 1 & -1 \\ -1 & 1 \end{pmatrix}$$

     both have ordered spectrum $\lambda^\downarrow(A_\pm) = (2, 0)$ and diagonal $\mathrm{diag}(A_\pm) = (1, 1)$, yet **neither** is permutation-similar to $\mathrm{diag}(2, 0)$ and $A_+$ is **not** permutation-similar to $A_-$.
   - **Upper endpoint failure without Hermiticity:** On general real matrices with real spectrum, attaining $\mathrm{diag}(B) = \lambda^\downarrow(B)$ does not imply permutation similarity to $\mathrm{diag}\bigl(\lambda^\downarrow(B)\bigr)$: both $B_1 = \begin{pmatrix} 1 & 1 \\ 0 & 0 \end{pmatrix}$ (diagonalizable over $\mathbb{Z}$ with distinct spectrum $\lambda^\downarrow(B_1) = (1, 0)$) and $B_2 = \begin{pmatrix} 1 & 1 \\ 0 & 1 \end{pmatrix}$ (Jordan block with spectrum $\lambda^\downarrow(B_2) = (1, 1)$) satisfy $\mathrm{diag}(B_i) = \lambda^\downarrow(B_i)$ while failing permutation similarity to $\mathrm{diag}\bigl(\lambda^\downarrow(B_i)\bigr)$.

2. **Reading II — Lidskii–Wielandt Eigenvalue Sum Majorization ($\lambda(A + B)$):**
   - For Hermitian (or real symmetric) $A, B$, Lidskii's chain

     $$\bigl(\lambda^\downarrow(A) + \lambda^\uparrow(B)\bigr)^\downarrow \;\prec\; \lambda^\downarrow(A + U B U^*) \;\prec\; \lambda^\downarrow(A) + \lambda^\downarrow(B)$$

     genuinely has endpoints formed from identically ordered and oppositely ordered spectra, but realizing those endpoints requires **unitary/orthogonal similarity** $U \in U(n)$ (or $O(n)$), **not** permutation similarity $P \in \mathcal{P}_n$.
   - Specifically, for the real symmetric integer matrices

     $$A = \begin{pmatrix} 25 & 0 \\ 0 & 0 \end{pmatrix}, \qquad B = \begin{pmatrix} 9 & 12 \\ 12 & 16 \end{pmatrix},$$

     both with ordered spectrum $\lambda^\downarrow = (25, 0)$, rational orthogonal matrices $U_{\mathrm{up}}, U_{\mathrm{low}} \in O(2, \mathbb{Q})$ realize the Lidskii upper endpoint $\lambda_{\mathrm{up}} = (50, 0)$ and lower endpoint $\lambda_{\mathrm{low}} = (25, 25)$, whereas **every** permutation matrix $P \in \mathcal{P}_2$ gives ordered spectrum $\lambda^\downarrow(A + P B P^\top) \in \{ (40, 10),\, (45, 5) \}$, strictly interior to the chain ($25 \lt 40 \lt 45 \lt 50$).

3. **Reading III — Fixed-Trace and PSD Slices of the Poset of Spectra:**
   - On the fixed-trace poset $\mathcal{S}_{n,\tau} = \{ \lambda \in \mathbb{R}_\downarrow^n : \sum_{i=1}^n \lambda_i = \tau \}$ ($n \ge 2$), majorization chains have **no upper endpoint** ($\lambda' = (\lambda_1 + 1, \lambda_2, \dots, \lambda_{n-1}, \lambda_n - 1)$ strictly majorizes $\lambda$).
   - On the positive-semidefinite slice $\mathcal{S}_{n,\tau}^+$ ($\tau \gt 0, n \ge 2$), the endpoints $\lambda_{\min} = \frac{\tau}{n}\mathbf{1}$ (rank $n$) and $\lambda_{\max} = (\tau, 0, \dots, 0)$ (rank $1$) have distinct spectra, so no realizing matrices are permutation-similar across endpoints, nor are realizations at $\lambda_{\max} = (2, 0)$ unique up to permutation similarity ($A_+$ vs. $\mathrm{diag}(2, 0)$).

---

## 3. Positive Non-Vacuity Results

To confirm that all definitions are faithful and to isolate the exact special cases that motivate the conjecture, we also prove four positive results:

1. **Collapse of opposite orderings (`nonvacuity_ordering_equivalence`):** $x^\downarrow \prec x^\uparrow$ and $x^\uparrow \prec x^\downarrow$, so opposite coordinate orderings represent the **same** maximum element in the majorization poset rather than opposite endpoints of a chain.
2. **General $n \times n$ Schur Frobenius theorem (`nonvacuity_schur_upper_endpoint_dim_n`):** Whenever $\|A\|_F^2 = \sum_{k=1}^n \lambda_k^2$ (automatic for symmetric/Hermitian $A$) and $\mathrm{diag}(A)$ is a permutation of $\lambda$, $A$ is diagonal and permutation-similar to $\mathrm{diag}(\lambda)$.
3. **Exact $2 \times 2$ symmetric upper-endpoint equivalence (`nonvacuity_schur_upper_endpoint_symm2`):** For symmetric $2 \times 2$ matrices $A$ with ordered spectrum $\lambda^\downarrow(A) = (l_1, l_2)$, $\lambda^\downarrow(A) \prec \mathrm{diag}(A)$ holds if and only if $A$ is permutation-similar to $\mathrm{diag}(l_1, l_2)$.
4. **Already-diagonal Lidskii realization (`nonvacuity_lidskii_diagonal_case`):** When $A = \mathrm{diag}(a_1, a_2)$ and $B = \mathrm{diag}(b_1, b_2)$ are already diagonal in the standard basis, both Lidskii endpoints are realized by permutation similarities of $B$.

---

## 4. Package Contents and Verification

| Path | Description |
| :--- | :--- |
| `SOURCE.md` | Original untouched bilingual problem statement |
| `README.md` | Overview of mathematical disproof, non-vacuity results, and verification |
| `main.tex` / `main.pdf` | Self-contained mathematical paper with complete proofs across all readings |
| `verify.py` | Zero-dependency Python 3.12 verification suite (exact `Fraction` + randomized stress tests) |
| `lean/lean-toolchain` | Pinned to `leanprover/lean4:v4.19.0` |
| `lean/lakefile.toml` | Self-contained Core Lean 4 package (`moreLeanArgs = ["-DwarningAsError=true"]`) |
| `lean/lake-manifest.json` | Clean Lake manifest with zero external dependencies |
| `lean/Main.lean` | Complete formalization with zero `sorry`, zero `native_decide`, and `#print axioms` checks |
| `verification/` | Build and audit logs (`lake-build.log`, `lean-axioms.log`, `lean-version.log`, `pdf-build.log`, `python-verify.log`, `SELF_REVIEW.md`) |

### Reproducing the Verification

1. **Lean 4.19.0 formalization:** Run `lake build` inside `lean/` (compiles `Main.lean` cleanly with `-DwarningAsError=true` and verifies that all main theorems use only `propext`, `Classical.choice`, and `Quot.sound`).
2. **Independent Python check:** Run `python verify.py` from the package root (exits with status `0`).
3. **Paper build:** Run `pdflatex -interaction=nonstopmode -halt-on-error main.tex` twice in the package root.
