# Conjecture 00000007153: Diagonal-Equality Lidskii Product Majorization

**Verdict:** **FALSE (Disproved across all standard interpretations)**

## Problem Statement

> **English.** Definition: Lidskii with the majorization of singular values. Conjecture: The strengthening in product form is the logarithmic majorization, and the equality of the majorization is the diagonal operator. (diagonal-equality Lidskii product majorization)
>
> **中文。** 定义：Lidskii：奇异值的优超。猜想：Lidskii 的强化：乘积形式的对数优超且超的等式为对角算子。（Lidskii 对角等式对数乘积优超强化）

## Mathematical Resolution

Lidskii's additive singular-value majorization $\sigma(A + B) \prec_w \sigma(A) + \sigma(B)$ (and $|\sigma(A) - \sigma(B)|^\downarrow \prec_w \sigma(A - B)$) strengthens multiplicatively for operator products to the classical **Horn--Lidskii--Wielandt product logarithmic majorization**

$$\sigma(AB) \prec_{\log} \sigma(A) \circ \sigma(B),$$

meaning $\prod_{j=1}^k \sigma_j(AB) \le \prod_{j=1}^k \sigma_j(A)\sigma_j(B)$ for $1 \le k \lt n$ with equality at $k = n$ via $|\det(AB)| = |\det A|\,|\det B|$.

However, the conjectured **diagonal-operator equality characterization** is **false** under every standard reading of "diagonal operator" and across all dimensions $n \ge 2$ (as well as for injective compact operators on $\ell^2(\mathbb{N})$):

1. **Refutation for canonical-basis diagonal operators (even on commuting symmetric positive definite integer matrices):**
   Let

   $$A_{\mathrm{spd}} = \begin{pmatrix} 3 & 1 \\ 1 & 3 \end{pmatrix}, \qquad B_{\mathrm{spd}} = \begin{pmatrix} 3 & 2 \\ 2 & 3 \end{pmatrix}, \qquad A_{\mathrm{spd}} B_{\mathrm{spd}} = \begin{pmatrix} 11 & 9 \\ 9 & 11 \end{pmatrix}.$$

   Then $\sigma(A_{\mathrm{spd}}) = (4, 2)$, $\sigma(B_{\mathrm{spd}}) = (5, 1)$, and $\sigma(A_{\mathrm{spd}} B_{\mathrm{spd}}) = (20, 2) = (4 \cdot 5,\, 2 \cdot 1)$, attaining exact equality in every partial product ($k = 1, 2$), while **none** of $A_{\mathrm{spd}}$, $B_{\mathrm{spd}}$, or $A_{\mathrm{spd}} B_{\mathrm{spd}}$ is diagonal.

2. **Refutation for normal (unitarily diagonalizable), commuting, and even similarity-diagonalizable operators over $\mathbb{C}$:**
   Using Euclid's Pythagorean rotations $R(p, q) \in \mathrm{SO}(2, \mathbb{Q})$, define

   $$A_{\mathrm{def}} = \begin{pmatrix} 16 & -12 \\ 3 & 4 \end{pmatrix}, \qquad B_{\mathrm{def}} = \begin{pmatrix} 173 & -216 \\ -36 & 212 \end{pmatrix}, \qquad A_{\mathrm{def}} B_{\mathrm{def}} = \begin{pmatrix} 3200 & -6000 \\ 375 & 200 \end{pmatrix}.$$

   Then $\sigma(A_{\mathrm{def}}) = (20, 5)$, $\sigma(B_{\mathrm{def}}) = (340, 85)$, and $\sigma(A_{\mathrm{def}} B_{\mathrm{def}}) = (6800, 425) = \sigma(A_{\mathrm{def}}) \circ \sigma(B_{\mathrm{def}})$, yet:
   - none of $A_{\mathrm{def}}$, $B_{\mathrm{def}}$, or $A_{\mathrm{def}} B_{\mathrm{def}}$ is diagonal or normal ($X^\top X \ne X X^\top$);
   - $A_{\mathrm{def}} B_{\mathrm{def}} \ne B_{\mathrm{def}} A_{\mathrm{def}}$;
   - **both** $A_{\mathrm{def}}$ ($\chi_{A_{\mathrm{def}}}(t) = (t - 10)^2$) and $A_{\mathrm{def}} B_{\mathrm{def}}$ ($\chi_{A_{\mathrm{def}} B_{\mathrm{def}}}(t) = (t - 1700)^2$) have non-trivial $2 \times 2$ Jordan blocks and are **not similar to any diagonal matrix over $\mathbb{C}$** (and the $4 \times 4$ block pair $\bigl(17 A_{\mathrm{def}} \oplus B_{\mathrm{def}}^\top,\, B_{\mathrm{def}} \oplus 17 A_{\mathrm{def}}^\top\bigr)$ makes all three of $\mathcal{A}, \mathcal{B}, \mathcal{A}\mathcal{B}$ Jordan-defective over $\mathbb{C}$).

3. **Exact true characterization of equality:**
   For simple positive singular values with SVDs $A = U_1 \Sigma_A V_1^*$ and $B = U_2 \Sigma_B V_2^*$, equality $\sigma(AB) = \sigma(A)\circ\sigma(B)$ holds if and only if the internal coupling unitary $W = V_1^* U_2$ is diagonal unitary (equivalently, in $2 \times 2$, $A^\top A$ commutes with $B B^\top$ and their traceless parts are positively aligned), leaving the outer unitary factors $U_1, V_2$ and shared inner basis $V_1$ completely arbitrary.

4. **Refutation of alternative single-operator interpretations:**
   - **Weyl's log-majorization $|\lambda(M)| \prec_{\log} \sigma(M)$:** Equality holds iff $M$ is normal, not diagonal; $W = \begin{pmatrix} 2 & 1 \\ 1 & 2 \end{pmatrix}$ is non-diagonal with $|\lambda(W)| = \sigma(W) = (3, 1)$.
   - **Diagonal pinching $|d(M)|^\downarrow$ vs. $\sigma(M)$:** While $|d(M)|^\downarrow \prec_w \sigma(M)$ holds additively, on $W = \begin{pmatrix} 2 & 1 \\ 1 & 2 \end{pmatrix}$ one has $|d(W)|^\downarrow = (2, 2)$ and $\sigma(W) = (3, 1)$, violating weak log-majorization in **both** directions ($2 \cdot 2 = 4 \gt 3 = 3 \cdot 1$ at $k = 2$, and $3 \gt 2$ at $k = 1$).

## Package Contents

- `SOURCE.md` — Unmodified competition problem statement.
- `main.tex`, `main.pdf` — Self-contained mathematical paper proving both the positive majorization theorems and all counterexamples across finite and compact Hilbert-space settings.
- `verify.py` — Standalone Python 3 verification suite (standard library only: exact integer/rational arithmetic and one-sided Jacobi SVD).
- `lean/` — Pure Core Lean 4 (`leanprover/lean4:v4.19.0`, zero external dependencies, `-DwarningAsError=true`) formalization of:
  - `LidskiiProduct/Algebra.lean`: Brahmagupta--Fibonacci identity and product-to-sum majorization bridges;
  - `LidskiiProduct/Matrix2.lean`: Uniqueness of $2 \times 2$ singular values (`hasSingularValues_unique`), universal $2 \times 2$ Horn--Lidskii product log-majorization (`lidskii_product_log_majorization`), exact Gram commutation/alignment iff characterization (`lidskii_product_eq_iff_gram_aligned`), Weyl's log-majorization (`weyl_log_majorization`), diagonal-pinching equality (`diag_abs_eq_sv_implies_diagonal`), and non-diagonalizability of defective matrices (`Mat2.defective_not_similar_to_diag`);
  - `LidskiiProduct/Counterexamples.lean`: Positive diagonal witness (`positive_witness_diagonal`), disproofs of all six interpretations, and the all-dimensions $n = m + 2 \ge 2$ counterexample family (`disproof_all_dimensions_ge_two`);
  - `LidskiiProduct.lean`: Master conjunction refutation `conjecture_00000007153_disproved`.
- `verification/` — Build, version, axiom-audit, PDF compilation, and Python verification logs, plus `SELF_REVIEW.md`.
