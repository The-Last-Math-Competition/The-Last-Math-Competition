# Self-Review Audit — Conjecture 00000007153

## 1. Verdict and Multi-Interpretation Completeness

- **Problem:** Conjecture `00000007153` (*diagonal-equality Lidskii product majorization*).
- **Verdict:** **FALSE (Disproved)**.
- **Coverage of Interpretations:**
  1. **Reading A1 (Canonical-basis diagonal factors in product log-majorization $\sigma(AB) \prec_{\log} \sigma(A)\circ\sigma(B)$):** Disproved even on commuting $2 \times 2$ symmetric positive definite integer matrices $A_{\mathrm{spd}} = \begin{pmatrix} 3 & 1 \\ 1 & 3 \end{pmatrix}$ and $B_{\mathrm{spd}} = \begin{pmatrix} 3 & 2 \\ 2 & 3 \end{pmatrix}$ ($\sigma(A_{\mathrm{spd}}) = (4, 2)$, $\sigma(B_{\mathrm{spd}}) = (5, 1)$, $\sigma(A_{\mathrm{spd}}B_{\mathrm{spd}}) = (20, 2)$).
  2. **Reading A2 (Canonical-basis diagonal product $AB$, or at least one of $A, B, AB$ diagonal):** Disproved for every finite dimension $n \ge 2$ via explicit rational-orthogonal SVDs $A^{(n)}, B^{(n)} \in M_n(\mathbb{Z})$, as well as for injective trace-class compact operators on $\ell^2(\mathbb{N})$.
  3. **Reading A3 (Unitarily diagonalizable / normal operators, or commuting operators):** Disproved by $A_{\mathrm{def}} = \begin{pmatrix} 16 & -12 \\ 3 & 4 \end{pmatrix}$ and $B_{\mathrm{def}} = \begin{pmatrix} 173 & -216 \\ -36 & 212 \end{pmatrix}$, where none of $A_{\mathrm{def}}, B_{\mathrm{def}}, A_{\mathrm{def}}B_{\mathrm{def}}$ is normal and $A_{\mathrm{def}}B_{\mathrm{def}} \ne B_{\mathrm{def}}A_{\mathrm{def}}$.
  4. **Reading A4 (Similarity-diagonalizable operators over $\mathbb{C}$):** Disproved by the same pair $(A_{\mathrm{def}}, B_{\mathrm{def}})$: both $A_{\mathrm{def}}$ ($\chi(t) = (t - 10)^2$) and $A_{\mathrm{def}}B_{\mathrm{def}}$ ($\chi(t) = (t - 1700)^2$) have non-trivial $2 \times 2$ Jordan blocks and are not similar to any diagonal matrix over $\mathbb{C}$ (and in $4 \times 4$, $\mathcal{A} = 17 A_{\mathrm{def}} \oplus B_{\mathrm{def}}^\top$ and $\mathcal{B} = B_{\mathrm{def}} \oplus 17 A_{\mathrm{def}}^\top$ make all three of $\mathcal{A}, \mathcal{B}, \mathcal{A}\mathcal{B}$ defective over $\mathbb{C}$).
  5. **Reading B (Weyl single-operator log-majorization $|\lambda(M)| \prec_{\log} \sigma(M)$):** Equality holds iff $M$ is normal, not diagonal; refuted by $W = \begin{pmatrix} 2 & 1 \\ 1 & 2 \end{pmatrix}$.
  6. **Reading C (Diagonal pinching $|d(M)|^\downarrow$ vs. $\sigma(M)$):** Weak log-majorization fails in both directions on $W = \begin{pmatrix} 2 & 1 \\ 1 & 2 \end{pmatrix}$ ($|d(W)|^\downarrow = (2, 2)$, $\sigma(W) = (3, 1)$).

## 2. Non-Vacuity and Definition Soundness Audit

- **Canonical Singular Value Definition:** `HasSingularValues M s1 s2` requires $0 \le s_2 \le s_1$, $s_1^2 + s_2^2 = \mathrm{tr}(M^\top M)$, and $(s_1 s_2)^2 = \det(M^\top M)$ — the exact characteristic-polynomial root conditions for $(s_1^2, s_2^2)$ on $M^\top M$. Uniqueness is formally proved in `hasSingularValues_unique`.
- **Orthogonal SVD Certificate (`n >= 2`):** `HasScaledOrthogonalSVD M v` requires non-negativity and non-increasing order of $v$, plus explicit integer matrices $U, V$ and positive scales $s_U, s_V > 0$ satisfying $U^\top U = s_U^2 I_n$, $V^\top V = s_V^2 I_n$, and $(s_U s_V) M = U\,\mathrm{diag}(v)\,V^\top$, directly witnessing the real orthogonal SVD $M = (U / s_U)\,\mathrm{diag}(v)\,(V / s_V)^\top$.
- **Positive Witness:** `positive_witness_diagonal` verifies that sorted positive diagonal matrices $D_1 = \mathrm{diag}(4, 2)$ and $D_2 = \mathrm{diag}(5, 1)$ satisfy `IsDiagonal`, `HasSingularValues`, and `LogMajorizesEq2`.
- **Universal Positive Theorems:** Rather than proving only ground counterexamples, `Matrix2.lean` proves universal $2 \times 2$ Horn--Lidskii product log-majorization (`lidskii_product_log_majorization`), its exact iff equality criterion (`lidskii_product_eq_iff_gram_aligned`), the implication $\prec_{\log} \implies \prec_w$ (`logMajorizes2_implies_weakMajorizes2`), Weyl's log-majorization and symmetry iff (`weyl_log_majorization`), and universal similarity non-diagonalizability of defective matrices (`Mat2.defective_not_similar_to_diag`).

## 3. Lean 4 Toolchain and Axiom Hygiene

- **Toolchain:** `leanprover/lean4:v4.19.0`, zero external dependencies in `lakefile.toml` (no `mathlib`), compiled with `moreLeanArgs = ["-DwarningAsError=true"]`.
- **Forbidden Constructs Scan:** Zero occurrences of `sorry`, `admit`, `native_decide`, custom `axiom`, `unsafe`, `extern`, `implemented_by`, or `opaque`.
- **Axiom Audit:** Verified via `#print axioms` in `verification/lean-axioms.log` that all main theorems depend only on standard Lean kernel axioms (`propext`, `Quot.sound`, or none at all).

## 4. Paper, Markdown, and Package Hygiene

- `SOURCE.md` is completely unmodified.
- `main.pdf` compiled cleanly via `pdflatex` (two passes) with zero unresolved references and zero overfull boxes; auxiliary TeX files (`.aux`, `.log`, `.out`) and `lean/.lake/` build artifacts removed prior to final packaging.
- `README.md` and `pr_body.md` pass automated checks for GitHub MathJax compliance (no `\operatorname`, `\bowtie`, `\coloneqq`, `\DeclareMathOperator`, `\newcommand`, raw `<` / `>` in math, `$(` inline math openers, or local machine paths).
