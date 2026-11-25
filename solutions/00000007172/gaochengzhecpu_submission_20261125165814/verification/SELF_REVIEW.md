# Self-Review Audit — Conjecture 00000007172

## 1. Source Integrity & Bilingual Mathematical Coverage
- `SOURCE.md` was verified byte-for-byte identical to its initial staged state.
- Both English and Chinese formulations were analyzed across all five candidate mathematical models on bipartite quantum systems $\mathcal{H}_A \otimes \mathcal{H}_B \cong \mathbb{C}^d \otimes \mathbb{C}^d$ ($d \ge 2$):
  1. **Model $\mathcal{M}_1$ — Operator & Density-Matrix Multiplicative Singular-Value Bounds:** Gel'fand–Naimark / Horn bounds $\prod_{j=1}^k \sigma_j(XY) \le \prod_{j=1}^k \sigma_j(X)\sigma_j(Y)$ ($1 \le k \le d^2$), including rank-$1$ pure-state projections, full-rank invertible operators, commuting and non-commuting pairs.
  2. **Model $\mathcal{M}_2$ — Global Unitary / Rational Orthogonal Obstruction & Akemann–Weaver POVM Paving:** Explicit rational orthogonal entangler $Q_{\mathrm{ent}} \in \mathrm{O}_4(\mathbb{Q})$ (and general discrete Weyl–Bell unitaries $U_{\mathrm{Bell}} \in \mathrm{U}(d^2)$) conjugating unentangled product POVMs isospectrally to maximally entangled POVMs, plus fixed-norm Parseval frame subset-norm comparisons.
  3. **Model $\mathcal{M}_3$ — Pure-State Schmidt Singular-Value Partial Products & Choi–Jamiołkowski Composition:** Exact AM–GM dichotomy proving that the single full $d$-fold product ($k = d$) is uniquely saturated at maximal entanglement ($s_j^2 = 1/d$), whereas every proper partial product ($1 \le k < d$) is uniquely saturated by non-maximally-entangled Schmidt-rank-$k$ states and strictly violated by maximally entangled states ($d^{-k} < k^{-k}$).
  4. **Model $\mathcal{M}_4$ — Kronecker Tensor Products $\sigma(A \otimes B)$ & Quantum Marginal Spectra $\sigma(\rho_{AB})$ vs. $\sigma(\rho_A \otimes \rho_B)$:** Explicit failure of naive upper bounds ($8 > 4$ at $d = 2, k = 2$) and bidirectional spectral incomparability on maximally entangled states vs. equality on product states.
  5. **Model $\mathcal{M}_5$ — Agnihotri–Woodward $\mathrm{SU}(d^2)$ Quantum Schubert Product Bounds:** Singular-value triviality ($\sigma_j(U) \equiv 1$) and saturation of principal eigenangle facets by non-entangling local diagonal unitaries $D_A \otimes I_B$.

## 2. Non-Vacuity & Edge-Case Robustness
- Rather than relying on orthogonal edge cases ($P_1 P_2 = 0$) or rank-deficient operators alone, we constructed exact rational counterexamples in $\mathbb{Q}^2 \otimes \mathbb{Q}^2$ covering:
  - Unentangled pure product projection $P_{|00\rangle}$ and invertible product operator $Y_{\mathrm{prod}} = \mathrm{diag}(2,1) \otimes \mathrm{diag}(4,1)$ saturating all $k$-fold bounds;
  - Non-orthogonal, non-commuting rational maximally entangled projections $P_1, P_2$ ($\langle\psi_1|\psi_2\rangle = 3/5$, $[P_1, P_2] \neq 0$, $\sigma_1(P_1 P_2) = 3/5 < 1$);
  - Invertible maximally-entangled-eigenbasis operators $X_1, X_2$ failing every proper partial product $k \in \{1,2,3\}$ ($X_1 X_2 = 8 I_4$ vs. $\sigma_1 = 8$, giving $8 < 64$, $64 < 1024$, $512 < 4096$);
  - Non-commuting invertible ME-principal-eigenvector operators $\widetilde{X}_1 = I_4 + 3 P_1$, $\widetilde{X}_2 = I_4 + 3 P_2$ ($[\widetilde{X}_1, \widetilde{X}_2] \neq 0$, $\|\widetilde{X}_1 \widetilde{X}_2\|_F^2 = 115 < 256 = \sigma_1(\widetilde{X}_1)^2 \sigma_1(\widetilde{X}_2)^2$).
- All field-level theorems in Lean 4 are instantiated concretely at the verified exact rational field `QField`, guaranteeing non-vacuity of every typeclass hypothesis.

## 3. Core Lean 4.19.0 Formalization Audit
- Toolchain: `leanprover/lean4:v4.19.0`, zero external dependencies, `moreLeanArgs = ["-DwarningAsError=true"]`.
- Audited `lean/Main.lean` for forbidden tokens: zero `sorry`, zero `admit`, zero `native_decide`, zero `axiom`, zero `unsafe`, zero `extern`, zero `implemented_by`, zero `opaque`.
- Verified `#print axioms` on `opNormSqBound_matMul`, `rankOneProj_prod_singValSq`, `rankOneProj_prod_saturated_iff_eq`, `schmidt_full_product_max_iff_maximally_entangled`, `schmidt_proper_partial_product_refutation`, `nonOrthogonal_maximallyEntangled_strict_nonsaturation`, `akemann_weaver_povm_orthogonal_equivalence`, and `conjecture_00000007172_resolution`: only standard Lean 4 core axioms (`propext`, `Classical.choice`, `Quot.sound`) appear.

## 4. Python Verification, PDF Visual Inspection, and Package Hygiene
- `verify.py` ran cleanly with pure standard-library Python 3 (exit code `0`), checking all exact rational identities and $5{,}800$ complex singular-value inequality checks across $d \in \{2, 3, 4\}$.
- `main.tex` compiled cleanly twice via `pdflatex -interaction=nonstopmode -halt-on-error main.tex`; every page of `main.pdf` was visually inspected with zero errors and zero overfull boxes.
- `README.md` and `pr_body.md` passed automated GitHub MathJax safety checks (zero forbidden macros, zero raw `<`/`>` inside `$...$` or `$$...$$`, zero inline math starting with `$(`, zero local paths).
- Temporary build artifacts (`lean/.lake/`, `*.aux`, `*.out`, `*.toc`, root `*.log`) were removed after archiving UTF-8 normalized build logs in `verification/`.
