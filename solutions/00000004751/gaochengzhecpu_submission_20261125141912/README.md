# Conjecture 00000004751 — Resolution & Formalization Package

## Verdict: **DISPROVED**

This package resolves Conjecture `00000004751` (*binomial correction table of R-composition*) in the negative across every standard interpretation of the $R$-transform and its composition in free probability, while establishing the exact positive combinatorial structure constants behind each operation.

---

## Summary of Mathematical Findings

1. **Clarification of the Definitional Premise:**
   The literal logarithmic moment series $L_{\mu}(z) = \log(1 + M_{\mu}(z))$ neither matches the free cumulant series $\mathcal{C}_{\mu}(z) = z R_{\mu}(z) = \sum_{n \ge 1} \kappa_{n}(\mu) z^{n}$ (differing already at degree $2$: $\ell_{2} = m_{2} - \frac{1}{2}m_{1}^{2} \neq m_{2} - m_{1}^{2} = \kappa_{2}$ whenever $m_{1} \neq 0$) nor linearizes additive free convolution $\boxplus$ (for $\delta_{1} \boxplus \delta_{1} = \delta_{2}$, $[z^{2}]L_{\delta_{2}}(z) = 2 \neq 1 = 2[z^{2}]L_{\delta_{1}}(z)$). Reading "logarithmic version" in the standard heuristic sense (Voiculescu's $R$-transform or Nica–Speicher's cumulant series $\mathcal{C}_{\mu}$), we examine all three canonical notions of composition:

2. **Operation (A) — Unshifted Voiculescu Composition $\bigl(R_{f} \circ R_{g})(z) = R_{f}(R_{g}(z)\bigr)$:**
   - **Algebraic & analytic non-closedness for $\kappa_{1}(g) \neq 0$:** The constant term $[z^{0}](R_{f} \circ R_{g}) = \sum_{k=1}^{\infty} \kappa_{k}(f)\kappa_{1}(g)^{k-1}$ fails to terminate finitely in the cumulant algebra, and blows up analytically for the Marchenko–Pastur law $R_{\mu}(z) = (1 - z)^{-1}$ composed with $\nu = \delta_{1}$ ($R_{\nu}(z) = 1$).
   - **Loss of positivity even for centered laws ($\kappa_{1} = 0$):** For the symmetric Rademacher probability measure $\mu = \frac{1}{2}(\delta_{-1} + \delta_{1})$, $R_{\mu}(0) = 0$ so $R_{h} := R_{\mu} \circ R_{\mu}$ is formally well-defined, yet $m_{0}(h) = 1, m_{2}(h) = 1, m_{4}(h) = 0$, giving $\langle m_{h}, (x^{2} - 1)^{2}\rangle = -1 \lt 0$ (and $3 \times 3$ Hankel determinant $-1 \lt 0$).

3. **Operation (B) — Centered Cumulant ($R$-)Series Composition $\bigl(\mathcal{C}_{f} \circ \mathcal{C}_{g})(z) = \mathcal{C}_{f}(\mathcal{C}_{g}(z)\bigr)$:**
   - **Loss of positivity closedness:** Self-composition yields a strictly negative sixth moment $m_{6} = -2 \lt 0$ for the Rademacher law $\mu = \frac{1}{2}(\delta_{-1} + \delta_{1})$, and $\langle m_{h}, (x^{3} - x)^{2}\rangle = -2 \lt 0$ for the standard Wigner semicircle law ($\mathcal{C}_{\mathrm{sc}}(z) = z^{2}$).
   - **Failure of block-structure invariance on $\mathrm{NC}(n)$:** Unlike the classical partition lattice $\Pi(n)$, the noncrossing Möbius inversion coefficient $\mu_{\mathrm{NC}}(\pi, 1_{n}) = \prod_{W \in K(\pi)} (-1)^{|W|-1} C_{|W|-1}$ is **not** determined by the block structure $\mathrm{type}(\pi)$ for any $n \ge 4$:
     - At $n = 4$, type $\bigl(2,1,1\bigr)$: $\mu_{\mathrm{NC}}(\{\{1,2\},\{3\},\{4\}\}, 1_{4}) = 2 \neq 1 = \mu_{\mathrm{NC}}(\{\{1,3\},\{2\},\{4\}\}, 1_{4})$.
     - At $n = 6$, singleton-free uniform type $\bigl(2,2,2\bigr)$: $\mu_{\mathrm{NC}}(\{\{1,2\},\{3,4\},\{5,6\}\}, 1_{6}) = 2 \neq 1 = \mu_{\mathrm{NC}}(\{\{1,6\},\{2,5\},\{3,4\}\}, 1_{6})$.
     Hence no block-structure correction table $B(\lambda)$ on $\mathrm{NC}(n)$ can relate $\mu_{\mathrm{NC}}(\pi, 1_{n})$ to any nonzero block-type-invariant partition weight.
   - **Exact positive formula & non-integrality:** Power-series composition is governed by the Boolean lattice of interval partitions $\mathrm{Int}(n)$ ($|\mathrm{Int}(n)| = 2^{n-1}$) with multinomial coefficients $S_{\mathrm{comp}}(\lambda) = \ell(\lambda)! / \prod_{r} m_{r}(\lambda)!$. Even after aggregating over $\mathrm{NC}_{\lambda}(n)$, the ratio to $M_{1}(\lambda) = \sum_{\pi \in \mathrm{NC}_{\lambda}(n)} \mu_{\mathrm{NC}}(\pi, 1_{n})$ is $\lparen -1)^{k-1} k / \binom{n+k-2}{k-1}$, which is non-integral for every $n \ge 3$ (e.g., $-2/3$ at $n = 3$ and $3/10$ at $n = 4$) and merely divides out the noncrossing Lagrange factor.

4. **Operation (C) — Nica–Speicher Boxed Convolution $\bigl(\mathcal{C}_{f} \star \mathcal{C}_{g})(z\bigr)$:**
   In $[z^{n}](\mathcal{C}_{f} \star \mathcal{C}_{g}) = \sum_{\pi \in \mathrm{NC}(n)} a_{\pi} b_{K(\pi)}$, partition weights are identically $+1$ on $\bigl(\pi, K(\pi)\bigr)$, and $\mathrm{type}(K(\pi))$ splits across single $\mathrm{type}(\pi)$ classes ($4 \cdot (3,1) + 2 \cdot (2,2)$ on $\bigl(2,1,1\bigr)$ at $n = 4$; $2 \cdot (3,1,1,1) + 3 \cdot (2,2,1,1)$ on $\bigl(2,2,2\bigr)$ at $n = 6$).

---

## Package Structure

- `SOURCE.md` — Original untouched conjecture statement (`00000004751`).
- `main.tex` / `main.pdf` — Self-contained mathematical manuscript with complete proofs and tables.
- `verify.py` — Standalone Python 3 standard-library symbolic and combinatorial verification suite.
- `lean/` — Core Lean 4.19.0 formalization (`warningAsError = true`, zero `sorry`/`admit`/`native_decide`, zero custom `axiom`):
  - `Conjecture00000004751/Noncrossing.lean` — Set partitions, $\mathrm{NC}(n)$, Catalan numbers, Kreweras complements, and poset Möbius inversion from first principles.
  - `Conjecture00000004751/FreeSeries.lean` — Interval partitions ($|\mathrm{Int}(n+1)| = 2^{n}$), formal power series composition, moment–cumulant maps, boxed convolution, and universal polynomial square positivity over $\mathbb{Z}[x]$.
  - `Conjecture00000004751/Refutation.lean` — Formal refutation theorems across Operations (A), (B), and (C), ending with `conjecture_00000004751_disproved`.
- `verification/` — Complete reproducibility logs (Python suite, Lean toolchain, `lake build`, `#print axioms` audit, forbidden-token static scan, and `pdflatex` compilation).

---

## Reproducing Verification

```bash
# 1. Run exact Python symbolic & combinatorial verification
python3 verify.py

# 2. Build Core Lean 4.19.0 formalization (-DwarningAsError=true)
cd lean && lake build

# 3. Compile LaTeX manuscript
pdflatex -interaction=nonstopmode -halt-on-error main.tex
pdflatex -interaction=nonstopmode -halt-on-error main.tex
```
