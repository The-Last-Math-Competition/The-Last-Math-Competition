# Conjecture 00000007172 — Quantum Singular-Value Product Bounds and Maximal-Entanglement Saturation

## Problem Statement

From `SOURCE.md`:

> **English.** Definition: Akemann-Weaver with the product bounds of singular values. Conjecture: The quantum version of the product inequality holds, and the saturation of the version is maximal entanglement. (maximally-entangled AW quantum saturation)
>
> **中文。** 定义：Akemann–Weaver：奇异值的乘积界。猜想：AW 的量子化：乘积不等式的量子版本且本的饱和为最大纠缠。（Akemann-Weaver 最大纠缠量子乘积饱和）

---

## Final Verdict: **FALSE** (Positive Product Bounds Proved; Maximal-Entanglement Saturation Refuted)

Let $\mathcal{H} = \mathcal{H}_A \otimes \mathcal{H}_B \cong \mathbb{C}^d \otimes \mathbb{C}^d$ ($d \ge 2$, global dimension $D = d^2$) be a finite-dimensional bipartite quantum system. Conjecture `00000007172` blends three distinct threads of matrix analysis and quantum theory:

1. **Gel'fand–Naimark / Horn multiplicative singular-value bounds** $\prod_{j=1}^k \sigma_j(XY) \le \prod_{j=1}^k \sigma_j(X)\sigma_j(Y)$ and **Agnihotri–Woodward (1998)** ("AW") *quantum Schubert calculus* product inequalities on $\mathrm{SU}(n)$ (where "quantum" denotes small quantum cohomology $QH^*(\mathrm{Gr}(k,n))$, not quantum entanglement);
2. **Akemann–Weaver (2014)** ("AW") noncommutative POVM / positive-operator Kadison–Singer paving bounds $\sigma_1\bigl(\sum_{i \in S} A_i\bigr)$ on $\mathcal{B}(\mathcal{H})$;
3. **Pure-state Schmidt singular-value products** on $\mathbb{C}^d \otimes \mathbb{C}^d$, where the **single full $d$-fold product** $\prod_{j=1}^d s_j(\psi)^2 \le d^{-d}$ (AM–GM under $\sum_{j=1}^d s_j(\psi)^2 = 1$) *is* uniquely saturated at maximal entanglement ($s_j^2 = 1/d$).

Across **all five natural mathematical models** ($\mathcal{M}_1$–$\mathcal{M}_5$) for every $d \ge 2$, **Conjecture `00000007172` is false**: whenever the singular-value product or paving inequality holds universally, maximal entanglement fails to characterize (and in proper partial-product and non-aligned operator cases strictly fails to achieve) saturation.

---

## Summary Across All Five Mathematical Models

| Model ($d \ge 2$) | Product / Paving Inequality | ME Saturation? | Exact Behavior and Counterexamples |
| :--- | :---: | :---: | :--- |
| **$\mathcal{M}_1$:** Operator product $\prod_{j=1}^k \sigma_j(XY) \le \prod_{j=1}^k \sigma_j(X)\sigma_j(Y)$ on $\mathcal{B}(\mathbb{C}^d \otimes \mathbb{C}^d)$ | **True** ($1 \le k \le d^2$) | **False** ($\not\Rightarrow$ and $\not\Leftarrow$) | Unentangled $P_{\lvert 00\rangle}$ and $\mathrm{diag}(2,1)\otimes\mathrm{diag}(4,1)$ saturate all $k$; rational ME states give $\sigma_1(P_1 P_2) = 3/5 \lt 1$ and $\sigma_1(X_1 X_2) = 8 \lt 64$ |
| **$\mathcal{M}_2$:** Akemann–Weaver POVM / frame subset paving $\sum_{i \in S} A_i$ | **True** (MSS / AW) | **False** (unitarily blind) | $Q_{\mathrm{ent}} \in \mathrm{O}_4(\mathbb{Q})$ conjugates unentangled POVM to ME POVM isospectrally; collinear product copies beat orthogonal ME pairs ($1 \gt 1/2$) |
| **$\mathcal{M}_3$:** Pure-state Schmidt partial products $\prod_{j=1}^k s_j(\psi)^2 \le k^{-k}$ | **True** ($1 \le k \le d$) | **True** at $k=d$; **False** for $1 \le k \lt d$ | Full product $k=d$ uniquely saturated at $s_j^2 = 1/d$; for every $1 \le k \lt d$, Schmidt-rank-$k$ states saturate $k^{-k}$ while ME gives $d^{-k} \lt k^{-k}$ |
| **$\mathcal{M}_4$:** Kronecker $\sigma(A \otimes B)$ and marginals $\sigma(\rho_{AB})$ vs. $\sigma(\rho_A \otimes \rho_B)$ | **False** ($k \ge 2$ / $k=1$) | **False** | $\sigma_1\sigma_2\bigl(\mathrm{diag}(2,1)^{\otimes 2}\bigr) = 8 \gt 4$; ME pure state has $\sigma_1(\rho_{AB}) = 1 \gt d^{-2}$ and $\sigma_1\sigma_2(\rho_{AB}) = 0 \lt d^{-4}$; product states give equality |
| **$\mathcal{M}_5$:** Agnihotri–Woodward $\mathrm{SU}(d^2)$ quantum Schubert bounds | **True** | **False** | All $U \in \mathrm{SU}(d^2)$ have $\sigma_j(U) \equiv 1$; eigenangle facets saturated by local non-entangling unitaries $D_A \otimes I_B$ |

---

## Explicit Rational Counterexamples in $\mathbb{Q}^2 \otimes \mathbb{Q}^2 \cong \mathbb{Q}^4$

All core counterexamples live over $\mathbb{Q}$ (with zero irrational square roots even in the normalized state vectors):

1. **Rational Orthogonal Entangler $Q_{\mathrm{ent}} \in \mathrm{O}_4(\mathbb{Q})$ (Models $\mathcal{M}_1, \mathcal{M}_2$):**
   $$Q_{\mathrm{ent}} = \frac{1}{2}\begin{pmatrix} 1 & 1 & 1 & -1 \\ -1 & 1 & 1 & 1 \\ 1 & -1 & 1 & 1 \\ 1 & 1 & -1 & 1 \end{pmatrix}, \qquad Q_{\mathrm{ent}}^T Q_{\mathrm{ent}} = Q_{\mathrm{ent}} Q_{\mathrm{ent}}^T = I_4.$$
   Every column $\lvert \beta_r \rangle \in \mathbb{Q}^4$ has unit norm and reduced density matrices $\rho_A(\beta_r) = \rho_B(\beta_r) = \frac{1}{2} I_2$ (**maximally entangled**). Conjugation $X \mapsto Q_{\mathrm{ent}} X Q_{\mathrm{ent}}^T$ preserves products, subset sums, and all singular values while mapping the unentangled computational basis $\{\lvert 00\rangle, \lvert 01\rangle, \lvert 10\rangle, \lvert 11\rangle\}$ onto $\{\lvert \beta_0\rangle, \lvert \beta_1\rangle, \lvert \beta_2\rangle, \lvert \beta_3\rangle\}$.

2. **Unentangled Product Saturation vs. Non-Orthogonal Rational Maximally Entangled Failure (Model $\mathcal{M}_1$):**
   - **Unentangled product state:** $\lvert 00\rangle = (1,0,0,0)^T$ has $\rho_A = \mathrm{diag}(1,0)$ (zero entanglement), yet $P_{\lvert 00\rangle}^2 = P_{\lvert 00\rangle}$ saturates $\prod_{j=1}^k \sigma_j(P_{\lvert 00\rangle}^2) = \prod_{j=1}^k \sigma_j(P_{\lvert 00\rangle})^2$ for all $1 \le k \le 4$ (as does the invertible product operator $Y_{\mathrm{prod}} = \mathrm{diag}(2,1) \otimes \mathrm{diag}(4,1)$).
   - **Non-orthogonal, non-commuting maximally entangled pair:** Let $\lvert \psi_1 \rangle = \lvert \beta_0 \rangle = \frac{1}{2}(1,-1,1,1)^T$ and $\lvert \psi_2 \rangle = (I_2 \otimes U)\lvert \psi_1 \rangle = \frac{1}{10}(7,1,-1,7)^T \in \mathbb{Q}^4$ where $U = \frac{1}{5}\begin{pmatrix} 3 & -4 \\ 4 & 3 \end{pmatrix} \in \mathrm{SO}_2(\mathbb{Q})$. Both are maximally entangled ($\rho_A = \rho_B = \frac{1}{2}I_2$), $\langle \psi_1 \vert \psi_2 \rangle = \frac{3}{5} \ne 0$, and $P_1 P_2 \ne P_2 P_1$, yet
     $$\sigma_1(P_1 P_2) = \lvert \langle \psi_1 \vert \psi_2 \rangle \rvert = \frac{3}{5} \lt 1 = \sigma_1(P_1)\,\sigma_1(P_2), \qquad \sigma_1(P_1 P_2)^2 = \frac{9}{25} \lt 1.$$
   - **Invertible ME operators:** $X_1 = 8 P_{\beta_0} + 4 P_{\beta_1} + 2 P_{\beta_2} + P_{\beta_3}$ and $X_2 = P_{\beta_0} + 2 P_{\beta_1} + 4 P_{\beta_2} + 8 P_{\beta_3}$ have $X_1 X_2 = 8 I_4$, strictly failing every proper $k \in \{1,2,3\}$ ($8 \lt 64$, $64 \lt 1024$, $512 \lt 4096$); the non-commuting pair $\widetilde{X}_1 = I_4 + 3 P_1$, $\widetilde{X}_2 = I_4 + 3 P_2$ satisfies $\sigma_1(\widetilde{X}_1 \widetilde{X}_2)^2 \le \lVert \widetilde{X}_1 \widetilde{X}_2 \rVert_F^2 = 115 \lt 256 = \sigma_1(\widetilde{X}_1)^2 \sigma_1(\widetilde{X}_2)^2$.

3. **Proper Schmidt Partial-Product Dichotomy (Model $\mathcal{M}_3$, All $d \ge 2$):**
   While $\prod_{j=1}^d s_j(\psi)^2 \le d^{-d}$ is uniquely saturated at $s_j^2 = 1/d$, for every $1 \le k \lt d$ the sharp bound $\prod_{j=1}^k s_j(\psi)^2 \le k^{-k}$ is uniquely saturated by non-maximally-entangled Schmidt-rank-$k$ states ($s_1^2 = \dots = s_k^2 = 1/k$, $s_{k+1}^2 = \dots = s_d^2 = 0$), whereas maximal entanglement yields $d^{-k} \lt k^{-k}$ (and at $k = 1$ achieves the global minimum $s_1^2 = 1/d \lt 1$).

---

## Package Contents and Verification

- `SOURCE.md` — Original bilingual problem statement (unmodified).
- `main.tex` and `main.pdf` — Self-contained mathematical paper proving all positive theorems, structural obstructions, rational counterexamples, and Lean declaration mappings.
- `verify.py` — Standalone pure-Python 3 verification script (standard library only) checking exact rational witnesses in $\mathbb{Q}^2 \otimes \mathbb{Q}^2$, Schmidt partial products for $2 \le d \le 7$, Kronecker and marginal spectra, $\mathrm{SU}(4)$ local-unitary saturation, and $5{,}800$ complex singular-value checks across $d \in \{2,3,4\}$ (exits with code `0`).
- `lean/` — Self-contained Core Lean `4.19.0` formalization (`lean-toolchain`, `lakefile.toml`, `lake-manifest.json`, `Main.lean`) with zero external dependencies, `moreLeanArgs = ["-DwarningAsError=true"]`, zero `sorry`/`admit`/`native_decide`, and standard axioms (`propext`, `Classical.choice`, `Quot.sound`) only.
- `verification/` — Complete build and audit logs (`lake-build.log`, `lean-axioms.log`, `lean-version.log`, `pdf-build.log`, `python-verify.log`, `SELF_REVIEW.md`).
