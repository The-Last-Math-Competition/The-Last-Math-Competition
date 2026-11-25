# Conjecture 00000007176 — Resolution Package

**Verdict:** **False in general** (across both the degree-power bound claim and the binomial-realization claim under every standard tensor eigenvalue definition and normalization, while admitting sharp dimension-power and norm-dependent bounds with complete algebraic rigidity classifications).

## Problem Statement

See [`SOURCE.md`](SOURCE.md) for the exact original English and Chinese statements (*The extrema of tensor eigenvalues with higher-order spectra / 张量特征值的极值：高阶谱*).

For real or complex symmetric tensors $\mathcal{A} = \bigl(a_{i_1 \dots i_m}\bigr)$ of order (degree) $m \ge 3$ on $\mathbb{R}^n$ or $\mathbb{C}^n$ ($n \ge 2$), the conjecture asserts two linked claims:
1. **Degree-power modulus bound:** the modulus upper bound of the spectrum of $\mathcal{A}$ is a power of the degree $m$ (such as $m^m$ or $m^{m-1}$).
2. **Binomial-type realization (rigidity):** equality in the spectral modulus bound is realized by tensors of binomial type.

## Mathematical Resolution Summary

### 1. Sharp Positive Theorems & Complete Spectral Rigidity (Exact True Bounds)
- **Qi's Entrywise $H$-Eigenvalue Bound & Complete Complex/Real Rigidity (`entrywise_H_bound_complex`, `entrywise_H_bound_real`, `entrywise_H_rigidity_complex`, `entrywise_H_rigidity_nonneg`, `entrywise_H_rigidity_odd_real`, `entrywise_H_rigidity_even_real`):**
  - Over $|a_{i_1 \dots i_m}| \le 1$, every complex or real $H$-eigenvalue ($\mathcal{A} x^{m-1} = \lambda x^{[m-1]}$, $x \ne 0$) satisfies $|\lambda_H| \le n^{m-1}$ — an exponential in $m - 1$ whose base is the **dimension $n$**, attained by the constant all-ones tensor $\mathcal{J}_{m,n}$ ($a_{i_1 \dots i_m} = 1$).
  - **Complete Rigidity:** Over $[0, 1]$-valued symmetric tensors, $|\lambda_H| = n^{m-1}$ is **uniquely** realized by $\mathcal{J}_{m,n}$ (whose homogeneous polynomial $F_{\mathcal{J}_{m,n}}(x) = \bigl(x_1 + \dots + x_n\bigr)^m = \sum_{|\alpha|=m} \binom{m}{\alpha} x^\alpha$ reduces to a binomial expansion only when $n = 2$, and only via orbit multiplicities rather than tensor entries). Over $[-1, 1]$-valued real symmetric tensors, equality holds iff $\mathcal{A} = \pm \mathcal{J}_{m,n}$ when $m$ is odd, and iff $\mathcal{A} = \pm s^{\otimes m}$ ($s \in \lbrace -1, +1 \rbrace^n$) when $m$ is even; over $\mathbb{C}$, iff $\mathcal{A} = \zeta \bigl(\overline{\omega}\bigr)^{\otimes m}$ with $|\zeta| = 1$ and $\omega_j^m = 1$.
- **Sharp Entrywise $Z$-Eigenvalue Bound (`entrywise_Z_bound`, `allOnes_attains_Z_bound_rat`):** Over $|a_{i_1 \dots i_m}| \le 1$, every real $Z$-eigenvalue ($\mathcal{A} x^{m-1} = \lambda x$, $\|x\|_2 = 1$) satisfies $|\lambda_Z| \le n^{m/2}$, sharply attained by $\mathcal{J}_{m,n}$ at $x = \frac{1}{\sqrt{n}}\mathbf{1}$ (rationally whenever $n = k^2$).
- **Banach's Frobenius $Z$-Bound & Rank-$1$ Rigidity (`frob_Z_bound`, `frob_Z_rigidity`, `monomial_attains_frob_Z_bound`):** Under $\|\mathcal{A}\|_F \le 1$, every $Z$-eigenvalue satisfies $|\lambda_Z| \le 1$, with equality iff $\mathcal{A} = \pm u^{\otimes m}$ ($\|u\|_2 = 1$).
- **Sharp Frobenius $H$-Bound via Polynomial Muirhead Inequality (`powSum_two_m_le`, `frob_H_bound`, `allOnes_attains_frob_H_bound`):** Under $\|\mathcal{A}\|_F \le 1$ ($m \ge 2$), every real $H$-eigenvalue satisfies $|\lambda_H| \le n^{(m-2)/2}$, sharply attained by $n^{-m/2}\mathcal{J}_{m,n}$.
- **Vandermonde Exact Spectrum of the Binomial-Entry Tensor (`binomialEntry_exact_H_radius`):** The binary symmetric tensor $\mathcal{B}_{m,2}$ with entries $a_{i_1 \dots i_m} = \binom{m}{\#\{r : i_r = 2\}}$ has exact $H$-spectral radius $\binom{2m-1}{m-1}$.

### 2. Five Decisive Counterexample Families (Refuting the Conjecture)
1. **Unboundedness Without Normalization (`refutation_unnormalized_unbounded`):** Scaling $\mathcal{A} \mapsto c \mathcal{A}$ scales all $H$-, $Z$-, and $E$-eigenvalues by $c$, so no finite degree-power bound exists without norm/entry constraints.
2. **Entrywise-Bounded Spectra Exceed Every Function of Degree Alone (`refutation_entrywise_H_exceeds_any_degree_bound`, `refutation_entrywise_Z_exceeds_any_degree_bound`, `refutation_J34_H_exceeds_deg_sq`, `refutation_J36_H_exceeds_deg_cube`, `refutation_J32_H_not_deg_power`, `refutation_J3_16_Z_exceeds_deg_cube`):**
   - For every fixed degree $m \ge 2$ and **any** proposed function $F(m)$ of the degree alone (including $m^m$, $m^{m-1}$, or $m^k$), $\mathcal{J}_{m,n}$ has $\lambda_H \gt F(m)$ for $n = F(m) + 2$ and $\lambda_Z \gt F(m)$ for $n = \bigl(F(m) + 2\bigr)^2$.
   - Explicitly at $m = 3$: $\lambda_H\bigl(\mathcal{J}_{3,4}\bigr) = 16 \gt 9 = 3^2$, $\lambda_H\bigl(\mathcal{J}_{3,6}\bigr) = 36 \gt 27 = 3^3$, and $\lambda_Z\bigl(\mathcal{J}_{3,16}\bigr) = 64 \gt 27 = 3^3$; meanwhile at $m = 3, n = 2$, the sharp bound is $4$, which equals $3^k$ for **no** $k \in \mathbb{N}$ and $4 \ne (3-1)^3 = 8$.
3. **Failure of Binomial-Type Realization (`refutation_two_var_binomial_suboptimal`, `refutation_binomial_entry_not_deg_power`, `refutation_binomial_entry_rescaled_suboptimal`, `refutation_even_order_sign_nonuniqueness`):**
   - In every dimension $n \ge 3$, the $2$-variable binomial form $\bigl(x_1 + x_2\bigr)^m$ achieves $|\lambda_H| \le 2^{m-1} \lt n^{m-1} = \lambda_H\bigl(\mathcal{J}_{m,n}\bigr)$.
   - For the binomial-entry tensor $\mathcal{B}_{m,2}$, its unnormalized radius $\binom{2m-1}{m-1}$ ($10, 35, 126, \dots$) is never a power of $m$, and for **every** $m \ge 2$ and **every** rescaling $c \ge 0$ with $|c \, a_\alpha| \le 1$, $|\lambda_H\bigl(c \mathcal{B}_{m,2}\bigr)| \lt 2^{m-1}$.
   - At even order $m = 4, n = 2$, the alternating tensor $\bigl(x_1 - x_2\bigr)^4$ attains $\lambda_H = 8 = 2^{4-1}$ while $\ne \pm \mathcal{J}_{4,2}$.
4. **Frobenius and $\ell_1$ Normalizations (`refutation_frob_Z_bound_lt_deg_pow`, `refutation_frob_H_exceeds_any_degree_bound`, `refutation_l1_binomial_suboptimal`):**
   - Under $\|\mathcal{A}\|_F \le 1$ ($m \ge 3$), $\max |\lambda_Z| = 1 \lt m^k$ ($\forall k \ge 1$, realized by monomial $e_1^{\otimes m}$), while $\max |\lambda_H| = n^{(m-2)/2} \to \infty$ as $n \to \infty$. Under $\|\mathcal{A}\|_1 = 1$, $2^{-m}\mathcal{J}_{m,2}$ achieves $\frac{1}{2} \lt 1 = \lambda_H\bigl(e_1^{\otimes m}\bigr)$.
5. **Unboundedness of Complex $E$-Eigenvalues (`refutation_complex_E_eigenvalue_unbounded`):**
   - Explicit rational $2 \times 2 \times 2$ real symmetric tensors $\mathcal{A}^{(t)}$ satisfying **both** $\|\mathcal{A}^{(t)}\|_\infty = \frac{1}{2} \le 1$ and $\|\mathcal{A}^{(t)}\|_F^2 \lt \frac{7}{16} \lt 1$ possess complex $E$-eigenpairs ($z_1^2 + z_2^2 = 1$ in $\mathbb{Q}[i]$) with $\lambda_E^{(t)} \gt \frac{t}{6} \to +\infty$.

## Package Layout & Reproduction

- [`SOURCE.md`](SOURCE.md) — Exact original conjecture statement (unmodified).
- [`main.tex`](main.tex) / [`main.pdf`](main.pdf) — Complete mathematical paper with proofs and Lean cross-reference tables.
- [`verify.py`](verify.py) — Standalone Python 3.12 verification suite (zero external packages).
- [`lean/`](lean/) — Zero-dependency Core Lean 4.19.0 formalization (`moreLeanArgs = ["-DwarningAsError=true"]`, zero `sorry`, zero custom axioms):
  - [`lean/Conjecture00000007176/Algebra.lean`](lean/Conjecture00000007176/Algebra.lean) — Self-contained `CommRing`, `IntegralDomain`, `OrderedDomain`, `ComplexOver R`, Pascal/Vandermonde combinatorics, and concrete `Int` & `RatField` (`ℚ`) instances.
  - [`lean/Conjecture00000007176/SumsInequalities.lean`](lean/Conjecture00000007176/SumsInequalities.lean) — Finite summation, real & complex Lagrange identities, Cauchy–Schwarz equality rigidity, and polynomial Muirhead inequality.
  - [`lean/Conjecture00000007176/SymmetricTensor.lean`](lean/Conjecture00000007176/SymmetricTensor.lean) — Multi-indices `Idx n m`, coordinate permutations `PermIdx`, `IsSymmetric`, contractions, standard extremal tensors, and Qi/Lim eigenpair predicates.
  - [`lean/Conjecture00000007176/PositiveBounds.lean`](lean/Conjecture00000007176/PositiveBounds.lean) — Qi's entrywise $H$- and $Z$-bounds, complete complex/real rigidity theorems, Banach's Frobenius $Z$-bound, sharp Frobenius $H$-bound, and Vandermonde radius of $\mathcal{B}_{m,2}$.
  - [`lean/Conjecture00000007176/Counterexamples.lean`](lean/Conjecture00000007176/Counterexamples.lean) — All five counterexample families and concrete `Int` / `RatField` non-vacuity instantiations.
- [`verification/`](verification/) — Build and audit logs (`lake-build.log`, `lean-axioms.log`, `lean-version.log`, `pdf-build.log`, `python-verify.log`, `SELF_REVIEW.md`).
