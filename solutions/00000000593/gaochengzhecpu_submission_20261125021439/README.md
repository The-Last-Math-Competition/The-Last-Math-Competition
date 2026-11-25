# Conjecture 00000000593 — Resolution and Formal Verification

## Verdict: **TRUE**

For every field $k$ (both non-modular $\mathrm{char}(k) \nmid |G|$ and modular $\mathrm{char}(k) = p \mid |G|$), every integer $n \ge 1$, and every finite linear group $G \le \mathrm{GL}_n(k)$ acting on $R = k[x_1, \dots, x_n]$, let $a_m = \dim_k\bigl(R_m^G\bigr)$ ($m \ge 0$) and let
$$H(R^G, t) = \sum_{m=0}^{\infty} a_m t^m \in \mathbb{Z}[[t]]$$
denote the Molien / Hilbert–Poincaré series of the invariant ring $R^G = k[x_1, \dots, x_n]^G$.

1. **Rational Generating Series and Explicit Strict Divisibility Chain:**
   $H(R^G, t) \in \mathbb{Q}(t)$ is a rational function whose reduced denominator $Q(t) \in \mathbb{Z}[t]$ ($Q(0) = 1$) divides $\bigl(1 - t^{|G|}\bigr)^n$, and therefore divides the explicit length-$n$ strictly increasing divisibility chain
   $$\prod_{i=1}^{n} \bigl(1 - t^{d_i}\bigr), \qquad d_i = 2^{i-1} |G| \quad \bigl(d_1 \mid d_2 \mid \dots \mid d_n,\; 0 \lt d_1 \lt d_2 \lt \dots \lt d_n\bigr).$$
   In the non-modular regime ($\mathrm{char}(k) \nmid |G|$), $|G|$ sharpens further to the group exponent $e = \exp(G)$ via the matrix geometric-series identity $\det(I_n - t A) \det\bigl(\sum_{s=0}^{e-1} t^s A^s\bigr) = \bigl(1 - t^e\bigr)^n$, with strict numerator degree bound $\deg P_G \le n(e - 1) \lt n e$. Both this unconditional $n \times n$ matrix Molien theorem and the constructive Hilbert–Serre tower theorem are formally verified from first principles in core Lean 4.19.0.

2. **Modular Periodic Structure (Quasi-Polynomiality):**
   Having rational generating series $P(t) / \bigl(1 - t^D\bigr)^n$ with $\deg P \lt n D$ is bidirectionally equivalent to vanishing of the $n$-th modular difference $\Delta_D^n a_m = 0$ for all $m \ge 0$, and to exact Newton binomial quasi-polynomiality on each residue class $c \in \{0, \dots, D - 1\}$:
   $$a_{q D + c} = \sum_{j=0}^{n-1} \bigl(\Delta_D^j a\bigr)_c \binom{q}{j} \qquad (q \ge 0).$$

3. **Sharpness and Boundary Analysis of Alternative Readings:**
   - **Necessity of "dividing" vs. "equal to":** For Klein's binary icosahedral group $G = \mathrm{SL}_2(5) \le \mathrm{GL}_2(\mathbb{C})$ ($|G| = 120$), $H(\mathbb{C}[x,y]^G, t) = P_{\mathrm{ico}}(t) / Q_{\mathrm{ico}}(t)$ has coprime integer polynomials certified by $\bigl(1 + t^4 - t^{12}\bigr) P_{\mathrm{ico}}(t) + \bigl(-t^2 + t^{10}\bigr) Q_{\mathrm{ico}}(t) = 1$. While $Q_{\mathrm{ico}}(t) \mid \bigl(1 - t^{12}\bigr)\bigl(1 - t^{60}\bigr)$, $Q_{\mathrm{ico}}(t)$ is **not** equal to any product $\prod_{i=1}^r \bigl(1 - t^{d_i}\bigr)$ (since multiplicity at $t = 1$ forces $r = 2$ and $d_1 d_2 = 120$, whereas $\deg Q_{\mathrm{ico}} = 18$ forces $d_1 + d_2 = 18$ and $d_1 d_2 \le 81 \lt 120$).
   - **Necessity of $|G|$ over $\exp(G)$ in modular characteristic:** For $G = (\mathbb{F}_4, +) \cong C_2 \times C_2$ acting on $\mathbb{F}_4[x, y]$ ($\mathrm{char}(k) = 2 \mid |G| = 4$, $\exp(G) = 2$), $\mathbb{F}_4[x,y]^G = \mathbb{F}_4[x, y^4 + x^3 y]$ has reduced denominator $Q_{\mathrm{mod}}(t) = (1 - t)\bigl(1 - t^4\bigr)$, which does **not** divide $\bigl(1 - t^{\exp(G)}\bigr)^2 = \bigl(1 - t^2\bigr)^2$ but divides $\bigl(1 - t^{|G|}\bigr)^2 = \bigl(1 - t^4\bigr)^2 \mid \bigl(1 - t^4\bigr)\bigl(1 - t^8\bigr)$.
   - **Minimum chain length $r \ge n$:** Whenever $n \ge 2$, $\bigl(1 - t\bigr)^n$ never divides any product $\prod_{i=1}^r \bigl(1 - t^{d_i}\bigr)$ of length $r \lt n$ (in particular, never a single factor $1 - t^d$).
   - **Refutation of hyper-literal index-rationality:** Reading $m \mapsto a_m$ literally as a rational function in $\mathbb{Q}(m)$ of the index $m$ (contradicting both the variable $t$ in $1 - t^d$ and modular periodicity) fails already for $n = 1$, $G = \{\pm 1\}$ on $k[x]$ ($\mathrm{char}(k) \ne 2$), where $a_m = 1, 0, 1, 0, \dots$ vanishes at infinitely many odd indices while $a_0 = 1$.

---

## Package Contents

- `SOURCE.md` — Original bilingual problem statement (untouched).
- `main.tex` / `main.pdf` — Complete mathematical exposition and self-contained proofs.
- `verify.py` — Pure Python 3.12 computational verification suite (exact univariate polynomial arithmetic over $\mathbb{Q}$ and $\mathbb{Z}$, matrix Molien verification on $A_4 \le \mathrm{SO}_3(\mathbb{Q})$, exact finite-field invariant subspace RREF over $\mathbb{F}_2, \mathbb{F}_3, \mathbb{F}_4$, and sharpness checks).
- `lean/` — Core Lean 4.19.0 formalization (`zero` external dependencies, `-DwarningAsError=true`, `zero` `sorry` / `admit` / `native_decide` / custom `axiom`):
  - `Conjecture00000000593/PolySeries.lean` — Polynomial and formal power-series algebra over $\mathbb{Z}$, Cauchy action, evaluation homomorphisms, and denominator monotonicity.
  - `Conjecture00000000593/ChainDivisibility.lean` — Universal strict chain upgrading (`strictDivChain_upgrade`, `uniformPower_dvd_uniformStrictChain`) and graded Hilbert–Serre induction (`hilbert_serre_strict_chain`).
  - `Conjecture00000000593/ModularPeriodic.lean` — Bidirectional equivalence between denominator divisibility into $\bigl(1 - t^D\bigr)^n$, vanishing of $\Delta_D^n a$, and discrete Newton quasi-polynomials (`modular_periodic_iff`).
  - `Conjecture00000000593/Determinant.lean` — $n \times n$ matrices over general commutative rings `CRing`, Laplace determinant `det`, and full multiplicativity `det_mul` ($\det(A B) = \det A \cdot \det B$).
  - `Conjecture00000000593/MatrixMolien.lean` — Polynomial matrix geometric-series identity (`charPolyMat_mul_geomPolyMat`), determinant cofactor theorem (`charDet_mul_geomDet_eq_chainProd`), formal power-series inversion (`invUnitPoly`), and unconditional matrix-group Molien theorems (`matrix_molien_unconditional`, `matrix_group_molien_theorem`, `groupNegId2_molien_verified`).
  - `Conjecture00000000593/Sharpness.lean` — Pole-order bound (`chain_length_ge_vars`), Klein $\mathrm{SL}_2(5)$ non-equality theorem (`klein_not_equal_any_chain`), modular $\mathbb{F}_4$ exponent failure (`modular_F4_witness`), index-rationality refutation (`paritySeq_not_rational_in_index`), and non-vacuity witnesses (`sym3_nonvacuity_witness`, `bertin_modular_witness`).
  - `Conjecture00000000593.lean` — Master module (`conjecture_00000000593_master`).
- `verification/` — Complete build and verification logs (`lake-build.log`, `lean-axioms.log`, `lean-version.log`, `pdf-build.log`, `python-verify.log`, `SELF_REVIEW.md`).
