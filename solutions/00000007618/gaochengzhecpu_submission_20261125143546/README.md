# Resolution of Conjecture 00000007618

## Problem Statement

> **English.** Definition: The intersection-correction law of projective formulas. Conjecture: The sign-correction term spectrum is complete; the combination of the correction is the dimension sum of subspaces; and the combination of the dimension sum is the mod-two reduction. (dimension-summed intersection sign correction)
>
> **中文。** 定义：射影公式的交修正律。猜想：符号修正项谱完全；且修正的组合为子空间维数和；且子空间维数和的组合为模二约化。（交符号修正维数和组合）

## Verdict: **FALSE (Refuted)**

Conjecture `00000007618` is **false** in general across every standard algebraic realization of projective subspace intersection (the Grassmann--Cayley regressive or "meet" product $A \vee B$), while holding inside a well-characterized **even-ambient-dimension forward three-star regime** ($n = 2m$, most notably 3D Projective Geometric Algebra $\mathbb{P}^3 = \mathbb{P}\bigl(V^4\bigr)$ at $n = 4$) that explains its origin.

Let $V = R^n$ ($n \ge 1$) be a free module over a commutative ring $R$ with $1 \neq -1$, let $\mathbb{P}\bigl(V\bigr) = \mathbb{P}^{n-1}$ be the associated projective space, and represent subspaces $U, W \subseteq V$ of vector-space dimensions $r = \dim U$ and $s = \dim W$ ($0 \le r, s \le n$, projective dimensions $p = r - 1$ and $q = s - 1$, codimensions $c_U = n - r$ and $c_W = n - s$) via Plücker blades $A \in \Lambda^r V$ and $B \in \Lambda^s V$. For $r + s \ge n$ ($k = r + s - n \ge 0$), the canonical Grassmann--Cayley regressive product is uniquely defined by Poincaré--Plücker duality

$$
\star\bigl(A \vee B\bigr) = \bigl(\star A\bigr) \wedge \bigl(\star B\bigr), \qquad A \vee B = \star^{-1}\bigl(\bigl(\star A\bigr) \wedge \bigl(\star B\bigr)\bigr).
$$

---

## Main Mathematical Results

### 1. Universal Dimension-Sum Parity Equivalence and Meet Duality Invariance

- **Universal Parity Equivalence of Subspace Dimension Sums (`dimension_sum_parity_equivalence`):** For all $1 \le r, s \le n$, vector-space dimension sum, projective flat dimension sum, and codimension sum have identical mod-two reduction:

$$
\bigl(r - 1\bigr) + \bigl(s - 1\bigr) \equiv \bigl(n - r\bigr) + \bigl(n - s\bigr) \equiv r + s \pmod{2}, \qquad \bigl(-1\bigr)^{(r-1)+(s-1)} = \bigl(-1\bigr)^{(n-r)+(n-s)} = \bigl(-1\bigr)^{r+s}.
$$

- **Left--Right Poincaré Duality Invariance (`vee_eq_leftStar_meet`):** Right-star duality $\star^{-1}\bigl(\bigl(\star A\bigr) \wedge \bigl(\star B\bigr)\bigr)$, left-star duality $\star_{\mathrm{L}}^{-1}\bigl(\bigl(\star_{\mathrm{L}} A\bigr) \wedge \bigl(\star_{\mathrm{L}} B\bigr)\bigr)$, and the Peano--Barnabei--Brini--Rota first-split shuffle formula agree identically with sign $+1$ across all dimensions $n$ and all grades $r, s$.

### 2. Exact Parity Dichotomy for the Forward Three-Star Formula (Origin & Refutation 1)

Writing the intersection using three forward star applications without $\star^{-1}$,

$$
A \vee B = \varepsilon_{\mathrm{dual}}\bigl(n, r, s\bigr)\,\star\bigl(\bigl(\star A\bigr) \wedge \bigl(\star B\bigr)\bigr),
$$

the exact sign factor is the double-star sign on grade $k = r + s - n$, which reduces modulo $2$ via $k^2 \equiv k \pmod{2}$ and $n\bigl(n - 1\bigr) \equiv 0 \pmod{2}$ (`intersection_double_star_mod_two`, `vee_eq_dimSum_factor_veeForward3Star`):

$$
\varepsilon_{\mathrm{dual}}\bigl(n, r, s\bigr) = \bigl(-1\bigr)^{k(n-k)} = \bigl(-1\bigr)^{(r+s)(n-1)}.
$$

- **Positive Even-Dimension Regime (`even_dim_forward3Star_regime`, `p3_proper_forward3Star_complete_and_valid`):** When $n = 2m$ ($m \ge 1$, i.e., odd-dimensional projective spaces $\mathbb{P}^{2m-1}$, notably 3D projective space $\mathbb{P}^3$ at $n = 4$), $2m - 1$ is odd so $\varepsilon_{\mathrm{dual}}\bigl(2m, r, s\bigr) = \bigl(-1\bigr)^{r+s}$ holds universally with complete spectrum $\{+1, -1\}$ (including strictly on proper nonempty flats $1 \le r, s \le 2m - 1$ for all $m \ge 2$). At $n = 2$ ($\mathbb{P}^1$), restricting to proper flats $1 \le r, s \le 1$ collapses the spectrum to $\{+1\}$ (`p1_proper_forward3Star_incomplete`).
- **Universal Odd-Dimension Collapse and Infinite Proper-Flat Refutation (`odd_dim_forward3Star_collapses_to_one`, `odd_dim_proper_point_hyperplane_refutation`, `p4_positive_meet_proper_refutation`):** In **every odd ambient dimension $n = 2m + 1$** (every even-dimensional projective space $\mathbb{P}^{2m}$, including the classical projective plane $\mathbb{P}^2$ at $n = 3$ and $\mathbb{P}^4$ at $n = 5$), $\bigl(2m + 1\bigr) - 1 = 2m$ is even, so $\varepsilon_{\mathrm{dual}}\bigl(2m + 1, r, s\bigr) = +1$ identically:
  1. **Clause 1 fails:** The sign-correction spectrum is $\{+1\} \subsetneq \{+1, -1\}$ (`-1` never occurs).
  2. **Clauses 2 & 3 fail on proper nonempty flats in every $\mathbb{P}^{2m}$ ($n = 2m + 3 \ge 3$):** For the proper point $A_m = e_{2m+2} \in \Lambda^1\bigl(\mathbb{Z}^{2m+3}\bigr)$ ($r = 1$) and proper hyperplane $B_m = e_0 \wedge \dots \wedge e_{2m+1} \in \Lambda^{2m+2}\bigl(\mathbb{Z}^{2m+3}\bigr)$ ($s = 2m + 2$), $A_m \vee B_m = 1 \neq 0$ forces the unique sign $+1$, whereas all three dimension sums ($r + s = 2m + 3$, projective sum $2m + 1$, codimension sum $2m + 3$) are odd and predict $-1 \neq +1$. At $m = 0$ ($n = 3$), this is a point and a line in $\mathbb{P}^2$. In $\mathbb{P}^4$ ($n = 5$), a proper plane ($r = 3$) and hyperplane ($s = 4$) meeting in a line ($k = 2 \ge 1$) likewise force $+1 \neq -1 = \bigl(-1\bigr)^{3+4}$.
- **4D Minkowski Signature Obstruction (`minkowski_cl31_double_star_refuted`):** Even at $n = 4$, replacing $\star$ by the Lorentzian Hodge star $\star_{3,1}$ on $\mathbb{R}^{3,1}$ flips every double-star sign by $\det G = -1$ (`cliffordRightStar_double`), giving $-\bigl(-1\bigr)^{r+s}$ (`-1 != +1` at $r = s = 2$).

### 3. Universal Refutations of All Remaining Canonical Conventions (`L2`–`L7`)

1. **Graded Commutation Law (`vee_graded_comm`, `commutation_proper_hyperplanes_refute_all_n_ge_2`, `commutation_not_fn_of_dim_sum_p3`):**
   - Satisfies $B \vee A = \bigl(-1\bigr)^{(n-r)(n-s)}\bigl(A \vee B\bigr)$ (governed by the **product of codimensions**, not the dimension sum).
   - Refuted in **every** dimension $n \ge 2$ by two proper coordinate hyperplanes $H_1, H_2 \in \Lambda^{n-1}\bigl(\mathbb{Z}^n\bigr)$ ($r = s = n - 1$), which satisfy $H_1 \vee H_2 \neq 0$ and $H_2 \vee H_1 = -\bigl(H_1 \vee H_2\bigr)$ (unique sign $-1$) while $r + s = 2n - 2$ is even ($+1 \neq -1$), and in the opposite direction by $\omega_n \vee H_1 = H_1 \vee \omega_n = H_1$ (unique sign $+1$ while $2n - 1$ is odd).
   - **Fails Clause 2 alone in $\mathbb{P}^3$ ($n = 4$):** Proper pairs $\bigl(2, 2\bigr)$ and $\bigl(1, 3\bigr)$ share the identical dimension sum $r + s = 4$, yet yield $+1$ vs. $-1$ on nonzero meets, so **no function $f\bigl(r + s\bigr)$ whatsoever** can govern commutation.
2. **Interior Contractions, Barnabei--Brini--Rota Second Split, and Unreverted Clifford Meet (`cartan_contraction_refuted`, `dorst_contraction_refuted`, `unreverted_clifford_refuted`):**
   - Cartan interior contraction $\iota_{\star A}\bigl(B\bigr) = \bigl(-1\bigr)^{k(n-r)}\bigl(A \vee B\bigr)$, second shuffle split $\bigl(-1\bigr)^{k(n-s)}\bigl(A \vee B\bigr)$, Dorst contraction $\bigl(\star A\bigr) \rfloor B = \bigl(-1\bigr)^{k(n-r) + \binom{n-r}{2}}\bigl(A \vee B\bigr)$, and unreverted Clifford meet $\bigl(\bigl(A\omega_n^{-1}\bigr)\wedge\bigl(B\omega_n^{-1}\bigr)\bigr)\omega_n = \bigl(-1\bigr)^{\binom{r}{2}+\binom{s}{2}+\binom{n-k}{2}+k(n-k)}\bigl(A \vee B\bigr)$ (period-4 reversion signs) **all** evaluate to $-1 \neq +1 = \bigl(-1\bigr)^{2+2}$ on two proper lines $e_0 \wedge e_1, e_1 \wedge e_2$ in $\mathbb{P}^2$ ($n = 3, r = s = 2$), and **all** fail Clause 2 alone on equal-sum proper flats in $\mathbb{P}^3$ ($n = 4$).

---

## Package Contents and Verification

- `SOURCE.md` — Unmodified bilingual competition problem statement.
- `main.tex`, `main.pdf` — Self-contained mathematical paper establishing the positive even-$n$ characterization and all multi-convention refutations.
- `verify.py` — Standalone Python 3 verification suite using exact rational arithmetic (`fractions.Fraction`) across $7$ metric signatures, $1{,}364$ blade pairs for canonical meet equivalence, and all $7$ sign-correction conventions.
- `lean/` — Zero-dependency Core Lean `v4.19.0` formalization (`-DwarningAsError=true`, zero `sorry`, zero custom axioms):
  - `Conjecture00000007618/Ring.lean` — `CRing` interface, `Int` instance, and modular parity theorems.
  - `Conjecture00000007618/ExteriorClifford.lean` — Constructive $2^n$-dimensional Clifford and exterior algebra `Cl R n` with `mul_assoc`, `invol_on_grade`, `rev_on_grade`, `wedge_hasGrade`, and `wedge_graded_comm`.
  - `Conjecture00000007618/ProjectiveMeet.lean` — Exterior Hodge star `IsHodgeStar`, Poincaré duality `poincare_wedge_nondeg`, arbitrary-metric double-star `cliffordRightStar_double`, exact inverse `pStarInv`, regressive meet `vee`, `vee_eq_leftStar_meet`, `vee_graded_comm`, `vee_eq_dimSum_factor_veeForward3Star`, and contraction dualities `cartanLeft_pStar_eq_sign_vee` & `dorstLeft_pStar_eq_sign_vee`.
  - `Conjecture00000007618/Main.lean` — Positive even-$n$ theorems, parameterized infinite proper-flat refutations, $\mathbb{P}^3$ Clause 2 impossibility proofs, Minkowski $\mathrm{Cl}_{3,1}$ refutation, and master bundled negation `conjecture_00000007618_false`.
- `verification/` — Complete build and verification logs (`lean-version.log`, `lake-build.log`, `lean-axioms.log`, `pdf-build.log`, `python-verify.log`, and `SELF_REVIEW.md`).
