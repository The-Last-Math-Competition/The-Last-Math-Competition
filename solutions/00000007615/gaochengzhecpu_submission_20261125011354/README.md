# Conjecture 00000007615 — Refutation and Exact Classification of the Hodge Double-Star Sign Law

## Verdict: **FALSE**

Conjecture `00000007615` (staged verbatim in `SOURCE.md` in both English and Chinese) asserts:

> **Definition:** The Hodge star as the duality-map structure.  
> **Conjecture:** (C1) The double-star sign is a power of minus one with exponent a dimension combination; (C2) the combination exponent is the product of codimensions; and (C3) the sign law gives the self-duality condition in middle dimension with condition codimension one. *(exact double-star sign law)*

We construct the exterior algebra $\Lambda^p\bigl(\mathbb{R}^{r,s}\bigr)$ ($n = r + s$) and the Hodge star operator $\star : \Lambda^p\bigl(\mathbb{R}^{r,s}\bigr) \to \Lambda^{n-p}\bigl(\mathbb{R}^{r,s}\bigr)$ from first principles via its defining duality relation $\alpha \wedge \star\beta = \langle \alpha, \beta \rangle\,\mathrm{vol}$, prove the **exact master double-star theorem**, and prove that the conjecture is **FALSE** across every natural reading of its clauses.

---

## Exact Mathematical Results

### 1. Master Double-Star Sign Law

On an oriented $n$-dimensional real inner-product space $\mathbb{R}^{r,s}$ of signature $\bigl(r, s\bigr)$ with $r + s = n$ ($r$ positive-definite directions and $s$ negative-definite directions), for every $0 \le p \le n$ and every $\omega \in \Lambda^p\bigl(\mathbb{R}^{r,s}\bigr)$,

$$\star\bigl(\star\omega\bigr) = \bigl(-1\bigr)^{p(n-p) + s}\,\omega.$$

In positive-definite Riemannian signature ($s = 0$), this specializes to $\star\bigl(\star\omega\bigr) = \bigl(-1\bigr)^{p(n-p)}\,\omega$.

### 2. Three Independent Failures of Conjecture `00000007615`

1. **Omission of the Metric Signature Index $s$ in Pseudo-Riemannian Geometry (Clauses C1–C2):**  
   Whenever the negative index of inertia $s$ is odd ($s \gt 0$), any exponent depending solely on $\bigl(n, p\bigr)$ fails:
   - On the Lorentzian plane $\mathbb{R}^{1,1}$ ($n = 2, r = 1, s = 1$) at degree $p = 0$, $\star 1 = e_0 \wedge e_1$ and $\star\bigl(e_0 \wedge e_1\bigr) = -1$, so $\star\bigl(\star 1\bigr) = -1 \neq +1 = \bigl(-1\bigr)^{0 \cdot (2 - 0)}$.
   - On $4$-dimensional Minkowski spacetime $\mathbb{R}^{3,1}$ ($n = 4, r = 3, s = 1$) at degree $p = 2$, $\star\bigl(\star(e_0 \wedge e_1)\bigr) = -\bigl(e_0 \wedge e_1\bigr) \neq +\bigl(e_0 \wedge e_1\bigr) = \bigl(-1\bigr)^{2(4-2)}\bigl(e_0 \wedge e_1\bigr)$.

2. **"Product of Codimensions" vs. Degree Times Codimension (Clause C2, even for $s = 0$):**  
   A $p$-form on an $n$-manifold has **degree** $p$ and **codimension** $n - p$. Even in Riemannian signature ($s = 0$), the literal product of codimensions $\bigl(n - p\bigr)^2$ disagrees with $p\bigl(n - p\bigr)$ whenever $n$ is odd and $p$ is even:
   - On Euclidean $\mathbb{R}^3$ ($n = 3, s = 0$) at degree $p = 0$, $\star\bigl(\star 1\bigr) = +1$, whereas $\bigl(-1\bigr)^{(3-0)^2} = \bigl(-1\bigr)^9 = -1 \neq +1$.

3. **Middle-Dimension Self-Duality "With Condition Codimension One" (Clause C3, under ALL readings):**  
   In even dimension $n = 2m$ ($m \ge 1$, $r + s = 2m$) at middle degree $p = m$, $\star^2 = \bigl(-1\bigr)^{m^2 + s}\,\mathrm{id}$ on $\Lambda^m\bigl(\mathbb{R}^{r,s}\bigr)$, and a non-zero self-dual form $\star\omega = \omega$ exists **if and only if $m^2 + s \equiv 0 \pmod{2}$** (equivalently $m \equiv s \pmod{2}$):
   - **Riemannian failure at codimension $1$ ($\mathbb{R}^2$, $n = 2, m = 1$):** Here $n - m = 1$, $\star e_0 = e_1$, $\star e_1 = -e_0$, and $\star^2 = -\mathrm{id}$, so $\Lambda^1_+\bigl(\mathbb{R}^2\bigr) = \{0\}$ (zero non-zero self-dual $1$-forms exist over $\mathbb{R}$, $\mathbb{C}$, or any scalar domain without $2$-torsion).
   - **Riemannian self-duality requires even $m \ge 2$ (codimension $\neq 1$):** Non-zero Riemannian self-dual $m$-forms exist iff $m = 2k$ ($n = 4k$). At the minimal positive instance $n = 4, m = 2$ (Euclidean $\mathbb{R}^4$, witnessed by the Yang–Mills self-dual $2$-form $\omega_{\mathrm{YM}} = e_0 \wedge e_1 + e_2 \wedge e_3$), the form codimension is $4 - 2 = 2 \neq 1$, and the linear-subspace codimension $\mathrm{codim}_{\Lambda^2}\bigl(\Lambda^2_+\bigr) = \binom{3}{2} = 3 \neq 1$. In fact, in Riemannian signature ($s = 0$), $\mathrm{codim}_{\Lambda^m}\bigl(\Lambda^m_+\bigr)$ **never** equals $1$ for any $m \ge 0$ (taking values $0, 2, 3, 20, 35, \dots$).
   - **Lorentzian signature ($s = 1$) does not rescue the conjecture:** Although $\mathbb{R}^{1,1}$ ($n = 2, m = 1$) admits the lightcone self-dual $1$-form $e_0 + e_1$, Clauses (C1)–(C2) fail on $\mathbb{R}^{1,1}$ itself (predicting $\bigl(-1\bigr)^{1 \cdot 1} = -1$ instead of $+1$), and Lorentzian self-duality holds for **all odd $m \ge 1$**—for instance on $\mathbb{R}^{5,1}$ ($n = 6, m = 3$), where $e_0 \wedge e_1 \wedge e_2 + e_3 \wedge e_4 \wedge e_5$ is non-zero and self-dual at form codimension $6 - 3 = 3 \neq 1$ and subspace codimension $\binom{5}{3} = 10 \neq 1$.

---

## Package Contents

| Path | Description |
| :--- | :--- |
| `SOURCE.md` | Original untouched bilingual problem statement for Conjecture `00000007615`. |
| `main.tex` / `main.pdf` | Publication-grade mathematical paper proving the exact classification and refuting all false clauses. |
| `verify.py` | Standalone exact integer and rational matrix verification suite (`0 <= n <= 8`, $4{,}097$ basis blades). |
| `lean/` | Core Lean `4.19.0` formalization (`HodgeDoubleStar`), zero external dependencies, `-DwarningAsError=true`. |
| `verification/` | Build, axiom-audit, version, PDF-compilation, and Python logs plus `SELF_REVIEW.md`. |

### Key Lean 4 Declarations (`lean/HodgeDoubleStar/`)

- `Basic.lean`: `invCount_eq_pairCount`, `invCount_add_invCount_comp`, `etaSign_mul_etaSign_comp`, `negIndex_sigOfRS`.
- `ExteriorHodge.lean`: `wedge`, `covector_wedge_anticomm`, `hodgeStar_wedge_duality`, `hodgeStar_unique`, `hodgeStar_hodgeStar`, `hodgeStar_hodgeStar_sigOfRS`, `hodgeStar_hodgeStar_riemannian`, `hodgeStarK_hodgeStarK`, `no_selfDualK_of_odd`.
- `ConjectureAnalysis.lean`: `exists_nonzero_selfDual_iff`, `riemannian_selfDual_iff_even`, `lorentzian_selfDual_iff_odd`, `sdDefect_sdSection`, `isSelfDual_iff_sdDefect_zero`, `selfDualSubspaceCodim_eq_one_iff`, `riemannian_selfDualSubspaceCodim_ne_one`, positive witnesses (`ymSelfDual2Form_selfDual`, `lor2SelfDual1Form_selfDual`, `lor6SelfDual3Form_selfDual`), clause refutations (`refute_sigFree_lor2_deg0`, `refute_sigFree_minkowski4_deg2`, `refute_codimProduct_riem3_deg0`, `refute_riemannian_codim1_selfDual`, `refute_lorentzian_exclusively_codim1`), and bundled negations (`not_Conjecture7615_LiteralRiemannian`, `not_Conjecture7615_CharitableRiemannian`, `not_Conjecture7615_PseudoRiemannian`).

---

## Reproducing Verification

1. **Lean 4 Formalization (`leanprover/lean4:v4.19.0`):**
   ```bash
   cd lean && lake build
   ```
2. **Exact Python Matrix Verification (Python 3.12, standard library only):**
   ```bash
   python3 verify.py
   ```
3. **LaTeX Manuscript (`pdflatex`):**
   ```bash
   pdflatex -interaction=nonstopmode -halt-on-error main.tex
   pdflatex -interaction=nonstopmode -halt-on-error main.tex
   ```
