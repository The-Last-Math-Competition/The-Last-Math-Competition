# Conjecture 00000007605 — Disproof and Complete Structural Analysis

## Conjecture Statement (`SOURCE.md`)

- **English:** *Definition: Spinors with the spinor-representation classification of Pin groups. Conjecture: The conversion constant is the representation classification of spinors with the unique type of irreducible representations; the spectrum is finite with count two (real and complex); and the kernel of uniqueness is the Clifford center. (spinor unique-type conversion)*
- **Chinese:** *定义：旋量：Pin 群的旋量表示分类。猜想：换算常数为旋量的表示分类且不可约表示的唯一型；谱有限且谱的个数为二（实与复）；唯一性的核为 Clifford 中心。（旋量唯一型换算常数结构）*

---

## Final Verdict: **FALSE (Refuted)**

Conjecture `00000007605` is **false** under every standard mathematical formulation of $\mathrm{Pin}$ groups and spinor representations in Clifford-algebra and Lie-group representation theory (under both the geometric convention $v^2 = +Q(v)$ and the Atiyah–Bott–Shapiro convention $v^2 = -Q(v)$).

Because canonical Grassmann basis blades $e_I = e_{i_1}\cdots e_{i_k}$ belong to $\mathrm{Pin}^\pm(p,q) \subset \mathrm{Cl}_{p,q}^\pm(\mathbb{R})^\times$, the subgroup $\mathrm{Pin}^\pm(p,q)$ spans $\mathrm{Cl}_{p,q}^\pm(\mathbb{R})$ linearly over $\mathbb{R}$. Consequently, $\mathrm{Pin}$-invariance, $\mathrm{Pin}$-irreducibility, $\mathrm{Pin}$-module isomorphism, and the commutant division algebras $\mathrm{End}_{\mathrm{Pin}}(S) = \mathrm{End}_{\mathrm{Cl}}(S)$ agree identically with those of real Clifford modules. Every one of the conjecture's three clauses fails:

1. **Refutation of Count-Two Spectrum ("real and complex") — Quaternionic Type $\mathbb{H}$ Gives Exact Count Three:**
   By Frobenius's theorem and Atiyah–Bott–Shapiro $\bmod\,8$ periodicity, the division-algebra spectrum $\mathrm{End}_{\mathrm{Pin}}(S)$ of irreducible real $\mathrm{Pin}$-spinor representations has exact cardinality **three** — $\{\mathbb{R}, \mathbb{C}, \mathbb{H}\}$ — never two. Specifically, Hamilton's non-commutative quaternion division algebra $\mathbb{H}$ (real dimension $4$, isomorphic neither to $\mathbb{R}$ nor to $\mathbb{C}$) already arises at signature $\bigl(0,2\bigr)$ under $v^2 = +Q(v)$ ($\mathrm{Cl}_{0,2}^+(\mathbb{R}) \cong \mathbb{H}$) and at Euclidean signature $\bigl(2,0\bigr)$ ($\mathrm{Pin}^-(2)$) under $v^2 = -Q(v)$ ($\mathrm{Cl}_{2,0}^-(\mathbb{R}) \cong \mathbb{H}$), where $\mathrm{End}_{\mathrm{Pin}}(\mathbb{H}) \cong \mathbb{H}$. By pigeonhole, no two-element family of algebras covers the spinor endomorphism types of $\mathrm{Pin}\bigl(0,0\bigr)$, $\mathrm{Pin}\bigl(0,1\bigr)$, and $\mathrm{Pin}\bigl(0,2\bigr)$ (nor of Euclidean $\mathrm{Pin}^-(0)$, $\mathrm{Pin}^-(1)$, and $\mathrm{Pin}^-(2)$). Equivalently, on irreducible complex spinor modules of compact $\mathrm{Pin}^\pm(n)$ ($n \le 2$), the Frobenius–Schur reality indicator takes all **three** values $\{+1, 0, -1\}$: $+1$ on $\mathrm{Pin}^+(2)$, $0$ on $\mathrm{Pin}^-(1)$, and $-1$ on $\mathrm{Pin}^-(2)$.

2. **Refutation of Unique Irreducible Spinor Type:**
   In split signatures $p - q \equiv 1, 5 \pmod{8}$ under $v^2 = +Q(v)$ (equivalently $q - p \equiv 3, 7 \pmod{8}$ under $v^2 = -Q(v)$), the Clifford algebra splits as $M_k(\mathbb{D}) \oplus M_k(\mathbb{D})$ and possesses **two** non-isomorphic irreducible $\mathrm{Pin}$-spinor representations $S_+ \not\cong S_-$. Minimal counterexamples are $\mathrm{Pin}^+(1,0)$ ($\mathrm{Cl}_{1,0}^+(\mathbb{R}) \cong \mathbb{R} \oplus \mathbb{R}$, with $1$-dimensional irreps $e_1 \mapsto +1$ and $e_1 \mapsto -1$) and compact Euclidean $\mathrm{Pin}^-(3)$ ($\mathrm{Cl}_{3,0}^-(\mathbb{R}) \cong \mathbb{H} \oplus \mathbb{H}$, which simultaneously violates both uniqueness and real/complex type).

3. **Refutation of "Kernel of Uniqueness Is the Clifford Center" & Finite Group Dual:**
   - For any central simple Clifford algebra such as $\mathrm{Cl}_{1,1}^+(\mathbb{R}) \cong M_2(\mathbb{R})$, the unique irreducible spinor representation $\rho$ on $\mathbb{R}^2$ is **faithful**: $\ker(\rho) = \{0\}$ whereas $Z(\mathrm{Cl}_{1,1}^+(\mathbb{R})) = \mathbb{R} \cdot I_2 \neq \{0\}$, and on the group $\mathrm{Pin}(1,1)$ we have $\ker(\rho|_{\mathrm{Pin}}) = \{+I_2\}$ whereas $-I_2 \in Z(\mathrm{Cl}_{1,1}^+(\mathbb{R})) \cap \mathrm{Pin}(1,1)$ acts non-trivially as $-I_2 \neq +I_2$. Moreover, in $\mathrm{Cl}_{0,1}^+(\mathbb{R}) \cong \mathbb{C}$, the irreducible real spinor module **is** unique despite $\dim_{\mathbb{R}} Z(\mathrm{Cl}_{0,1}^+(\mathbb{R})) = 2 \gt 1$.
   - If "spectrum" is instead read as the full irreducible group representation spectrum of $\mathrm{Pin}^\pm(p,q)$, then $\mathrm{Pin}(1,0) \cong C_2 \times C_2$ already has **$4$** non-isomorphic $1$-dimensional irreps, and $\mathrm{Pin}^-(2)$ admits an **infinite** sequence $\{\sigma_{2k}\}_{k \ge 1}$ of pairwise non-isomorphic $2$-dimensional irreducible representations.

4. **Positive Non-Vacuity & Salvage Theorem (Complexified Clifford Algebras $\mathbb{C}\mathrm{l}_n$):**
   Over quadratic/complex scalars $K = F(i)$ (when $F = \mathbb{R}$, $K = \mathbb{C}$), $\mathbb{C}\mathrm{l}_{2m} \cong M_{2^m}(\mathbb{C})$ has **$1$** unique irreducible spinor module of division-ring type $\mathbb{C}$ and center $\mathbb{C} \cdot 1$, whereas $\mathbb{C}\mathrm{l}_{2m+1} \cong M_{2^m}(\mathbb{C}) \oplus M_{2^m}(\mathbb{C})$ has **$2$** non-isomorphic $\mathrm{Pin}$ spinor modules $S_+, S_-$ separated by their central kernels inside $Z(\mathbb{C}\mathrm{l}_{2m+1}) \cong \mathbb{C} \oplus \mathbb{C}$, whose restrictions to the even subalgebra $\mathbb{C}\mathrm{l}_{2m+1}^0$ ($\mathrm{Spin}(2m+1)$) become isomorphic.

---

## Package Structure & Verification Artifacts

- `SOURCE.md` — Original bilingual problem statement (unmodified).
- `main.tex` / `main.pdf` — Complete mathematical paper proving the Pin–Clifford span theorem, all refutations across conventions, and the complexified Clifford salvage theorem.
- `verify.py` — Standalone Python 3.12 symbolic verification script using exact `fractions.Fraction` linear algebra (verifying all $30$ Clifford algebras with $p + q \le 4$ under both $\pm Q$ conventions, exact centers, Bott $\bmod\,8$ periodicity, $\mathrm{End}_{\mathrm{Pin}}(S_{\mathbb{H}}) \cong \mathbb{H}$, Frobenius–Schur indicators, $40$ distinct $\mathrm{Pin}^-(2)$ harmonic traces via $\bigl(3+4i\bigr)^N \equiv 3+4i \pmod{5}$, and $\mathbb{C}\mathrm{l}_2/\mathbb{C}\mathrm{l}_3$ spinors).
- `lean/` — Core Lean `v4.19.0` formalization (`moreLeanArgs = ["-DwarningAsError=true"]`, zero external dependencies, zero `sorry`/`admit`/`native_decide`, zero custom axioms):
  - `Conjecture00000007605/FieldAndAlgebras.lean` — `FormallyRealField F`, reflective `Bool` polynomial normalizer `RExpr`, constructive rational witness `QField`, division algebras `realAlg F`, `ComplexOver F`, `QuatOver F`, and `three_division_types_pairwise_noniso`.
  - `Conjecture00000007605/ModulesAndPin.lean` — Textbook `Subspace`/`Irreducible` definitions, `InPin` unit-vector subgroup, two-sided inverse closure `inPin_inv_mem`, and Pin–Clifford span equivalence (`pinIrreducible_iff_irreducible`, `pinIso_iff_repIso`, `pinEndAlgIsoEndAlg`).
  - `Conjecture00000007605/RealCliffordCounterexamples.lean` — Universal properties and complete counterexample theorems for $\mathrm{Cl}_{0,0}$, $\mathrm{Cl}_{1,0}^+$, $\mathrm{Cl}_{0,1}^+$, $\mathrm{Cl}_{0,2}^+ = \mathrm{Cl}_{2,0}^- \cong \mathbb{H}$, and $\mathrm{Cl}_{1,1}^+ \cong M_2(F)$ (`quat_spinor_endAlg_neither_real_nor_complex`, `no_two_types_cover_pin_spinor_endAlgs`, `classify_pin10_irreducible`, `center_vs_kernel_cl11`).
  - `Conjecture00000007605/InfinitePinSpectrumAndComplexSalvage.lean` — Four irreps of $\mathrm{Pin}(1,0)$, infinite pairwise non-isomorphic harmonic irreps `pin2Minus_infinite_pairwise_noniso_irreps` of $\mathrm{Pin}^-(2,0)$, and `complex_clifford_non_vacuity`.
  - `Conjecture00000007605.lean` — Root master theorem `conjecture_00000007605_refuted` and ground witness `conjecture_00000007605_ground_witness`.
- `verification/` — Build and verification logs (`lake-build.log`, `lean-axioms.log`, `lean-version.log`, `pdf-build.log`, `python-verify.log`, `SELF_REVIEW.md`).
