# Self-Review Audit — Conjecture `00000007628`

## 1. Fidelity to `SOURCE.md` (Bilingual Verification)

- **Source untouched:** `SOURCE.md` is byte-identically preserved from the problem statement.
- **English & Chinese parity checked:**
  - *Definition:* Minimal ideals with the ideal dimension law of Clifford algebras (`极小理想：Clifford 代数的理想维数律`).
  - *Clause I:* The conversion constant is the ideal dimension law and the minimal-ideal dimension is exactly the spinor dimension (`换算常数为理想的维数律且极小理想维数恰为旋量维数`).
  - *Clause II:* The law is exact with test by semisimple decomposition (`律精确且精确的检验为半单分解`).
  - *Clause III:* The automorphism group of the ideal is the symplectic group (`理想的自同构群为辛群`).
- **All standard mathematical readings analyzed:**
  - Minimal **left** ideals vs. minimal **two-sided** ideals.
  - Nondegenerate vs. degenerate quadratic spaces $\bigl(V, Q\bigr)$.
  - Geometric/complexified spinor dimension $2^{\lfloor n/2 \rfloor}$ vs. algebraic simple-module spinor dimension $\dim_K S$.
  - Five distinct notions of ideal automorphism group:
    1. Left $\mathrm{Cl}$-module automorphisms $\mathrm{Aut}_{\mathrm{Cl}}(S)$,
    2. $K$-linear automorphisms $\mathrm{GL}_K(S)$,
    3. Non-unital $K$-algebra automorphisms $\mathrm{Aut}_{K\text{-alg}}(S)$ of a minimal left ideal,
    4. Unital $K$-algebra automorphisms $\mathrm{Aut}_{K\text{-alg}}(J)$ of a minimal two-sided ideal,
    5. Spinor bilinear pairing isometries $\mathrm{Aut}_K(S, \beta)$ for canonical reversion and Clifford conjugation.

## 2. Positive Non-Vacuity & Sharp Counterexamples

- **Positive Non-Vacuity Theorem (`conjecture_00000007628_positive_split_case`):** Verified over arbitrary fields $K$ with $\mathrm{char}(K) \neq 2$ that $\mathrm{Cl}_{1,1}(K) \cong M_2(K)$ decomposes semisimply into two minimal left ideals $S_1 \oplus S_2$ of exact spinor dimension $2 = 2^{2/2}$ (conversion constant $4/2 = 2$), and that Clifford conjugation induces an alternating spinor pairing $\omega$ with $\mathrm{Aut}_K(S_1, \omega) = \mathrm{Sp}_2(K)$.
- **Counterexamples (`conjecture_00000007628_complete_refutation`):**
  - Minimal two-sided ideal of $\mathrm{Cl}_{1,1}(K) \cong M_2(K)$ has $\dim_K = 4 \neq 2$.
  - Degenerate exterior algebra $\mathrm{Cl}(K^2, 0) = \Lambda(K^2)$ has non-trivial nilpotent radical $\Lambda^+(K^2)$, only $\{0, 1\}$ as idempotents, no left-ideal complement to $\Lambda^2(K^2)$, and unique minimal nonzero left ideal of $\dim_K = 1 \neq 2$.
  - Nondegenerate division Clifford algebra $\mathrm{Cl}_{0,2}(\mathbb{Q}) \cong \mathbb{H}_{\mathbb{Q}}$ has $\overline{q} q = \mathrm{normSq}(q) > 0$ ($q \neq 0$), forcing unique minimal nonzero left ideal dimension $4 \neq 2$.
  - Polymorphic group non-isomorphisms over arbitrary fields ($K, F$ with $\mathrm{char}(F) \neq 2$):
    - $\mathrm{Aut}_{\mathrm{Cl}}(S_1) \cong K^\times$ (abelian) $\not\cong \mathrm{Sp}_2(F)$ (non-abelian),
    - $\mathrm{GL}_2(K) \neq \mathrm{Sp}_2(K)$ ($\det = -1$ reflection; order $48 \neq 24$ over $\mathbb{F}_3$; odd dim $1$ on $\mathrm{Cl}_{1,0}(K)$ admits no nonzero alternating form),
    - $\mathrm{Aut}_{K\text{-alg}}(S_1) \cong \mathrm{Aff}_1(K)$ (metabelian) $\not\cong \mathrm{Sp}_2(F)$ (non-abelian derived subgroup),
    - $\mathrm{Aut}_{K\text{-alg}}(M_2(K))$ (trivial center) $\not\cong \mathrm{Sp}_2(F)$ (nontrivial center $\{\pm I_2\}$).
  - Canonical spinor forms: $\mathrm{Cl}_{2,0}(K)$ reversion form is symmetric Euclidean ($\mathrm{O}_2$, order $8 \neq 24$ over $\mathbb{F}_3$), and at $n = 8$ ($\mathrm{Cl}_{4,4}(K) \cong M_{16}(K)$), both reversion and Clifford conjugation fix $136 = \frac{16 \cdot 17}{2} \neq 120$ blades, yielding $\mathrm{O}_{16}$ rather than $\mathrm{Sp}_{16}$.

## 3. Formalization, Code, & Typography Hygiene Checklist

- [x] **Core Lean 4.19.0:** `leanprover/lean4:v4.19.0`, `moreLeanArgs = ["-DwarningAsError=true"]`, zero external dependencies.
- [x] **Zero Forbidden Lean Constructs:** Audited for zero `sorry`, `admit`, `native_decide`, and custom `axiom` declarations; `#print axioms` recorded in `verification/lean-axioms.log` (only standard Lean kernel axioms `propext`, `Classical.choice`, and `Quot.sound`, with computational theorems axiom-free).
- [x] **Standalone Python Verification (`verify.py`):** Uses only Python 3.12 standard library (`fractions.Fraction` and exact modular arithmetic), exits `0`, logged in `verification/python-verify.log`.
- [x] **PDF Build & Visual Inspection (`main.pdf`):** Compiled cleanly via `pdflatex` with `0` errors, `0` overfull boxes, `0` unresolved references, and visually inspected page-by-page.
- [x] **Package Cleanliness & GitHub Markdown Math:** `.lake/` and LaTeX auxiliary files removed; `README.md` and `pr_body.md` audited for zero `\operatorname`, `\bowtie`, `\coloneqq`, `\DeclareMathOperator`, `\newcommand`, raw `<`/`>` inside `$...$`/`$$...$$`, leading `$(` in inline math, or local machine paths.
