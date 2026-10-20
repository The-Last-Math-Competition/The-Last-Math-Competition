# Conjecture 00000005613 — a subresultant coefficient-minor counterexample

The conjecture's individual-minor vanishing equivalence fails under the standard subresultant coefficient/principal convention. For f = X³−4X and g = X²−1, the first subresultant matrix is generated from rows f, Xg, g. Its coefficient minor M₃,₁ is zero, but its corresponding leading principal minor M₃,₀ is −3. The inputs are monic, squarefree, coprime and have strictly interlacing roots −2 < −1 < 0 < 1 < 2.

This concerns an **individual coefficient minor**, not the whole polynomial subresultant. The whole first subresultant equals −3X and is nonzero. We do not claim this example refutes an equivalence involving the vanishing of the whole polynomial, nor do we assign a meaning to the conjecture's other undefined spectral terminology.

## Files

- `Subresultant.lean`: complete formal development, importing only `Std`.
- `Audit.lean`: axiom audit for every named theorem in the development.
- `solution.tex`, `solution.pdf`: editable LaTeX and the three-page mathematical proof.
- `check_arithmetic.py`: separate exact-arithmetic checks, using Python's standard library.
- `lakefile.lean`, `lean-toolchain`: standalone Lean 4.31.0 project with no third-party dependencies.

## Reproduce

With Lean 4.31.0 on PATH:

```
lean -DwarningAsError=true Subresultant.lean
lake build
lake env lean -DwarningAsError=true Audit.lean
lake env leanchecker Subresultant
python3 check_arithmetic.py
```

No package installation or dependency download is needed if Lean 4.31.0 and Python 3 are already installed.

To rebuild the PDF on an installed TeX distribution:

```
pdflatex -output-format=pdf -interaction=nonstopmode -halt-on-error solution.tex
pdflatex -output-format=pdf -interaction=nonstopmode -halt-on-error solution.tex
```

## Exact construction and theorem map

`Polynomial` records ascending rational coefficients. `sylvesterSubmatrix p q i F G` generates the prescribed shifted coefficient rows in descending degree order. Its first q−i rows come from shifts of F and its next p−i rows from shifts of G. Thus for p=3,q=2,i=1 the actual rows are F, XG, G.

`det` is recursive Laplace expansion. `coefficientMinor A k t` selects the first k rows, first k−1 columns and column k+t, using one-based descriptive numbering. The principal case is t=0. `subresultantValue` assembles the coefficient minors in the standard order.

Important theorems, all in namespace `TLMC5613`:

- `input_degrees`: exact degrees three/two and monicity.
- `f_product_coefficients`, `g_product_coefficients`: finite coefficient-list products for the factorizations.
- `f_coefficient_list`, `g_coefficient_list`: exact links from those coefficient lists to the input polynomial functions.
- `f_factorization`, `g_factorization`, `f_roots`, `g_roots`: rational factorizations and exact rational root sets.
- `strict_interlacing`: explicit ordered roots and complete splitting identities, not merely a list of selected roots.
- `bezout_identity`, `bezout_coefficients`: the identity Xf+(3−X²)g=−3, both pointwise and coefficientwise.
- `generated_matrix`: the generated three-by-four matrix agrees entrywise with the displayed matrix.
- `principal_minor_value`, `constant_minor_value`: exact third-order determinant values −3 and 0.
- `first_subresultant_value`: the first subresultant is −3X.
- `counterexample`: the verified hypotheses and unequal vanishing behavior.
- `conjecture_00000005613_false`: negates the precise restricted clause `VanishingEquivalence`.

## Formal and interpretive boundaries

Lean checks rational coefficients, polynomial coefficient identities, rational roots and their strict order. It does not import or construct a type of real or complex numbers. The same coefficient identities transfer along the ordinary embeddings of Q into R and C, establishing the real-root and mathematical polynomial-coprimality statements in the written proof. That elementary transfer is explained mathematically, not claimed as separately formalized. In particular, `no_common_root` quantifies over Rat and is not a general formal polynomial-gcd theorem.

The printed statement leaves “spectrum,” “conversion,” and “corresponding” undefined. Our target uses the standard canonical coefficient/principal minor correspondence, not an arbitrary chosen principal minor. This convention is stated in Michael Kerber, *Geometric Algorithms for Algebraic Curves and Surfaces* (2009), Definitions 2.3.10–2.3.12, printed page 30:
https://www.geometrie.tugraz.at/kerber/kerber_papers/kerber_diss.pdf

## Verification

Strict Lean 4.31.0 compilation passes. Every theorem's axiom closure is contained in `[propext, Classical.choice, Quot.sound]`. There are no custom axioms, admitted proofs, `native_decide`, unsafe declarations, or kernel bypasses. The Python checks supplement rather than replace the formal proof.

Official statement:
https://github.com/The-Last-Math-Competition/The-Last-Math-Competition/blob/main/conjectures/00000005613.md

The live source was checked on 20 October 2026 (Git blob SHA `b659307baec1b29f28ba161e5afb27c468bd7301`). The metadata row marked neither proven nor disproven; the solution directory was absent; all-state short/full-number PR searches and a complete historical PR ID scan found no existing submission before preparation.
