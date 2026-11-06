# Conjecture 00000005207 — disproof

The noncommutative-minus-commutative rank gap is not multiplicative under tensor products.
Over Q, the 3×3 skew-symmetric matrix space S has (commutative rank, noncommutative rank) = (2, 3). The 1×1 scalar matrix space U has ranks (1, 1), and S tensor U is S entrywise. Consequently the tensor-product gap is 1, while the product of factor gaps is 1×0 = 0. Both factors and their product have size at most 3.

## Files

- `RankGap.lean`: complete formal development, importing only `Std`.
- `solution.tex`: mathematical proof, exact rank conventions, and formal-scope disclosure.
- `solution.pdf`: compiled three-page proof.
- `lakefile.lean`, `lean-toolchain`: standalone Lean 4.31.0 project, no third-party dependencies.

## Reproduce

With Lean 4.31.0 available on PATH:

```
lean -DwarningAsError=true RankGap.lean
lake build
lake env leanchecker RankGap
```

To rebuild the PDF on a normal TeX installation:

```
pdflatex -output-format=pdf -interaction=nonstopmode -halt-on-error solution.tex
pdflatex -output-format=pdf -interaction=nonstopmode -halt-on-error solution.tex
```

No software downloads or dependency fetches are required if Lean 4.31.0 and LaTeX are already installed.

## Theorem map

- `skew_determinant_zero`: the full 3×3 determinant vanishes for every rational scalar substitution.
- `skew_minor_two`: a scalar specialization has a 2×2 minor of determinant 1.
- `skew_blowup_determinant`: the displayed 6×6, d=2 block substitution has determinant 1.
- `skew_commutative_rank` and `skew_noncommutative_rank`: exact ranks 2 and 3, respectively.
- `unit_commutative_rank` and `unit_noncommutative_rank`: both scalar-space ranks are exactly 1.
- `tensor_unit`: the actual coefficient tensor product is entrywise equal to the skew pencil.
- `counterexample`: all six factor/product rank statements and the unequal gap values.
- `conjecture_00000005207_false`: negation of the precise multiplicativity law `MultiplicativeGap`.

All theorem names above belong to namespace `TLMC5207`.

## Definitions and formal scope

`det` is ordinary recursive Laplace expansion. `RankLE` and `RankGE` use the standard nonsingular-minor characterization over Q, selecting all strictly increasing row/column index lists. These definitions do not encode any rank values for the example.

`CommutativeRank` is maximum rank over all rational scalar evaluations. `NoncommutativeRank` is maximum normalized rank over tensor blowups. Exact rank means a universal upper bound together with an attaining nonsingular minor. The noncommutative upper bound quantifies over every positive blowup size and every rational block substitution; it is not a bounded search.

This is the standard equivalent tensor-blowup definition of noncommutative rank. The development does not construct free skew fields or formalize the general equivalence with free-skew-field rank. That correspondence is cited, not inserted as an axiom. Reference: Derksen–Makam, *On non-commutative rank and tensor rank*, Definitions 1.3, 1.5 and 1.9, Lemmas 1.4 and 1.8, https://arxiv.org/abs/1606.06701.

The claim refuted is the posted explicit multiplicativity clause, interpreted conventionally as gap(S tensor U) = gap(S)gap(U). No interpretation of the separate undefined phrase “multiplicative deficit” is required. The familiar skew-symmetric example itself is not claimed as a new mathematical construction.

## Verification

Lean 4.31.0, standard library only. Strict compilation passes with warnings treated as errors. The two final theorem axiom closures are exactly:

```
[propext, Classical.choice, Quot.sound]
```

No admitted proofs, custom axioms, `native_decide`, unsafe declarations, or kernel bypasses are used. The source contains ordinary theorem-producing `simp`, `grind`, `omega`, and `decide` proofs.

Official statement: https://github.com/The-Last-Math-Competition/The-Last-Math-Competition/blob/main/conjectures/00000005207.md

Source checked on 20 October 2026; Git blob SHA `74afbaf0aafcb8c077141a71b1232932418e3031`. Live metadata marked neither proven nor disproven, and an all-state PR search plus the complete 1,060-entry PR collection found no submission for this problem before preparation.
