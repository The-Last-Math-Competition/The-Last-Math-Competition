# Disproof of Conjecture 00000006338

The cyclic difference set D={3,6,7,12,14} in Z/21Z has parameters (21,5,1). Its full multiplier group, allowing translations, is {1,2,4,8,16,11}, of order 6. This order divides none of v, k, or lambda, nor k-lambda=4 or v*k*lambda=105.

## Scope

The counterexample refutes the explicit parameter-divisibility conjunct using the standard (v,k,lambda) parameters of a nontrivial cyclic difference set. The developed symmetric 2-design is also verified. All additive automorphisms of the cyclic group are covered, and translations are allowed before proving that they must vanish. No resolution of the separate number-field-unit or fixed-point assertions is needed to disprove the conjunction.

## Formalization

Lean uses the actual ZMod 21 ring, ordered-difference counts, translated blocks, unit group and Subgroup. It verifies the (21,5,1) difference-set property, 21 distinct blocks of size 5, and unique block incidence for every distinct point pair. It classifies all translate-allowing multipliers, proves that the constructed subgroup is the full multiplier group, checks the correspondence with arbitrary additive automorphisms, and proves its cardinality is 6 and all stated divisibilities fail. Finite computations are kernel checked. The supplementary Python checker reproduces the counts without serving as a proof oracle.

## Reproduction

In `lean/`, run `lake exe cache get`, `lake build`, and
`lake env lean -DwarningAsError=true Main.lean`.
Lean 4.19.0 and Mathlib `c44e0c8ee63ca166450922a373c7409c5d26b00b`
are pinned in portable public-Git project metadata. Only verified official
dependency artifacts are reused; this project is freshly rebuilt.
Run `python verify.py` for the supplementary finite checks and
`tectonic main.tex` for the PDF.

`SOURCE.md` contains the exact bilingual conjecture. `verification/`
contains provenance, actual build and execution logs, hashes and review records.
The author performed a separate adversarial self-review; no independent
reviewer or subagent was used.
