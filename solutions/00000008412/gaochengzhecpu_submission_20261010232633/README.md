# Disproof of Conjecture 00000008412

An explicit 13-element subset of (Z/3Z)^3 is a (27,13,6) difference set and is fixed by the coordinate cycle (a,b,c) -> (b,c,a). This is an additive automorphism but not multiplication by any integer. The ambient group has no even-order subgroup quotient and no index-two subgroup.

## Scope

This refutes the restriction in the second clause of the conjecture: nonnumerical multipliers already occur without an order-16 exception or its order-32 index-two extension, even in any subgroup quotient. The source does not separately define coexists; the paper states the exact group-theoretic exclusion and does not give that word a meaning involving unrelated groups. The other two clauses are not needed.

## Formalization

Lean checks the actual product group, all ordered difference counts, an actual additive automorphism with inverse, setwise preservation, and failure to equal any integer scalar map. The multiplier predicate allows translations. Lagrange divisibility excludes even-order sections for arbitrary subgroups and subgroup quotients, and excludes every index-two subgroup. All finite checks are kernel checked; verify.py independently reproduces the orbit-union discovery and enumeration.

## Reproduction

In `lean/`, run `lake exe cache get`, `lake build`, and
`lake env lean -DwarningAsError=true Main.lean`.
Lean 4.19.0 and Mathlib `c44e0c8ee63ca166450922a373c7409c5d26b00b`
are pinned in public-Git project metadata. Only verified official dependency
artifacts are reused; the submitted project is freshly rebuilt.
Run `python verify.py` for the exact supplementary discovery and checks;
it requires only the standard library. Run `tectonic main.tex` for the PDF.

`SOURCE.md` preserves the exact bilingual source. `verification/` contains
provenance, actual build logs, hashes and review records. The author performed
a separate adversarial self-review; no independent reviewer or subagent was used.
