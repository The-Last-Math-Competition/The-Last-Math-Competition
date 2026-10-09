# Conjecture 00000004316: no universal local-density product one half

The source's existence-density interpretation is refuted by the nondegenerate integral quadratic form Q(x,y)=xy. Every target modulo every positive q is represented by (a,1), so the actual represented-target fraction is q/q=1, every local density exists and is 1, and the prime product is 1, not 1/2. The original x^2+y^2=3 counterexample is retained separately for fixed-target representation density, where the factor at 2 is zero.

## Scope

The two meanings of local density are kept separate: the fraction of represented right-hand sides, and the normalized number of pairs representing one fixed target. The source names no particular form or target, assumes neither positive definiteness nor local solubility, and explicitly uses existence-density wording in Chinese. The primary xy form is indefinite but nondegenerate, with actual polar determinant -1. A statement with additional positivity, solvability, or normalization requirements is not claimed to be refuted. The convergence-rate clause is not needed.

## Formal correspondence

A single Main.lean and one library contain both arguments. The new ExistenceDensity namespace defines a genuine Mathlib QuadraticForm xy, proves its actual polar determinant is -1 and its polar kernel is trivial, connects form evaluation with the modular expression, and counts an actual finite existential target set. The target count is q, hence the genuine local limits and all prime-filtered finite products are 1. The proof constructs the existing local-factor family and excludes any such family with product limit 1/2. The retained original namespace uses the actual quadratic form x^2+y^2, a fixed-target solution subtype, its modulo-4 obstruction, the local limit zero at 2, and the eventual-zero prime product.

## Files and reproduction

- `main.tex` and `main.pdf`: the full two-part disproof and Lean correspondence.
- `SOURCE.md`: unchanged bilingual source, with exact upstream and hash provenance under `verification/`.
- `lean/`: portable Lean 4.19.0 project with Mathlib pinned to c44e0c8ee63ca166450922a373c7409c5d26b00b and public Git dependencies.
- `verification/`: fresh-build evidence, theorem axioms, compiler results, PDF inspection, development history, and reviews.

In `lean/`, run `lake build`, then `lake env lean -DwarningAsError=true Main.lean`. A new machine can fetch pinned official dependency artifacts with `lake exe cache get`. Run `tectonic main.tex` from the submission directory to export the PDF. No supplementary numerical program is needed.

The first development agent contributed the fixed-target proof and its self-review. A second development agent added the main existence-density argument after the parent identified the source ambiguity. Original review and build metadata remain as explicitly historical records; current validation is in `BUILD.json`. The parent reviews the combined final submission. No external independent review is claimed.
