# Solo adversarial review: 00000006338

Verdict: PASS for the mathematical argument and semantic scope. Final clean-build and PDF checks are recorded separately.

Main.lean SHA-256: `b0000b4e01c4076fb26dfe405df2f431a3a86d14ea1fdcc0da4beebda073a037`

1. The standard ordered-difference property is checked for every nonzero residue, not inferred from set size. The set is nontrivial and develops to a genuine symmetric 2-(21,5,1) design; its block counts and pair incidence are formally checked.
2. Multipliers are units and may translate the set. The proof checks all translations and only then concludes that the translation is zero. It does not confuse a setwise stabilizer with the full multiplier group.
3. The actual subgroup carrier is proved equivalent to the defining multiplier condition. The order is computed from this subgroup's cardinality. The additive-automorphism correspondence is proved from the image of 1, so non-numerical automorphisms are not silently omitted.
4. The residues coprime to 21 form H union -H, each of size 6. H fixes D while -H sends it to the different set -D. The centroid argument forcing translation zero is valid because 5 is a unit modulo 21.
5. The order 6 divides none of the standard parameters 21, 5, 1. It also fails to divide the derived order 4 and product 105. The proof targets this explicit necessary conjunct and does not invent a formula for the vague separate clauses.
6. Standard finite decision procedures produce kernel-checked proof terms. The supplemental Python checker does not enter the Lean proof. No independent review, external oracle, proof placeholder or custom axiom is claimed or used.

No independent reviewer or subagent was used.

## Final artifact verification

Actual fresh lake build, strict direct Lean check and supplementary Python calculation passed. Printed theorem dependencies contain only standard foundational axioms.

Main.tex SHA-256: `af960e7a4d248027d839b31e8c6c3052fc51669b610d331f02216ac5b6ad4711`

Main.pdf SHA-256: `449929f278dee5686a5a313760303f7a466cf1ff93f93879fbef679edbfa4eb1`

The author inspected all three final rendered pages: the ordered-difference table, subgroup computation, divisibility statements, formal correspondence, reproduction commands and references are readable. There are no clipped lines, overlaps or compiler warnings. Native editor compilation passed for the same TeX hash.
