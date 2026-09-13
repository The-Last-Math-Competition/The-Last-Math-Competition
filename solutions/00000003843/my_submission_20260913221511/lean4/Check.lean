import Main

/-! Verification entry point: prints every computed quantity and, crucially,
`#print axioms` for every theorem.  Each theorem must report
"'...' does not depend on any axioms". -/

-- Structure of H_3(0): six elements, associative, with identity and absorption.
#eval Tlmc3843.hSize
#eval Tlmc3843.assocHolds
#eval Tlmc3843.identityHolds
#eval Tlmc3843.absorptionHolds

-- Green's relations: number of two-sided (J) and left (L) classes.
#eval Tlmc3843.jClasses
#eval Tlmc3843.lClasses

-- The characteristic vectors of the six principal two-sided ideals.
#eval Tlmc3843.allIdx.map Tlmc3843.jVec

-- Partitions of 3 and the hook-length bookkeeping.
#eval Tlmc3843.partitionsOf 3
#eval Tlmc3843.pCount 3
#eval Tlmc3843.hooksOf [3]
#eval Tlmc3843.hooksOf [2, 1]
#eval Tlmc3843.hooksOf [1, 1, 1]
#eval Tlmc3843.sumDistinctHooks 3

-- Every theorem is axiom-free (in particular: no `sorryAx`, no `Classical.choice`).
#print axioms Tlmc3843.hSize_eq
#print axioms Tlmc3843.assoc_ok
#print axioms Tlmc3843.identity_ok
#print axioms Tlmc3843.absorption_ok
#print axioms Tlmc3843.jClasses_eq
#print axioms Tlmc3843.lClasses_eq
#print axioms Tlmc3843.pCount3_eq
#print axioms Tlmc3843.sumHooks3_eq
#print axioms Tlmc3843.refutation_part_one
#print axioms Tlmc3843.refutation_part_two
#print axioms Tlmc3843.summary
