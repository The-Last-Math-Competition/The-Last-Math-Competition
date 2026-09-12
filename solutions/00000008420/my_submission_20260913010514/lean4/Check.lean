import Main

/-! Verification entry point: prints the Boolean witnesses and, crucially,
`#print axioms` for every theorem.  Each theorem must report
"'..._property' does not depend on any axioms". -/

-- The Boolean witnesses evaluate to `true`.
#eval Tlmc8420.stsBool
#eval Tlmc8420.resolvableBool
#eval Tlmc8420.translationInvariantBool
#eval Tlmc8420.transitiveBool

-- Sanity: the point/line counts.
#eval Tlmc8420.points.length
#eval Tlmc8420.lines.length

-- Every theorem is axiom-free (in particular: no `sorryAx`, no `Classical.choice`).
#print axioms Tlmc8420.sts_property
#print axioms Tlmc8420.resolvable
#print axioms Tlmc8420.translation_invariant
#print axioms Tlmc8420.transitive
#print axioms Tlmc8420.refute
