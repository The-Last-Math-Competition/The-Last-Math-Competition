/-
  Axiom / statement audit for the 00000007121 submission.

  Confirms that the formalised results exist and that their proofs depend on
  no `sorryAx` (and no custom axioms). `#print axioms` must report only the
  standard core axioms of Lean (or nothing at all), and never `sorryAx`.
-/
import Main

namespace Hirsch7121

#check conjunction_is_contradictory
#check counterexample_refutes_bound
#check hirsch_as_written_false
#check conjecture_00000007121_false

#print axioms conjunction_is_contradictory
#print axioms counterexample_refutes_bound
#print axioms hirsch_as_written_false
#print axioms conjecture_00000007121_false

end Hirsch7121
