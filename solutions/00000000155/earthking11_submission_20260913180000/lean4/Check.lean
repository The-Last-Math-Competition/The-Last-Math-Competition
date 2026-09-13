import Main

open Tlmc155

/-! Axiom audit.  Each of these should print no axioms (or at most `propext`),
and in particular must not contain `sorryAx` or `Lean.ofReduceBool`. -/

#print axioms bell_two
#print axioms bell_three
#print axioms bell_seven
#print axioms bell_thirteen
#print axioms prime_877
#print axioms prime_27644437
#print axioms conjecture_00000000155_false
