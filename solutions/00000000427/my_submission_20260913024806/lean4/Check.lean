/-
  Certification check for the disproof of TLMC conjecture 00000000427.
  Run with:  lake env lean Check.lean
  Every `#print axioms` below must report "does not depend on any axioms";
  the project contains no `sorry` and no `axiom` declarations.
-/

import Main

#print axioms Tlmc0427.macMahon1
#print axioms Tlmc0427.symCount1
#print axioms Tlmc0427.formula1
#print axioms Tlmc0427.refute1
#print axioms Tlmc0427.allTuplesLen2
#print axioms Tlmc0427.macMahon2
#print axioms Tlmc0427.symCount2
#print axioms Tlmc0427.cycSymCount2
#print axioms Tlmc0427.formula2
#print axioms Tlmc0427.refute2
