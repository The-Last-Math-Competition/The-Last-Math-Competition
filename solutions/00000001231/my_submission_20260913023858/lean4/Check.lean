import Lean
import Main

/-! Verification harness: every theorem of `Main.lean` must be axiom-free. -/

#print axioms Tlmc1231.tau_K4
#print axioms Tlmc1231.f_odd
#print axioms Tlmc1231.prod_f4
#print axioms Tlmc1231.prod_f4_odd
#print axioms Tlmc1231.sixteen_even
#print axioms Tlmc1231.prod_f4_ne_16
#print axioms Tlmc1231.refute
#print axioms Tlmc1231.mod2_step
#print axioms Tlmc1231.mod2_add_dbl
#print axioms Tlmc1231.go_mod

open Lean in
#eval show MetaM Unit from do
  let names := [``Tlmc1231.tau_K4, ``Tlmc1231.f_odd, ``Tlmc1231.prod_f4,
                ``Tlmc1231.prod_f4_odd, ``Tlmc1231.sixteen_even,
                ``Tlmc1231.prod_f4_ne_16, ``Tlmc1231.refute,
                ``Tlmc1231.mod2_step, ``Tlmc1231.mod2_add_dbl, ``Tlmc1231.go_mod]
  for n in names do
    let axs ← Lean.collectAxioms n
    unless axs.isEmpty do
      throwError "{n} depends on axioms: {axs}"
  logInfo "AXIOM CHECK PASSED: all theorems depend on no axioms"
