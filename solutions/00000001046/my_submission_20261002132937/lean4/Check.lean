import Main
import Lean

-- add #print axioms <name> for every theorem:
#print axioms TLMC1046.bound16_true
#print axioms TLMC1046.cnt16_1_0
#print axioms TLMC1046.cnt16_1_0_ne_2
#print axioms TLMC1046.delta16_eq_4
#print axioms TLMC1046.cnt256_1_0
#print axioms TLMC1046.cnt256_1_0_ne_2
#print axioms TLMC1046.cnt1024_1_0
#print axioms TLMC1046.cnt1024_1_0_ne_2
#print axioms TLMC1046.disproof

-- Machine audit: recompute every theorem's axiom list through
-- Lean.collectAxioms (the same API `#print axioms` uses) and report it in a
-- normalized one-line form.  A non-empty list here would also break the
-- `#print axioms` lines above, so the two audits must agree.
open Lean in
#eval show Lean.Elab.Command.CommandElabM Unit from do
  for n in [`TLMC1046.bound16_true, `TLMC1046.cnt16_1_0, `TLMC1046.cnt16_1_0_ne_2,
            `TLMC1046.delta16_eq_4, `TLMC1046.cnt256_1_0, `TLMC1046.cnt256_1_0_ne_2,
            `TLMC1046.cnt1024_1_0, `TLMC1046.cnt1024_1_0_ne_2, `TLMC1046.disproof] do
    if (← getEnv).contains n then
      let axs ← Lean.collectAxioms n
      IO.println s!"'{n}' depends on axioms: {axs.toList}"
    else
      throwError s!"missing declaration {n}"
