import Main
import Lean

open Lean Elab Command

/- The audit traverses every authored theorem, not just the final theorem.
Only Lean's standard logical axioms are permitted. -/
run_cmd do
  let env ← getEnv
  let mut count := 0
  for (name, ci) in env.constants.toList do
    if name.toString.startsWith "TLMC506." && ci.isTheorem then
      let axioms ← collectAxioms name
      for ax in axioms do
        unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
          throwError "Forbidden axiom {ax} in {name}"
      logInfo m!"AUDIT {name}: {axioms}"
      count := count + 1
  if count < 100 then throwError "Suspiciously incomplete audit: {count} theorems"
  logInfo m!"PASS: audited all {count} authored theorems."

#print axioms TLMC506.conjecture506_counterexample
#check TLMC506.conjecture506_counterexample
