import Graphs
import Main
import PolynomialCore
import PolynomialRing
import Principal
import RawPolynomial
import ThreeCore
import ThreeExtras
import ThreeGrading
import ThreeRaw
import ThreeRing
import TriangleBetti
import TriangleCore
import TriangleGraded
import TriangleModule
import TwoExtras
import Lean

open Lean Elab Command

run_cmd do
  let env ← getEnv
  let modules : List Name := [`Graphs, `Main, `PolynomialCore, `PolynomialRing, `Principal, `RawPolynomial, `ThreeCore, `ThreeExtras, `ThreeGrading, `ThreeRaw, `ThreeRing, `TriangleBetti, `TriangleCore, `TriangleGraded, `TriangleModule, `TwoExtras]
  let mut count := 0
  let mut constants := 0
  for (name, ci) in env.constants.toList do
    if let some idx := env.getModuleIdxFor? name then
      let moduleName := env.header.moduleNames[idx.toNat]!
      if modules.contains moduleName then
        constants := constants + 1
        if ci.isAxiom then throwError "Authored axiom {name} in {moduleName}"
        if ci.isTheorem then
          let axioms ← collectAxioms name
          for ax in axioms do
            unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
              throwError "Forbidden axiom {ax} in {name}"
          logInfo m!"AUDIT {moduleName}: {name}: {axioms}"
          count := count + 1
  if count != 554 then throwError "Incomplete theorem audit: {count}"
  logInfo m!"PASS: independently audited {count} authored theorems among {constants} authored constants, selected by origin module."

#print axioms TLMC3322.complete_counterexamples
#check TLMC3322.complete_counterexamples
