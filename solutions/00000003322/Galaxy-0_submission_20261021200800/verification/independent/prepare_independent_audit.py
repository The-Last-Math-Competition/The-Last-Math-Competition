#!/usr/bin/env python3
"""Prepare a module-origin-based all-theorem audit for a frozen source snapshot."""
import pathlib, sys

root=pathlib.Path(sys.argv[1])
modules=sorted(p.stem for p in root.glob('*.lean')
               if p.stem not in {'Audit','AuditAll','IndependentAudit'})
assert 'Main' in modules
source=''.join('import '+m+'\n' for m in modules)+'import Lean\n\n'
source+='open Lean Elab Command\n\n'
source+='run_cmd do\n'
source+='  let env ← getEnv\n'
source+='  let modules : List Name := ['+', '.join('`'+m for m in modules)+']\n'
source+='  let mut count := 0\n'
source+='  let mut constants := 0\n'
source+='  for (name, ci) in env.constants.toList do\n'
source+='    if let some idx := env.getModuleIdxFor? name then\n'
source+='      let moduleName := env.header.moduleNames[idx.toNat]!\n'
source+='      if modules.contains moduleName then\n'
source+='        constants := constants + 1\n'
source+='        if ci.isAxiom then throwError "Authored axiom {name} in {moduleName}"\n'
source+='        if ci.isTheorem then\n'
source+='          let axioms ← collectAxioms name\n'
source+='          for ax in axioms do\n'
source+='            unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do\n'
source+='              throwError "Forbidden axiom {ax} in {name}"\n'
source+='          logInfo m!"AUDIT {moduleName}: {name}: {axioms}"\n'
source+='          count := count + 1\n'
source+='  if count < 250 then throwError "Incomplete theorem audit: {count}"\n'
source+='  logInfo m!"PASS: independently audited {count} authored theorems among {constants} authored constants, selected by origin module."\n\n'
source+='#print axioms TLMC3322.complete_counterexamples\n'
source+='#check TLMC3322.complete_counterexamples\n'
(root/'IndependentAudit.lean').write_text(source)
print('\n'.join(modules))
