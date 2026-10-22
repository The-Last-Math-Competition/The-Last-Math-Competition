# Author strict Lean check

Result: PASS, process exit code 0.
Working directory: the draft's lean directory.
Command: lake env lean -DwarningAsError=true Main.lean.
Executable: tools/lean-4.19.0-windows/bin/lake.exe in the project.
Lean version: 4.19.0.

This check was run after adding the readable edge sets, their
uniformity/cardinality theorems, the complete triple-encoding bridges,
the non-Steiner theorems, and the negation of the Steiner clause.
No Lean source changes were made after this successful check.

SHA-256 of lean/Main.lean:
0d0236cd3cd074a3c79afa45b11efa835c5bf9f1b59917df0c95576fae1b2466.

The command printed the following axiom reports:

```text
'Conjecture1683.same_deck' depends on axioms: [propext, Classical.choice, Quot.sound]
'Conjecture1683.not_isomorphic' depends on axioms: [propext, Classical.choice, Quot.sound]
'Conjecture1683.conjecture1683_false' depends on axioms: [propext, Classical.choice, Quot.sound]
'Conjecture1683.edgeX_iff_mem' depends on axioms: [propext, Classical.choice, Quot.sound]
'Conjecture1683.edgeY_iff_mem' depends on axioms: [propext, Classical.choice, Quot.sound]
'Conjecture1683.X_not_steiner' depends on axioms: [propext, Classical.choice, Quot.sound]
'Conjecture1683.Y_not_steiner' depends on axioms: [propext, Classical.choice, Quot.sound]
'Conjecture1683.steiner_clause_false' depends on axioms: [propext, Classical.choice, Quot.sound]
```

This is an author check record, not a claim of a fresh isolated build
or a compiled/rendered PDF. The coordinator performs those final checks.
