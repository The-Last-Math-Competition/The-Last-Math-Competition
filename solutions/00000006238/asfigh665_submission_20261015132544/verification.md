# Verification record

Verified on October 15, 2026, with the official Windows Lean 4.24.0
distribution and only its standard library.

Commands run from `lean4/`:

```console
lake build
lake exe verify
lake env lean Conjecture6238.lean
```

All three commands finished successfully. `lake build` reported
`Build completed successfully (6 jobs)`.

The source's axiom audit reported:

```text
Conjecture6238.complement_square:
  [propext, Classical.choice, Quot.sound]
Conjecture6238.no_fixed_subset:
  no axioms
Conjecture6238.not_discrete_fixed_point_claim:
  no axioms
Conjecture6238.not_universal_fixed_point_claim:
  no axioms
Conjecture6238.refutes_every_claim_covering_discrete_case:
  no axioms
```

The only axioms used by the general double-complement identity are Lean's
standard foundational axioms. The counterexample's main refutation theorems
depend on no axioms. A scan of the Lean source found no proof holes, native
decision procedure, or custom axiom declaration.

The mathematical reduction is the explicit fixed-point clause of the
original conjecture. The counterexample uses a nonempty proper singleton
of the discrete two-point space, and the formal source supplies the
topology axioms and complete powerset operations, not merely a Boolean
truth-value calculation detached from the stated objects.

## Final report and duplicate check

The final two-page PDF compiled twice with shell escape disabled, with no LaTeX warnings or overfull/underfull boxes. Both pages were rendered and visually inspected. The coordinating reviewer independently checked the definitions and logical refutation. At upstream `cce2d90c`, both solved flags were false and no solution directory existed; all-state PR search for `00000006238` returned no previous submission.
