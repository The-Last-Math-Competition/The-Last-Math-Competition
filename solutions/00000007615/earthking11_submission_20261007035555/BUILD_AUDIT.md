# Build and axiom audit

## Environment

- Lean toolchain: `leanprover/lean4:v4.33.1`
- Mathlib revision: `0df444a360eaa60ab8c11dca51a86af692955474`
- The independent Lean project is in `lean/`; `.lake/` is ignored and is not part of this submission.

## Results

`lake build` completed successfully. The project contains the following audit commands in `Check.lean`:

```text
#print axioms TLMC7615.lorentz_signature_and_orientation
#print axioms TLMC7615.hodgeStar_satisfies_definition
#print axioms TLMC7615.hodgeStar_unique
#print axioms TLMC7615.hodgeStar_square
#print axioms TLMC7615.conjecture_counterexample
```

Observed dependencies:

```text
lorentz_signature_and_orientation: [propext, Classical.choice, Quot.sound]
hodgeStar_satisfies_definition: [propext, Classical.choice, Quot.sound]
hodgeStar_unique: [propext, Classical.choice, Quot.sound]
hodgeStar_square: [propext, Classical.choice, Quot.sound]
conjecture_counterexample: [propext, Classical.choice, Quot.sound]
```

These are standard Lean/Mathlib dependencies. There are no `sorry`, `admit`, `native_decide`, or custom axioms. The key bridge is formalized: `hodgeStar_satisfies_definition` proves the Hodge defining identity on all covectors, and `hodgeStar_unique` proves that this identity uniquely determines the map used by the counterexample.
