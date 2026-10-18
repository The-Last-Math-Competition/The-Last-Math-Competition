# Proof of conjecture 00000000951

This submission proves the stated upper bound under the standard finite-frame reading: `n` is the number of indexed frame vectors, and a split is an **unordered** partition into two complementary subfamilies. Fix one distinguished index in one side. Each of the other `n - 1` indices has two choices, so there are exactly `2^(n - 1)` possible splits before imposing the Riesz-sequence condition. Requiring both parts to be Riesz sequences only selects a subset of those splits.

The formal proof does not need any property of Riesz sequences. It proves the count for every predicate on the possible splits, which includes the predicate that both subfamilies are Riesz sequences. The report explains the interpretation boundary: if `n` is meant to be ambient dimension or if ordered pairs are counted separately, the problem statement needs those conventions specified.

## Files

- `main.tex` and `main.pdf`: proof and formalization correspondence.
- `lean4/`: a self-contained Lean 4.33.1 project using only `Std`.
- `verification.txt`: build, theorem audit, and source hash.

## Reproduce

From `lean4/` run:

```text
lake build
lake env lean Check.lean
```

The checked source has no `sorry`, `native_decide`, or custom axioms. The reported dependencies are standard Lean axioms only.
