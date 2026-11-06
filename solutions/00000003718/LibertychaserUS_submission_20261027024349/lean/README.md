# Lean 4 project for conjecture 00000003718

Toolchain `leanprover/lean4:v4.33.1`, Mathlib `v4.33.1`
(revision `0df444a360eaa60ab8c11dca51a86af692955474`, pinned in `lake-manifest.json`).

```
lake exe cache get
lake build
```

`lake build` elaborates `Submission/Verification.lean`, which prints the axioms of every result;
each depends only on `propext`, `Classical.choice`, `Quot.sound`.

| File | Content |
|---|---|
| `Submission/DetLeaf.lean` | leaf expansion of a determinant (`TLMC3718.det_leaf`) |
| `Submission/MatchingPoly.lean` | matchings, matching polynomial, leaf recurrence |
| `Submission/Leaf.lean` | a forest with an edge inside `s` has a leaf inside `s` |
| `Submission/Charpoly.lean` | `μ(F) = charpoly(A(F))` for forests |
| `Submission/Main.lean` | real roots and moment identity; `TLMC3718.conjecture_00000003718` |
| `Submission/Verification.lean` | `#print axioms` |
