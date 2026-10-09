# Build

The Lean development uses the core library of Lean 4.19.0 only.

```sh
cd lean
lake build
lean -DwarningAsError=true Disproof.lean
```

The disproof is `TLMC408.staircase_two_breaks_the_equivalence`.
