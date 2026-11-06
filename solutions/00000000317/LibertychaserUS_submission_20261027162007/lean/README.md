# Lean 4 project for conjecture 00000000317

Toolchain `leanprover/lean4:v4.33.1`, Mathlib `v4.33.1` (pinned in `lake-manifest.json`).

```
lake exe cache get
lake build
```

The build elaborates `Disproof.lean`, whose final `#print axioms` line lists only
`propext`, `Classical.choice`, `Quot.sound` (or a subset).

Auxiliary script `check.py` (Python 3 with sympy) prints the exact Gauss-map states and partial quotients; `python3 check.py --write` regenerates `lean/Disproof.lean`.
