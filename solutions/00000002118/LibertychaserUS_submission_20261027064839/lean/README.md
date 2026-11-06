# Lean 4 project for conjecture 00000002118

Toolchain `leanprover/lean4:v4.33.1`, Mathlib `v4.33.1` (pinned in `lake-manifest.json`).

```
lake exe cache get
lake build
```

The build elaborates `Disproof.lean`, whose final `#print axioms` line lists only
`propext`, `Classical.choice`, `Quot.sound` (or a subset).

Auxiliary script `check.py` needs Python 3 with numpy, sympy and networkx.
