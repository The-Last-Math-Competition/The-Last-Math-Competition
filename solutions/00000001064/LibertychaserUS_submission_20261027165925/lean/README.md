# Lean 4 project for conjecture 00000001064

Toolchain `leanprover/lean4:v4.33.1`, Mathlib `v4.33.1` (pinned in `lake-manifest.json`).

```
lake exe cache get
lake build
```

The build elaborates `Kakeya.lean`, whose final `#print axioms` line lists only
`propext`, `Classical.choice`, `Quot.sound` (or a subset).

The auxiliary `check.py` (Python 3, standard library only) brute-forces the minimum for small primes; q = 11 takes a few minutes. `PROOF.md` is the paper proof in plain text.
