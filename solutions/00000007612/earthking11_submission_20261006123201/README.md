# Disproof of conjecture 00000007612

The claimed universal dimension formula `2^(n/2)` already fails in odd
dimension.  For the one-generator complex Clifford algebra
`Cl_1(C) = C[e]/(e^2-1)`, evaluation at `e = 1` is a one-dimensional
irreducible representation.  Its dimension is therefore `1`, whereas the
stated formula gives `sqrt(2)`, which is not even an integer.

Files:

- `main.tex` / `main.pdf`: complete mathematical disproof.
- `lean4/Main.lean`: an explicit one-dimensional character of the algebra
  with relation `e^2=1`, plus the arithmetic obstruction `1^2 != 2` for this
  explicit one-dimensional representation.
- `lean4/Check.lean`: axiom audit.

Verification:

```text
cd lean4
lake build
lake env lean Check.lean
```

The project uses Lean core/Std only and contains no `sorry`,
`native_decide`, or additional axiom.
