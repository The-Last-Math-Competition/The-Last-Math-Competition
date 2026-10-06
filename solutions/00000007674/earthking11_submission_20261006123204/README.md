# Disproof of conjecture 00000007674

Take the allowed algebraic value `q = 1/2`.  The quantity
`kappa = limsup n^(-2) log d_n` is nonnegative because each positive integer
pole order satisfies `d_n >= 1`.  The conjectured value is instead
`log |q| = log(1/2) < 0`.  A nonnegative number cannot equal that value.

The Lean theorem formalizes the decisive sign contradiction abstractly for
every strictly increasing logarithm with `log(1)=0`; it kernel-checks
`1/2 < 1`, derives `log(1/2) < 0`, and rules out equality with a nonnegative
`kappa`.

Verification:

```text
cd lean4
lake build
lake env lean Check.lean
```

The project uses Lean core/Std only.  No `sorry`, `native_decide`, or
additional axiom is used.
