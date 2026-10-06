# Disproof of conjecture 00000007684

For the claimed scalar spectral point `lambda = 0`, the equation is
`D_q f = 0`, hence `f(qz) = f(z)`.  With `0 < |q| < 1`, comparison of power
series coefficients forces every positive-degree coefficient of an analytic
solution to vanish.  Thus `f` is constant; the boundary condition `f(1)=0`
then makes `f=0`.  The solution space has dimension `0`, not `1`.

The Lean project formalizes the normalized coefficient equations for the
specific allowed value `q=1/2`, the boundary equation, and proves that the
zero coefficient sequence is the unique solution.

Verification:

```text
cd lean4
lake build
lake env lean Check.lean
```

No `sorry`, `native_decide`, or additional axiom is used.
