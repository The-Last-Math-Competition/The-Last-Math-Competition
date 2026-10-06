# Disproof of conjecture 00000007669

At level `m = 3`, the two moves produce eight binary move words.  If nodes
mean tree nodes (histories), the count is therefore `8`.  If histories that
reach the same parameters are identified, the moves commute and the only
endpoints are `(3,0)`, `(2,1)`, `(1,2)`, and `(0,3)`, so the count is `4`.
Neither natural interpretation gives the conjectured `Fib(5) = 5`.

The Lean project enumerates all eight depth-three histories and their four
distinct exponent-pair endpoints and checks both inequalities against the
Fibonacci value.

Verification:

```text
cd lean4
lake build
lake env lean Check.lean
```

No `sorry`, `native_decide`, or additional axiom is used.
