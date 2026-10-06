# Disproof of conjecture 00000007623

The conjecture's asserted nilpotency-index spectrum (at most two, with a
degenerate exception of index three) is false.  The standard nilpotent
Jordan shift on a four-dimensional space has nilpotency index exactly four.

The report gives the explicit matrix.  The Lean project gives the same
linear map in coordinates, proves its fourth iterate is zero, and exhibits a
vector on which its third iterate is nonzero.  Therefore its nilpotency index
is exactly `4`.

Verification:

```text
cd lean4
lake build
lake env lean Check.lean
```

No `sorry`, `native_decide`, or additional axiom is used.
