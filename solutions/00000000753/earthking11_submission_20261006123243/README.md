# Disproof of conjecture `00000000753`

**Verdict: FALSE as stated.**

The conjecture claims that the number of polynomials whose coefficients obey
`|a_i|_p <= p^{-i}` has the exact form `p^{i(i+1)/2}`. At `i=0`, the formula is
`p^0=1`. But the coefficient condition is merely `|a_0|_p <= 1`, and the two
distinct constant polynomials

```
P_0(X)=0,   P_1(X)=1
```

both satisfy it for every prime `p`. Thus the count is at least `2`, not `1`.
In fact, over `Q_p` the unit ball contains infinitely many constants, so
without a finite residue quotient the proposed finite count is not even of the
right cardinality.

The Lean theorem `counterexample` constructs the two constant polynomials,
certifies their distinctness, and computes the conjectured index-zero count as
one.

## Verification

```bash
cd lean4
lake build
```

Lean `v4.33.1`; no `sorry`, `native_decide`, or added axiom. `#print axioms
Tlmc753.counterexample` reports only `[propext]`.

Build the PDF with `tectonic main.tex --outdir build`.
