# Disproof of conjecture `00000003295`

**Verdict: FALSE.**

The conjecture says that Dawson's reciprocal odd series has the whole real
axis as its convergence domain. Dawson's integral has the standard large-`x`
asymptotic expansion

```
F(x) ~ sum_{n>=0} (2n-1)!! / (2^{n+1} x^{2n+1}).
```

At `x=1` the terms are `a_n=(2n-1)!!/2^{n+1}` and satisfy

```
a_{n+1} = ((2n+1)/2) a_n.
```

For `n>=1` the multiplier is at least `3/2`; in particular, from `n=4`
onward `a_n>=1`. The terms do not approach zero, so the series diverges at
`x=1`. Hence it cannot converge on the whole real axis. The reciprocal series
is asymptotic, not convergent (for any fixed nonzero `x`, the factorially
growing coefficients eventually dominate the power of `x`).

Lean defines the odd double factorial and proves `2^{n+1} <= (2n-1)!!` for all
`n>=4`, then directly negates the eventual term-to-zero condition.

## Verification

```bash
cd lean4
lake build
```

Lean `v4.33.1`; no `sorry`, `native_decide`, or added axiom. The printed axiom
audit reports only `[propext, Quot.sound]`.

Build the PDF with `tectonic main.tex --outdir build`.
