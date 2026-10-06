# Disproof of conjecture `00000000961`

**Verdict: FALSE.**

The conjecture states that the third free-cumulant correction has coefficient
`sqrt(2)`, described explicitly as the ratio of the third free cumulant to the
third classical cumulant.

Classical and free moment-cumulant relations are identical through order
three:

```
kappa_3 = r_3 = m_3 - 3 m_2 m_1 + 2 m_1^3.
```

Take `P(X=-1)=2/3` and `P(X=2)=1/3`. Its first three moments are `(0,2,2)`.
Therefore `kappa_3=r_3=2`, and their ratio is `1`, not `sqrt(2)`.

Lean verifies the probability-weighted moments after clearing the common
denominator `3`, evaluates both cumulants to `2`, and disproves the necessary
square identity `r_3^2=2*kappa_3^2`.

## Verification

```bash
cd lean4
lake build
```

Lean `v4.33.1`; no `sorry`, `native_decide`, or extra axiom. Both printed main
theorems report `does not depend on any axioms`.

Build the PDF with `tectonic main.tex --outdir build`.
