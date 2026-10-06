# Disproof of conjecture `00000000752`

**Verdict: FALSE.**

The conjecture says that the entropy of a one-sided shift of finite type on
`Z_p` is `log lambda`, where `lambda` is the real number maximizing the p-adic
norm among the roots of the characteristic polynomial.

Take the full shift on two symbols and `p=3`. Its adjacency matrix is `[2]`.
There are exactly `2^n` admissible words of length `n`, so its topological
entropy is

```
lim (1/n) log(2^n) = log 2 > 0.
```

The characteristic polynomial is `X-2`, whose only root is `2`. Since `3` does
not divide `2`, the 3-adic norm is `|2|_3=1`. The proposed formula therefore
gives `log 1=0`, contradicting the actual entropy.

The Lean certificate formalizes the finite word count and the 3-adic unit-norm
calculation, then proves the conjecturally required equality fails already for
words of length `1` (`2 != 1`). This finite mismatch is the exponentiated form
of `log 2 != log 1`.

## Verification

```bash
cd lean4
lake build
```

The project uses Lean `v4.33.1`, contains no `sorry`, no `native_decide`, and
adds no axiom. `#print axioms Tlmc752.counterexample` reports only `[propext,
Quot.sound]`.

Build the PDF with `tectonic main.tex --outdir build`.
