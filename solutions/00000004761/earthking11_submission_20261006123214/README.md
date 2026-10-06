# Disproof of conjecture `00000004761`

**Verdict: false as stated.** The total Möbius sum is not always zero.  Take
the noncrossing-partition lattice `NC(1)`.  It contains one element only: the
partition `{{1}}`.  For every locally finite poset,

```text
mu(x,x) = 1.
```

Therefore the complete sum on `NC(1)` is the one-term sum

```text
sum mu = mu(x,x) = 1 != 0.
```

This is not a convention issue: `mu(x,x)=1` is forced by Möbius inversion,
since it must be the convolution inverse of the zeta function.  The familiar
zero-sum identity requires a **strict** interval `x<y`; the conjecture says
the total sum is always zero and supplies no non-degeneracy hypothesis.

## Formal verification

`lean4/Main.lean` represents `NC(1)` by `Unit`, defines its zeta and Möbius
values, checks the convolution-inverse equation, evaluates the total sum as
`1`, and proves the universal zero-total statement false.

```sh
tectonic --outdir build main.tex
cd lean4
lake build
lake env lean Check.lean
```
