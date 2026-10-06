# Disproof of conjecture `00000006289`

**Verdict: false.** The statement says that for finite groups trace support is
the identity conjugacy class and the trace vanishes off it.  The trivial
one-dimensional representation of the two-element group `C_2` is an immediate
counterexample.

Let `rho(g)=[1]` for both `g=e` and the nonidentity element `s`.  This is a
representation because `[1][1]=[1]`.  Its character is

```text
chi(e)=tr([1])=1,
chi(s)=tr([1])=1.
```

Thus `chi(s)` is nonzero away from the identity.  Since `C_2` is abelian, its
conjugacy classes are `{e}` and `{s}`; the trace support is the whole group,
not only the identity class.

The claim would be true for the **regular character**, but the conjecture says
finite-group trace support without imposing regularity.  The trivial character
shows the omitted hypothesis is essential.

## Formal verification

Lean defines the group law of `C_2` on `Bool`, the constant scalar
representation `rho(g)=1`, verifies multiplicativity, computes both trace
values and the two-element support, and negates identity-only support.

```sh
tectonic --outdir build main.tex
cd lean4
lake build
lake env lean Check.lean
```
