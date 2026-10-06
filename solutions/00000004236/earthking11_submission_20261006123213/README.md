# Disproof of conjecture `00000004236`

**Verdict: false.** Consider a triangle with nonnegative edge weights

```text
w(0,1)=1,  w(0,2)=1,  w(1,2)=3.
```

Root at vertex `0`.  The two weight-`1` edges form a shortest-path tree:
the direct distances from `0` to `1` and `2` are both `1`, while the routes
through the other vertex have weight `4`.  Cutting away that tree leaves the
single residual edge of weight `3`.

The graph has only one nontrivial simple 1-cycle, the triangle, whose weight is
`1+1+3=5`.  Hence

```text
minimum cycle weight = 5 != 3 = minimum residual edge weight.
```

All weights are nonnegative, so this directly refutes the claimed strict
identity in its stated domain.  (The correct fundamental-cycle quantity adds
the residual edge to the tree path joining its endpoints.)

## Formal verification

The Lean project records the complete three-edge graph, proves the tree is
shortest by explicit path comparisons, computes the residual minimum and
cycle weight, and negates the universal identity.

```sh
tectonic --outdir build main.tex
cd lean4
lake build
lake env lean Check.lean
```
