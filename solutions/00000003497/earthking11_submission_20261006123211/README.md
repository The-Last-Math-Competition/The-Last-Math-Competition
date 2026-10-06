# Disproof of conjecture `00000003497`

**Verdict: false.** The claimed one-to-one correspondence fails already for
the trivial holomorphic line bundle over a point (and equally over any
connected complex manifold with constant metrics).

Give the one-dimensional complex vector space two Hermitian metrics

\[
h_1(z,w)=z\overline w,\qquad h_2(z,w)=2z\overline w.
\]

They are different: `h_1(1,1)=1` while `h_2(1,1)=2`.  On a point there is
only one connection, so their Chern connections coincide.  On a trivial line
bundle over a complex manifold the same computation is
`A=h^{-1} partial h=0` for both constant metrics.  Thus the map from metrics
to Chern connections is not injective, hence not a bijection.

The standard uniqueness theorem is not contradicted: a Chern connection is
unique **after both** a holomorphic structure and a Hermitian metric have been
fixed.  It does not say that the connection recovers the metric without a
normalization.

## Formal verification

`lean4/Main.lean` models a Hermitian metric on the one-dimensional fibre by
its positive integer scale and the unique connection on a point by `Unit`.
It constructs scales `1` and `2`, proves they are distinct, proves that their
Chern connections agree, and negates injectivity and bijectivity.

```sh
tectonic --outdir build main.tex
cd lean4
lake build
lake env lean Check.lean
```

The Lean project uses only core Lean/Std, contains no proof placeholders, and
`Check.lean` audits the axioms of the main refutation theorem.
