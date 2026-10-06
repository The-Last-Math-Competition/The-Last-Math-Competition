# Disproof of conjecture `00000005244`

**Verdict: false because the filed clauses contradict each other.** The first
clause says the moduli space is irreducible for every genus `g >= 2`.  Taking
`g=2` says the genus-two space has exactly one irreducible component.  The next
clause calls genus `2` exceptional and says it has two irreducible components.

In component-count notation `c(g)`, the conjecture simultaneously requires

```text
forall g >= 2, c(g) = 1,
c(2) = 2.
```

Substituting `g=2` into the first equation gives `c(2)=1`, contradicting the
second equation.  The component dimensions and Lange-locus clause cannot
repair a contradiction that occurs before those data are used.

This does not decide which intended theorem is correct; it establishes that
the conjunction actually filed cannot be true.  A corrected problem would
need either `g>2` in the first clause or removal of the genus-two exception.

## Formal verification

Lean models `c : Nat -> Nat` and proves that no component-count function can
satisfy both clauses.  The proof is pure arithmetic and fully kernel checked.

```sh
tectonic --outdir build main.tex
cd lean4
lake build
lake env lean Check.lean
```
