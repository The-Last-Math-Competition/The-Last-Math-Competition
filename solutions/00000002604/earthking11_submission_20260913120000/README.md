# Refutation of conjecture 00000002604

**Conjecture (id 00000002604).** *Distributive-lattice layer-thickness rigidity:*
finite distributive lattices with the same layer-count vector are isomorphic; the
realizable vectors are characterized as the minimal family satisfying
Kruskal–Katona type inequalities.

**Verdict: FALSE**, under the natural reading of the conjecture. A finite
distributive lattice is isomorphic to the ideal lattice `J(P)` of a finite poset
`P` (Birkhoff's representation theorem), and the "layer-count vector" is the
rank-size vector of `J(P)`: the number of order ideals of `P` of each cardinality.
The claim that this vector determines `J(P)` up to isomorphism is false.

## The counterexamples

### Minimal counterexample (n = 4)

| poset | strict relations on `{0,1,2,3}` | ideal-count vector |
|-------|--------------------------------|--------------------|
| `P` | `0<1<2`, `3` isolated | `(1,2,2,2,1)` |
| `Q` | `0<2`, `0<3`, `1<2` | `(1,2,2,2,1)` |

`P` and `Q` have equal layer-count vectors but are non-isomorphic: `3` is isolated
in `P`, while `Q` has no isolated element. Brute force over all `4! = 24`
bijections confirms that no order-isomorphism exists. Hence `J(P)` and `J(Q)` are
non-isomorphic distributive lattices with the same layer-count vector.

### Counterexample on n = 5

| poset | strict relations on `{0,1,2,3,4}` | ideal-count vector |
|-------|-----------------------------------|--------------------|
| `A` | `0<1, 0<2, 0<3, 1<3, 2<3`, `4` isolated | `(1,2,3,3,2,1)` |
| `B` | `1<2, 2<3, 0<4` (closure: `1<3`) | `(1,2,3,3,2,1)` |

Again equal vectors, non-isomorphic (`A` has an isolated element, `B` does not;
`A` has 5 comparabilities, `B` has 3). Verified over all `5! = 120` bijections.

### Minimality

Exhaustive enumeration of all labelled posets on `n <= 4` elements, grouped by
ideal-count vector with isomorphism tested by brute force over all `n!`
bijections, gives:

| n | labelled posets | distinct vectors | non-isomorphic colliding pairs |
|---|-----------------|------------------|--------------------------------|
| 1 | 1   | 1  | 0 |
| 2 | 3   | 2  | 0 |
| 3 | 19  | 5  | 0 |
| 4 | 219 | 15 | 576 |

No non-isomorphic collision exists for `n <= 3`, so `n = 4` is the minimum size of
a counterexample.

## On the reading

The refutation targets the reading described by the statement's own language: the
layer-count vector records the rank sizes of the lattice (order ideals by
cardinality). If instead the invariant were enriched so that it already determines
the poset (e.g. the isomorphism type of the join-irreducible subposet), the claim
would be trivially true; that is a different statement.

## Files

- `main.tex` — standalone article with the definition, both counterexamples,
  non-isomorphism certificates, and the minimality remark. Compiled to
  `build/main.pdf`.
- `reproduce.py` — stdlib-only exhaustive verification; prints `PASS`/`FAIL`,
  exits `0`.
- `lean4/` — formalisation in core Lean 4 (`import Std`, no Mathlib, no `sorry`,
  no `axiom`, no `native_decide`).
  - `Main.lean` — posets `leP`, `leQ` on `Fin 4`, the computable ideal-count
    vector, `vectors_equal`, `not_isomorphic`, and `conjecture_00000002604_false`.
  - `Check.lean` — `#print axioms` audit.

## Reproducing

```sh
python3 reproduce.py
export PATH="/opt/homebrew/bin:$PATH"
cd lean4 && lake build && lake env lean Check.lean
cd .. && mkdir -p build && tectonic --outdir build main.tex
```

All checks pass. The Lean development depends only on the standard axiom
`propext` (from `decide`); no `sorryAx` and no `Lean.ofReduceBool`.
