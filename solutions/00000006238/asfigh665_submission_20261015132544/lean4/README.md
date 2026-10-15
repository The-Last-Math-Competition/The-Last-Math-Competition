# Lean verification for conjecture 00000006238

This project is pinned to Lean 4.24.0 and uses only its standard library.

```console
lake build
lake exe verify
lake env lean Conjecture6238.lean
```

`Conjecture6238.lean` contains the mathematical definitions and theorems.
`Main.lean` prints a human-readable summary; its printed output is not
used as a proof. The proof terms are checked when the library is compiled.

The final negated claim quantifies over all subsets of a concrete discrete
two-point space. The topology, complement, openness, and closedness are
defined from ordinary set membership. The witness is the singleton
containing `false`, whose complement is the singleton containing `true`.

The file prints the axiom dependencies of the involution theorem and the
principal refutation theorems. There are no external packages or custom
axioms, and no proof holes or native decision procedure.
