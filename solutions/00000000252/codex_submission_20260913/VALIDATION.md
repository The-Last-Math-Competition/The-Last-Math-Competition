# Validation

Validated on 2026-09-13 using the official Lean 4.19.0 Windows distribution.

## Lean

Commands executed from `lean/`:

```text
lake build
lake env lean Conjecture252.lean
```

Both exited successfully (exit code 0). Build output:

```text
Built Conjecture252
'Conjecture252.conjecture_false' depends on axioms: [propext, Quot.sound]
Build completed successfully.
```

The direct check printed the same axiom dependencies. These are standard
Lean axioms; there is no `sorryAx` and no user-defined axiom. The proof does
not use `native_decide`. The bundled `Std` library is its only import.

The formalization checks all three counterexample properties, then applies
the proposed universal assertion to the graph to derive a contradiction.
It does not assume any property of the counterexample as an added axiom.

## PDF

Compiled `proof.tex` with Tectonic 0.17.0, using the official bundle
`https://data1.fullyjustified.net/tlextras-2022.0r0.tar`.

Compilation exited with code 0. The PDF has two pages. Both pages were
rendered with Poppler and visually inspected. The final TeX log contains
no overfull boxes or undefined-reference warnings.

The Windows environment emitted Fontconfig cache/configuration diagnostics;
the PDF was nevertheless produced successfully and its rendered text and
mathematical symbols were checked. These are environment diagnostics, not
unresolved mathematical or LaTeX errors.
