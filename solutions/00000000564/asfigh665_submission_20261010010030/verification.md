# Local verification

Verified on October 10, 2026, with Lean 4.24.0 and TeX Live 2025.

## Lean

Each of the following commands completed with exit code 0:

```console
lake build
lake env lean Conjecture564.lean
lake exe verify
```

The build completed successfully with six jobs. The executable reported:

```text
Conjecture 00000000564: core Lean 4 verified the type-A2 counterexample.
First-mutated F polynomial: 1 + y_1; F(1) = 2; generalized Catalan(A2) = 5.
The theorem not_A2DivisibilityClaim proves the required divisibility claim false.
```

The printed axiom dependencies were:

| Theorem | Axioms |
| --- | --- |
| `a2_first_mutation_polynomial` | `propext`, `Quot.sound` |
| `a2_coxeter_order_three` | `propext` |
| `a2_coxeter_characteristic` | `propext` |
| `a2_generalizedCatalan` | `propext`, `Classical.choice`, `Quot.sound` |
| `a2_counterexample` | `propext`, `Classical.choice`, `Quot.sound` |
| `not_A2DivisibilityClaim` | `propext`, `Classical.choice`, `Quot.sound` |
| `refutesEveryClaimCoveringA2` | `propext`, `Classical.choice`, `Quot.sound` |

A source scan found no proof holes, custom axioms, native decision procedure,
unsafe declarations, external implementations, or unsafe reducibility settings
in the two Lean source files. `lake-manifest.json` lists no external packages.

## Report and submission

The final LaTeX source compiled twice with shell escape disabled, yielding a
two-page A4 PDF. The final log had no warnings or overfull/underfull boxes.
Both rendered pages were visually checked for legibility and complete formulas.

The refreshed upstream snapshot was
`9b795e7a94a6076e49a65a6489e1caf9153abd23`. Its metadata had both solved flags
false for conjecture 00000000564, and it had no solution directory for this
problem. All-state GitHub PR searches for `00000000564` and `00564` found no
earlier submissions. The contribution changes only this personal directory.
