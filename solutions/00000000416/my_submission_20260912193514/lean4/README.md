# Lean 4 project: refutation of 00000000416

Core Lean only — no Mathlib, no `sorry`.

## Build

```bash
export ELAN_HOME=<your elan dir>   # if elan is not already on PATH
export PATH="$ELAN_HOME/bin:$PATH"

lake build
lake env lean Check.lean
```

The toolchain is pinned in `lean-toolchain` (`leanprover/lean4:v4.33.1`).

## What is in `Main.lean`

| item | statement |
|---|---|
| `isSYT22b` | boolean test: is a filling of `(2,2)` a standard Young tableau |
| `cands` | all `4^4 = 256` fillings of the diagram `(2,2)` |
| `sols` | the standard ones |
| `sols_length` | `sols.length = 2`, proved by `rfl` — **no axioms** |
| `sols_eq` | `sols = [(0,1,2,3), (0,2,1,3)]`, proved by `rfl` |
| `orbit_bound` | two nonempty parts, one of size ≥ 2 ⟹ total ≥ 3 |
| `no_such_orbits` | no such splitting can total exactly 2 |
| `refutation_at_two` | no such splitting of the tableaux of shape `(2,2)` |
| `refutation_abstract` | the same, phrased without the enumeration |

## Note on the `rfl` proofs

The kernel has to walk all 256 candidates to evaluate `sols`, so the recursion
limit is raised (`set_option maxRecDepth 100000`). The proofs are still `rfl`,
not `native_decide`: the computation is checked by the kernel, and the resulting
theorems depend on no axioms. Using `native_decide` would have introduced
`Lean.ofReduceBool` and made the axiom profile worse for no benefit.

## Axioms

`Check.lean` prints them. The result:

- `sols_length` — **no axioms**
- `orbit_bound`, `no_such_orbits`, `refutation_at_two`, `refutation_abstract` —
  `[propext, Quot.sound]`, inherited from the standard treatment of lists
