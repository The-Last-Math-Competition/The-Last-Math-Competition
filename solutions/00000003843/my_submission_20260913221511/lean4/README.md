# Lean 4 formalisation (kernel + core only)

No Mathlib, no `sorry`, no `Classical.choice`.

## Build

```bash
export ELAN_HOME=<your elan home>
export PATH="$ELAN_HOME/bin:$PATH"
lake build
lake env lean Check.lean
```

Toolchain: `leanprover/lean4:v4.33.1` (pinned in `lean-toolchain`).

## What is in `Main.lean`

`namespace Tlmc3843`

**Utilities (all by structural recursion / pattern matching)**
`band`, `bor` (Boolean connectives), `ltB` (`Nat` order as a `Bool`), `minB`,
`idxD` (list indexing with a default), `memBEq`, `ins`, `nub`, `posOf`,
`sumList`.

**`H_3(0)`** — `perms3` (the six permutations in one-line notation), `words3`
(a reduced word for each), `swapAt`, `invCount` (Coxeter length), `stepP`
(right multiplication by a generator, with the absorption rule), `mul`
(the 0-Hecke product), `g0`/`g1`/`e`.

**Green's relations** — `growJ` (close under `x·g0, x·g1, g0·x, g1·x`), `growL`
(close under `g0·x, g1·x`), `closureN`, `charOf`, `jIdeal`, `lIdeal`, `jVec`,
`lVec`, `jClasses`, `lClasses`. Since `a J b ⟺ HaH = HbH`, the number of
`J`-classes is the number of *distinct* principal ideals, which is what
`jClasses` counts.

**Self-checks** — `assocHolds` (exhaustive over all `6^3` triples),
`identityHolds`, `absorptionHolds`.

**Partitions and hooks** — `partsAux`, `partitionsOf`, `pCount`, `hooksOf`,
`distinctHooks`, `sumDistinctHooks`.

## Theorems and axiom audit

| theorem | statement | axioms |
|---|---|---|
| `hSize_eq` | `\|H_3(0)\| = 6` | none |
| `assoc_ok` | associativity on all 216 triples | none |
| `identity_ok` | two-sided identity | none |
| `absorption_ok` | `π_i² = π_i` for both generators | none |
| `jClasses_eq` | `J`-classes = 6 | none |
| `lClasses_eq` | `L`-classes = 6 | none |
| `pCount3_eq` | `p(3) = 3` | none |
| `sumHooks3_eq` | hook-length sum = 8 | none |
| `refutation_one_bool` | `(jClasses == pCount 3) = false` | none |
| `refutation_two_bool` | `(lClasses == sumDistinctHooks 3) = false` | none |
| `refutation_part_one` | `jClasses ≠ pCount 3` | `[propext]` |
| `refutation_part_two` | `lClasses ≠ sumDistinctHooks 3` | `[propext]` |
| `summary` | conjunction of the above | `[propext]` |

The `[propext]` on the last three comes from Lean's generated no-confusion
machinery used to discharge `6 = 3` / `6 = 8`; it is not an assumption about
mathematics. The zero-axiom Boolean witnesses
(`refutation_one_bool`, `refutation_two_bool`) carry the same content.

## Gotcha worth remembering

Two core/Std constructs silently introduce `propext` into otherwise-pure
computations:

1. The short-circuiting operators `&&` and `||` elaborate to `if <Bool> then`,
   which goes through `CoeSort Bool Prop` and `Decidable (b = true)`.
2. The standard-library list accessor that takes a default value does the same.

Replacing them with functions defined by pattern matching (`band`, `bor`,
`idxD`) is what makes the eight computational theorems above axiom-free.
Verified by isolating each candidate in a one-line `rfl` theorem and running
`#print axioms`: `List.foldl`, `List.map`, `List.range`, `List.length`,
`BEq (==)` on `Nat` and on `List Nat`, and hand-rolled membership/dedup are all
clean; only the default-value accessor was not.
