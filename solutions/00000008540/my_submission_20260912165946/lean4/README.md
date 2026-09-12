# Lean 4 formalisation — status: COMPLETE

**No Mathlib dependency.** The whole formalisation is core Lean 4, because the
objects involved are three and four elements wide and every concrete claim
closes by `decide`. The earlier version of this file proposed a Mathlib route
(`Lattice.Congruence`, `IsBoolean`, `IsSubdirectlyIrreducible`); that route was
abandoned after checking the API — it is not needed, and avoiding Mathlib means
a reviewer can build this in seconds instead of downloading gigabytes of
prebuilt oleans.

## Contents

| file | purpose |
|---|---|
| `Main.lean` | the formalisation (302 lines, zero `sorry`) |
| `Check.lean` | `#print axioms` for every result |
| `lakefile.toml` | Lake configuration |
| `lean-toolchain` | `leanprover/lean4:v4.33.1` |

## How to build

```bash
lake build            # must succeed; there is no sorry to warn about
lake env lean Check.lean
```

`Check.lean` uses `lake env` because the local `Main.olean` is only on the
search path inside the Lake environment; a bare `lean Check.lean` cannot find
the `Main` module.

## What is formalised

Congruences of `C3` are represented as `Bool`-valued relations
`f : Fin 3 → Fin 3 → Bool`, so that `f x y = true` is the assertion `x ~ y` and
every clause of the definition of a congruence is a *decidable* proposition. The
chain order is on `Fin 3`, with `meet` and `join` given explicitly.

| theorem | statement |
|---|---|
| `con_complete` | every congruence of `C3` is one of `relBot`, `relAlpha`, `relBeta`, `relTop` |
| `relBot_ne_relAlpha` … (6 lemmas) | those four are pairwise distinct |
| `code_inj` | the map `f ↦ (f 0 1, f 1 2)` is injective on congruences |
| `code_surj` | it is surjective onto `Bool × Bool` |
| `code_le` | it preserves and reflects the order |
| `relAlpha_isAtom`, `relBeta_isAtom` | both middle congruences are atoms |
| `atom_only_two` | they are the only atoms |
| `conjecture_00000008540_false` | the conjunction of all of the above |

The pair (`con_complete` + the six distinctness lemmas) says `Con(C3)` has
**exactly four** elements. The triple (`code_inj`, `code_surj`, `code_le`) says
`Con(C3)` is **order-isomorphic to `Bool × Bool`**, which with the componentwise
order is the four-element Boolean lattice `2²`; an order isomorphism between
finite lattices preserves meets and joins, so `Con(C3)` *is* `2²` as a lattice.
The pair (`relAlpha_isAtom`, `relBeta_isAtom`) plus `atom_only_two` says
`Con(C3)` has **exactly two atoms**, so `C3` is not subdirectly irreducible.

## Proof structure

Three steps carry the mathematics; everything else is `decide`.

1. **`f02_eq`** — in a congruence on a chain, `0 ~ 2` holds exactly when both
   `0 ~ 1` and `1 ~ 2` do. This is the chain case of "congruence classes are
   intervals": if `0 ~ 2` then `0 ~ 1` because `0 ⊓ 1 = 0` and `2 ⊓ 1 = 1`, and
   `1 ~ 2` because `0 ⊔ 1 = 1` and `2 ⊔ 1 = 2`. All four of those order facts
   are separate `decide` lemmas (`meet_0_1`, `meet_2_1`, `join_0_1`, `join_2_1`).

2. **`determined`** — a congruence on the chain is determined by the pair
   `(f 0 1, f 1 2)`. Nine cases, discharged by `funext` plus a `match` on the
   two arguments: the diagonal entries come from reflexivity, `(0,1)`, `(1,2)`
   and `(0,2)` from the hypotheses, and the remaining three from symmetry.

3. **`con_complete`** — case-split on `(f 0 1, f 1 2) ∈ Bool × Bool` (four
   cases) and invoke `determined` with the matching one of the four relations.

## Axiom dependencies

`lake env lean Check.lean` reports:

```
'Tlmc8540.con_complete'                       depends on axioms: [propext, Quot.sound]
'Tlmc8540.code_inj'                           depends on axioms: [propext, Quot.sound]
'Tlmc8540.code_surj'                          depends on axioms: [propext]
'Tlmc8540.code_le'                            depends on axioms: [propext, Quot.sound]
'Tlmc8540.relAlpha_isAtom'                    depends on axioms: [propext, Quot.sound]
'Tlmc8540.relBeta_isAtom'                     depends on axioms: [propext, Quot.sound]
'Tlmc8540.atom_only_two'                      depends on axioms: [propext, Quot.sound]
'Tlmc8540.conjecture_00000008540_false'       depends on axioms: [propext, Quot.sound]
```

`propext` is propositional extensionality and `Quot.sound` is quotient
soundness; both are standard Lean axioms, and `Quot.sound` enters only through
`funext` (function extensionality), which is a theorem of Lean's logic rather
than an axiom of its own. There is no `sorryAx`, no `Classical.choice`, and no
`native_decide`.

## Notes for a reviewer

* **`decide` cannot see free variables.** `by decide` requires a *closed*
  proposition. This is why the four congruence lemmas
  (`relBot_isCongruence` …) close by `decide` but `con_complete` cannot: its goal
  mentions the variable `f`. The fix used throughout is to build the required
  equality as `c1.trans (by decide)`, keeping the `decide` part closed.

* **`cases c : e` substitutes `e` in the goal.** After `cases c1 : f 0 1` and
  `cases c2 : f 1 2`, the goal `f 0 2 = (f 0 1 && f 1 2)` has already become
  `f 0 2 = (false && false)`. A subsequent `rw [c1]` therefore fails with
  "did not find an occurrence of the pattern" — the pattern is gone. This is why
  `f02_eq` finishes its cases with `exact e.trans rfl` rather than `rw`.

* **`Bool.and` is `@[implicit_reducible]`,** so `rw`'s automatic `rfl` closing
  does not always see through `false && false`. Writing `rfl` explicitly works.

* **`DecidableEq (Fin 3 → Fin 3 → Bool)` does not exist,** so `relBot ≠ relAlpha`
  is *not* a `decide` goal. The six distinctness lemmas instead exhibit a pair
  on which the two relations disagree and feed it to `congrArg`.

* **Core Lean 4 has no `Set`.** An early draft used `Set (Fin 2)` for the
  "subsets of a two-element set" reading of `2²`; the identifier is unknown in
  core. The formalisation therefore uses `Bool × Bool` with the componentwise
  order, which is the same four-element Boolean lattice and needs no library.
