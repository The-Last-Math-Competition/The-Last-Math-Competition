# Lean 4 formalisation — disproof of conjecture `00000002175`

Core Lean only (`import Std`), no Mathlib, no `sorry`. The project pins
`lean-toolchain` to `leanprover/lean4:v4.33.1` and defines the library `Main` in
`lakefile.toml`.

## Build and audit

```sh
lake build
lake env lean Check.lean
```

`Check.lean` prints `#print axioms` for every theorem, so a reviewer can confirm
the absence of `sorryAx` and of Mathlib dependencies.

## Statement formalised

The conjecture is refuted at `n = 4`. Writing `{1,2}`, `{1,3}`, `{1,4}`,
`{1,2,3,4}` for the indicator vectors of those subsets of a 4-element ground
set, the four-subset family

```lean
def F : List (List Bool) :=
  [[true, true, false, false], [true, false, true, false],
   [true, false, false, true], [true, true, true, true]]
```

is 3-wise odd-intersecting: every one of the four triples of distinct members
meets in exactly `{1}`, of odd size 1. But `|F| = 4 > 2^{4-3} = 2`, so the
claimed maximum is false already at `n = 4`. A 5-element family `G5` is also
formalised, showing the true maximum at `n = 4` is at least `5 > 2`.

## Representation and why `List Bool`

Members are indicator vectors represented as `List Bool`. The natural
alternative `Fin 4 → Bool` is *not* usable in core Lean: the function type
`Fin 4 → Bool` has no `DecidableEq` instance without Mathlib, so the bounded
quantifier

```lean
def TripleOdd (F : List (List Bool)) : Prop :=
  ∀ a ∈ F, ∀ b ∈ F, ∀ c ∈ F, a ≠ b → a ≠ c → b ≠ c → interSize a b c % 2 = 1
```

would fail to synthesise the `Decidable` instance needed by `decide`. With lists
everything is decidable by evaluation. (Core Lean has no `Finset`, `ZMod`,
`Nat.Prime`, `Fintype`, or `Matrix`; `Rat` is not reduced by `decide`.)

## Definitions

```lean
def interSize (a b c : List Bool) : Nat :=
  (((a.zip b).zip c).filter (fun p => p.1.1 && p.1.2 && p.2)).length

def TripleOdd (F : List (List Bool)) : Prop :=
  ∀ a ∈ F, ∀ b ∈ F, ∀ c ∈ F, a ≠ b → a ≠ c → b ≠ c → interSize a b c % 2 = 1

def checkFamily (F : List (List Bool)) : Bool :=
  F.all fun a => F.all fun b => F.all fun c =>
    (a == b) || (a == c) || (b == c) || (interSize a b c % 2 == 1)
```

`interSize` zips the three indicator vectors and counts the positions where all
three entries are `true`; `TripleOdd` is the property; `checkFamily` is its
`Bool`-valued mirror.

## Theorem table

| Theorem | Statement | Role |
|:--------|:----------|:-----|
| `F_eq` | `F = [m12, m13, m14, m1234]` | `F` is the four named members |
| `witness_members_pairwise_distinct` | the four members are pairwise distinct | all four triples must be checked |
| `triple_123` | `interSize m12 m13 m14 = 1` | first triple meets in `{1}` |
| `triple_124` | `interSize m12 m13 m1234 = 1` | second triple meets in `{1}` |
| `triple_134` | `interSize m12 m14 m1234 = 1` | third triple meets in `{1}` |
| `triple_234` | `interSize m13 m14 m1234 = 1` | fourth triple meets in `{1}` |
| `witness_all_triples_meet_in_one` | conjunction of the four above | the explicit 4-triple check |
| `witness_oddTriples` | `TripleOdd F` | `F` is 3-wise odd-intersecting |
| `witness_check` | `checkFamily F = true` | the Boolean checker accepts `F` |
| `witness_length` | `F.length = 4` | `\|F\| = 4` |
| `claimed_bound_n4` | `2 ^ (4 - 3 : Nat) = 2` | the conjecture's value at `n = 4` |
| `witness_breaks_bound` | `F.length > 2 ^ (4 - 3 : Nat)` | `4 > 2`: the size claim fails |
| `witness_refutes_size_claim` | packaged conjunction | the refutation of the size claim at `n = 4` |
| `G5_oddTriples` | `TripleOdd G5` | a 5-element family on 4 points |
| `G5_check` | `checkFamily G5 = true` | the Boolean checker accepts `G5` |
| `G5_length` | `G5.length = 5` | `\|G5\| = 5` |
| `true_max_n4_exceeds_claim` | `G5.length > 2 ^ (4 - 3 : Nat)` | `5 > 2` |
| `n4_max_at_least_five` | packaged conjunction | true `M(4) ≥ 5 > 2 = 2^{4-3}` |

## Proof strategy

- **Explicit intersections.** `triple_123`, `triple_124`, `triple_134`,
  `triple_234` are each `decide`: `interSize` unfolds to list operations on the
  concrete `List Bool` literals and reduces to `1 = 1`.
- **3-wise odd-intersecting.** `witness_oddTriples` unfolds `TripleOdd` and the
  list `F` (`simp only [F, List.mem_cons, List.mem_nil_iff, or_false]`), then
  case-splits with `rcases … <;> rcases … <;> rcases …` on the four possible
  members for each of `a`, `b`, `c`. Each of the `4^3 = 64` goals is closed by
  the first applicable tactic among `absurd rfl hab`, `absurd rfl hac`,
  `absurd rfl hbc` (distinctness contradictions) and `decide` (the remaining
  concrete arithmetic facts, all of which say `interSize … % 2 = 1`).
- **Breaking the bound.** `witness_length`, `claimed_bound_n4` and
  `witness_breaks_bound` are pure evaluations of `List.length` and `Nat`
  arithmetic, closed by `decide`.
- **The 5-element family.** `G5` is proved by the same case-split pattern as
  `F`; `n4_max_at_least_five` packages it with `G5.length = 5 > 2`.

## Scope

- Formalised: the `n = 4` witness — the family is 3-wise odd-intersecting, has
  four members, and `4 > 2^{4-3}` — plus a 5-element family establishing
  `M(4) ≥ 5`.
- Not formalised: the exact maxima `M(n) = 1,2,2,4,5,7,8,10` for `n = 0..7` and
  the failure of the affine-subspace characterisation. These are finite
  computations over all subfamilies / all affine cosets and are carried out by
  `reproduce.py` (standard library only); they are not needed for the
  refutation, which is already complete at `n = 4`.
- Axiom audit: `lake env lean Check.lean` reports no `sorryAx`. The purely
  computational theorems depend on no axioms at all; the ones stated through the
  bounded `TripleOdd` quantifier use only `propext` and `Quot.sound`.

## Environment

Lean 4.33.1, Lake, no Mathlib. `lake build` needs no cache download.
