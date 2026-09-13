# Lean 4 formalisation — disproof of conjecture `00000001070`

Core Lean only (`import Std`), no Mathlib, no `ZMod`, no `sorry`, no `axiom`,
no `native_decide`. The project pins `lean-toolchain` to
`leanprover/lean4:v4.33.1` and defines the library `Main` in `lakefile.toml`.

## Build and audit

```sh
lake build
lake env lean Check.lean
```

`Check.lean` prints `#print axioms` for every theorem so a reviewer can confirm
the absence of `sorryAx` and of Mathlib dependencies.

## What is formalised

The field `F_7` is modelled as `Fin 7` with its cyclic addition; there is no
`ZMod` (which would require Mathlib). The three-fold sumset
`A + A + A` (repetitions allowed) is expressed both as a Boolean enumeration
and as a proposition:

```lean
def isThreefoldSum (A : List F7) (y : F7) : Bool :=
  A.any (fun a => A.any (fun b => A.any (fun c => a + b + c == y)))

def IsThreefoldSum (A : List F7) (y : F7) : Prop :=
  ∃ a b c : F7, a ∈ A ∧ b ∈ A ∧ c ∈ A ∧ a + b + c = y
```

| Theorem | Statement | Role |
|:--------|:----------|:-----|
| `witness_threefold_bool` | `(finRange 7).all (isThreefoldSum [0,1,3]) = true` | the 27 triples of `A = {0,1,3}` cover all 7 residues |
| `isThreefoldSum_sound` | `isThreefoldSum A y = true → IsThreefoldSum A y` | soundness bridge from the Boolean test to the sumset predicate |
| `witness_threefold` | `∀ y : Fin 7, IsThreefoldSum [0,1,3] y` | `3A = F_7` for the witness |
| `witness_size` | `([0,1,3] : List F7).eraseDups.length = 3` | `\|A\| = 3` |
| `witness_threefold_set` | every residue occurs among the 27 sums | explicit `3A = F_7` |
| `no_two_elements` | all 21 two-element subsets fail to cover | minimality: no `\|A\| = 2` works |
| `formula_at_seven` | `(7+1+2)/3 + 1 = 4` | the conjectured value `⌈(p+1)/3⌉ + 1` at `p = 7` |
| `corrected_at_seven` | `(7+2+2)/3 = 3` | the universal threshold `⌈(p+2)/3⌉` at `p = 7` |
| `corrected_matches_witness` | `(7+2+2)/3 = ([0,1,3]).eraseDups.length` | that threshold is tight at `p = 7` |
| `formula_too_large` | `(7+1+2)/3 + 1 ≠ ([0,1,3]).eraseDups.length` | `4 ≠ 3` |
| `conjecture_00000001070_false` | conjunction of the above | the collected disproof |

## Proof strategy

- The Boolean enumeration `witness_threefold_bool` evaluates the nested
  `List.any` over the `3 × 3 × 3 = 27` triples of `[0,1,3]` and all `7`
  residues; it is closed by `decide`.
- `isThreefoldSum_sound` converts the Boolean witness to the propositional
  sumset predicate using `List.any_eq_true` and `beq_iff_eq`.
- `witness_threefold` lifts the Boolean enumeration over `List.finRange 7` to
  the genuine universal statement `∀ y : Fin 7` via `List.all_eq_true` and
  `List.mem_finRange`.
- `no_two_elements` lists all `C(7,2) = 21` two-element subsets (`allPairs`)
  and closes the resulting `Bool` computation by `decide`.
- The arithmetic facts about `⌈(p+1)/3⌉ + 1` and `⌈(p+2)/3⌉` at `p = 7` are
  encoded with natural-number division (`(a + b + 2) / 3` for `⌈a/b⌉`) and
  closed by `decide`.

## Note on `Fintype` (why the bridge lemma is needed)

`Fintype`/`Finset` live in Mathlib and are deliberately avoided. Core `Std`
has no `Fintype (Fin 7)` instance, so `decide` cannot be used directly on a
quantifier `∀ y : Fin 7` (the error is `failed to synthesize Decidable (∀ y :
F7, ...)`). The formalisation therefore proves the Boolean enumeration
`witness_threefold_bool` by `decide` and derives the propositional universal
statement `witness_threefold` from it through the small soundness lemma
`isThreefoldSum_sound`. No Mathlib infrastructure is used.

## Axiom audit

`lake env lean Check.lean` reports only `propext` and `Quot.sound` (from the
standard library lemmas used by `decide`, `rw` and `simpa`); `no_two_elements`,
`formula_at_seven` and `corrected_at_seven` depend on no axioms at all. No
theorem reports `sorryAx`, `native_decide`'s `ofReduceBool`, or any Mathlib
constant.

## Scope note

The formalisation establishes the decisive counterexample at `p = 7`:

1. `∀ y : Fin 7, IsThreefoldSum [0,1,3] y`, i.e. `3·{0,1,3} = F_7`;
2. `|{0,1,3}| = 3`;
3. the conjectured expression `⌈(7+1)/3⌉ + 1 = 4` is different from `3`.

Hence the smallest `|A|` with `3A = F_p` is not `⌈(p+1)/3⌉ + 1`. The file also
records that no two-element subset of `F_7` covers, so the witness is minimal
at `p = 7`. The general behaviour of the existential minimum for `p ≤ 30` is
handled computationally in `../reproduce.py`.

## Environment

Lean 4.33.1, Lake, no Mathlib. `lake build` needs no cache download.
