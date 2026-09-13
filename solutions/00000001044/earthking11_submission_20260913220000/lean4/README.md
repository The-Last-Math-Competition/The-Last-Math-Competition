# Lean 4 formalisation — disproof of conjecture `00000001044`

Core Lean only (`import Std`), no Mathlib, no `sorry`. The project pins
`lean-toolchain` to `leanprover/lean4:v4.33.1` and defines the library `Main`
in `lakefile.toml` (project name `tlmc1044`).

## Build and audit

```sh
lake build
lake env lean Check.lean
```

`Check.lean` prints `#print axioms` for every theorem so a reviewer can confirm
the absence of `sorryAx` and of Mathlib dependencies.

## What is formalised

Residues of `F_q` are represented as naturals reduced with `% q`, so no
`ZMod`/`Finset`/`Fintype` (Mathlib) is needed. Note that `q` must be a variable
`Nat` (not `Fin q`), because a variable `q` breaks the `OfNat (Fin q)` instance.

```lean
def D (q : Nat) : Nat → Nat → Nat → Nat
  | 0,   a, x => 2 % q
  | 1,   a, x => x % q
  | k+2, a, x => ((x * D q (k+1) a x) + (q - (a * D q k a x) % q)) % q

def valueSet (q n a : Nat) : List Nat :=
  ((List.range q).map (D q n a)).eraseDups

def compSize (q n a : Nat) : Nat := q - (valueSet q n a).length
```

`D` is the Dickson recursion `D_0 = 2`, `D_1 = x`,
`D_k = x·D_{k-1} − a·D_{k-2}`; `valueSet` is the image over `F_q` as a
duplicate-free list; `compSize` is the size of its complement in `F_q`.
`biggerValueSet q n a` is the Boolean
`(valueSet q n 0).length < (valueSet q n a).length`, and `tieWithZero`,
`nonzeroBeatsZero`, `minComp` are bounded (`a < q`) search predicates, used
because an unbounded `∃ a : Nat, …` has no `Decidable` instance.

| Theorem | Statement | Role |
|:--------|:----------|:-----|
| `q3n2_d` | `Nat.gcd 2 (3*3-1) = 2` | `d = gcd(n, q²−1) = 2` at `(q,n) = (3,2)` |
| `q3n2_d_gt_one` | `Nat.gcd 2 (3*3-1) > 1` | the conjecture's hypothesis `d > 1` holds |
| `q3n2_formula` | `(3-1)/2 = 1` | the conjectured value `(q−1)/d = 1` |
| `q3n2_a0` | `compSize 3 2 0 = 1` | `a = 0` attains complement `1` |
| `q3n2_a1` | `compSize 3 2 1 = 1` | `a = 1` has value set `{1,2}`, complement `1` |
| `q3n2_a2` | `compSize 3 2 2 = 1` | `a = 2` has value set `{0,2}`, complement `1` |
| `q3n2_a0_is_formula` | `compSize 3 2 0 = (3-1)/2` | `a = 0` attains the formula value |
| `q3n2_a1_ties` | `compSize 3 2 1 = compSize 3 2 0` | `a = 1` ties `a = 0` |
| `q3n2_a2_ties` | `compSize 3 2 2 = compSize 3 2 0` | `a = 2` ties `a = 0` |
| `q3n2_a1_not_bigger` | `biggerValueSet 3 2 1 = false` | `a = 1` does **not** give a strictly larger value set |
| `q3n2_a2_not_bigger` | `biggerValueSet 3 2 2 = false` | `a = 2` does **not** give a strictly larger value set |
| `q3n2_no_a_strictly_bigger` | `(List.range 3).all (… !(biggerValueSet 3 2 a)) = true` | no `a` gives a strictly larger value set |
| `q3n2_nonunique` | `∃ a, a < 3 ∧ a ≠ 0 ∧ compSize 3 2 a = compSize 3 2 0` | `a = 0` is not the unique minimiser |
| `q3n2_tie` | `tieWithZero 3 2 = true` | a nonzero `a` ties `a = 0` |
| `q3n2_min` | `minComp 3 2 = 1` | the minimum is `1`, but attained by several `a` |
| `conjecture_00000001044_false` | conjunction of the above | **the packaged disproof** |
| `q5n2_d`, `q5n2_formula` | `Nat.gcd 2 24 = 2`, `(5-1)/2 = 2` | hypothesis and formula at `(5,2)` |
| `q5n2_all` | `∀ a, a < 5 → compSize 5 2 a = 2` | all five `a` tie |
| `q5n2_min`, `q5n2_tie` | `minComp 5 2 = 2`, `tieWithZero 5 2 = true` | minimum attained by all `a` |
| `q5n2_no_a_strictly_bigger` | bounded all-quantifier | no `a` gives a strictly larger value set |
| `q7n2_d`, `q7n2_formula` | `Nat.gcd 2 48 = 2`, `(7-1)/2 = 3` | hypothesis and formula at `(7,2)` |
| `q7n2_all` | `∀ a, a < 7 → compSize 7 2 a = 3` | all seven `a` tie |
| `q7n2_min`, `q7n2_tie` | `minComp 7 2 = 3`, `tieWithZero 7 2 = true` | minimum attained by all `a` |
| `q7n3_d`, `q7n3_formula` | `Nat.gcd 3 48 = 3`, `(7-1)/3 = 2` | hypothesis and formula at `(7,3)` |
| `q7n3_a0` | `compSize 7 3 0 = 4` | `a = 0` gives the **largest** complement |
| `q7n3_a1` | `compSize 7 3 1 = 2` | `a = 1` gives complement `2` |
| `q7n3_reversal` | `compSize 7 3 0 > compSize 7 3 1` | direction is backwards |
| `q7n3_a0_exceeds_formula` | `compSize 7 3 0 > (7-1)/3` | `a = 0` exceeds the claimed minimum |
| `q7n3_a0_largest` | `∀ a, a < 7 → compSize 7 3 a ≤ compSize 7 3 0` | `a = 0` **maximises** the complement |
| `q7n3_nonzero_beats` | `nonzeroBeatsZero 7 3 = true` | nonzero `a` beat `a = 0` |
| `q5n3_a0_permutes` | `compSize 5 3 0 = 0` | `x³` permutes `F_5` although `d = 3 > 1` |
| `q5n3_d_not_dvd` | `¬ (3 ∣ (5-1))` | `d` need not divide `q−1` |
| `q5n3_min` | `minComp 5 3 = 0` | true minimum is `0`, not `(q−1)/d` |
| `q5n4_d` | `Nat.gcd 4 24 = 4` | `d = 4` at `(5,4)` |
| `q5n4_a0`, `q5n4_a2` | `compSize 5 4 0 = 3`, `compSize 5 4 2 = 2` | `a = 2` beats `a = 0` |
| `q5n4_beats` | `nonzeroBeatsZero 5 4 = true` | a nonzero `a` strictly beats `a = 0` |
| `q5n4_min` | `minComp 5 4 = 2` | true minimum is `2`, not the claimed `(q−1)/d = 1` |
| `q5n4_no_a_attains_formula` | bounded all-quantifier | no `a` attains the claimed value `1` |
| `q3n4_d`, `q3n4_tie` | `Nat.gcd 4 8 = 4`, `tieWithZero 3 4 = true` | `a = 0` ties `a = 2` at `(3,4)` |
| `q3n4_d_not_dvd` | `¬ (4 ∣ (3-1))` | `(q−1)/d` is not an integer at `(3,4)` |
| `table_3_2` … `table_5_4` | `(List.range q).map (compSize q n) = […]` | machine-checked tables matching `reproduce.py` |

## Proof strategy

Every theorem is a finite computation over `F_q` for a fixed small `q`, so all
of them are discharged by `decide` (with
`set_option maxRecDepth 1000000`). The universal statements such as
`q5n2_all`, `q7n2_all` and `q7n3_a0_largest` are of the form
`∀ a, a < q → …`, which `decide` closes by bounded enumeration because the
bound `a < q` is decidable. The quantified statements are deliberately kept
bounded: an unbounded `∃ a : Nat, …` (or `∀ a : Nat, …`) has no `Decidable`
instance in core Lean, so `decide` cannot be used and such statements are
expressed with `List.any`/`List.all` predicates (`tieWithZero`,
`nonzeroBeatsZero`) or supplied with an explicit witness (`q3n2_nonunique`).

All 51 audited theorems report **no axioms at all**, except the two
divisibility facts `q5n3_d_not_dvd` and `q3n4_d_not_dvd`, which use only
`propext`. None reports `sorryAx`, `Classical.choice`, `Quot.sound`, or any
Mathlib axiom.

## Scope note

- The refutation is complete and unconditional at `(q,n) = (3,2)`:
  `Nat.gcd 2 (3*3-1) = 2 > 1`, `(3-1)/2 = 1`, and all three `a` give
  `compSize 3 2 a = 1`, so `a = 0` is not the unique minimiser and the other
  `a` do not give a strictly larger value set. This is the negation of the
  conjecture's second clause and refutes the claim as stated.
- The `n = 2` ties at `(5,2)` and `(7,2)` and the `(7,3)` reversal are
  formalised as finite `decide` computations, together with the extra
  breakages at `(5,3)`, `(5,4)` and `(3,4)`.
- The formalisation covers the definition of the value set over `F_q` exactly
  as the conjecture states it (`valueSet q n a` is the image of `D_n(·,a)` on
  `{0,…,q−1}`). The torus-reading caveat discussed in the main document is a
  remark about an alternative interpretation and is not formalised here.
- The package name is `tlmc1044` (`tl` = target lemma, `mc` = conjecture
  identifier `00000001044`).

## Environment

Lean 4.33.1, Lake 5.0.0, no Mathlib. `lake build` needs no cache download. The
axiom audit reports no `sorryAx`; every concrete computation is axiom-free and
the two divisibility facts use only `propext`.
