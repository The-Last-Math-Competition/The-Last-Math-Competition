# Lean 4 formalisation — disproof of conjecture `00000002048`

Core Lean only (`import Std`), no Mathlib, no `sorry`. The project pins
`lean-toolchain` to `leanprover/lean4:v4.33.1` and defines the library `Main` in
`lakefile.toml`.

## Build and audit

```sh
lake build
lake env lean Check.lean
```

`Check.lean` prints `#print axioms` for every theorem so a reviewer can confirm
the absence of `sorryAx` and of Mathlib dependencies.

## What is formalised

Residues of `F_p` are represented as naturals reduced with `% p`, so no
`ZMod`/`Finset`/`Fintype` (Mathlib) is needed. The 3-fold sum is the decidable
predicate/list

```lean
def inSum3 (p : Nat) (A : List Nat) (s : Nat) : Bool :=
  A.any fun x => A.any fun y => A.any fun z => ((x + y + z) % p == s)

def sum3 (p : Nat) (A : List Nat) : List Nat :=
  (List.range p).filter fun s => inSum3 p A s

def coversNonzero (p : Nat) (A : List Nat) : Bool :=
  ((List.range (p - 1)).map (fun k => k + 1)).all fun s => inSum3 p A s
```

| Theorem | Statement | Role |
|:--------|:----------|:-----|
| `witness_sum3` | `sum3 5 [0,1] = [0,1,2,3]` | the 3-fold sum of the witness is exactly `{0,1,2,3}` |
| `witness_sum3_eq_range` | `sum3 5 [0,1] = List.range 4` | same, as an interval |
| `witness_four_nonzero` | `4 % 5 ≠ 0` | `4` is a nonzero element of `F_5` |
| `witness_misses_four` | `(sum3 5 [0,1]).contains 4 = false` | `4 ∉ 3A` |
| `witness_inSum3_four` | `inSum3 5 [0,1] 4 = false` | `4` is not a sum of three elements of `A` |
| `witness_card` | `[0,1].length = 2` | `|A| = 2` |
| `witness_threshold` | `3 * 2 > 5 - 1` | `|A| > (p-1)/3` (cross-multiplied) |
| `conjecture_00000002048_false` | `coversNonzero 5 [0,1] = false` | the conjecture's coverage claim fails at `p = 5` |
| `conjecture_00000002048_not_holds` | `¬ (coversNonzero 5 [0,1] = true)` | negation form |
| `witness_refutes_conjecture` | conjunction of the above | packaged counterexample |
| `family_misses_pred` | for `2 ≤ p`: `inSum3 p (familyA p) (p-1) = false` | the residue `p-1` is absent |
| `family_not_cover` | for `2 ≤ p`: `coversNonzero p (familyA p) = false` | the family never covers `F_p \ {0}` |
| `family_threshold` | for `p % 3 = 2`: `3 * (familyA p).length > p - 1` | the family meets the size hypothesis |
| `cauchy_davenport_at_threshold` | for `p % 3 = 2`: `min p (3*((p+1)/3) - 2) = p - 1` | Cauchy–Davenport only certifies `p-1` |
| `general_family_refutes` | size hypothesis ∧ non-coverage, for `2 ≤ p`, `p % 3 = 2` | the general disproof |
| `family_primes_prime` | all of `[5,11,…,89]` pass `primeB` | the listed primes are prime |
| `family_primes_mod` | all of `[5,11,…,89]` are `2 mod 3` | the listed primes qualify |
| `general_family_verified` | `familyCheck = true` | machine check over the listed primes |
| `listed_family_refutes` | conjunction of the three above | packaged list check |

Here `familyA p = List.range ((p - 2) / 3 + 1) = {0, 1, …, (p-2)/3}`.

## Proof strategy

- **Concrete witness.** `witnessA = [0,1]`, `sum3 5 witnessA` filters
  `List.range 5`, and `coversNonzero` checks the four nonzero residues
  `1,2,3,4`; every one of these finite facts is closed by `decide`.
- **Residue `p-1` is never attained.** For `x, y, z ∈ {0,…,(p-2)/3}` we have
  `x = y = z ≤ (p-2)/3`, hence
  `x + y + z ≤ 3·((p-2)/3) ≤ p-2 < p` (using `Nat.div_mul_le_self` and
  `omega`). So `Nat.mod_eq_of_lt` applies and `(x+y+z) % p = x+y+z ≤ p-2 < p-1`;
  the Boolean `== p-1` is therefore `false`. The nested `List.any` is unfolded
  with `List.any_eq_false`, and the final `beq_eq_false_iff_ne` turns the
  disequality into the `false` equation.
- **Non-coverage of the whole nonzero range.** `family_not_cover` uses
  `List.all_eq_false` and exhibits `p-1`, which is a member of
  `List.range (p-1) |>.map (·+1)` because `p-2 < p-1`, and whose `inSum3` value
  is `false`.
- **Size hypothesis.** `familyA p` has length `(p-2)/3 + 1`, and when
  `p % 3 = 2` this gives `3·|A| = p + 1 > p - 1` (`family_threshold`).
- **Cauchy–Davenport.** `cauchy_davenport_at_threshold` records the arithmetic
  that `min p (3·((p+1)/3) - 2) = p - 1`, i.e. the bound leaves exactly one
  residue uncovered and cannot force coverage. (The inequality
  `|A+B| ≥ min(p, |A|+|B|-1)` itself is not reproved here; only the evaluation
  at the threshold, which is the point relevant to the conjecture, is
  formalised.)
- **Listed primes.** `familyCheck` runs `primeB`, the `2 mod 3` test, the size
  test and the missing-residue test over `[5,11,17,23,29,41,47,53,59,71,83,89]`
  and is closed by `decide`.

## Scope note

- The concrete counterexample is fully formalised: `p = 5`, `A = {0,1}`,
  `3A = {0,1,2,3}`, `4 ∉ 3A`, `|A| = 2 > (p-1)/3`, and
  `coversNonzero 5 witnessA = false`.
- The general statement is formalised strongly and symbolically:
  `family_not_cover` holds for **every** `p ≥ 2` (primality is not needed to
  miss `p-1`), and `family_threshold` holds for every `p ≡ 2 (mod 3)`. Together
  (`general_family_refutes`) they give the conjecture's hypothesis and
  conclusion-failure for all such `p`, not merely a finite range.
- The only step left informal is the interpretation of `F_p` as a field and the
  statement `|A+B| ≥ min(p, |A|+|B|-1)` (Cauchy–Davenport). Neither is needed
  for the refutation: the counterexample is a concrete computation over the
  residues `{0,1,2,3,4}`, and non-coverage is witnessed by an explicit missing
  residue.
- `familyCheck` is a finite corroboration of the listed primes
  `5, 11, …, 89`; it is redundant given the symbolic theorems and is included
  for reproducibility.

## Environment

Lean 4.33.1, Lake, no Mathlib. `lake build` needs no cache download. The
axiom audit reports no `sorryAx` and no `Lean.ofReduceBool`; the concrete
witness theorems depend on no axioms at all, while the general ones use only
`propext`, `Quot.sound`, and `Classical.choice`.
