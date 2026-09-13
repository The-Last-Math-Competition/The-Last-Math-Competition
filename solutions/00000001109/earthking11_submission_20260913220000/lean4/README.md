# Lean 4 formalisation — refutation of conjecture `00000001109`

Core Lean only (`import Std`), no Mathlib, no `sorry`, no `native_decide`. The
project pins `lean-toolchain` to `leanprover/lean4:v4.33.1` and defines the
library `Main` in `lakefile.toml`.

## Build and audit

```sh
lake build
lake env lean Check.lean
```

`Check.lean` prints `#print axioms` for every theorem so a reviewer can confirm
the absence of `sorryAx` and of Mathlib dependencies. The concrete `decide`
theorems are axiom-free; the parametric ones use only `propext`, `Quot.sound`
(and, where relevant, `Classical.choice` is not needed at all here).

## What is formalised

The exponent list of a finite Coxeter group is encoded concretely as a
`List Nat`. Distinctness is `List.Nodup`; multiplicity is `List.count`; the
conjecture's conclusion is the predicate

```lean
def HasRepeatedExponent (l : List Nat) : Prop :=
  ∃ x, x ∈ l ∧ 2 ≤ l.count x
```

The exponent lists are

```lean
def expsH3 : List Nat := [1, 5, 9]
def expsH4 : List Nat := [1, 11, 19, 29]
def expsI2 (m : Nat) : List Nat := [1, m - 1]   -- m ≥ 5
```

| Theorem | Statement | Role |
|:--------|:----------|:-----|
| `count_eq_one_of_nodup` | `l.Nodup → ∀ x ∈ l, l.count x = 1` | distinctness forces multiplicity one (by list induction) |
| `h3_nodup` | `(expsH3).Nodup` | exponents of H₃ are pairwise distinct |
| `h4_nodup` | `(expsH4).Nodup` | exponents of H₄ are pairwise distinct |
| `i2_nodup` | `m − 1 ≠ 1 → (expsI2 m).Nodup` | exponents of I₂(m) are distinct |
| `h3_no_repeat` | `¬ HasRepeatedExponent expsH3` | no exponent of H₃ has multiplicity ≥ 2 |
| `h4_no_repeat` | `¬ HasRepeatedExponent expsH4` | no exponent of H₄ has multiplicity ≥ 2 |
| `i2_no_repeat` | `m − 1 ≠ 1 → ¬ HasRepeatedExponent (expsI2 m)` | no repeated exponent for I₂(m) |
| `conjecture_00000001109_false` | conjunction of the three above | collected refutation (universal reading) |
| `h3_h_not_exponent` | `(expsH3.contains hH3) = false` | `h = 10` is NOT an exponent of H₃ |
| `h4_h_not_exponent` | `(expsH4.contains hH4) = false` | `h = 30` is NOT an exponent of H₄ |
| `h3_with_h_no_repeat` | `¬ HasRepeatedExponent (expsH3 ++ [10])` | adjoining `h` still gives no repeat |
| `h4_with_h_no_repeat` | `¬ HasRepeatedExponent (expsH4 ++ [30])` | adjoining `h` still gives no repeat |
| `reducible_has_repeated` | `HasRepeatedExponent (expsA1 ++ expsH3)` | HONEST SCOPE: A₁ × H₃ DOES have a repeat |
| `reducible_count_one` | `(expsA1 ++ expsH3).count 1 = 2` | the repeated exponent in A₁ × H₃ is 1, mult. 2 |

Here `hH3 = 10`, `hH4 = 30`, and `expsA1 = [1]` (exponents add over direct
products of Coxeter groups).

## Proof strategy

- **Concrete distinctness and non-repetition.** `expsH3`, `expsH4` are literal
  lists. `decide` reduces `¬ ∃ x, x ∈ l ∧ 2 ≤ l.count x` over the concrete
  finite candidate set; these proofs are axiom-free.
  (`HasRepeatedExponent` is a `def`, so the proofs start with
  `unfold HasRepeatedExponent` before `decide`, otherwise instance synthesis
  cannot see the underlying decidable proposition.)
- **General lemma.** `count_eq_one_of_nodup` is proved by induction on the list:
  for `a :: t` with `a ∉ t` and `t.Nodup`, a member equal to `a` has count
  `t.count a + 1 = 0 + 1 = 1` (`List.count_cons_self`,
  `List.count_eq_zero_of_not_mem`), and a member `x ≠ a` has
  `(a :: t).count x = t.count x = 1` (`List.count_cons_of_ne`, induction
  hypothesis).
- **Parametric I₂(m).** `i2_nodup` reduces `(expsI2 m).Nodup` with `simp` to
  `1 ≠ m − 1` and flips the hypothesis `m − 1 ≠ 1` with `Ne.symm`. Plain `omega`
  cannot see through truncated subtraction on the raw `List.Nodup` goal, which
  is why `simp`/`Ne.symm` is used; `omega` is then used only in
  `i2_no_repeat` after the count is known to be `1`.
- **No `sorry`, no `native_decide`.** All finite facts are closed by the kernel
  `decide`; the only axioms reported for parametric results are `propext` and
  `Quot.sound`.

## Scope

**The formalised refutation is the UNIVERSAL reading over irreducible finite
non-crystallographic Coxeter groups.** The complete list of such types is
H₃, H₄, and I₂(m) for `m ≥ 5`; their exponent lists are shown above and are
pairwise distinct in every case. Therefore the conclusion "some exponent has
multiplicity ≥ 2" fails for all of them, and the universal claim is false. This
is what the conjecture's own wording signals: 重数结构普遍性 / "universality of
the multiplicity structure".

**Honest boundary — the reducible case.** Under an EXISTENTIAL reading that also
admits REDUCIBLE non-crystallographic groups, the conjecture is TRUE, and the
file proves the counterexample: `A₁ × H₃` is a non-crystallographic Coxeter
group whose exponent multiset is `1, 1, 5, 9` (exponents add over direct
products). The exponent `1` therefore has multiplicity `2`
(`reducible_has_repeated`, `reducible_count_one`). So the refutation is NOT
unconditional: it is correct precisely under the universal reading that the
conjecture's phrase "universality" indicates, and it is FALSE as an existential
claim about arbitrary (possibly reducible) non-crystallographic groups.

**The `(h, 1)` reading.** Under the standard convention the exponents of a
finite Coxeter group are the degrees minus one and `h` is the largest degree, so
`h` is not an exponent and the phrase `(h, 1)` is vacuous. This is recorded by
`h3_h_not_exponent` and `h4_h_not_exponent`. If instead one adjoins `h` to the
exponent list (the generous reading), the conclusion still fails:
`1, 5, 9, 10` and `1, 11, 19, 29, 30` remain all-distinct
(`h3_with_h_no_repeat`, `h4_with_h_no_repeat`).

**Cited, not reproved.** The classification of finite Coxeter groups and their
exponent/degree tables (Humphreys, *Reflection Groups and Coxeter Groups*;
Bourbaki, *Groupes et algèbres de Lie*, Ch. V–VI) are cited inputs. This file
formalises only the finite multiplicity arithmetic on the exponent lists; it
does not reprove the classification.

## Environment

Lean 4.33.1, Lake, no Mathlib. `lake build` needs no cache download
(`lake-manifest.json` has an empty package list). The axiom audit reports no
`sorryAx` and no Mathlib dependency.
