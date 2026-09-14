# Lean 4 formalisation — disproof of conjecture `00000003844`

**Core Lean only, no imports at all** (the strongest form: no `Std`, no Mathlib),
no `sorry`. The project pins `lean-toolchain` to `leanprover/lean4:v4.33.1` and
defines the library `Main` in `lakefile.toml`.

## Build and audit

```sh
lake build
lake env lean Check.lean
```

`lake build` exits `0`; `Check.lean` prints `#print axioms` for every theorem so
a reviewer can confirm the absence of `sorryAx` and of any dependency beyond the
core axioms.

## What is formalised

The conjecture's first clause asserts that **every** finite-type 0-Hecke monoid
has infinite covering number. A single counterexample suffices, and the smallest
one is `H(S_3)`, the 0-Hecke monoid of type `A_2` (6 elements). The file builds
it from its 6 x 6 Demazure-product table and proves that its covering number is
exactly 2.

Because there are no imports, `Finset`, the `Monoid`/`Submonoid` typeclasses and
`Nat.Prime` are unavailable; everything is hand-rolled over `List`/`Nat`.

```lean
/-- Demazure product on the six elements, from an explicit 6 x 6 table. -/
def tbl : List (List Nat) :=
  [[0, 1, 2, 3, 4, 5],
   [1, 1, 4, 5, 4, 5],
   [2, 3, 2, 3, 5, 5],
   [3, 3, 5, 5, 5, 5],
   [4, 5, 4, 5, 5, 5],
   [5, 5, 5, 5, 5, 5]]

def mul (a b : Nat) : Nat := (tbl.getD a []).getD b 0

/-- A submonoid: contains the identity and is closed under the product. -/
def sub (S : List Nat) : Bool :=
  S.contains 0 && S.all (fun a => S.all (fun b => S.contains (mul a b)))
```

Index labelling: `0 = e`, `1 = s_2`, `2 = s_1`, `3 = s_1s_2`, `4 = s_2s_1`,
`5 = w_0`. The witness cover is

```lean
def A : List Nat := [0, 1]            -- {e, s_2}
def B : List Nat := [0, 2, 3, 4, 5]   -- H(S_3) \ {s_2}
```

| Theorem | Statement | Role |
|:--------|:----------|:-----|
| `assoc` | associativity over all `6^3 = 216` triples | monoid axiom (exhaustive) |
| `identity` | `0 = e` is a two-sided identity | monoid axiom |
| `gen_idem_s1`, `gen_idem_s2` | `s_1 s_1 = s_1`, `s_2 s_2 = s_2` | generator idempotence |
| `braid` | `s_1 s_2 s_1 = s_2 s_1 s_2` | Coxeter braid relation |
| `s1_mul_s2`, `s2_mul_s1` | `s_1 s_2 = 3`, `s_2 s_1 = 4` | table sanity |
| `A_sub`, `B_sub` | `A`, `B` are submonoids | the two covering pieces |
| `A_proper`, `B_proper` | `|A| < 6`, `|B| < 6` | both are **proper** |
| `cover` | `A ∪ B = H(S_3)` | the covering |
| `no_one_cover` | all 64 subsets are tried, none is a proper covering submonoid | covering number `≠ 1` |
| `covering_number_le_two` | a 2-cover exists | `cov ≤ 2` |
| `covering_number_ne_one` | no 1-cover | `cov ≥ 2` |
| `covering_number_is_two` | both together | **`cov = 2`** |
| `conjecture_00000003844_false` | `∃ A B, …` | **the conjecture's first clause is false** |

All statements are decided by `by decide`; there is no `sorry`, no axiom beyond
`propext`, and no `import`.

## Proof strategy

- **Monoid structure.** `assoc` is a bounded exhaustive check over the 216
  triples; `identity` checks the two-sided identity; `gen_idem_*` and `braid`
  verify the 0-Hecke presentation `π_i² = π_i`, `π_1π_2π_1 = π_2π_1π_2`.
- **A 2-cover.** `A = {e, s_2}` is a submonoid because `s_2` is idempotent.
  `B = H \ {s_2}` is a submonoid because of the length identity
  `ℓ(x ⋆ y) ≥ max(ℓ(x), ℓ(y))` for the Demazure product: if `x ⋆ y = s_2` then
  `1 = ℓ(s_2) ≥ max(ℓ(x), ℓ(y))`, so `ℓ(x), ℓ(y) ≤ 1` and
  `x, y ∈ {e, s_1, s_2}`; since `x, y ≠ s_2` this gives `x, y ∈ {e, s_1}`, and
  the table shows every product of two elements of `{e, s_1}` lies again in
  `{e, s_1}`, never equal to `s_2`. Hence `x, y ∈ B ⟹ x ⋆ y ∈ B`. (For the
  general finite-type statement of rank `≥ 2`, the same case analysis on
  `{e} ∪ (S \ {s})` is used; see `../main.tex`.) Both are proper and `A ∪ B = H`.
- **No 1-cover.** The 64 subsets are enumerated by bitmask (`maskSub`), each is
  tested for closure and containment of `e`, and none that is proper covers all
  six elements. (`A` proper submonoid can never equal the whole monoid, so this
  is a consistency check that the enumeration is faithful.)
- **Refutation.** `covering_number_is_two` gives `cov(H(S_3)) = 2`, so the claim
  "every finite-type 0-Hecke monoid has infinite covering number" fails.

## Axiom audit

`lake env lean Check.lean` reports:

- `A_proper`, `B_proper`, `cover`: **no axioms**;
- every other theorem, including `covering_number_is_two` and
  `conjecture_00000003844_false`: **`propext` only**.

No `sorryAx` appears. There are no Mathlib dependencies (there are no
dependencies at all).

## Scope note

- The formalisation refutes the conjecture by an explicit finite counterexample;
  it does **not** formalise the general theorem "every finite-type 0-Hecke monoid
  of rank `≥ 2` has covering number exactly 2". That theorem, and the
  direct-product bound `cov(M1 × M2) ≤ cov(M1)·cov(M2)`, are proved in prose in
  `../main.tex` and verified computationally (including `H(S_4)`, 24 elements,
  10577 submonoids) in `../reproduce.py`. A counterexample is logically
  sufficient to disprove the conjecture as filed.
- The length identity is used in the *proof sketch* in the comments and in the
  write-up; inside `Main.lean` the closure of `B` is checked exhaustively by
  `decide`, so the formal proof does not depend on that identity.
- `#eval` is applied to the underlying `Bool` definitions (`checkAssoc`,
  `checkIdentity`, `checkCover`, `checkNoOneCover`), never to proof terms: Lean
  refuses to evaluate proofs ("proofs are not computationally relevant").

## Environment

Lean 4.33.1, Lake, **no imports** and no dependencies; `lake build` needs no
cache download.
