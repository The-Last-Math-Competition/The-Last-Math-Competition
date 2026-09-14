# Lean 4 formalisation — disproof of conjecture `00000002192`

Core Lean only (`import Std`), no Mathlib, no `sorry`. The project pins
`lean-toolchain` to `leanprover/lean4:v4.33.1` and defines the library `Main`,
whose name is `tlmc2192`, in `lakefile.toml`.

## Build and audit

```sh
lake build
lake env lean Check.lean
```

`Check.lean` prints `#print axioms` for every theorem so a reviewer can confirm
the absence of `sorryAx` and of Mathlib dependencies.

## What is formalised

The conjecture claims that the maximal dimension of height-2 posets is
`⌈log₂ log₂ n⌉`. The refutation is a single witness: the standard example
`S_2` on `n = 4` elements has height 2 and dimension exactly 2, while
`⌈log₂ log₂ 4⌉ = 1`.

`S_2` is modelled on `Fin 4` as the relation

```lean
def ltS2 (x y : E) : Prop := (x = 0 ∧ y = 3) ∨ (x = 1 ∧ y = 2)
```

that is, `0 < 3` and `1 < 2` and nothing else. A linear extension is a list of
all four elements respecting those relations, and the intersection of a family
is the pointwise intersection of the induced strict orders:

```lean
abbrev IsLinExt (L : List E) : Prop :=
  L.Nodup ∧ L.length = 4 ∧ ∀ x y : E, ltS2 x y → L.idxOf x < L.idxOf y

abbrev Intersection (Ls : List (List E)) (x y : E) : Prop :=
  ∀ L ∈ Ls, L.idxOf x < L.idxOf y
```

The dimension is then defined through the existence of realizers:

```lean
def DimLe (d : Nat) : Prop := ∃ Ls : List (List E), Ls.length = d ∧ IsRealizer Ls
def DimEq (d : Nat) : Prop := DimLe d ∧ ∀ e : Nat, DimLe e → d ≤ e
```

| Theorem | Statement | Role |
|:--------|:----------|:-----|
| `ltS2_irrefl`, `ltS2_asymm` | `ltS2` is irreflexive and asymmetric | sanity of the relation |
| `ltS2_03`, `ltS2_12` | `ltS2 0 3`, `ltS2 1 2` | the two relations |
| `not_ltS2_01`, `not_ltS2_10` | `¬ ltS2 0 1`, `¬ ltS2 1 0` | `0` and `1` are incomparable |
| `no_three_chain` | no `x, y, z` with `ltS2 x y ∧ ltS2 y z` | no chain of three elements |
| `height_two` | the `2`-chain `0 < 3` exists and no `3`-chain does | **`S_2` has height 2** |
| `isLinExt_L1`, `isLinExt_L2` | `[0,3,1,2]` and `[1,2,0,3]` are linear extensions | the two halves of the realizer |
| `inter_L1_L2` | `Intersection [L1, L2] = ltS2` | **upper bound `dim ≤ 2`** |
| `no_single` | no single linear extension realises `ltS2` | **lower bound `dim ≰ 1`** |
| `not_dim_le_zero` | `¬ DimLe 0` | `dim ≰ 0` |
| `not_dim_le_one` | `¬ DimLe 1` | `dim ≰ 1` |
| `dim_le_two` | `DimLe 2` | `dim ≤ 2` |
| `dim_eq_two` | `DimEq 2` | **the dimension is exactly 2** |
| `formula_at_four` | `Nat.log2 (Nat.log2 4) = 1` | the conjectured value at `n = 4` |
| `conjecture_00000002192_false` | `HeightTwo ∧ DimEq 2 ∧ formula = 1 ∧ 2 ≠ 1` | **the conjecture is false** |

## Proof strategy

- **Upper bound** (`inter_L1_L2`). With `L1 = [0,3,1,2]` (order
  `0 < 3 < 1 < 2`) and `L2 = [1,2,0,3]` (order `1 < 2 < 0 < 3`), both respect
  `0 < 3` and `1 < 2`. The pair `{0,1}` is ordered `0 < 1` in `L1` and `1 < 0`
  in `L2`, and likewise `{2,3}` is ordered `3 < 2` in `L1` and `2 < 3` in
  `L2`; so their intersection contains exactly the two relations `ltS2`. The
  whole statement is a closed decidable proposition, discharged by `decide`.
- **Lower bound** (`no_single`). Suppose a single extension `L` realises the
  poset. Since `L` respects `0 < 3` and `1 < 2` we have
  `L.idxOf 0 < L.idxOf 3` and `L.idxOf 1 < L.idxOf 2`, and since
  `L.idxOf 3 ≤ L.length = 4` and `L.idxOf 2 ≤ 4`, both `0` and `1` occur in
  `L`. Realising the poset with one extension forces
  `ltS2 0 1 ↔ L.idxOf 0 < L.idxOf 1`; as `ltS2 0 1` is false,
  `¬ (L.idxOf 0 < L.idxOf 1)`, and symmetrically
  `¬ (L.idxOf 1 < L.idxOf 0)`. Hence `L.idxOf 0 = L.idxOf 1 =: k` with
  `k < L.length`, and `List.getElem_idxOf` gives `L[k] = 0` and `L[k] = 1`,
  contradicting `0 ≠ 1` in `Fin 4`.
- **Dimension** (`dim_eq_two`). `DimLe 2` is the pair `[L1, L2]`, and any
  `DimLe e` with `e < 2` is ruled out by `not_dim_le_zero` and
  `not_dim_le_one`.

## The integer reading of `⌈log₂ log₂ 4⌉`

Core Lean has no real logarithm, so the right-hand side at `n = 4` is
formalised by the exact integer iterated logarithm

```lean
theorem formula_at_four : Nat.log2 (Nat.log2 4) = 1 := by decide
```

`Nat.log2 4 = 2` and `Nat.log2 2 = 1` exactly, so for `n = 4` this equals
`⌈log₂ log₂ 4⌉ = 1` with no rounding ambiguity. The refutation only needs the
value at `n = 4`, where the integer and real readings coincide; the contrast
`2 ≠ 1` is then purely arithmetic. The formula at general `n` is discussed in
`../main.tex` and `../README.md`; `reproduce.py` evaluates it with
`math.log2`.

## Scope note

- The formalisation proves the *specific* contradiction at `n = 4`, which is
  logically sufficient to refute the universally quantified assertion that the
  maximal dimension of height-2 posets equals `⌈log₂ log₂ n⌉` for all `n`: the
  value at `n = 4` is wrong.
- The companion script `../reproduce.py` (Python 3 standard library only)
  additionally computes `dim(S_k) = k` exactly for `k = 2, 3, 4` by a bitmask
  search over tuples of linear extensions, and exhaustively enumerates all
  height-`≤ 2` posets on `n ≤ 6` elements, obtaining the maximum dimensions
  `1, 2, 2, 2, 2, 3`.
- The true growth is `⌊n/2⌋` for `n ≥ 4` (Dushnik–Miller / Hiraguchi),
  attained by `S_{⌊n/2⌋}`. This is stated and tabulated in `../main.tex`; the
  Lean project formalises the `n = 4` witness, not the general theorem.

## Axiom audit

`lake env lean Check.lean` reports:

- `formula_at_four`: **no axioms**;
- concrete computations (`ltS2_irrefl`, `ltS2_asymm`, `ltS2_03`, `ltS2_12`,
  `not_ltS2_01`, `not_ltS2_10`, `isLinExt_L1`, `isLinExt_L2`, `inter_L1_L2`,
  `dim_le_two`): `propext` alone;
- `no_three_chain`, `height_two`, `inter_singleton`, `not_dim_le_zero`:
  `propext` and `Quot.sound` (the existential and singleton statements);
- `no_single`, `not_dim_le_one`, `dim_eq_two`, `conjecture_00000002192_false`:
  `propext`, `Classical.choice`, `Quot.sound`.

No `sorryAx` appears for any theorem.

## Environment

Lean 4.33.1, Lake, no Mathlib. `lake build` needs no cache download.
