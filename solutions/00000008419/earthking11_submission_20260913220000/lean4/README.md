# Lean 4 formalisation — disproof of conjecture `00000008419`

Core Lean only (`import Std`), no Mathlib, no `Finset`, no `sorry`. The project
pins `lean-toolchain` to `leanprover/lean4:v4.33.1` and defines the library
`Main` in `lakefile.toml`.

## Build and audit

```sh
lake build
lake env lean Check.lean
```

`Check.lean` prints `#print axioms` for every theorem so a reviewer can confirm
the absence of `sorryAx` and of Mathlib dependencies.

## What is formalised

The witness is the binary `[5,2,3]` code, written with coordinate 1 first:

```lean
def gA : List Bool := [false, true, true, false, true]   -- 01101, support {2,3,5}
def gB : List Bool := [true, false, false, true, true]   -- 10011, support {1,4,5}
def code : List (List Bool) := [zero5, gA, gB, xorList gA gB]  -- {00000,01101,10011,11110}
```

Words are `List Bool` of length 5 and XOR is a hand-written Boolean XOR
(`xorB`/`xorList`), so the kernel reducer evaluates every definition; the opaque
`Nat.xor` is not used. The design predicate enumerates all `t`-subsets of the
five coordinates and checks that each is contained in the same number of blocks.

| Theorem | Statement | Role |
|:--------|:----------|:-----|
| `gAB_eq` | `gAB = [true,true,true,true,false]` | `01101 + 10011 = 11110` |
| `code_closed` | `inCode gAB = true ∧ inCode zero5 = true` | the listed set is closed under the two generators |
| `weights` | `weight zero5 = 0 ∧ weight gA = 3 ∧ weight gB = 3 ∧ weight gAB = 4` | weight distribution |
| `minWeight_eq_three` | `minWeight = 3` | minimum distance `d = 3` |
| `no_codeword_of_other_weight` | every codeword has weight `0`, `3` or `4` | no codeword of weight 1, 2 or 5 |
| `gA_is_min`, `gB_is_min` | `isMinWeightWord gA = true`, `isMinWeightWord gB = true` | the generators are minimum-weight |
| `minWeightWords_spec` | length `2` and every element is `gA` or `gB` | exactly two minimum-weight codewords |
| `dualDistance_eq_two` | `dualDistance = 2` | `d^⊥ = 2` |
| `dual_word_of_weight_two` | `isDual [false,true,true,false,false] = true` | the weight-2 dual word `01100` |
| `no_dual_word_of_weight_one` | no dual word has weight 1 | so `d^⊥ = 2` exactly |
| `support_gA` | `(List.finRange 5).filter (support5 gA) = [1,2,4]` | support `{2,3,5}` (0-based indices) |
| `support_gB` | `(List.finRange 5).filter (support5 gB) = [0,3,4]` | support `{1,4,5}` |
| `blocks_length` | `blocks.length = 2` | one block per minimum-weight codeword |
| `multiplicity_five` | `countBlocks blocks [4] = 2` | coordinate 5 lies in both blocks |
| `multiplicity_one` … `multiplicity_four` | `countBlocks blocks [i] = 1` for `i = 0,1,2,3` | the other coordinates lie in one block |
| `isTDesign_one_false` | `isTDesign 1 blocks = false` | the supports are not a 1-design |
| `not_one_design` | `¬ (isTDesign 1 blocks = true)` | negation form |
| `hypothesis_holds` | `dualDistance ≥ 1 + 1` | the conjecture's hypothesis holds at `t = 1` |
| `conjecture_00000008419_false` | `dualDistance = 2 ∧ minWeight = 3 ∧ isTDesign 1 blocks = false ∧ countBlocks blocks [4] = 2 ∧ countBlocks blocks [0] = 1` | the packaged refutation |

## Proof strategy

- **Everything is a closed computation.** All statements are equalities or
  Boolean equations over the 32 words of length 5, discharged by `decide`. For
  `decide` to reduce, XOR is implemented as explicit Boolean pattern matching
  (`xorB`, `xorList`) instead of `Nat.xor`, which is opaque to the reducer.
- **Dual distance.** `dualWords` filters the 32 words for orthogonality to all
  four codewords; `dualDistance` takes the minimum weight. The explicit dual
  word `01100` and the absence of weight-1 dual words pin `d^⊥ = 2`.
- **Design predicate.** `tSubsets 1` is the list of the five singleton
  coordinate sets; `countBlocks` counts blocks containing a subset;
  `isTDesign` checks that all counts agree. `support_gA`/`support_gB` identify
  the supports as `{2,3,5}` and `{1,4,5}`, and `multiplicity_five` together with
  `multiplicity_one` gives counts `2` and `1`, so `isTDesign_one_false` follows
  by `decide`.

## Scope note

- The formalisation covers the main witness W1 and the literal main clause
  (C1): `d^⊥ = 2 ≥ t+1 = 2` while the minimum-weight codewords are not a
  `1`-design. This is enough to falsify the filed conjecture, whose first clause
  is this implication and whose third clause claims the minimal failure is at
  `d^⊥ = 5`.
- The additional witnesses reported in `reproduce.py` (a minimum-weight-4 code
  W2, the Hamming `[7,4,3]` code W3, the `[6,3,3]` code W4, and the control
  W5) are not separately formalised in Lean; they are checked by exact integer
  computation in `reproduce.py`. They close the alternative readings discussed
  in `../README.md`.
- The phrase "the converse of the Assmus–Mattson theorem" in the filed
  conjecture is not made precise; its exact content is not formalised. The
  refutation does not rely on it.
- No Mathlib, no `Finset` (`import Std` only), no `sorry`. The axiom audit
  reports no `sorryAx`; the only axiom ever reported is `propext`, on the
  theorems whose conclusions are list equalities.
