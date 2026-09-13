# Lean 4 formalisation — disproof of conjecture `00000000418`

Core Lean only (`import Std`), no Mathlib, no `sorry`. The project pins
`lean-toolchain` to `leanprover/lean4:v4.33.1` and defines the library `Main` in
`lakefile.toml` (project name `tlmc418`).

## Build and audit

```sh
lake build
lake env lean Check.lean
```

`Check.lean` prints `#print axioms` for every theorem. Observed output: every
theorem reports either `does not depend on any axioms` or `depends on axioms:
[propext]`; no `sorryAx` and no Mathlib axiom appears anywhere.

## The claim and the two readings

The conjecture (as filed) says that the proportion of *lattice* words of weight
λ among *Yamanouchi* words of weight λ equals
`f^λ / (n! · K_{λ,λ})`, attaining a maximum `1/2^{n-1}` at rectangles. Its own
definition supplies two readings of "lattice word":

* **Reading (A)**: the parenthetical in "Yamanouchi (lattice) word" makes
  "lattice" a synonym of "Yamanouchi". The proportion is then `1` identically.
* **Reading (B)**: "a lattice word is one appearing as the reading word of a
  standard tableau". Reading words are permutations, of weight `(1^n)`.

The formalisation refutes the conjecture at `λ = (2,1)`, `n = 3`, under both
readings. It documents, for each theorem, which reading it addresses (the names
carry `A`/`B` suffixes, and the file comments state the reading explicitly).

## What is formalised

Words of length `3` over `{1,2}` are enumerated with `List.range`, and the
numerical facts are closed by `decide`. Rational comparisons are done by
*cross-multiplication in `Nat`*, never with `Rat` (whose operations `decide`
cannot reduce). `Nat.factorial` is not in `import Std`, so a local `fact` is
defined. No function equality is decided; tableaux are lists of rows.

| Theorem | Statement | Reading / role |
|:--------|:----------|:---------------|
| `allWords3_length` | `allWords3.length = 8` | enumeration of the 8 words of length 3 over `{1,2}` |
| `word_112_isYam`, `word_121_isYam` | `isYam 112 = true`, `isYam 121 = true` | prefix (Yamanouchi) condition |
| `word_211_not_yam` | `isYam 211 = false` | `211` fails: prefix `2` has counts `(0,1)` |
| `yamWords21_eq` | `yamWords21 = [[1,1,2],[1,2,1]]` | exactly two Yamanouchi words of weight `(2,1)` |
| `card_yamWords21`, `numYam21_eq` | `yamWords21.length = 2` | count of Yamanouchi words = 2 |
| `card_syts21` | `syts21.length = 2` | the two standard tableaux of shape `(2,1)` |
| `latticeReading_syt21a/b` | readings `= [1,1,2]`, `= [1,2,1]` | row-index reading of the two SYT |
| `latticeReadings21_eq` | `latticeReadings21 = [[1,1,2],[1,2,1]]` | row-index readings |
| `yam_eq_latticeReadings` | `yamWords21 = latticeReadings21` | every Yamanouchi word of weight `(2,1)` is a reading word (A) |
| `every_yam_is_latticeReading` | `∀ w ∈ yamWords21, w ∈ latticeReadings21` | membership form of the above |
| `numLattice21_A_eq` | `numLattice21_A = 2` | reading (A): # lattice words = # Yamanouchi words = 2 |
| `entryReading_syt21a/b` | readings `= [3,1,2]`, `= [2,1,3]` | entry reading of the two SYT (reading B) |
| `entryReading_weight_111` | the entry readings have content `(1,1,1)` | reading (B): reading words are permutations |
| `numLattice21_B_eq` | `numLattice21_B = 0` | reading (B): no lattice word of weight `(2,1)` |
| `hookProduct21_eq`, `fact3_eq`, `f21_eq` | `3·1·1 = 3`, `3! = 6`, `f^(2,1) = 2` | hook-length formula |
| `f21_eq_card_syts21` | `f21 = syts21.length` | hook-length count matches enumerated SYT |
| `ssyt21_21_eq`, `K21_eq` | `ssyt21_21 = [[1,1,2]]`, `K21 = 1` | `K_{(2,1),(2,1)} = 1` by brute force |
| `claimNum_eq`, `claimDen_eq` | `2`, `6` | conjectured value is `2/(6·1)` |
| `propNumA_eq`, `propDenA_eq` | `2`, `2` | reading (A) proportion `2/2` |
| `proportionA_is_one` | `propNumA = propDenA` | reading (A) proportion equals 1 |
| `claim_not_one` | `claimNum ≠ claimDen` | `2/6 ≠ 1` |
| `proportionA_ne_claim` | `propNumA * claimDen ≠ claimNum * propDenA` | **reading (A) contradiction**: `2/2 ≠ 2/6` |
| `cross_values` | `12` and `4` | cross products `2·6` and `2·2` |
| `twelve_ne_four` | `12 ≠ 4` | numeric core of the contradiction |
| `proportionB_ne_claim` | `propNumB * claimDen ≠ claimNum * propDenB` | **reading (B) contradiction**: `0/2 ≠ 2/6` |
| `quarter_lt_one` | `1·1 < 4·1` | `1/4 < 1` |
| `proportionA_exceeds_max` | `propNumA * 4 > 1 * propDenA` | reading (A) proportion exceeds `1/2^{n-1} = 1/4` |
| `f3_eq`, `f111_eq` | `f^(3) = 1`, `f^(1,1,1) = 1` | the two rectangle shapes of size 3 |
| `nonrectangle_beats_rectangles` | `f21 * 6 > f3 * 6` | the non-rectangle `(2,1)` maximises `f^λ/n!` |
| `rectangle_not_max` | `f3 * 4 ≠ 1 * 6` | the rectangle value `1/6` is not `1/4` |
| `max_claim_wrong_for_formula` | `f21 * 4 > 1 * 6` | `f^(2,1)/3! = 1/3 > 1/4` |
| `conjecture_00000000418_refuted` | conjunction of the above | the collected disproof |

## Proof strategy

* **`isYam`** is `(List.range (w.length + 1)).all (fun m => countOcc (w.take m) 1 ≥ countOcc (w.take m) 2)`:
  in every prefix the count of `1` is at least the count of `2`, which for a
  two-letter alphabet is exactly "the prefix counts form a partition".
* **`yamWords21`** filters `allWords3` (the 8 words of length 3 over `{1,2}`)
  by `isYam` and by having content `(2,1)`. `decide` evaluates the filter and
  proves the result is `[[1,1,2],[1,2,1]]`, hence a count of `2`.
* **Readings.** `latticeReading` sends an SYT to the word of 1-based row indices
  of the entries `1,2,3`; this is the standard bijection SYT ↔ lattice words.
  `decide` proves `latticeReading syt21a = [1,1,2]` and
  `latticeReading syt21b = [1,2,1]`, so this reading recovers exactly the
  Yamanouchi words (reading (A)). `entryReading` reads entries bottom-to-top;
  `decide` proves the readings are `[3,1,2]` and `[2,1,3]`, whose content is
  `(1,1,1)`, so none has weight `(2,1)` (reading (B)).

  *Note on conventions.* The task is to prove that every Yamanouchi word of
  weight `(2,1)` is "a reading word", so the reading used for reading (A) is the
  row-index reading, under which the statement is true; the entry reading is
  used for reading (B), under which the statement fails and the proportion is
  `0`.
* **Hook lengths and `K`.** `f21 = fact 3 / (3*1*1) = 2`; the semistandard
  tableaux of shape and content `(2,1)` are enumerated by filtering the same
  list of 8 fillings against the row/column conditions, giving the single
  superstandard tableau `[[1,1,2]]`, so `K21 = 1`.
* **Contradiction.** `claimNum/claimDen = 2/6` and the two proportions are
  `2/2` (reading A) and `0/2` (reading B). Fractions are compared by
  cross-multiplication in `Nat`: `2·6 ≠ 2·2` (`12 ≠ 4`) and `0·6 ≠ 2·2`
  (`0 ≠ 4`). `1/4 < 1` is likewise `1·1 < 4·1`, and the reading-(A) proportion
  exceeds `1/4` since `2·4 > 1·2`.

## Scope note

The formalisation fixes the two smallest counterexample-reading pairs rather
than the full general statement:

* under reading (A) the proportion is `1` for every `λ`, and the file proves
  this at `λ = (2,1)` together with the numeric contradiction `12 ≠ 4` against
  the claimed `2/6`;
* under reading (B) the file proves at `λ = (2,1)` that entry reading words have
  weight `(1,1,1) ≠ (2,1)` and hence that the proportion is `0/2 = 0`.

The general collapse `K_{λ,λ} = 1 ⇒ claimed value = f^λ/n!`, the identity
`#Yamanouchi words of weight λ = f^λ`, and the non-rectangularity of the
maximisers of `f^λ/n!` for `n = 3, 5, 6` are proved/verified in
`main.tex` and by exhaustive computation in `reproduce.py`; reproducing them in
Lean for all `λ` would require a general theory of Young tableaux that is
outside core Lean.

## Environment

Lean 4.33.1, Lake, no Mathlib. `lake build` needs no cache download and
succeeds in under a second; `lake env lean Check.lean` prints the axiom audit.
