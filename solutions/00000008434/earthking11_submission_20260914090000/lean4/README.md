# Lean 4 formalisation — disproof of conjecture `00000008434`

Core Lean only (`import Std`), no Mathlib, no `sorry`. The project pins
`lean-toolchain` to `leanprover/lean4:v4.33.1` and defines the library `Main`
in `lakefile.toml` (name `tlmc8434`).

## Build and audit

```sh
lake build
lake env lean Check.lean
```

`Check.lean` prints `#print axioms` for every theorem so a reviewer can confirm
the absence of `sorryAx` and of Mathlib dependencies.

## Encoding

There is no `Nat.popcount`, no `Finset` and no `ZMod` in `import Std`, so
everything is done with `Nat` and `List`:

* a block is an 8-bit `Nat` mask (bit `i` = point `i`);
* `pc m` is the population count, defined as the structural fold
  `(List.range 9).foldl (fun a i => if m.testBit i then a + 1 else a) 0`;
* `b &&& c` (`Nat.land`) is the intersection of two blocks;
* `spec` is the intersection spectrum, defined by structural recursion over the
  list of blocks,

  ```lean
  def spec : List Nat → List Nat
    | [] => []
    | b :: bs => (bs.map (fun c => pc (b &&& c))) ++ spec bs
  ```

  This structural recursion is essential: it reduces in the kernel, whereas a
  well-founded definition would not, so the `decide` proofs below would fail.

All goals are closed by kernel `decide` under
`set_option maxRecDepth 1000000`. No `sorry`, no `native_decide`, no axioms
beyond `propext`.

## What is formalised

```lean
def blocks : List Nat := [15,51,60,85,90,102,105,150,153,165,170,195,204,240]
def triples : List Nat := (List.range 256).filter (fun m => pc m == 3)
def countIn (T : Nat) : Nat := (blocks.filter (fun B => (T &&& B) == T)).length
def s0 : Nat := (spec blocks).foldl Nat.min 1000
def s1 : Nat := (spec blocks).foldl Nat.max 0
def inSpectrum (i : Nat) : Bool := (spec blocks).any (fun s => s == i)
def IntervalSpectrum : Prop := ∀ i : Nat, s0 ≤ i → i ≤ s1 → inSpectrum i = true
def intervalFull : Bool := (List.range (s1 - s0 + 1)).all (fun i => inSpectrum (s0 + i))
```

| Theorem | Statement | Role |
|:--------|:----------|:-----|
| `blocks_length` | `blocks.length = 14` | the 14 affine planes |
| `blocks_size_four` | all blocks have `pc = 4` | planes have 4 points |
| `blocks_distinct` | the 14 masks are pairwise distinct | genuine 14 blocks |
| `triples_length` | `triples.length = 56` | `C(8,3) = 56` triples |
| `each_triple_in_one_block` | every triple has containment count 1 | **`AG(3,2)` is a `3-(8,4,1)` design** |
| `ag32_is_3_8_4_1` | bundle of the four facts above | the SQS certificate |
| `spectrum_length` | `(spec blocks).length = 91` | `C(14,2) = 91` pairs |
| `spectrum_values` | every intersection is `0` or `2` | spectrum ⊆ `{0,2}` |
| `spec_count_zero` | `7` pairs intersect in `0` | multiplicity of 0 |
| `spec_count_one` | `0` pairs intersect in `1` | **the missing value** |
| `spec_count_two` | `84` pairs intersect in `2` | multiplicity of 2 |
| `s0_eq`, `s1_eq` | `s0 = 0`, `s1 = 2` | the interval `[0,2]` |
| `one_absent` | no spectrum entry equals `1` | `1` is absent |
| `intervalFull_false` | the Boolean sweep over `[s0,s1]` is `false` | **clause 1 fails** |
| `interval_missing_value` | `∃ i, s0 ≤ i ∧ i ≤ s1 ∧ inSpectrum i = false` | explicit witness `i = 1` |
| `intervalSpectrum_false` | `¬ IntervalSpectrum` | **clause 1 fails, `Prop` form** |
| `conjecture_first_clause_false` | `s0 = 0 ∧ s1 = 2 ∧ ¬ IntervalSpectrum` | bundled |
| `pasch_length`, `pasch_block_size` | `pasch.length = 4`, all size 3 | the Pasch design |
| `pasch_spectrum_length` | `(spec pasch).length = 6` | `C(4,2) = 6` pairs |
| `pasch_spectrum_all_one` | every Pasch intersection is `1` | constant intersection |
| `pasch_s0_eq_s1` | `min = max` for the Pasch spectrum | `s0 = s1` |
| `pasch_is_1_design` | each of the 6 points lies in exactly 2 blocks | `1-(6,3,2)` |
| `pasch_not_symmetric` | `¬ Symmetric 4 6` | `b = 4 ≠ 6 = v` |
| `second_clause_fails` | `s0 = s1 ∧ ¬ Symmetric` for Pasch | **clause 2 fails for 1-designs** |

## Proof strategy

There is no clever proof: the objects are finite and tiny, and every statement
is a closed `Bool`/`Nat` computation. `decide` evaluates the definitions in the
kernel, and `set_option maxRecDepth 1000000` raises the recursion limit enough
for the largest goal (`each_triple_in_one_block`, 56 triples against 14 blocks,
and `intervalFull_false`). The only non-computational steps are

* unfolding the `abbrev Symmetric` so that `Decidable` can be synthesised, and
* the `Prop`-level negation `intervalSpectrum_false`, which instantiates the
  universally quantified `IntervalSpectrum` at `i = 1`: the hypothesis gives
  `inSpectrum 1 = true` while `decide` gives `inSpectrum 1 = false`, a
  contradiction closed by `cases`.

No indexing, no well-founded recursion, and no Mathlib are involved.

## Axiom audit

`lake env lean Check.lean` reports:

* `blocks_length`, `blocks_distinct`, `pasch_length`, `pasch_not_symmetric`:
  **no axioms**;
* every other theorem: `propext` only.

No `sorryAx` appears for any theorem. The build pins
`leanprover/lean4:v4.33.1` and needs no cache download; `lake build` completes
in about 5 seconds.

## Scope note

* The formalisation proves the negation of clause 1 for the explicit witness
  `AG(3,2)` — which is all that is needed to disprove a universally quantified
  conjecture — and the negation of clause 2 for the explicit Pasch 1-design.
* It also proves the positive structural facts (`3-(8,4,1)`, all block sizes 4,
  all 91 intersection sizes, the multiplicities 0:7/1:0/2:84), so the witness
  cannot be dismissed as an artefact of a degenerate reading.
* The general statement "for a genuine 2-design, constant pairwise intersection
  forces `b = v`" is proved on paper in `main.tex` and is **not** formalised; it
  is a fairness remark, not part of the refutation.
* The encoding is 8-bit and specific to `AG(3,2)` and the Pasch design; no
  general design theory is developed. This is intentionally minimal: the claim
  is existential, and a single verified counterexample suffices.
