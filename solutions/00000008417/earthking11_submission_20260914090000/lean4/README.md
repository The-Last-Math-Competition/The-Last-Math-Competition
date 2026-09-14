# Lean 4 formalisation — refutation of conjecture `00000008417`

Core Lean only (`import Std`), no Mathlib, no `sorry`. The project pins
`lean-toolchain` to `leanprover/lean4:v4.33.1` and defines the library `Main` in
`lakefile.toml` (`name = "tlmc8417"`).

## Build and audit

```sh
cd lean4
lake build
lake env lean Check.lean
```

Measured on the development machine (Apple Silicon, Lean 4.33.1):

```
✔ [2/3] Built Main (63s)
Build completed successfully (3 jobs).
real 63.43   user 120.31   sys 4.46
```

`lake build` wall time: **≈63 s** (dominated by the kernel reduction of the
single heavy theorem `every_five_in_exactly_one_block`). `lake env lean
Check.lean` then runs in ≈0.6 s because the compiled `Main.olean` is reused.
The whole project builds from scratch with no cache download and no
dependencies.

## What is formalised

The witness is the small Witt design W_12 = S(5,6,12). Points are `0..11`; a
subset is a 12-bit `Nat` mask (bit `i` = point `i`). Because `Nat.popcount` and
`Nat.digits` are **absent** from this core, `popcount` is defined by hand over
bits `0..11`:

```lean
def popcount (n : Nat) : Nat :=
  (List.range 12).foldl (fun a i => a + (if Nat.testBit n i then 1 else 0)) 0

def blocks : List Nat := [ ...132 six-bit masks... ]            -- W_12
def fives : List Nat := (List.range 4096).filter (fun m => popcount m == 5)
def covered (m : Nat) : Nat := (blocks.filter (fun b => (m &&& b) == m)).length
```

The 132 masks in `blocks` are **bit-for-bit identical** to the design produced
by `reproduce.py` via exact cover.

| Theorem | Statement | Role |
|:--------|:----------|:-----|
| `blocks_all_popcount_six` | `blocks.all (fun b => popcount b == 6) = true` | every block has size 6 |
| `blocks_nodup` | `blocks.Nodup` | the 132 blocks are distinct |
| `blocks_length` | `blocks.length = 132` | block count |
| `fives_all_popcount_five` | `fives.all (fun m => popcount m == 5) = true` | the 5-subsets are exactly the popcount-5 masks |
| `fives_length` | `fives.length = 792` | `C(12,5) = 792` |
| `total_incidences` | `blocks.foldl (fun a b => a + popcount b) 0 = 792` | `132·6 = 792` |
| `every_five_in_exactly_one_block` | `fives.all (fun m => covered m == 1) = true` | **existence certificate: a 5-(12,6,1) design** |
| `every_five_covered` | `fives.all (fun m => 1 ≤ covered m) = true` | covering form |
| `div_i0 … div_i5` | `792 = 132·6`, `330 = 66·5`, `120 = 30·4`, `36 = 12·3`, `8 = 4·2`, `1 = 1·1` | the six divisibility conditions |
| `divisibility_conditions_hold` | conjunction of the six | all six hold at `(5,6,12)` |
| `IsDesign5612` | `B.Nodup ∧ B.length = 132 ∧ … ∧ every 5-subset exactly once` | Prop-level design predicate |
| `witt_is_design` | `IsDesign5612 blocks` | the explicit blocks form a design |
| `exists_S5612` | `∃ B, IsDesign5612 B` | **a 5-(12,6,1) design exists** |
| `exists_and_divisible` | `(∃ B, IsDesign5612 B) ∧ (792 = 132·6)` | existence *and* divisibility at `n = 12` |

## How the certificate works

- The 132 masks list every 6-subset of `{0,…,11}` that is a block of W_12.
  `covered m` counts the blocks containing the 5-subset `m` by the bit test
  `(m &&& b) == m`.
- `every_five_in_exactly_one_block` scans the 792 five-subsets against the 132
  blocks and proves, by `decide`, that every count is exactly 1. This single
  kernel reduction is what takes ≈63 s. `set_option maxRecDepth 1000000` and
  `set_option maxHeartbeats 0` are set for it.
- The six divisibility conditions are proved as exact products, so no
  divisibility obligation is left open.

## Axiom audit

`lake env lean Check.lean` reports (verbatim excerpt):

```
'Tlmc8417.blocks_all_popcount_six' depends on axioms: [propext]
'Tlmc8417.blocks_nodup' does not depend on any axioms
'Tlmc8417.blocks_length' does not depend on any axioms
'Tlmc8417.fives_all_popcount_five' depends on axioms: [propext]
'Tlmc8417.fives_length' depends on axioms: [propext]
'Tlmc8417.total_incidences' depends on axioms: [propext]
'Tlmc8417.every_five_in_exactly_one_block' depends on axioms: [propext]
'Tlmc8417.every_five_covered' depends on axioms: [propext]
'Tlmc8417.div_i0' does not depend on any axioms
'Tlmc8417.div_i1' does not depend on any axioms
'Tlmc8417.div_i2' does not depend on any axioms
'Tlmc8417.div_i3' does not depend on any axioms
'Tlmc8417.div_i4' does not depend on any axioms
'Tlmc8417.div_i5' does not depend on any axioms
'Tlmc8417.divisibility_conditions_hold' does not depend on any axioms
'Tlmc8417.witt_is_design' depends on axioms: [propext]
'Tlmc8417.exists_S5612' depends on axioms: [propext]
'Tlmc8417.exists_and_divisible' depends on axioms: [propext]
```

The only axiom appearing is `propext`. In particular **`sorryAx` is absent**, and
because the heavy theorem uses kernel `decide` (not `native_decide`) there is
**no `Lean.ofReduceBool`** either. This is the fully kernel-checked variant.

## Scope note

- The certificate is an **existence at `n = 12`**: `exists_S5612` exhibits a
  concrete 5-(12,6,1) design and proves it is one. Consequently any existence
  threshold function satisfies `n_0(5,6) ≤ 12`.
- Uniqueness of W_12 up to isomorphism is a classical theorem of Witt; it is not
  needed for the refutation (existence alone contradicts `n_0(5,6) > 12`) and is
  not formalised here. It is checked computationally in `reproduce.py`
  (`|Aut(W_12)| = 95040 = |M_12|`).
- The general "exists iff divisibility for large `n`" direction (Keevash's
  theorem, non-effective) is **not** disputed and is not formalised; this
  submission targets only the definite false conjunct `n_0(5,6) > 12`.
- No real analysis (e.g. asymptotics of `(kt)^{ct}`) is formalised; the Lean
  content is precisely the finite existence certificate and the six divisibility
  identities.

## Environment

Lean 4.33.1, Lake 5.0.0, no Mathlib, no external dependencies. `lake build`
needs no cache download.
