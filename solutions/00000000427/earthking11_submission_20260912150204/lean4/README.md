# Lean 4 formalisation — status: COMPLETE

This project formalises the disproof of conjecture `00000000427` and targets
**core Lean 4 only** (no Mathlib), with no `sorry`.

```bash
lake build                  # Build completed successfully
lake env lean Check.lean    # prints the axiom dependencies of every theorem
```

The build was verified with the pinned toolchain: `lake build` succeeds and
`Check.lean` reports only the standard core axioms (no `sorryAx`).

## Contents

| file | purpose |
|---|---|
| `Main.lean` | the formalisation |
| `Check.lean` | `#print axioms` for each theorem — the machine-checkable evidence |
| `lakefile.toml` | Lake configuration, no dependencies |
| `lean-toolchain` | pins `leanprover/lean4:v4.33.1` |

## What is formalised

```lean
def oddDF : Nat → Nat
  | 0 => 1
  | n + 1 => (2 * n + 1) * oddDF n

def F (n : Nat) : Rat :=
  mkRat ((2 : Int) ^ (n * n / 4) * (oddDFProd n : Int)) (factProd n)
```

`oddDF i` is `(2i-1)!!`.  Since
`prod_{i=1..n} (2i-1)!!/i! = (prod_{i=1..n} (2i-1)!!) / (prod_{i=1..n} i!)`,
`F n` is the conjectured formula `2^{floor(n^2/4)} * prod_{i=1..n} (2i-1)!! / i!`
as an exact rational, built with `mkRat` from an explicit integer numerator and
natural denominator.

| theorem | statement |
|---|---|
| `oddDF_four` | `oddDF 4 = 105` |
| `oddDFProd_four` | `oddDFProd 4 = 4725` |
| `factProd_four` | `factProd 4 = 288` |
| `F_one` | `F 1 = 1` |
| `F_two` | `F 2 = 3` |
| `F_three` | `F 3 = 15` |
| `F_four` | **`F 4 = 525 / 2`** |
| `F_four_den` | `(F 4).den = 2` |
| `F_four_not_integer` | `(F 4).den ≠ 1` |
| `nat_cast_den` | for every `m : Nat`, `(m : Rat).den = 1` |
| `conjecture_00000000427_false` | **`∀ m : Nat, (m : Rat) ≠ F 4`** |
| `no_nat_eq_F_four` | `¬ ∃ m : Nat, (m : Rat) = F 4` |

The main theorem is `conjecture_00000000427_false`: no natural number equals
`F 4`.  Since a count at `t = 1` is a cardinality and therefore a natural
number, the conjectured equality fails already at `n = 4`.

## Proof structure

1. `oddDF`, `oddDFProd`, `fact`, `factProd` are structurally recursive
   definitions, so all of their closed values (`oddDF 4 = 105` etc.) are
   discharged by `decide`.

2. `F` is built with `mkRat`, whose closed values reduce under `decide` (unlike
   the core operations `Rat.mul` and `Rat.inv`, which are `@[irreducible]`).
   The odd double factorial values give `F 4 = mkRat 75600 288`.

3. `F 4 = 525 / 2`: `Rat.ext` splits the equality into numerator and
   denominator.  Each side is rewritten past `Rat.div`'s irreducible
   multiplication/inversion using the core lemmas `Rat.div_def`,
   `Rat.num_mul`, `Rat.den_mul`, `Rat.num_inv`, `Rat.den_inv`, `Rat.num_ofNat`,
   `Rat.den_ofNat`.  What remains is closed `Int` / `Nat` arithmetic
   (`75600 = 2^4·4725`, `288 = 1!·2!·3!·4!`), discharged by `decide`.  Since
   `gcd 75600 288 = 144`, this is `525/2` in lowest terms.

4. `(F 4).den = 2` is then a closed `decide` check, and `nat_cast_den` records
   that a natural number cast to `Rat` has denominator `1` (core Lean proves
   this by `rfl`: `Rat.den_natCast`).

5. The main theorem applies `congrArg Rat.den` to a hypothetical equality
   `(m : Rat) = F 4`, producing `(m : Rat).den = (F 4).den`, i.e. `1 = 2` after
   rewriting by `nat_cast_den m` and `F_four_den`.  The contradiction `1 ≠ 2`
   is `by decide`.

The mathematical content of the paper — that `v2(F(n)) < 0` for all `n ≥ 4` —
is not reproved in Lean; the formalisation pins the refutation to the single
concrete counterexample `n = 4`, whose closed value `525/2` settles the claim
because a count is a natural number.

## Why core Lean suffices

- **No Mathlib.** The project has no dependencies, so `lake build` needs no
  cache download and completes in about 0.3 s.
- **Only `Rat`, `Nat`, `Int`, and structural recursion are used.** The only
  library facts invoked are `Rat.den_natCast` and the `Rat` rewrite lemmas
  listed above, all part of core Lean.
- **No Mathlib-only tactics.** There is no `norm_num`, `linarith`, or `omega`;
  the proof uses `decide`, `rw`, `simp only`, `intro`, `exact`, `rintro`, and
  `Rat.ext` only.  In particular the closed computations use `decide` (kernel
  reduction), not `native_decide`, so no compiler-trust axiom is introduced.
- **No `sorry`.** `#print axioms` in `Check.lean` is the evidence.

## Axiom dependencies

`lake env lean Check.lean` prints exactly:

```
'Tlmc427.oddDF_four' does not depend on any axioms
'Tlmc427.oddDFProd_four' does not depend on any axioms
'Tlmc427.factProd_four' does not depend on any axioms
'Tlmc427.F_one' depends on axioms: [propext, Classical.choice, Quot.sound]
'Tlmc427.F_two' depends on axioms: [propext, Classical.choice, Quot.sound]
'Tlmc427.F_three' depends on axioms: [propext, Classical.choice, Quot.sound]
'Tlmc427.F_four' depends on axioms: [propext, Classical.choice, Quot.sound]
'Tlmc427.F_four_den' depends on axioms: [propext, Classical.choice, Quot.sound]
'Tlmc427.F_four_not_integer' depends on axioms: [propext, Classical.choice, Quot.sound]
'Tlmc427.nat_cast_den' depends on axioms: [propext, Quot.sound]
'Tlmc427.conjecture_00000000427_false' depends on axioms: [propext, Classical.choice, Quot.sound]
'Tlmc427.no_nat_eq_F_four' depends on axioms: [propext, Classical.choice, Quot.sound]
```

These are the standard core axioms (`propext`, `Quot.sound`, and
`Classical.choice`, pulled in by the `Rat` library).  There is no `sorryAx` and
no `Lean.ofReduceBool`.

## Environment

Lean 4 `v4.33.1` (pinned by `lean-toolchain`), core only, no Mathlib.
