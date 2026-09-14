# Lean 4 formalisation — disproof of conjecture `00000000429`

Core Lean only (`import Std`), no Mathlib, no `sorry`. The project pins
`lean-toolchain` to `leanprover/lean4:v4.33.1` and defines the library `Main`
(project name `tlmc429`) in `lakefile.toml`.

## Build and audit

```sh
lake build
lake env lean Check.lean
```

`Check.lean` prints `#print axioms` for every theorem so a reviewer can confirm
the absence of `sorryAx` and of Mathlib dependencies. The observed output
reports only `propext` and `Quot.sound` for the general statements, and no
axioms at all for the concrete integer evaluations.

## What is formalised

The q-binomial coefficient is evaluated at `q = -1` by the exact **integer**
Pascal recursion

```lean
/-- [n choose k]_{q=-1} by the integer Pascal recursion. -/
def qb : Nat → Nat → Int
  | _, 0 => 1
  | 0, _+1 => 0
  | n+1, k+1 => qb n k + (-1 : Int)^(k+1) * qb n (k+1)
```

This is the value of `[n choose k]_q` at `q = -1`:
`[n choose k]_{q} = [n-1 choose k-1]_q + q^k [n-1 choose k]_q`, and at `q = -1`
the factor `q^k` becomes `(-1)^k` (the index `k+1` appears because the third
equation is indexed by `n+1, k+1`). There is **no division and no `Rat`**, so
`decide` can reduce concrete instances by kernel computation. (The naive product
formula is `0/0` at `q = -1` and is deliberately not used.)

| Theorem | Statement | Role |
|:--------|:----------|:-----|
| `qb_6_2` | `qb 6 2 = 3` | **decisive witness**: `3` is not a signed power of two |
| `qb_8_4` | `qb 8 4 = 6` | further witness (also kills the even-`n` restriction) |
| `qb_7_3` | `qb 7 3 = 3` | further witness |
| `qb_10_2` | `qb 10 2 = 5` | further witness |
| `qb_2_1` | `qb 2 1 = 0` | smallest value not a power of two at all |
| `pow2_ne_three` | `∀ t : Nat, (2:Int)^t ≠ 3` | `3` is not an unsigned power of two (induction on `t`) |
| `negpow2_ne_three` | `∀ t : Nat, -((2:Int)^t) ≠ 3` | `3` is not a negated power of two (`Int.pow_pos`) |
| `six_eq_two_mul_three` | `(6:Int) = 3*2` | `6` *is* signed-power2, so it is not misused as a signed witness |
| `not_pow2_unsigned` | `¬ ∀ n k, ∃ t, qb n k = 2^t` | **the literal (unsigned) claim fails** |
| `not_pow2_signed` | `¬ ∀ n k, ∃ t, qb n k = 2^t ∨ qb n k = -2^t` | **the signed reading fails too** |
| `conjecture_00000000429_false` | `¬ ∃ v, ∀ n k, qb n k = 2^(v n k)` | the conjecture, stated for an arbitrary `v` |
| `conjecture_00000000429_false_signed` | `¬ ∃ v, ∀ n k, qb n k = 2^(v n k) ∨ qb n k = -(2^(v n k))` | signed variant |

The last two are the formal versions of the conjecture as filed: they quantify
over *every* candidate valuation formula `v : Nat → Nat → Nat`, so the failure
is not an artefact of one particular choice of `v`.

## Proof strategy

- **Concrete values** (`qb_6_2`, `qb_8_4`, `qb_7_3`, `qb_10_2`, `qb_2_1`).
  `qb` is defined by structural recursion with no division, so the kernel
  reduces `qb 6 2` to the literal `3`; `decide` closes the goal.
- **`pow2_ne_three`** by induction on `t`. Base `t = 0`: `1 ≠ 3` by `decide`.
  Step: rewrite `2^(t+1) = 2^t * 2` (`Int.pow_succ`) and let `omega` refute the
  integer equation `2^t * 2 = 3` (the coefficient `2` is linear in the atom
  `2^t`; `2*x = 3` has no integer solution).
- **`negpow2_ne_three`**: `Int.pow_pos` gives `0 < 2^t`, so `-2^t < 0 < 3` and
  `omega` closes.
- **`not_pow2_unsigned` / `not_pow2_signed`**: instantiate the claimed
  universally quantified statement at `(n,k) = (6,2)`, rewrite `qb 6 2` to `3`,
  and dispatch the two cases with `pow2_ne_three` / `negpow2_ne_three`.
- **The conjecture statements** are immediate from the above by providing the
  candidate `v`'s value at `(6,2)`.

## Pitfalls avoided (verified in this environment)

- `norm_num` is a **Mathlib** tactic and is absent under `import Std`; it is not
  used.
- The generic names `pow_succ` / `pow_pos` are absent; the `Int`-qualified
  `Int.pow_succ` / `Int.pow_pos` are used.
- `Nat.factorial` is not in `Std` (irrelevant here, but noted).
- `decide` **cannot** reduce `Rat`, which is why the recursion is stated over
  `Int` rather than `Rat`.
- No `sorry`, and the audit reports no `sorryAx`.

## Axiom audit

`lake env lean Check.lean` reports:

- `qb`, `qb_6_2`, `qb_8_4`, `qb_7_3`, `qb_10_2`, `qb_2_1`,
  `six_eq_two_mul_three`: **no axioms**;
- `pow2_ne_three`, `negpow2_ne_three`, `not_pow2_unsigned`, `not_pow2_signed`,
  `conjecture_00000000429_false`, `conjecture_00000000429_false_signed`:
  `propext`, `Quot.sound`.

No `sorryAx` appears for any theorem.

## Scope note

- The refutation is symbolic, not a finite check: `not_pow2_signed` holds for
  the *whole* family `qb n k`, and the conjecture statements quantify over all
  `v`. Only the arithmetic facts `qb 6 2 = 3` and `3 ≠ ±2^t` are needed, and
  both are proved in general (`pow2_ne_three` is a theorem about every `t`).
- The q-Lucas characterisation of the *whole* table (the correct description)
  is stated and verified in `reproduce.py` (0 mismatches for `n ≤ 20`) and
  proved informally in `main.tex`; it is not formalised in Lean, since the
  refutation does not require it. The Lean content is precisely what is needed
  to defeat the claim for an arbitrary `v`.
- `v_2` and Kummer's theorem are likewise not formalised; they are context, not
  part of the refutation.

## Environment

Lean 4.33.1, Lake, no Mathlib. `lake build` needs no cache download and
compiles in well under a second (`Built Main (592ms)`).
