# Lean 4 verification (tlmc7986)

Machine-checked verification of the disproof of conjecture 00000007986
(main clause: `rho(C) <= n - sqrt(n d)` for codes with nontrivial
2-transitive automorphism group).

Toolchain: `leanprover/lean4:v4.33.1` (core only, no external dependencies).

## Theorems (namespace `Tlmc7986`)

| Theorem | Statement | Meaning |
|---|---|---|
| `rho_C4` | `coverRad4 = 2` | covering radius of the repetition code C4 = {0000, 1111} in F_2^4, computed by exhaustive enumeration of all 16 points |
| `refute_bound_4` | `¬ ((2:Int) ≤ (4:Int) - 4)` | the conjectured bound for C4 is 4 - sqrt(4*4) = 0, and `rho = 2 <= 0` is false |
| `rho_C2` | `coverRad2 = 1` | covering radius of C2 = {00, 11} in F_2^2 (4-point enumeration) |
| `refute_bound_2` | `¬ ((1:Int) ≤ (2:Int) - 2)` | the conjectured bound for C2 is 2 - sqrt(2*2) = 0, and `rho = 1 <= 0` is false |

Hypothesis check (also machine-relevant): both codes are stabilized
setwise by the full coordinate-permutation group `S_n` acting on
`F_2^n`, which is nontrivial and 2-transitive for `n >= 2`, so both
counterexamples satisfy the conjecture's hypothesis.

## Build and check

```bash
lake build
lake env lean Check.lean
```

`Check.lean` prints the computed covering radii and runs `#print axioms`
on all four theorems. Expected output:

```
"coverRad4 = 2   (expected 2)"
"coverRad2 = 1   (expected 1)"
'Tlmc7986.rho_C4' does not depend on any axioms
'Tlmc7986.refute_bound_4' does not depend on any axioms
'Tlmc7986.rho_C2' does not depend on any axioms
'Tlmc7986.refute_bound_2' does not depend on any axioms
```

Zero axioms, no `sorry`.

## Implementation notes

- `coverRad4`/`coverRad2` are plain computable definitions:
  explicit lists of the 16 (resp. 4) points of `F_2^n`, Hamming distance
  via `List.finRange n` + `List.filter`, and a hand-rolled structurally
  recursive `listMax`. (Core Lean 4.33.1 has no `List.maximum`, and
  proof-carrying substitutes do not reduce under `decide`.)
- The covering-radii theorems are proved by `rfl`, i.e. direct kernel
  evaluation, which yields axiom-free proof terms. (The `decide` tactic
  pulls in `propext` through its rewriting lemmas, which would spoil the
  zero-axiom property; the numeric `Int` refutations below remain
  `decide`-proved and are axiom-free.)
- The refuted inequalities are stated over `Int` because the exact value
  of the bound `n - sqrt(n d)` is the integer `4 - 4 = 0` (resp.
  `2 - 2 = 0`) — `n*d` is a perfect square — and core Lean's `Rat` lacks
  the usual `OfNat`/`LE`/`HSub` instances. The statement is identical in
  content: `rho <= 0` fails.
- Numeral notation for `Fin` (e.g. `(0 : Fin 2)`) drags `propext` into
  definitions through its `OfNat` instance proof, so the digits are
  constructed explicitly with basic `Nat` lemmas
  (`Nat.zero_le`, `Nat.succ_le_succ`, `Nat.lt_of_succ_le`), and `mk4`/
  `mk2` dispatch on `i.val` by pattern matching.

## Files

- `lakefile.toml` — lake config (`defaultTargets = ["Main"]`, lean_lib `Main`)
- `lean-toolchain` — `leanprover/lean4:v4.33.1`
- `Main.lean` — definitions and the four theorems
- `Check.lean` — `#eval` of the computed radii + `#print axioms` for all theorems
