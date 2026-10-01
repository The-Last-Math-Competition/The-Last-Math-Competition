# Lean certificate for the disproof of conjecture 00000000556

Conjecture: `HH¹(Λ) = 0` iff Λ is representation-finite and rigid.

Counterexample: Λ = k[x]/(x²) (dual numbers) — representation-finite and rigid
(Frobenius ⇒ self-injective), but `HH¹(Λ) ≅ k ≠ 0`.

This library instantiates the computational core over the base `Nat`:
`L = Nat × Nat` with `(a, b) * (c, d) = (a*c, a*d + b*c)`, i.e. `a + b·x`, `x² = 0`.
The `Nat` base keeps every proof pure-constructive; the same computation over
`Int` or an arbitrary field is done in `reproduce.py` / `main.tex`.

Main results (see `Main.lean`):

| theorem | content |
|---|---|
| `d556_leib`, `d556_is_derivation` | `d(1) = 0`, `d(x) = x` (i.e. `d = x·∂`) is a derivation |
| `ad_zero` | every inner derivation vanishes (Λ commutative): `Inn = 0` |
| `d556_not_inner`, `hh1_nonzero` | `x·∂` is a non-inner derivation: `HH¹ ≠ 0` |
| `deriv_apply`, `deriv_scalar` | classification `f(a,b) = (0, b·q)`: `Der ≅ Nat`, `HH¹ ≅ Nat` |
| `frobenius_nondegenerate` | Frobenius form nondegenerate: Λ self-injective (rigid) |
| `dualnumbers_certificate` | conjunction of all of the above |

## Build and verify

```sh
lake build
lake env lean Check.lean
```

`Check.lean` prints `... does not depend on any axioms` for every theorem:
**zero axioms (no `propext`, no `Quot.sound`, no `Classical.choice`), zero `sorry`.**
Requires `leanprover/lean4:v4.33.1` (core only, no Mathlib, no dependencies).

Note: derivations are represented as a subtype `Der` of `L → L` (`f.1` is the
underlying function); `f.2.1`/`f.2.2.1`/`f.2.2.2` are additivity, `f(1) = 0`
and the Leibniz rule.
