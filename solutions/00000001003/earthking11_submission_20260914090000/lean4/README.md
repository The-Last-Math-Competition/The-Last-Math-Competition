# Lean 4 formalisation — disproof of conjecture `00000001003`

Core Lean only (`import Std`), no Mathlib, no `sorry`, no `native_decide`. The
project pins `lean-toolchain` to `leanprover/lean4:v4.33.1` and defines the
library `Main` in `lakefile.toml`.

## Build and audit

```sh
cd lean4
lake build
lake env lean Check.lean
```

`lake build` exits `0` (about 7 seconds on an Apple-silicon laptop, first build).
`Check.lean` prints `#print axioms` for every theorem so a reviewer can confirm
that nothing depends on `sorryAx`, on `Lean.ofReduceBool` (the `native_decide`
marker), or on Mathlib.

## What is formalised

The conjecture claims that the maximal cap size in `PG(4,q)` is

```
q^2 + q + 1 + floor((q+1)/3)   for all odd q.
```

At `q = 3` this formula evaluates to `9 + 3 + 1 + 1 = 14`. The Lean development
exhibits an explicit, executable 20-point cap in `PG(4,3)`, so the maximum is at
least `20 > 14` and the `q = 3` instance (an odd prime power) is false.

```lean
/-- The conjecture's formula at a prime power `q`. -/
def formula (q : Nat) : Nat := q * q + q + 1 + (q + 1) / 3

/-- Executable cap test: no three distinct points of `S` are collinear. -/
def isCap (S : List Pt) : Bool := ...

/-- The explicit 20-point cap in PG(4,3). -/
def pts20 : List Pt := ...
```

| Theorem | Statement | Role |
|:--------|:----------|:-----|
| `isCap_collinear_false` | `isCap collinearTriple = false` | non-vacuity: the test rejects a real collinear triple |
| `isCap_independent_true` | `isCap independentTriple = true` | non-vacuity: the test accepts a non-collinear triple |
| `bad_witness` | `bad (1,0,0,0,0) (0,1,0,0,0) (1,1,0,0,0) = true` | direct witness that the collinearity predicate fires |
| `pts20_nodup` | `pts20.Nodup` | the 20 points are pairwise distinct |
| `pts20_length` | `pts20.length = 20` | the cap has exactly 20 points |
| `pts20_isCap` | `isCap pts20 = true` | **no three of the 1140 triples are collinear** |
| `formula_three` | `formula 3 = 14` | the conjecture predicts 14 at q = 3 |
| `twenty_gt_fourteen` | `(20 : Nat) > 14` | the arithmetic fact |
| `formula_three_lt_length` | `formula 3 < pts20.length` | the formula's value is below the cap |
| `refutes_conjecture` | `∃ S, S.length = 20 ∧ isCap S = true ∧ formula 3 < S.length` | **main refutation** |
| `conjecture_00000001003_false` | `∃ S, isCap S = true ∧ S.length = 20 ∧ formula 3 = 14 ∧ 20 > 14` | the same, with the numbers spelled out |

## Representation and executability

A point of `PG(4,3)` is a `structure Pt` with five `Nat` fields, deriving
`DecidableEq, Repr, BEq`. This is deliberate:

- `ZMod`, `Finset` and `Fintype` are **not** available in `import Std`;
- there is no `DecidableEq` instance for function types such as
  `Fin 5 → Fin 3`, so coordinates are stored as plain `Nat`s and reduced with
  `% 3`;
- `decide` cannot reduce `Rat`, so only `Nat` arithmetic is used.

The collinearity predicate `bad p q r` is complete over `F_3`: for two distinct
projective points `p, q`, the projective line through them is
`{p, q, normalize(p+q), normalize(p+2q)}`. Hence `isCap S = true` really means
"no three distinct points of `S` are collinear", and `pts20_isCap` is checked by
kernel reduction over all `20³` ordered triples (equivalently, all
`C(20,3) = 1140` unordered triples).

## Axiom audit

`lake env lean Check.lean` reports, for every one of the eleven theorems:

```
'…' does not depend on any axioms
```

In particular there is no `sorryAx` and no `Lean.ofReduceBool`; the whole file
is kernel-checked definitional computation. (Unlike the template submission for
`00000000463`, no `propext` / `Quot.sound` / `Classical.choice` is needed
anywhere, because every statement here is a decidable `Nat`/list computation.)

## Scope note

The Lean component proves that a 20-point cap **exists** in `PG(4,3)`. This
gives `max ≥ 20 > 14 = formula 3`, which is exactly what is needed to refute the
conjecture's value `14` at `q = 3`. It is a *lower*-bound certificate; it
deliberately does not formalise an upper bound.

The exact value `max = 20` (no 21-point cap exists) is **not** formalised. It
rests on a SAT certificate described in the top-level `README.md`: a cap of size
`≥ 21` spans `PG(4,3)` and contains 5 linearly independent points; `GL(5,3)` is
transitive on ordered bases, so one may assume the 5 standard basis points lie in
the cap, and the resulting SAT instance with `≥ 21` points required is UNSAT.
The refutation of the conjecture does not depend on this upper bound. Likewise
the failure of the general formula in `PG(4,5)` (a 47-point cap exists) and the
failure of the even-`q` clause at `q = 2` are computational facts reported in
`reproduce.py` and `README.md`, not Lean theorems.

## Environment

Lean 4.33.1, Lake 5.0.0-src, no Mathlib. `lake build` needs no cache download
(the manifest is created from scratch on first build).
