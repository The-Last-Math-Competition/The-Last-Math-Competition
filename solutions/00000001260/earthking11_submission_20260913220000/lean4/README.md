# Lean 4 formalisation — disproof of conjecture `00000001260`

Core Lean only (`import Std`), no Mathlib, no `sorry`. The project pins
`lean-toolchain` to `leanprover/lean4:v4.33.1` and defines the library `Main`
in `lakefile.toml` (package name `tlmc1260`).

## Build and audit

```sh
cd lean4
lake build
lake env lean Check.lean
```

`Check.lean` prints `#print axioms` for every theorem so a reviewer can confirm
the absence of `sorryAx` and of Mathlib dependencies.

## What is formalised

The Thue–Morse word is represented by a *structural* recursion, so that the
concrete facts reduce under `decide` (a well-founded definition would get stuck
at `WellFounded.fix` and would not reduce):

```lean
def step : List Bool → List Bool
  | [] => []
  | b :: t => (if b then [true, false] else [false, true]) ++ step t

def gen : Nat → List Bool
  | 0 => [false]
  | k + 1 => step (gen k)

def tm (n : Nat) : Bool :=
  (List.range (n + 1)).foldl (fun a i => if Nat.testBit n i then !a else a) false

def fac3 : List (List Bool) :=
  (List.range 62).map (fun i => [tm i, tm (i + 1), tm (i + 2)])
```

`step` is the substitution `0 ↦ 01, 1 ↦ 10` (`false` is `0`, `true` is `1`);
`gen k = σ^k(0)` is the substitution-generated prefix; `tm` is the closed form
("parity of the binary digit sum"); and `fac3` is the list of length-3 blocks
starting at positions `0, …, 61`.

| Theorem | Statement | Role |
|:--------|:----------|:-----|
| `tm_prefix_agrees` | `(List.range 64).map tm = gen 6` | the closed form agrees with the substitution on a prefix |
| `tm_p3_ge_6` | `6 ≤ fac3.eraseDups.length` | **lower bound** `p(3) ≥ 6` |
| `tm_six_factors` | `fac3.eraseDups` is the explicit list of six blocks `011,110,101,010,100,001` | the six distinct factors |
| `tm_p3_eq_6` | `fac3.eraseDups.length = 6` | the count is exactly `6` |
| `tm_refutes_bound` | `fac3.eraseDups.length > 3 + 2` | the bound `p(n) ≤ n+2` fails at `n = 3` |
| `incidence_positive` | `∀ r ∈ incidence, ∀ c ∈ r, 0 < c` | incidence matrix `[[1,1],[1,1]]` is positive, witnessing primitivity |
| `conjecture_00000001260_false` | `fac3.eraseDups.length = 6 ∧ ¬ (fac3.eraseDups.length ≤ 3 + 2)` | packaged refutation |

## Proof strategy

- **Only a lower bound is needed.** Refuting a universal *upper* bound
  `p(n) ≤ n+2` requires exhibiting, for one word and one `n`, a *lower* bound
  `p(n) > n+2`. Each entry of `fac3` is a genuine factor of the Thue–Morse
  word because it is the length-3 block starting at an explicit position
  `i ∈ {0,…,61}`; therefore `fac3.eraseDups.length` is a lower bound for the
  true complexity `p(3)`. **No completeness (upper-bound) proof — no argument
  that there are at most six length-3 factors — is needed or given.** This is
  the key point of the formalisation.
- **Everything is closed by `decide`.** The definitions are structural
  recursions and `List` folds over concrete lists, so the kernel reduces them:
  `tm_p3_ge_6`, `tm_p3_eq_6`, `tm_refutes_bound`, `tm_six_factors`,
  `tm_prefix_agrees`, `incidence_positive`, and
  `conjecture_00000001260_false` are all discharged by `decide`, without
  `sorry`, `Lean.ofReduceBool`, or any axiom beyond `propext`.
- **Consistency of the representation.** `tm_prefix_agrees` checks that the
  closed form `tm` (parity of digit sum) equals the prefix produced by iterating
  the substitution, tying the two standard definitions of Thue–Morse together.
- **Primitivity.** `incidence_positive` states that every entry of the
  incidence matrix `[[1,1],[1,1]]` is positive. Since the matrix is positive,
  so is every power `M^k`, which is the standard witness of primitivity.

## Definitional caveat

The filed conjecture says "purely substitutive class" (纯替换类) with **no
alphabet restriction and no exclusion of constant-length substitutions**. Under
that literal reading the Thue–Morse word qualifies: it is the fixed point of an
actual substitution, that substitution is primitive (positive incidence
matrix), and it is standardly called purely substitutive. The only structural
feature that might be used to exclude it — being constant-length / two-letter —
is **not** mentioned in the filed text. The formalisation therefore records the
refutation of the literal universal reading; it does **not** claim to refute a
hypothetical reading in which "purely substitutive" is silently restricted to
three-letter or Pisot-type substitutions, or reinterpreted as a claim about the
minimal growth rate over the class. No such reading appears in the text.

## Environment

Lean 4.33.1, Lake, `import Std` only, no Mathlib, no cache download.
`lake env lean Check.lean` reports `propext` for the theorems that use `decide`
and no axioms at all for `incidence_positive`; in particular no `sorryAx` and
no `Lean.ofReduceBool`.
