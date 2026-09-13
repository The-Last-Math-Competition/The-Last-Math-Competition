# Lean 4 formalisation — disproof of conjecture `00000001203`

Core Lean only (`import Std`), no Mathlib, no `sorry`. The project pins
`lean-toolchain` to `leanprover/lean4:v4.33.1` and defines the library `Main`
in `lakefile.toml`.

## Build and audit

```sh
lake build
lake env lean Check.lean
```

`Check.lean` prints `#print axioms` for every theorem so a reviewer can confirm
the absence of `sorryAx` and of Mathlib dependencies. The audit reports
`[propext, Quot.sound]` (and no axioms at all for
`three_dvd_two_sq_sub_one`); no `sorryAx`.

## The game and the witnesses

For a move set `S`, the SG sequence is defined by the mex recursion

```
g(0) = 0,    g(n) = mex { g(n - s) : s ∈ S, s ≤ n }.
```

The formalisation fixes the **primary witness** `S = {1, 3}`:

```lean
def g : Nat → Nat
  | 0 => 0
  | 1 => mex [g 0]
  | 2 => mex [g 1]
  | n + 3 => mex [g (n + 2), g n]     -- moves 3 (to n) and 1 (to n + 2)
termination_by n => n
decreasing_by all_goals omega
```

Its closed form is `g n = n % 2`, proved by strong recursion (`g_eq`); note that
plain `decide` cannot kernel-reduce a well-founded definition, so every numeric
fact about `g` is routed through `g_eq`. The sequence is therefore
`0, 1, 0, 1, 0, 1, …` with least period `2`.

The **clause-1 witness** `S = {1, 2}` is formalised as `g12`, with closed form
`g12 n = n % 3` (`g12_eq`) and least period `3 = 2^2 − 1`.

## Statements

| Theorem | Statement | Role |
|:--------|:----------|:-----|
| `g_eq` | `g n = n % 2` | closed form of the primary witness `S = {1,3}` |
| `g_period` | `g (n+2) = g n` | `2` is a period |
| `least_period_two` | `IsLeastPeriod 2` | `2` is the **least** period |
| `not_least_period_four` | `¬ IsLeastPeriod (3 + 1)` | the conjecture's second clause (k = 3 ∈ S) demands period `k+1 = 4`; contradicted |
| `two_not_dvd_seven` | `¬ (2 ∣ 7)` | literal-reading clause 1 for the fragile `S = {1}` witness |
| `g12_eq` | `g12 n = n % 3` | closed form of the clause-1 witness `S = {1,2}` |
| `g12_period` | `g12 (n+3) = g12 n` | `3` is a period |
| `least_period_three_12` | `IsLeastPeriod12 3` | `3` is the least period of `g12` |
| `three_dvd_two_sq_sub_one` | `3 ∣ 2^2 − 1` | the period divides `2^k − 1` for `k = 2` |
| `clause1_fails_charitable` | `¬ ((3 ∣ 2^2−1) ↔ (0 < [1,2].length ∧ ¬ 2 ∈ [1,2]))` | clause 1 fails under the charitable reading `k = max(S) = 2` |
| `conjecture_00000001203_false` | conjunction of the above | the packaged disproof |

`IsLeastPeriod` is defined exactly as required:

```lean
def IsLeastPeriod (p : Nat) : Prop :=
  0 < p ∧ (∀ n, g (n + p) = g n) ∧
    ∀ q, 0 < q → (∀ n, g (n + q) = g n) → p ≤ q
```

and `IsLeastPeriod12` is the identical predicate for `g12`.

## Proof strategy

- **Closed forms.** `g_eq` and `g12_eq` are proved by `Nat.strongRecOn`. In each
  successor case the recursive calls are rewritten by the induction hypothesis,
  leaving `mex` of two concrete residues; the residues are separated with
  `Nat.mod_two_eq_zero_or_one` (for `g`) or by `omega` on `n % 3 < 3` (for
  `g12`), after which `decide` evaluates `mex`.
- **Least period.** `least_period_two` supplies the period-2 relation
  `g_period` and shows any positive period `q` satisfies `2 ≤ q`; the cases
  `q = 0` and `q = 1` are eliminated (`q = 1` would force `g 1 = g 0`, i.e.
  `1 = 0`). `not_least_period_four` invokes minimality of `2` to contradict
  `4 ≤ 2`. `least_period_three_12` is analogous, splitting `q < 3` into
  `q = 1` and `q = 2` and deriving `1 = 0` / `2 = 0`.
- **Clause 1.** `three_dvd_two_sq_sub_one` is `⟨1, rfl⟩`-style, and
  `clause1_fails_charitable` proves the right-hand side
  `0 < [1,2].length ∧ ¬ (2 ∈ [1,2])` false by `decide`, then feeds the left-hand
  side into the assumed biconditional.

## Scope note and honest caveats

- The refutation is unconditional for the primary witness `S = {1, 3}` with
  `k = 3`: `max(S) = 3 = k`, so the two possible readings of the parameter `k`
  (ambient bound vs. `k = max(S)`) coincide. The formalised statement
  `¬ IsLeastPeriod (3 + 1)` therefore refutes the conjecture's second clause
  under **either** reading.
- The exact reading of `k` is genuinely ambiguous in the conjecture text (it is
  introduced as the bound of `{1, …, k}`, but the phrase "does not contain `k`"
  would be non-vacuous only if `k` were the ambient bound). The informal
  write-up discusses both readings; the Lean formalisation avoids the ambiguity
  by using the interpretation-free primary witness.
- The clause-1 witness `S = {1, 2}` is also interpretation-free at the level of
  numbers: `max(S) = 2`, and both the charitable reading (`k = 2`, period `3`
  divides `2^2 − 1 = 3` although `k ∈ S` forces "does not divide") and the
  ambient reading with `k = 3` (period `3 ∤ 2^3 − 1 = 7` although `k ∉ S`
  forces "divides") fail. Lean formalises the charitable case
  (`clause1_fails_charitable`).
- No claim is made that restricting the second clause to the full sets
  `{1, …, k}` repairs the conjecture: `S = {1, 2}` violates clause 1 regardless.
- `#eval` lines at the end of `Main.lean` display the first 20 values
  `0,1,0,1,…` and `0,1,2,0,1,2,…`; they are display-only and carry no proof
  obligation.

## Environment

Lean 4.33.1, Lake, no Mathlib. `lake build` needs no cache download. The axiom
audit reports no `sorryAx`.
