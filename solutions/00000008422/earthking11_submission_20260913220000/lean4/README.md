# Lean 4 formalisation — disproof of conjecture `00000008422`

Core Lean only (`import Std`), no Mathlib, no `sorry`, no `native_decide`.
The project pins `lean-toolchain` to `leanprover/lean4:v4.33.1` and defines the
library `Main` in `lakefile.toml` (package name `tlmc8422`).

## Build and audit

```sh
lake build
lake env lean Check.lean
```

`Check.lean` prints `#print axioms` for every theorem, so a reviewer can
confirm the absence of `sorryAx`, of Mathlib dependencies, and of
`Lean.ofReduceBool`.

## Encoding

A 3-element subset of `Fin 6` is written as a 6-bit `Nat` mask. Residue/point
membership uses `Nat` bit operations only, so no `Finset`/`Fintype`
(`Finset` is not in `import Std`) and no function extensionality is needed.

```lean
def popcount6 (m : Nat) : Nat :=
  (List.range 6).foldl (fun a i => a + ((m >>> i) &&& 1)) 0

def triples : List Nat := (List.range 64).filter (fun m => popcount6 m == 3)  -- 20 triples
def pairs   : List Nat := (List.range 64).filter (fun m => popcount6 m == 2)  -- 15 pairs

def isDesign (blocks : List Nat) (lam : Nat) : Bool :=
  pairs.all (fun pm => (blocks.filter (fun b => (b &&& pm) == pm)).length == lam)
```

`isDesign blocks lam` is the pair-covering condition: every pair of points lies
in exactly `lam` of the listed triples. `sublistsLen n xs` lists all sublists of
`xs` of length `n`; its recursion is structural on `xs`, so the kernel can
evaluate it inside `by decide` (a `termination_by`/well-founded version cannot
be reduced by the kernel).

`complement c = triples.filter (fun b => !(c.contains b))` is the complement of
a set of triples inside all twenty triples.

## What is formalised

| Theorem | Statement | Role |
|:--------|:----------|:-----|
| `triples_len` | `triples.length = 20` | C(6,3) = 20 blocks are available |
| `pairs_len` | `pairs.length = 15` | C(6,2) = 15 pairs must be covered |
| `design2_is` | `isDesign design2 2 = true` | explicit 2-(6,3,2) design exists |
| `design2_len` | `design2.length = 10` | its block count is b = 10 |
| `design4_is` | `isDesign triples 4 = true` | complete 2-(6,3,4) design exists |
| `design4_len` | `triples.length = 20` | its block count is b = 20 |
| `no_design_1` | `(sublistsLen 5 triples).all (fun c => !(isDesign c 1)) = true` | no 2-(6,3,1) design; all C(20,5) = 15504 candidate 5-subsets checked |
| `no_design_3` | `(sublistsLen 5 triples).all (fun c => !(isDesign (complement c) 3)) = true` | no 2-(6,3,3) design (complement of a 5-subset) |
| `spectrum_6_3` | conjunction of the four above | the (6,3) spectrum is exactly {2,4} |
| `criterion_6_3` | `predicted6.all (fun l => (15*l) % 3 == 0)` | criterion predicts all of {1,2,3,4} at (6,3) |
| `criterion_22_3` | `predicted22.all (fun l => (231*l) % 3 == 0)` | criterion predicts all of {1,…,20} at (22,3) |
| `forced_out_6_3` | `(predicted6.filter (fun l => (5*l) % 2 != 0)) = [1,3]` | values ruled out at (6,3) by `2*r = 5*lambda` |
| `budget_6_3` | 2 forced-out values `≤ k^2 = 9` | (6,3) is absorbed by the exception clause |
| `forced_out_22_3` | 10 forced-out values at (22,3) | the ten odd lambda are ruled out |
| `budget_22_3` | `3^2 < 10` | (22,3) exceeds the k^2 = 9 exception budget |
| `parity_6_3` | `2*r = 5*lambda → 2 ∣ lambda` | final arithmetic step of the divisibility argument |
| `parity_22_3` | `2*r = 21*lambda → 2 ∣ lambda` | same at (22,3) |
| `no_odd_lambda_22_3` | odd `lambda` admits no `r` with `2*r = 21*lambda` | odd lambda are not attainable |
| `decisive_22_3` | criterion predicts {1,…,20} ∧ 10 forced out ∧ 9 < 10 | packaged decisive refutation |

## Proof strategy

- **Existence (finite computation).** `design2_is` and `design4_is` are closed
  by `decide`: the pair-covering condition is a Boolean computation over the 15
  pair masks.
- **Non-existence (finite computation).** `no_design_1` reduces
  `(sublistsLen 5 triples).all …` and is closed by `decide`. The search space is
  exactly C(20,5) = 15504 five-element sublists, matching `reproduce.py`.
  `no_design_3` uses that the complete design has lambda = 4, so complementing a
  block set inside the twenty triples sends lambda to 4 − lambda; a
  2-(6,3,3) design is therefore the complement of a 2-(6,3,1) design, and the
  same 15504-element enumeration rules it out. `maxRecDepth` is raised to
  `1000000` and `maxHeartbeats` is disabled to let the kernel finish.
- **Divisibility / parity.** In a 2-(v,k,lambda) design each block through a
  point contains k−1 further points, and each of the v−1 pairs at that point is
  covered lambda times; counting the flags (block through p, second point)
  gives `(k-1) * r = (v-1) * lambda`. For k = 3 this is `2*r = (v-1)*lambda`.
  The counting identity is the standard double count and is proved on paper in
  `main.tex`; `parity_6_3` and `parity_22_3` formalise the final arithmetic
  consequence with the identity as an explicit hypothesis, and
  `no_odd_lambda_22_3` is its contrapositive. `decide` supplies the counts
  `forced_out_*` and `budget_*`.

## Scope note

- Fully formalised: the (6,3) existence and non-existence statements (the
  exhaustive C(20,5) search is carried out in the kernel), the criterion's
  predicted sets at (6,3) and (22,3), the counts of forced-out values, the
  arithmetic parity consequences, and the packaged `decisive_22_3`.
- **Not** formalised: the general double-counting lemma
  `(k-1) * r = (v-1) * lambda` for an arbitrary design. Formalising it in core
  Lean would require a list-sum swap / partition lemma; it is instead proved on
  paper in `main.tex` and instantiated numerically in `reproduce.py`. The Lean
  development keeps the identity as an explicit hypothesis in `parity_6_3` and
  `parity_22_3`, so the missing step is isolated and visible.
- Also not formalised: the equivalence "complement of a 2-(6,3,3) design is a
  2-(6,3,1) design" as a general theorem; `no_design_3` instead re-runs the
  exhaustive enumeration directly over the 15504 complements. The parity step
  `2*r = 21*lambda → 2 | lambda` is proved by `omega`.
- No Mathlib, no `sorry`, no `native_decide`.

## Environment

Lean 4.33.1, Lake, no Mathlib. `lake build` needs no cache download. The axiom
audit in `Check.lean` reports no `sorryAx` and no `Lean.ofReduceBool`. The
`decide`-proved theorems depend on no axioms at all (`criterion_*`,
`forced_out_*`, `budget_*`, `decisive_22_3`) or only on `propext`
(`triples_len`, `design2_is`, `design4_is`, `no_design_1`, `no_design_3`,
`spectrum_6_3`); the `omega`-proved parity theorems (`parity_6_3`,
`parity_22_3`, `no_odd_lambda_22_3`) use `propext` and `Quot.sound`. These are
all core Lean axioms; none is `sorryAx` and none is a Mathlib axiom.

Exact audit output (from `lake env lean Check.lean`):

```text
'Tlmc8422.triples_len' depends on axioms: [propext]
'Tlmc8422.pairs_len' depends on axioms: [propext]
'Tlmc8422.design2_is' depends on axioms: [propext]
'Tlmc8422.design2_len' does not depend on any axioms
'Tlmc8422.design4_is' depends on axioms: [propext]
'Tlmc8422.design4_len' depends on axioms: [propext]
'Tlmc8422.no_design_1' depends on axioms: [propext]
'Tlmc8422.no_design_3' depends on axioms: [propext]
'Tlmc8422.spectrum_6_3' depends on axioms: [propext]
'Tlmc8422.criterion_6_3' does not depend on any axioms
'Tlmc8422.criterion_22_3' does not depend on any axioms
'Tlmc8422.forced_out_6_3' does not depend on any axioms
'Tlmc8422.budget_6_3' does not depend on any axioms
'Tlmc8422.forced_out_22_3' does not depend on any axioms
'Tlmc8422.budget_22_3' does not depend on any axioms
'Tlmc8422.parity_6_3' depends on axioms: [propext, Quot.sound]
'Tlmc8422.parity_22_3' depends on axioms: [propext, Quot.sound]
'Tlmc8422.no_odd_lambda_22_3' depends on axioms: [propext, Quot.sound]
'Tlmc8422.decisive_22_3' does not depend on any axioms
```
