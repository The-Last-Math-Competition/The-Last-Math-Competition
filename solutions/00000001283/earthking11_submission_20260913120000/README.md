# Rule-3 disproof of conjecture 00000001283

**Verdict: FALSE.** The claim that the nim-equation `x ⊕ y = x · y`
(with `⊕` carry-free binary addition, and `x, y ≥ 1`) has solutions
`(2,2)` and `(0,0)`, and that every other pair `x, y > 2` has nim-sum minus
product equal to `±2^j`, is refuted in three independent ways.

## The claim under test

From `conjectures/00000001283.md`:

> A nim-equation is an integer solution of `x⊕y = x·y` with `x, y ≥ 1`,
> where `⊕` is binary addition without carry. Conjecture: The only solutions
> are `(2,2)` and `(0,0)`; for all other candidate pairs with `x, y > 2`,
> the difference between the nim-sum and the product is a sign flip of a
> power of two.

## The three defects

1. **`(2,2)` is not a solution.**  `2 ⊕ 2 = 10₂ ⊕ 10₂ = 0`, while
   `2 · 2 = 4`.  Since the conjecture explicitly lists `(2,2)` as a solution,
   the first clause is literally false.  (The other listed pair `(0,0)` is a
   solution but lies outside the stated domain `x, y ≥ 1`.)

2. **There are no solutions with `x, y ≥ 1` at all.**  For `x = 1` one has
   `1 ⊕ y = y ± 1 ≠ y`; for `x, y ≥ 2` one has
   `x ⊕ y ≤ x + y ≤ x · y`, with equalities impossible (the second forces
   `x = y = 2`, where the first fails since `2 ⊕ 2 = 0 ≠ 4`).  Exhaustive
   search over `0 ≤ x, y < 500` returns the single solution `(0,0)`; over
   `1 ≤ x, y < 500` it returns the empty set.

3. **The second clause is false.**  At `(3,3)`,
   `3 ⊕ 3 = 0`, `3 · 3 = 9`, so the difference is `-9`, which is not `±2^j`
   for any `j` (the powers of two near `9` are `8 = 2³` and `16 = 2⁴`).
   Over the box `x, y ∈ [3, 499]` (`247 009` pairs), only `39` pairs have
   the difference equal to `±2^j`; the remaining `246 970` violate the clause.
   E.g. `(3,4)`: `7 − 12 = −5` and `(3,6)`: `5 − 18 = −13` are not signed
   powers of two.

A charitable reading of the first clause as “there are no *other* solutions”
would make that half vacuous, since the `x, y ≥ 1` solution set is empty --
but the sentence as written asserts that `(2,2)` *is* a solution, which is
false, and the second clause is independently false in any case.

## Contents

| Path | Purpose |
| --- | --- |
| `main.tex` | Standalone article: the conjecture, the `(2,2)` counterexample, the proof that no `x, y ≥ 1` solve the equation, and the failure of the second clause at `(3,3)`. |
| `reproduce.py` | Stdlib-only exhaustive checks: solution set for `x, y < 500`, the `x, y ≥ 1` and `x, y ≥ 2` sub-cases, and the `±2^j` count over `[3,499]²`. PASS/FAIL, exit 0. |
| `build/main.pdf` | Compiled article (`tectonic --outdir build main.tex`). |
| `lean4/` | Core-Lean formalisation (no Mathlib, no `sorry`, no `axiom`, no `native_decide`). |
| `lean4/lean-toolchain` | `leanprover/lean4:v4.33.1`. |
| `lean4/lakefile.toml` | Lake project `tlmc1283`, target `Main`. |
| `lean4/Main.lean` | The `(2,2)` counterexample, the bounded solution search, and the failure of the second clause at `(3,3)`. |
| `lean4/Check.lean` | `#print axioms` audit for every theorem. |
| `lean4/README.md` | Build and audit instructions. |

## Reproduction

```sh
# Numerical check
python3 reproduce.py

# Formal check (Lean 4.33.1; the toolchain must already be installed)
export PATH="/opt/homebrew/bin:$PATH"
cd lean4
lake build                 # exit 0
lake env lean Check.lean   # axiom audit

# PDF
tectonic --outdir build main.tex   # -> build/main.pdf
```

Expected: `reproduce.py` prints `OVERALL: PASS` and exits 0; `lake build`
succeeds; the axiom audit reports only `propext` and `Quot.sound` (never
`sorryAx` or `Lean.ofReduceBool`).

## Honest scope

* The unbounded statement “no `x, y ≥ 1` solve the equation” is proved on
  paper in `main.tex` (Theorem 2); in Lean it is witnessed by a bounded search
  over `0 ≤ x, y < 200` (`no_pos_solutions`), not by a general inequality
  proof.  See `lean4/README.md`.
* The disproof does not depend on that gap: the `(2,2)` failure and the
  `(3,3)` failure of the second clause are each fully formalised and each
  refutes the conjecture as written.
* We refute only this sentence of conjecture 00000001283.  A charitable
  reading of the first clause (as “no solutions besides the listed ones”)
  would remove the first defect but not the second.
