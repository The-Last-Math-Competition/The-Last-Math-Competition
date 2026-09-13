# Refutation of conjecture 00000001299 (Ducci cycles)

**Verdict: FALSE.**

Conjecture (from `conjectures/00000001299.md`): for `n` a power of two the
Ducci sequence reaches zero, for non-powers of two nontrivial cycles exist,
**and the minimal cycle length is an odd factor of `n`**.

The first two clauses are the classical Ducci zero criterion and are **not**
disputed. The last clause is false.

**Counterexample.** The Ducci map is `T(x)_i = |x_i - x_{i+1}|` cyclically. For
`n = 5` the seed `(0,0,0,1,1)` lies on a cycle of minimal non-trivial length
**15**. The number `15` is odd but `15 ∤ 5`, so the minimal cycle length is not
an odd factor of `n`. The 15 states are distinct and the cycle closes via
`T(1,1,1,1,0) = (0,0,0,1,1)`.

**Secondary.** For `n = 10` the minimal non-trivial period is also **15**, and
`15 ∤ 10` (exhaustive over `{0..3}^10`: period set `{1, 15, 30}`). Further data:
`n = 11` has minimal non-trivial period `341` (`341 ∤ 11`), `n = 13` has `819`
(`819 ∤ 13`).

**Cleanest statement:** for `n = 5`, the minimal non-trivial cycle length is
`15 = 3 · 5`, which is not a divisor of `5`; the conjecture's final clause
therefore fails at the smallest non-power-of-two case where it can.

## Contents

| Path | Description |
| --- | --- |
| `main.tex` | Standalone article: the Ducci map, the explicit 15-cycle, exhaustive/random period data, the classical zero criterion as context, and honest notes on the non-rigorous mod-2 argument and alternative readings. Build with `tectonic --outdir build main.tex`. |
| `reproduce.py` | Stdlib-only direct iteration. Prints the explicit 15-cycle, period sets for `n = 5` (exhaustive `[0..9]^5` and random larger seeds) and `n = 10` (exhaustive `[0..3]^10` and random), confirms `15 ∤ 5` and `15 ∤ 10`, prints `PASS`, exits `0`. |
| `lean4/` | Core-Lean (no Mathlib) machine-checked formalisation. |
| `lean4/README.md` | Model, theorems, and axiom audit. |

## Reproduce

```sh
python3 reproduce.py                  # direct iteration, PASS/FAIL
cd lean4 && lake build                # builds the formalisation (exit 0)
lake env lean Check.lean              # prints the axiom audit
tectonic --outdir build main.tex      # from the submission root -> build/main.pdf
```

## Formalisation

`lean4/Main.lean` defines the Ducci map `T` on `Fin 5 → Nat` via truncated
subtraction (`(a - b) + (b - a) = |a - b|`), the seed `s = (0,0,0,1,1)`, and
the iterate `iter`, and proves by kernel `decide` (no `sorry`, no `axiom`, no
`native_decide`):

* `returns_at_15 : iter 15 = s`;
* `no_return_below_15` / `distinct_first_15`: no positive iterate below 15
  returns to `s`;
* `min_period_five`: the minimal non-trivial period of `s` is 15;
* `fifteen_not_divides_five : ¬ (15 ∣ 5)`;
* `conjecture_00000001299_false`: collects the 15-cycle, its minimality, and
  `15 ∤ 5`.

Because core Lean (`import Std`) has no `DecidableEq` instance for function
types, equalities of states are checked pointwise over `Fin 5` (`∀ i, x i = y i`)
and the function-level statement is obtained with `funext`. See
`lean4/README.md` for details.

## Honest notes

* The earlier attempted argument "the mod-2 reduction has periods `{1,15}`,
  hence integer cycle lengths must be divisible by 15" is **not rigorous** and
  is **not used**: in one sample of 300 random `n = 5` seeds, 16 have integer
  period 15 while their mod-2 reduction has period 1 (the count is
  random-sample dependent; the phenomenon is robust). The conclusion is
  established by direct verification.
* If "minimal cycle length" included the trivial fixed point, then `1` is an
  odd factor of every `n` and the clause is vacuous; that is not the natural
  reading (the conjecture contrasts "nontrivial cycles" with zero). `n = 9`
  happens to satisfy the clause (minimal non-trivial period `3 = 9/3`), but one
  counterexample refutes the universal claim.
* "Odd factor of `n`" may be a garbling of "odd divisor of `2^k − 1`" (indeed
  `15 = 2^4 − 1`); neither reading rescues the literal wording, under which the
  verdict is FALSE.
