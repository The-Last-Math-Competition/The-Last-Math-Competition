# Submission for conjecture 00000000458

**Verdict: FALSE (refuted).**

## The conjecture

From `conjectures/00000000458.md`:

> The absolute value of the Möbius number of the Tamari lattice `T_n` is
> `(n-2)(-1)^n` (a closed formula verifiable up to `n = 8`).

## Two independent refutations

**(a) Sign contradiction (enumeration-free).** The right-hand side is
asserted to equal an *absolute value*, hence must be nonnegative. But at
`n = 3` it is `(3-2)(-1)^3 = -1`, a negative number. No absolute value is
negative, so the statement is already internally inconsistent at `n = 3`.
The same happens for every odd `n > 2`.

**(b) The true value is `1`.** Enumerating the genuine Tamari lattice
(binary trees with `n` internal nodes under the right-rotation order) for
`n = 1..8` gives `μ(0̂,1̂) = (-1)^{n-1}`, hence `|μ(T_n)| = 1` for every
`n`. The conjectured value `(n-2)(-1)^n` is
`1, 0, -1, 2, -3, 4, -5, 6` and agrees only accidentally at `n = 1`.

Validation of the enumeration: `|T_n| = Catalan(n)` (1, 2, 5, 14, 42, 132,
429, 1430), cover counts `(n-1)·Catalan(n)/2`, a unique minimum and maximum
in every case, and the full lattice property (existence of meets and joins)
checked for `n ≤ 6`.

**Indexing objection.** No reindexing `T_n → T_{n+k}` can rescue the claim:
the left side is eventually the constant sequence `1`, while
`(n-2)(-1)^n` is unbounded and negative for odd `n > 2`. See
`main.tex`, Section 5.

## Files

```
README.md            this file
main.tex             standalone article (amsmath/amssymb/amsthm)
reproduce.py         stdlib-only enumeration, n = 1..8, exits 0
lean4/
  lean-toolchain     leanprover/lean4:v4.33.1
  lakefile.toml      library tlmc458 (entry point Main)
  Main.lean          statement + refutation
  Check.lean         #print axioms audit
  README.md          build and coverage notes
```

## Reproduce

Python (standard library only):

```
python3 reproduce.py
```

It enumerates the Tamari lattice for `n = 1..8`, checks cardinalities,
cover counts, unique bottom/top, the lattice property for `n ≤ 6`, computes
`μ(0̂,1̂) = (-1)^{n-1}` and prints the table against the claimed
`(n-2)(-1)^n`, then prints `PASS` (conjecture refuted) and exits 0.

Lean 4 (`leanprover/lean4:v4.33.1`):

```
export PATH="/opt/homebrew/bin:$PATH"
cd lean4
lake build
lake env lean Check.lean   # axiom audit
```

`Main.lean` uses core Lean only (`import Std`, no Mathlib, no `sorry`, no
`axiom`, no `native_decide`). It formalises the sign contradiction in full
and computes `μ(T_3) = 1` by genuine enumeration of the five binary trees
with three internal nodes under the right-rotation order.

LaTeX:

```
tectonic --outdir build main.tex   # -> build/main.pdf
```

## What the Lean file formalises

* The integer absolute value `iabs` (core Lean has none), with
  `modulus_nonneg` and `no_abs_eq_neg_one`.
* The claimed value at `n = 3`: `formula_at_three`,
  `formula_at_three_literal`, `contradiction_sign`,
  `contradiction_sign_strong`.
* A computable Tamari model: `Tree`, `rotations` (right rotation),
  `closure` (reflexive-transitive closure by Floyd–Warshall), `muRel` (the
  Möbius recurrence), `mobiusTamari`.
* Enumeration checks: `card_T3` (five trees), `bottom_is_min`,
  `top_is_max`.
* The decisive computation: `mu_T3 : mobiusTamari 3 = 1` and
  `abs_mu_T3 : iabs (mobiusTamari 3) = 1`.
* The collected `conjecture_00000000458_false`.

The general statement `|μ(T_n)| = 1` for `n = 1..8` is verified by
`reproduce.py`; the Lean development formalises the `n = 3` instance plus
the enumeration-independent sign contradiction.
