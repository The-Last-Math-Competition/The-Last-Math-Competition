# Disproof of conjecture `00000000416`

**Verdict: FALSE.** The conjecture makes three simultaneous claims about the
orbits of the evacuation operator on standard Young tableaux of shape `(n,n)`.
The first and third are jointly impossible already at `n = 2`: together they
require at least **three** tableaux, and the shape `(2,2)` carries exactly
**two**.

## The conjecture

> **Definition:** The evacuation operator `e` acts on standard Young tableaux of
> two-row shape `(n,n)`; its orbits are the cycles of the iterates of `e`.
> **Conjecture:** The number of orbits is `2^{n-1}`, every orbit length divides
> `2n`, and the number of orbits of length exactly 2 is the Fibonacci number
> `F_{n-1}`.

## Reading used

We take the three clauses at face value as assertions about a single
decomposition of the tableaux of shape `(n,n)` into orbits, with `F_0 = 0`,
`F_1 = 1`. **No reading of the word "evacuation" is required.** The refutation
below uses exactly one property of the orbits — that they are nonempty — and is
therefore insensitive to how `e` is defined. Any map whatsoever whose iterates
split the tableaux into two orbits, one of size 2, would require at least three
tableaux. See "What the argument does not use" below.

## Why it is false

### Step 1: the shape `(2,2)` has exactly two standard tableaux

The entries are `1,2,3,4`. The top-left entry is smaller than its row neighbour
and its column neighbour, and (via the top row) smaller than the bottom-right
entry, so it equals `1`. Symmetrically the bottom-right entry equals `4`. The
remaining entries `2` and `3` occupy the two off-diagonal cells, and both
placements are admissible:

```
1 2        1 3
3 4        2 4
```

So `|T_2| = 2`. This agrees with the classical count `|T_n| = C_n`, the `n`-th
Catalan number, which gives `C_2 = 2`.

### Step 2: the conjecture requires three

At `n = 2` the conjecture asserts:

- **number of orbits** `= 2^{2-1} = 2`;
- **orbits of length exactly 2** `= F_{2-1} = F_1 = 1`.

One orbit therefore contains exactly two tableaux, and the second orbit is
nonempty, so it contains at least one more. Hence at least `2 + 1 = 3` tableaux
are needed. But only `2` exist.

**The conjunction of the first and third clauses fails at `n = 2`, and with it
the conjecture.**

## What the argument does not use

This matters, because "evacuation" is standard but not defined in the conjecture
itself. The refutation does **not** use:

- that `e` is an involution (it is, but we do not need it);
- that orbit lengths are 1 or 2;
- anything about how `e` acts on a particular tableau;
- the clause that every orbit length divides `2n`.

So the refutation survives any reasonable variant definition of `e`. It is a
pure counting obstruction, and `n = 2` is the first nontrivial case.

## A second, independent failure

If one *does* use that evacuation is an involution, then every orbit has length
1 or 2, and the first and third clauses together force

```
|T_n| = 2^{n-1} + F_{n-1}
```

exactly. For `n = 4` this gives `8 + 2 = 10`, whereas `C_4 = 14`. So the
conjecture also fails at `n = 4`, and at every `n ≥ 4`. (`n = 1` and `n = 3`
happen to satisfy the identity: `1 = 1 + 0` and `5 = 4 + 1`.) This is an
independent second refutation, not the one we rely on.

## Verification

| what | how |
|---|---|
| enumeration of the tableaux of shape `(2,2)` | `python3 reproduce.py` — section 1 lists both and asserts the count is 2 |
| the counting comparison for `n ≤ 7` | `python3 reproduce.py` — sections 3 and 4 |
| formal proof | `lean4/` — `lake build && lake env lean Check.lean` |

The Lean 4 project (core only, no Mathlib, no `sorry`) contains:

- an exhaustive enumeration of all `4^4 = 256` fillings of `(2,2)`, filtered to
  the standard ones. `sols_length : sols.length = 2` is proved by `rfl`, so the
  kernel itself performs the search — **this theorem depends on no axioms at
  all**;
- `orbit_bound`: two nonempty parts, one of size at least 2, imply a total of at
  least 3;
- `refutation_at_two`: no such splitting of the tableaux of shape `(2,2)` exists.

Axioms used: `propext` and `Quot.sound`, inherited from the standard treatment
of lists.

## Files

| file | what it is |
|---|---|
| `README.md` | this file |
| `main.tex` | LaTeX source of the write-up |
| `build/main.pdf` | compiled write-up |
| `build/log.txt` | build log |
| `lean4/Main.lean` | the formalisation |
| `lean4/Check.lean` | prints the enumeration, the theorems, and the axioms |
| `lean4/lakefile.toml`, `lean4/lean-toolchain` | Lean build configuration (`leanprover/lean4:v4.33.1`) |
| `lean4/README.md` | how to build the Lean project |
| `reproduce.py` | standalone reproduction of the enumeration and the comparison (standard library only) |

## Scope of the claim

We refute the conjunction as stated. We make no claim about what the correct
orbit counts are, and no claim about the divisibility clause. If the corpus
intends the conjecture to hold only for `n ≥ 3`, the refutation moves to
`n = 4` (see above) and still stands.
