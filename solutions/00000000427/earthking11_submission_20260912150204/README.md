# Disproof of conjecture `00000000427`

**Verdict: FALSE.** The claimed count at `t = 1`,

```
F(n) = 2^{floor(n^2/4)} * prod_{i=1..n} (2i-1)!! / i!,
```

is not an integer for any `n >= 4`; already `F(4) = 525/2`. A count at `t = 1`
is a cardinality, hence a non-negative integer, so the claimed equality fails.

## The conjecture

> **Definition:** Spin symmetric plane partitions are plane partitions in a
> cubic box symmetric under all diagonals and weighted by spin.
> **Conjecture:** Their count at `t = 1` equals
> `2^{⌊n²/4⌋}·∏_{i=1}^{n}(2i−1)!!/i!`, and the ratio of this formula to the
> unsymmetrized MacMahon formula is exactly a product of a power of two and
> double factorials, with no other prime factors.

## Why it is false

Let `F(n)` be the formula, read as an exact rational number, and let `ν₂` be
the 2-adic valuation. Each `(2i−1)!!` is a product of odd factors, so

```
ν₂((2i−1)!!) = 0.
```

Writing `D(n) = Σ_{i=1}^{n} ν₂(i!)`, this gives the valuation identity

```
ν₂(F(n)) = ⌊n²/4⌋ − D(n).                                  (∗)
```

**The counterexample `n = 4`.** We have
`D(4) = ν₂(1!) + ν₂(2!) + ν₂(3!) + ν₂(4!) = 0 + 1 + 1 + 3 = 5`, while
`⌊4²/4⌋ = 4`. By (∗),

```
ν₂(F(4)) = 4 − 5 = −1,
```

so `F(4)` is not an integer. Explicitly,

```
F(4) = 2^4 · (1·3·15·105) / (1!·2!·3!·4!) = 16·4725/288 = 525/2.
```

**All `n >= 4`.** The gap is non-increasing. Since
`⌊n²/4⌋ − ⌊(n−1)²/4⌋ = ⌊n/2⌋` and, by Legendre's formula,
`ν₂(n!) = Σ_{j≥1} ⌊n/2^j⌋`, we get

```
(⌊n²/4⌋ − D(n)) − (⌊(n−1)²/4⌋ − D(n−1))
  = ⌊n/2⌋ − ν₂(n!) = −Σ_{j≥2} ⌊n/2^j⌋ ≤ 0.
```

For `n >= 4` the term `⌊n/4⌋ >= 1` makes the gap strictly decreasing, and
`⌊3²/4⌋ − D(3) = 2 − 2 = 0`. Hence `ν₂(F(n)) <= −1 < 0` for every `n >= 4`.
The mechanism is simply that `ν₂(n!) = n − s₂(n)` (with `s₂` the number of
ones in the binary expansion) grows faster than `⌊n/2⌋`.

`F(1) = 1`, `F(2) = 3`, `F(3) = 15` are integers — presumably why the claim
looked plausible — but integrality fails at `n = 4` and never recovers. A count
cannot equal `525/2`, so conjecture `00000000427` is false.

The secondary ratio claim also fails under its natural reading of "a product
of a power of two and double factorials" as an integer: at `n = 4` the ratio is
`(525/2)/232848 = 525/465696`, whose denominator is even and whose numerator is
odd.

## Supporting enumeration

An independent, exhaustive computation of order ideals of the product poset
`[n]³` (equivalently, plane partitions in the `n`-cube), and of how many of
them are invariant under **all** permutations of the three coordinates:

| `n` | order ideals of `[n]³` (MacMahon total) | invariant under all coordinate permutations |
|---|---|---|
| 1 | 2 | 2 |
| 2 | 20 | 5 |
| 3 | 980 | 16 |
| 4 | 232848 | 66 |

The totals `2, 20, 980, 232848` independently reproduce the MacMahon formula,
validating the enumerator. The invariant counts are `2, 5, 16, 66`, whereas the
conjectured formula gives `1, 3, 15, 525/2`. It already disagrees at `n = 1`
(1 vs 2), `n = 2` (3 vs 5) and `n = 4` (not an integer).

## Files

| file | purpose |
|---|---|
| `README.md` | this file |
| `main.tex` | the proof (LaTeX) |
| `build/main.pdf` | compiled PDF, built with `tectonic --outdir build main.tex` (tectonic 0.17.0); checked-in build artifact |
| `reproduce.py` | exact rational checks and exhaustive order-ideal enumeration; `python3 reproduce.py` exits 0 and prints `PASS` |
| `lean4/` | Lean 4 formalisation, core Lean only (no Mathlib), no `sorry`; built with `lake build` and axiom-checked with `lake env lean Check.lean` |

## Reproducing

Pure Python 3, standard library only, no dependencies:

```bash
python3 reproduce.py
```

It computes `F(n)` exactly for `n = 1..10` and reports which values are
integers, verifies `ν₂(F(n)) < 0` for all `n` in `[4, 400]`, exhaustively
enumerates order ideals of `[n]³` for `n = 1..4`, and prints a final
`PASS`/`FAIL` summary. It runs in well under a minute.

To rebuild the PDF (requires `tectonic`; the project pins Lean 4
`v4.33.1` for the formalisation):

```bash
tectonic --outdir build main.tex     # writes build/main.pdf
```

To build and check the Lean 4 project:

```bash
cd lean4
lake build
lake env lean Check.lean             # prints the axiom dependencies
```

## The enumeration caveat

The exact definition of "spin symmetric plane partition" is not pinned down by
the conjecture, so the invariant-order-ideal count above is offered as
*independent supporting evidence* rather than as the definition. The refutation
does not depend on it: whatever the intended object, its `t = 1` value is a
count, and no count equals `525/2`.

## Status against the submission rules

Rule 3 requires a LaTeX source, a compiled PDF, and a Lean 4 project. All three
are present.

- **LaTeX source:** `main.tex`.
- **Compiled PDF:** `build/main.pdf`, built with
  `tectonic --outdir build main.tex` (tectonic 0.17.0) and checked in.
- **Lean 4 project:** `lean4/`, pinned to `leanprover/lean4:v4.33.1`, using
  **core Lean 4 only** (no Mathlib) with **no `sorry`**. It defines the odd
  double factorial and `F : Nat → Rat`, proves the closed value `F 4 = 525 / 2`,
  and proves `conjecture_00000000427_false : ∀ m : Nat, (m : Rat) ≠ F 4`. It
  builds with `lake build` on the pinned toolchain (exit 0, no errors), and
  `lake env lean Check.lean` reports that the theorems depend on
  `[propext, Classical.choice, Quot.sound]` (some on none), with no `sorryAx`
  and no `Lean.ofReduceBool`; see `lean4/README.md` for the statement table and
  proof strategy.

The enumeration in `reproduce.py` is a check, not a proof; the proof is the
`ν₂` argument above.
