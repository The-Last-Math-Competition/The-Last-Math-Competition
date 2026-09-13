# Disproof of conjecture `00000000463`

**Verdict: FALSE.**

This submission disproves conjecture `00000000463` as stated. The refutation is
unconditional, completely elementary, and does not depend on any unproved
hypothesis: for every `n ≥ 4` the integer `n^(n−2)` is divisible by the square
of a prime, so the counting function on the left-hand side of the conjectured
asymptotic is bounded, whereas `c·N/√(log N)` tends to infinity for every
`c > 0`.

## The conjecture

Quoted verbatim from `conjectures/00000000463.md`:

> **English.** Definition: τ(K_n) = n^{n-2}. Conjecture:
> #{n ≤ N : n^{n−2} squarefree} ~ c·N/√log N (a density compatible with abc).
>
> **中文。** 定义：τ(K_n) = n^{n-2}。猜想：#{n ≤ N : n^{n−2} 无平方因子}
> ~ c·N/√log N(与 abc 兼容的密度)。

Here `τ(K_n) = n^{n−2}` is Cayley's formula for the number of spanning trees of
the complete graph `K_n`. The conjecture claims that the set of `n ≤ N` for
which this tree count is squarefree has size asymptotic to `c·N/√(log N)`.

## Conventions

The statement is informal at three points. We fix the conventions and show the
verdict is unchanged under every reasonable choice.

1. **Domain.** `n ∈ {1, 2, 3, …}`, as `#{n ≤ N}` suggests.
2. **The exponent `n−2` at `n = 1`.** `1^{1−2} = 1^{−1}` is not defined in `ℕ`
   (negative exponents leave `ℕ`); it equals `1` in `ℤ` or `ℚ`. We exclude
   `n = 1` from the main count and record that including it (with
   `1^{−1} := 1`) adds exactly one index.
3. **Is `1` squarefree?** Yes, by the standard convention (its factorisation is
   empty; no prime square divides it). So `2^0 = 1` is squarefree. Under the
   convention of item 2, `1^{−1} = 1` is squarefree too.
4. **Meaning of `~`.** The standard meaning: `f(N) ~ g(N)` iff `f(N)/g(N) → 1`.
   In particular `g` must be unbounded when `f` is.

## The argument

**Theorem.** For every integer `n ≥ 4`, `n^(n−2)` is not squarefree.

**Proof.** Let `n ≥ 4` and let `p` be any prime divisor of `n` (one exists since
`n ≥ 2`). Write `v_p` for the `p`-adic valuation. Since
`n^(n−2) = ∏_q q^{(n−2)·v_q(n)}`,

```
v_p(n^(n−2)) = (n−2)·v_p(n) ≥ 2·1 = 2.
```

Hence `p² | n^(n−2)`: a prime square divides `n^(n−2)`, so it is not squarefree.

**Corollary.** The only `n ≥ 2` with `n^(n−2)` squarefree are `n = 2`
(`2^0 = 1`) and `n = 3` (`3^1 = 3`). Adding `n = 1` under the convention
`1^{−1} := 1` gives one more. So for every `N ≥ 3` the count is `2`
(excluding `n = 1`) or `3` (including it), while `c·N/√(log N) → ∞` for every
`c > 0`. Therefore

```
#{n ≤ N : n^(n−2) squarefree} / (c·N/√(log N)) ≤ 3√(log N)/(c·N) → 0 ≠ 1,
```

and the asserted asymptotic equivalence is false. If `c = 0` no asymptotic
equivalence is defined, and "a density compatible with abc" clearly intends
`c > 0`.

## Count table

`c = 1` is shown; any `c > 0` only rescales the last column.

| `N` | count (`n ≥ 2`) | count (`n ≥ 1`, `1^{−1}:=1`) | `N/√log N` |
|----:|:---------------:|:---------------------------:|-----------:|
| 10        | 2 | 3 | 6.59 |
| 10²       | 2 | 3 | 46.60 |
| 10³       | 2 | 3 | 380.48 |
| 10⁴       | 2 | 3 | 3295.05 |
| 10⁵       | 2 | 3 | 29471.83 |
| 10⁶       | 2 | 3 | 269039.80 |

Exhaustively verified (exact factorisation of the base `n`) for `2 ≤ n ≤ 3000`:
the squarefree indices are exactly `[2, 3]`. For `n ≤ 12` the script additionally
factors `n^(n−2)` directly by trial division and confirms agreement.

## Alternative readings

We tried to save the conjecture by varying each convention; none succeeds.

| Reading | Outcome |
|:--------|:--------|
| `n` starts at 2 | count is exactly 2 for all `N ≥ 3`; still bounded, still refuted. |
| `n` starts at 1, `1^{−1} := 1`, `1` squarefree | count is 3 for all `N ≥ 3`; still bounded, still refuted. |
| "squarefree" excludes 1 | then `n = 2` (`2^0 = 1`) is excluded too and the count is 1; even more bounded. |
| Domain restricted to primes `n` | for prime `n ≥ 5`, `v_n(n^(n−2)) = n−2 ≥ 3`, so not squarefree; only 2 and 3 survive, count 2. |
| Read "`n^(n−2)` squarefree" as "`n` squarefree" | count is `~ (6/π²)N`; ratio to `c·N/√log N` is `~ (6/(π²c))√log N → ∞`, so no constant `c` works. |
| Read `~` as `≪` (big-O) | a bounded count *is* `O(N/√log N)`, but that is a strictly weaker, different claim and contradicts the standard meaning of `~` and "density compatible with abc". |

Only the last line changes the meaning of the symbol `~` rather than a
convention on the domain; it does not express the conjecture as filed, so the
refutation stands. We record it as a caveat, not as an ambiguity.

## Caveats

- The constant `c` is never specified in the conjecture. This does not matter:
  the failure holds for every `c > 0`, and for `c ≤ 0` the right-hand side is
  not a positive density.
- The `n = 1` convention is the only genuinely ambiguous point. Both choices
  (exclude `n = 1`, or set `1^{−1} := 1`) give a bounded count, so the verdict
  is unaffected.
- If one deliberately re-reads `~` as `O`, the claim becomes true but trivial
  and is no longer the conjecture as written. This is documented above.

## Files

| File | Description |
|:-----|:------------|
| `README.md` | This document: verdict, bilingual quote, conventions, argument, table, alternative readings, caveats, reproducibility, rule-3 status. |
| `main.tex` | LaTeX source of the disproof (standalone `article`), compiles with `tectonic main.tex`. |
| `build/main.pdf` | PDF produced by `tectonic --outdir build main.tex`. |
| `reproduce.py` | Python 3 (standard library only, no `sympy`): exact factorisation of the base `n` for `2 ≤ n ≤ 3000`, direct cross-check for `n ≤ 12`, count table, `PASS`/`FAIL`, non-zero exit on failure. |
| `lean4/lean-toolchain` | Pins `leanprover/lean4:v4.33.1`. |
| `lean4/lakefile.toml` | Lake configuration; library `Main`, no dependencies. |
| `lean4/Main.lean` | Lean 4 formalisation, core Lean only (`import Std`, no Mathlib, no `sorry`). |
| `lean4/Check.lean` | `#print axioms` audit for every theorem. |
| `lean4/README.md` | Statement table, proof strategy, scope note. |

## Reproducing

Python (dependency-free, runs in a fraction of a second):

```sh
python3 reproduce.py
```

It factors each base `n` by trial division, uses the exact identity
`v_p(n^(n−2)) = (n−2)·v_p(n)`, cross-checks against direct trial division of
`n^(n−2)` for `n ≤ 12`, prints the count table, and exits `0` on `PASS`.

LaTeX document:

```sh
tectonic --outdir build main.tex
```

Lean 4 project:

```sh
cd lean4
lake build
lake env lean Check.lean
```

`lake build` exits `0`; `Check.lean` prints `#print axioms` for every theorem
and reports no `sorryAx` (only `propext`, `Quot.sound`, and `Classical.choice`
for the general statements; the concrete computations depend on no axioms).

## Status against the submission rules

Rule 3 requires each submission to contain the LaTeX source, a PDF document,
and a Lean 4 project.

- **LaTeX source** — present (`main.tex`), a standalone `article` using only
  `geometry`, `amsmath`, `amssymb`, `amsthm`, `array`, `parskip`, `booktabs`;
  compiles with `tectonic main.tex`.
- **PDF document** — present at `build/main.pdf`.
- **Lean 4 project** — present under `lean4/`, with `lean-toolchain`,
  `lakefile.toml`, `Main.lean`, `Check.lean`, and a `README.md`. It formalises
  `not_squarefree_pow` (`∀ n ≥ 4`, `n^(n−2)` is not squarefree), the base cases
  `Squarefree 1`, `Squarefree (2^(2−2))`, `Squarefree (3^(3−2))`, the
  characterisation `Squarefree (n^(n−2)) ↔ n ≤ 3` for `n ≥ 1`, and the count
  bound `sqfreeCount N ≤ 3`. It uses core Lean only (no Mathlib) and contains
  no `sorry`; the audit reports no `sorryAx`.
