# Disproof of conjecture `00000001006`

**Verdict: FALSE.**

The conjecture claims that `m`-ovoids of the parabolic quadric `Q(4,q)` exist
only when `m | (q+1)`. At the smallest case `q = 2`, `m = 2` the claim fails:
`Q(4,2)` has an ovoid (a 1-ovoid), and the complement of that ovoid meets every
one of the 15 generating lines in exactly `2` points, so it is a **2-ovoid**.
But `2` does not divide `q + 1 = 3`.

The refutation is unconditional, finite, and exact: no search heuristics, no
probabilistic steps, no reliance on unpublished results.

## The conjecture

Quoted verbatim from `conjectures/00000001006.md`:

> **English.** Definition: An m-ovoid (meeting every generating line in exactly
> m points). Conjecture: m-ovoids of Q(4,q) exist only when m | (q+1) (an
> existence criterion for m-ovoids).
>
> **中文。** 定义：m-ovoid(每条生成线恰交 m 点)。猜想：Q(4, q) 的 m-ovoid 仅在
> m | (q+1) 存在(m-ovoid 存在判据)。

Both languages write the relation with the divisibility symbol `|`
(“`m` divides `q+1`”). The claim to be refuted is the necessary condition

```
an m-ovoid of Q(4,q) exists  ⟹  m | (q+1).        (∗)
```

## Definitions

**The quadric `Q(4,2)`.** `Q(4,q)` is the parabolic quadric in `PG(4,q)`,
a classical generalized quadrangle of order `(q,q)`. For `q = 2` we use the
standard vector model: points are the nonzero vectors `x ∈ F_2^5` with

```
Q(x) = x0 + x1*x2 + x3*x4 = 0        (over F_2, x0^2 = x0),
B(a,b) = a1*b2 + a2*b1 + a3*b4 + a4*b3,
```

so that `Q(a+b) = Q(a) + Q(b) + B(a,b)`.

**Generating lines.** The lines of `Q(4,2)` are the triples `{a, b, a+b}` where
`a, b` are distinct points with `B(a,b) = 0` (equivalently, `a+b` is again a
point). Direct enumeration gives:

| quantity | value |
|:---------|:------|
| points | `15` |
| lines | `15` |
| points per line | `3 = q+1` |
| lines per point | `3 = q+1` |
| total incidences | `15 * 3 = 45` |

**`m`-ovoid.** A set of points of `Q(4,q)` that meets every generating line in
exactly `m` points. A `1`-ovoid is called an **ovoid**.

## The explicit ovoid and its complement

Enumerating all `5`-subsets (`C(15,5) = 3003`) shows that `Q(4,2)` has **exactly
6 ovoids**. One of them is

```
O = { (0,1,0,0,0), (0,0,1,0,0), (1,1,1,1,0), (1,1,1,0,1), (0,1,1,1,1) }
```

(with binary encodings `{2, 4, 15, 23, 30}`). It has `|O| = 5 = q^2 + 1` points
and meets each of the 15 lines in exactly `1` point. Its complement is

```
O^c = { (1,1,1,0,0), (0,0,0,1,0), (0,1,0,1,0), (0,0,1,1,0), (0,0,0,0,1),
        (0,1,0,0,1), (0,0,1,0,1), (1,0,0,1,1), (1,1,0,1,1), (1,0,1,1,1) }
```

(with binary encodings `{7, 8, 10, 12, 16, 18, 20, 25, 27, 29}`), with
`|O^c| = 10 = q^2 + q` points. Since each line has `3` points and `O` occupies
exactly one, `O^c` occupies exactly the other `2`: **`O^c` is a 2-ovoid of
`Q(4,2)`**.

## Line-hit table

Each line is written as `{a,b,a+b}` in coordinates `(x0,x1,x2,x3,x4)`; the last
two columns give the number of its points lying in `O` and in `O^c`.

| # | generating line `{a, b, a+b}` | `\|L ∩ O\|` | `\|L ∩ O^c\|` |
|--:|:------------------------------|:------:|:------:|
| 1 | `{(0,1,0,0,0),(0,0,0,1,0),(0,1,0,1,0)}` | 1 | 2 |
| 2 | `{(0,1,0,0,0),(0,0,0,0,1),(0,1,0,0,1)}` | 1 | 2 |
| 3 | `{(0,1,0,0,0),(1,0,0,1,1),(1,1,0,1,1)}` | 1 | 2 |
| 4 | `{(0,0,1,0,0),(0,0,0,1,0),(0,0,1,1,0)}` | 1 | 2 |
| 5 | `{(0,0,1,0,0),(0,0,0,0,1),(0,0,1,0,1)}` | 1 | 2 |
| 6 | `{(0,0,1,0,0),(1,0,0,1,1),(1,0,1,1,1)}` | 1 | 2 |
| 7 | `{(1,1,1,0,0),(0,0,0,1,0),(1,1,1,1,0)}` | 1 | 2 |
| 8 | `{(1,1,1,0,0),(0,0,0,0,1),(1,1,1,0,1)}` | 1 | 2 |
| 9 | `{(1,1,1,0,0),(1,0,0,1,1),(0,1,1,1,1)}` | 1 | 2 |
| 10 | `{(0,1,0,1,0),(0,0,1,0,1),(0,1,1,1,1)}` | 1 | 2 |
| 11 | `{(0,1,0,1,0),(1,1,1,0,1),(1,0,1,1,1)}` | 1 | 2 |
| 12 | `{(0,0,1,1,0),(0,1,0,0,1),(0,1,1,1,1)}` | 1 | 2 |
| 13 | `{(0,0,1,1,0),(1,1,1,0,1),(1,1,0,1,1)}` | 1 | 2 |
| 14 | `{(1,1,1,1,0),(0,1,0,0,1),(1,0,1,1,1)}` | 1 | 2 |
| 15 | `{(1,1,1,1,0),(0,0,1,0,1),(1,1,0,1,1)}` | 1 | 2 |
| | **totals** | **15** | **30** |

The `15` listed lines are exactly the complete line set of `Q(4,2)`; this
completeness is part of the exact computation and of the Lean theorem
`lines15_is_all_lines`.

## The conclusion: `2 ∤ 3`

```
q + 1 = 3,   m = 2,   3 = 2·1 + 1   ⟹   2 ∤ 3.
```

A `2`-ovoid of `Q(4,2)` exists (the complement of the ovoid `O` above), yet
`m = 2` does not divide `q+1 = 3`. The necessary condition `(∗)` — and hence
conjecture `00000001006` — is false.

More generally, if `Q(4,q)` has an ovoid `O` then every line meets `O` once and
therefore meets `O^c` exactly `q` times, so `O^c` is a `q`-ovoid while
`q ∤ q+1` for all `q ≥ 2`. This submission formalises the smallest instance
`q = 2`; the general complement construction is recorded as context.

## Caveats

- **The literal reading is divisibility.** Both the English and the Chinese
  statements write `m | (q+1)`; there is no inequality and no other condition in
  the file. The witness refutes precisely this reading.
- **Weaker `m ≤ q+1` reading.** If the condition were replaced by `m ≤ q+1`,
  then `2 ≤ 3` would be consistent and the witness would not apply. That is not
  what the filed statement says; it is recorded only to make the reading
  explicit. (Note that the witness satisfies `m ≤ q+1` anyway.)
- **One-directional or biconditional, both fail.** “Only when” is a necessary
  condition, formalised as `(∗)`. The witness violates it, so the conjecture
  fails under either reading.
- **The vector model is the standard one.** `Q(4,2)` has `15` points and `15`
  lines in every model; the model used here is the parabolic quadric
  `x0 + x1x2 + x3x4 = 0` in `PG(4,2)`. The Chinese phrase “生成线” and the
  English “generating line” both refer to the lines of the quadrangle.
- **Finite and exact.** Everything is an exhaustive finite computation; the
  ovoid is given explicitly, and no result about `Q(4,q)` for general `q` is
  needed for the `q=2` refutation.

## Files

| File | Description |
|:-----|:------------|
| `README.md` | This document: verdict, bilingual quote, definitions, witness, table, conclusion, caveats, reproduction, status. |
| `main.tex` | LaTeX source of the disproof. Standalone `article` (with `ctex` for the Chinese quote), compiles with `tectonic main.tex --outdir build`. |
| `build/main.pdf` | PDF produced by `tectonic` (the artifact is placed in `build/`). |
| `reproduce.py` | Python 3 (standard library only) exact enumeration: rebuilds `Q(4,2)`, enumerates all ovoids, checks the hit counts of `O` and `O^c`, checks `2 ∤ 3`; prints `PASS`/`FAIL`, non-zero exit on failure. |
| `lean4/lean-toolchain` | Pins `leanprover/lean4:v4.33.1`. |
| `lean4/lakefile.toml` | Lake configuration; library `Main`, project `tlmc1006`, no dependencies. |
| `lean4/Main.lean` | Lean 4 formalisation, core Lean only (`import Std`, no Mathlib, no `sorry`). |
| `lean4/Check.lean` | `#print axioms` audit for every theorem. |
| `lean4/README.md` | Statement table, proof strategy, and scope note for the formalisation. |

## Reproducing

Python (dependency-free, runs in well under a second):

```sh
python3 reproduce.py
```

It prints the point/line/ovoid counts, the explicit ovoid and complement, the
line-hit table, and `PASS` (exit code `0`) exactly when every check holds.

LaTeX document:

```sh
tectonic main.tex --outdir build      # produces build/main.pdf
```

Lean 4 project:

```sh
cd lean4
lake build
lake env lean Check.lean
```

## Status against the submission rules

Rule 3 requires each submission to contain the LaTeX source code, a PDF
document, and a Lean 4 project.

- **LaTeX source** — present (`main.tex`), a standalone `article` using
  `geometry`, `amsmath`, `amssymb`, `amsthm`, `array`, `parskip`, `booktabs`,
  and `ctex` (the last only to typeset the Chinese quote); it compiles with
  `tectonic main.tex`.
- **PDF document** — present at `build/main.pdf`, produced by `tectonic` and
  non-empty.
- **Lean 4 project** — present under `lean4/` with `lean-toolchain`,
  `lakefile.toml`, `Main.lean`, `Check.lean`, and a `README.md`. It models
  points as `Fin 5 → Bool`, defines `Q`, the bilinear form `B`, the line
  relation and the predicate `IsMOvoid`, hardcodes the ovoid `O`, and proves by
  `decide` that `O` is a 1-ovoid, that `O^c` is a 2-ovoid, that a 2-ovoid
  exists, and that `¬ (2 ∣ 3)`. It uses core Lean only (no Mathlib) and
  contains no `sorry`; `lake env lean Check.lean` reports no `sorryAx`
  (the `decide` proofs depend at most on `propext`).
