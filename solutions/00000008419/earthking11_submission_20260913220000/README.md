# Disproof of conjecture `00000008419`

**Verdict: FALSE.**

This submission disproves conjecture `00000008419` as filed. The refutation is
unconditional and finite. The binary `[5,2,3]` code

```
C = {00000, 01101, 10011, 11110}
```

has minimum distance `d = 3` and dual distance `d^⊥ = 2`. Taking `t = 1`, the
conjecture's hypothesis `d^⊥ ≥ t+1` holds (`2 ≥ 2`), but the two
minimum-weight codewords have supports `{2,3,5}` and `{1,4,5}`, which are not a
`1-(5,3,λ)` design: coordinate 5 lies in both blocks while coordinates 1–4 lie
in one each. The failure therefore occurs already at `d^⊥ = 2`, destroying both
the main clause ("all minimal codewords form `t`-designs") and the clause "the
minimal failure of the converse occurs at `d^⊥ = 5`".

## The conjecture (verbatim, bilingual)

**English.** Definition: The correspondence between covering radius and design
strength of codes: the supports of dual codewords of weight w form t-designs.
Conjecture: For a code with dual distance d-perp at least t+1, all minimal
codewords form t-(n,w,lambda) designs; the converse of the Assmus-Mattson
theorem holds at weight 4, and the minimal failure of the converse occurs at
d-perp = 5. (converse of the Assmus-Mattson theorem)

**中文。** 定义：码的覆盖半径与设计强度的对应：权 w 的对偶码字的支撑集为
t-设计。猜想：对偶距离 d^⊥ ≥ t+1 的码的一切极小码字为 t-(n,w,λ) 设计；
Assmus–Mattson 定理的逆在权 4 情形成立，逆的失效最小例为 d^⊥ = 5。
（Assmus–Mattson 逆定理）

## What the statement asserts (it is garbled)

The filed text mixes a definition with a compound conjecture. We isolate three
claims:

| clause | content | status |
|:-------|:--------|:-------|
| **(C1)** | If a binary linear code has `d^⊥ ≥ t+1`, then all minimum-weight codewords form `t-(n,w,λ)` designs. | **false** (witness W1) |
| **(C2)** | The converse of the Assmus–Mattson theorem holds at weight `w = 4`. | false as a general statement (W2 is a weight-4 failure of (C1); see caveats) |
| **(C3)** | The minimal failure of the converse occurs at `d^⊥ = 5`. | **false** (failures occur at `d^⊥ = 2, 3, 4`) |

Because the conjecture is the conjunction of its clauses, falsifying (C1) alone
refutes it as filed.

Two readings of "minimal codewords" are natural: minimum-**weight** codewords,
and codewords whose support is minimal under inclusion. Both readings are
refuted (see "Alternative readings" below). We use the minimum-weight reading
for the main argument, because only then do all blocks have one common size `w`
and the expression `t-(n,w,λ)` design is well defined.

## The code

Coordinates are `1,…,5`; a word is the string `b₁b₂b₃b₄b₅` whose `i`-th
character is the entry at coordinate `i`.

```
C = span_{F₂}{01101, 10011} = {00000, 01101, 10011, 11110}.
```

| word | weight | support |
|:-----|:------:|:--------|
| `00000` | 0 | — |
| `01101` | 3 | `{2,3,5}` |
| `10011` | 3 | `{1,4,5}` |
| `11110` | 4 | `{1,2,3,4}` |

- `d = 3` (minimum nonzero weight).
- `d^⊥ = 2`. The dual code has weights `{2,3,4}`; the word `01100` (support
  `{2,3}`) is orthogonal to `01101`, `10011` and `11110`, and no unit vector is
  (each coordinate is nonzero on some nonzero codeword), so no dual word has
  weight 1.

### The minimum-weight codewords and the `1`-design test

| block | support | coordinate multiplicities |
|:------|:--------|:--------------------------|
| `01101` | `{2,3,5}` | `μ₁=1, μ₂=1, μ₃=1, μ₄=1, μ₅=2` |
| `10011` | `{1,4,5}` | (same) |

The multiplicities are `(μ₁,…,μ₅) = (1,1,1,1,2)`, which is not constant.
Equivalently the putative `λ` would be `b·w/n = 2·3/5 = 6/5 ∉ ℤ`. So the two
supports are **not** a `1-(5,3,λ)` design, although `d^⊥ = 2 ≥ t+1 = 2`. This
is the refutation of (C1).

### Why this does not contradict Assmus–Mattson

The AM theorem requires, in addition to `1 ≤ t ≤ d^⊥ − 1`, that the number of
weights of `C^⊥` in `{1,…,n−t}` is at most `d − t`. For `C` and `t = 1` that
count is `3` (weights `2,3,4` of `C^⊥` lie in `{1,…,4}`) while `d − t = 2`, so
the AM hypothesis fails and the theorem simply does not apply. Clause (C1)
proposes to replace the weight-count condition by the much weaker hypothesis
`d^⊥ ≥ t+1`; it is this strengthening that is false.

## Alternative readings

| reading | counterexample | data |
|:--------|:---------------|:-----|
| (a) `d^⊥ ≥ t+1` at the claimed `t` | **W1** `[5,2,3]` | `t=1`, `d^⊥=2`; multiplicities `(1,1,1,1,2)`; not a 1-design |
| (b) "minimal" = minimal-support | **W1** and **W2** | for W1 all three nonzero words (weights 3,3,4) are minimal-support; the weight-3 ones are the two generators, still not a 1-design. For W2 likewise all three nonzero words (weights 4,4,6) are minimal-support; the weight-4 ones are the two generators, still not a 1-design |
| (c) restrict to weight `4` | **W2** `[7,2,4]` = `span{1110001, 1001110}` | `d=4`, `d^⊥=2`; supports `{1,4,5,6}`, `{1,2,3,7}`; multiplicities `(2,1,1,1,1,1,1)`; not a 1-design |
| (d) `t = 2` | **W4** `[6,3,3]` = `span{110001, 101010, 011100}` | `d^⊥=3 ≥ 3`; 1-design holds, 2-design fails (pair counts take values `0` and `1`) |
| (e) `d^⊥ = 4`, `t = 3` | **W3** Hamming `[7,4,3]` | `d^⊥=4 ≥ 4`; 1- and 2-designs hold, 3-design fails (triple counts `0` and `1`) |

Each reading of the phrase "`d^⊥` at least `t+1`" that keeps the clause "all
minimal codewords form `t-(n,w,λ)` designs" is therefore false.

## Further witnesses and a control

| code | generators | `d` | `d^⊥` | `t` | design property of minimum-weight codewords |
|:-----|:-----------|:---:|:-----:|:---:|:--------------------------------------------|
| W1 `[5,2,3]` | `01101, 10011` | 3 | 2 | 1 | **not** a 1-design; multiplicities `(1,1,1,1,2)` |
| W2 `[7,2,4]` | `1110001, 1001110` | 4 | 2 | 1 | **not** a 1-design; multiplicities `(2,1,1,1,1,1,1)` |
| W3 Hamming `[7,4,3]` | `1000011, 0100101, 0010110, 0001111` | 3 | 4 | 3 | 1- and 2-designs, **not** a 3-design |
| W4 `[6,3,3]` | `110001, 101010, 011100` | 3 | 3 | 2 | 1-design, **not** a 2-design |
| W5 ext. Hamming `[8,4,4]` (control) | `11111111, 00001111, 00110011, 01010101` | 4 | 4 | 3 | **is** a `3-(8,4,1)` design |

W5 is included to show the design test is not vacuously negative, and to show
that a weight-4 code with `d^⊥ = 4` can genuinely satisfy the design claim: the
failure is a property of the individual code, not of the tester.

## Caveats

- **The statement is garbled**, and the clause about "the converse of the
  Assmus–Mattson theorem" is not made precise in the filing. We refute the
  literal main implication (C1) together with the location claim (C3). A reading
  that discards (C1) and (C3) entirely and keeps only an unstated, stricter
  "converse" would not be a reading of the filed text.
- The proposal in the task statement lists the same code as
  `{00000, 01111, 10110, 11001}` with minimum-weight supports `{2,3,5}` and
  `{1,4,5}`. That listing reads each binary string with the **last** character
  as coordinate 1. Reversing every word (`i ↦ 6−i`) gives the listing used here,
  `{00000, 01101, 10011, 11110}`, with identical supports and multiplicities;
  the two are the same code up to coordinate reversal. The proposal's
  conclusion is correct; only the coordinate convention needed pinning down.
- The "converse holds at weight 4" clause (C2) is not formalised: its precise
  content is unclear (converse of which implication, quantified how?). W2 shows
  that a minimum-weight-4 code with `d^⊥ = 2` fails clause (C1)'s conclusion, so
  any reading of (C2) that implies (C1) at weight 4 is false. We flag this as
  the one clause whose truth value we do not settle independently.
- AM's weight-count hypothesis is violated by W1, so this submission does not
  (and does not claim to) contradict the Assmus–Mattson theorem itself.

## Files

| File | Description |
|:-----|:------------|
| `README.md` | This document: verdict, bilingual quote, the code, support/multiplicity tables, AM background, alternative readings, caveats, file list, repro commands, rule-3 status. |
| `main.tex` | LaTeX source of the disproof. Standalone `article`, compiles with `tectonic main.tex`; uses `geometry`, `amsmath`, `amssymb`, `amsthm`, `array`, `parskip`, `booktabs` only (no CJK package, so no missing-glyph PDF). |
| `build/main.pdf` | PDF produced by `tectonic --outdir build main.tex`. |
| `reproduce.py` | Python 3 (standard library only) reproduction: builds W1–W5 from generator matrices over `F₂` with integer bitsets, computes `d`, `d^⊥`, minimum-weight codewords and supports, tests the `t`-design property, prints `PASS`/`FAIL`, non-zero exit on failure. |
| `lean4/lean-toolchain` | Pins `leanprover/lean4:v4.33.1`. |
| `lean4/lakefile.toml` | Lake configuration; library `Main`, no dependencies. |
| `lean4/Main.lean` | Lean 4 formalisation of W1, core Lean only (`import Std`, no Mathlib, no `sorry`). |
| `lean4/Check.lean` | `#print axioms` audit for every theorem. |
| `lean4/README.md` | Statement table, proof strategy, and scope note for the formalisation. |

## Reproducing

Python (dependency-free, runs in well under a second):

```sh
python3 reproduce.py
```

Expected tail:

```
PASS: the binary [5,2,3] code refutes conjecture 00000008419.
  d = 3, d^perp = 2; at t = 1 the hypothesis d^perp >= t+1 holds,
  yet the minimum-weight supports {2,3,5}, {1,4,5} are not a
  1-design (coordinate 5 has multiplicity 2, the others 1).
  Failures also occur at d^perp = 3, 4 and at minimum weight 4, so
  the claimed minimal failure at d^perp = 5 is false.
```

LaTeX document:

```sh
tectonic --outdir build main.tex      # writes build/main.pdf
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

- **LaTeX source** — present (`main.tex`), a standalone `article` using only
  `geometry`, `amsmath`, `amssymb`, `amsthm`, `array`, `parskip`, `booktabs`,
  compiling with `tectonic` (the PDF is placed in `build/`).
- **PDF document** — present at `build/main.pdf`, produced by
  `tectonic --outdir build main.tex`; non-empty (about 71 KiB).
- **Lean 4 project** — present under `lean4/`, with `lean-toolchain`,
  `lakefile.toml`, `Main.lean`, `Check.lean`, and a `README.md`. It formalises
  the witness `C = {00000, 01101, 10011, 11110}`: minimum distance `3`, dual
  distance `2`, the two minimum-weight codewords with supports `{2,3,5}` and
  `{1,4,5}`, and the failure of the `1`-design property (coordinate 5 has
  multiplicity 2, coordinates 1–4 have multiplicity 1). It uses core Lean only
  (no Mathlib, no `Finset`) and contains no `sorry`; `lake env lean Check.lean`
  reports no `sorryAx` (the only axiom ever reported is `propext`).
- **No modifications outside this directory** — all generated artifacts live
  under this submission directory; no files were deleted. Lean build products
  live under `lean4/.lake/` and the PDF under `build/`.
