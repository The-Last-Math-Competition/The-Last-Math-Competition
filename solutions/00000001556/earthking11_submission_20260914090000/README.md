# Disproof of conjecture `00000001556`

**Verdict: FALSE.**

Conjecture `00000001556` claims that the chromatic number of the planar distance
graph `G(Z², D)` with `D = {1, 2, 4}` is `7`. It is false: the explicit map

```
c5(x, y) = (x + 2y) mod 5
```

is a proper **5-colouring** of the lattice distance graph under *both* standard
readings of the distance set, so `χ ≤ 5 < 7`. In fact the exact chromatic
numbers are

| reading | chromatic number | lower bound | upper bound |
|:--------|:----------------:|:------------|:------------|
| squared norms in `{1,2,4}` | **5** | 5-clique `C5` | colouring `c5` |
| Euclidean norms in `{1,2,4}` | **3** | 3-clique `C3` | colouring `c3(x,y) = (x+y) mod 3` |
| union of the two | **5** | 5-clique `C5` | colouring `c5` |

A non-standard Manhattan (L1) reading has an explicit 9-clique, so `χ ≥ 9`
there and `7` is false as well.

## The conjecture, quoted verbatim (bilingual)

From `conjectures/00000001556.md`:

> **English.** Conjecture: The chromatic number of the planar distance graph
> G(Z², D) with D = {1, 2, 4} is 7 (the exact chromatic number of a fixed small
> distance set).
>
> **中文。** 猜想：平面距离图 G(Z², D),D = {1, 2, 4} 的色数为 7(固定小距离集的精确色数)。

## The definitional ambiguity, and how one witness covers both readings

The conjecture writes three scalars `D = {1, 2, 4}`, so `D` is a set of
*distances*, not of integer displacement vectors. There are two standard,
equally natural renderings:

1. **Squared-norm reading** (common in lattice-colouring work, where squared
   distances are integral): a displacement `d = (dx,dy)` is an edge iff
   `dx² + dy² ∈ {1,2,4}`. This is `Dsq`, 12 vectors:
   `(±1,0), (0,±1), (±1,±1), (±2,0), (0,±2)`.
2. **Euclidean-norm reading** (the literal reading of "distance"): a
   displacement is an edge iff `√(dx² + dy²) ∈ {1,2,4}`, i.e.
   `dx² + dy² ∈ {1,4,16}`. This is `Deuc`, 12 axis vectors:
   `(±1,0), (0,±1), (±2,0), (0,±2), (±4,0), (0,±4)`.

Their union `D_union = Dsq ∪ Deuc` has **16** vectors; the Euclidean reading
adds `(±4,0), (0,±4)` beyond the squared reading. Because

```
χ(G) ≤ max(χ(edge sets))   for the union graph, and
every edge of either reading is an edge of the union graph,
```

proving properness of one colouring for the 16-vector union covers both
readings at once. That is exactly what the witness `c5` does.

**Why the modulus 5 and the coefficients (1, 2)?** For an edge `u → u+d` the
colour difference is `c5(u+d) − c5(u) ≡ dx + 2dy (mod 5)`, regardless of the
base point `u`. So properness is equivalent to the single finite statement

```
for every displacement d in the (union) set:  (dx + 2·dy) mod 5 ≠ 0.
```

The table below verifies it for all 16 displacements.

**How a periodic colouring covers all of Z².** `c5` is defined by a formula on
every lattice point, so it is a global colouring, not a finite-box check. More
generally, by the **de Bruijn–Erdős compactness theorem** the chromatic number
of a locally finite graph equals the supremum of the chromatic numbers of its
finite subgraphs; for a lattice graph `G(Z²,D)` this is
`χ = sup_{F finite ⊂ Z²} χ(F)`. Hence a finite clique certifies a lower bound
and a periodic colouring certifies a global upper bound — the two ingredients
used below.

## Forbidden-residue table (all 16 union displacements)

| displacement `(dx,dy)` | reading(s) | `dx+2dy` | `mod 5` | `dx²+dy²` | Euclidean length |
|:----------------------:|:----------:|---------:|:-------:|----------:|:----------------:|
| `(1, 0)`   | both    |  1 | 1 |  1 | 1 |
| `(-1, 0)`  | both    | -1 | 4 |  1 | 1 |
| `(0, 1)`   | both    |  2 | 2 |  1 | 1 |
| `(0, -1)`  | both    | -2 | 3 |  1 | 1 |
| `(1, 1)`   | squared |  3 | 3 |  2 | √2 |
| `(1, -1)`  | squared | -1 | 4 |  2 | √2 |
| `(-1, 1)`  | squared |  1 | 1 |  2 | √2 |
| `(-1, -1)` | squared | -3 | 2 |  2 | √2 |
| `(2, 0)`   | both    |  2 | 2 |  4 | 2 |
| `(-2, 0)`  | both    | -2 | 3 |  4 | 2 |
| `(0, 2)`   | both    |  4 | 4 |  4 | 2 |
| `(0, -2)`  | both    | -4 | 1 |  4 | 2 |
| `(4, 0)`   | euclid  |  4 | 4 | 16 | 4 |
| `(-4, 0)`  | euclid  | -4 | 1 | 16 | 4 |
| `(0, 4)`   | euclid  |  8 | 3 | 16 | 4 |
| `(0, -4)`  | euclid  | -8 | 2 | 16 | 4 |

All sixteen residues are nonzero modulo 5, so `c5` never uses the same colour
on the two ends of an edge. Therefore `χ ≤ 5` for the union graph, hence for
both readings, and the claimed value `7` is impossible.

## Exact values, with cliques and colourings

### Squared-norm reading: `χ = 5`

- **Lower bound.** The five points

  ```
  C5 = { (0,0), (1,0), (-1,0), (0,1), (0,-1) }
  ```

  form a clique: their ten pairwise differences are
  `(±1,0), (0,±1), (±2,0), (0,±2), (±1,±1), (±1,∓1)`, all of squared norm
  `1`, `2` or `4`. (The centre of the lattice plus its four nearest neighbours.)
  Hence `χ ≥ 5`.
- **Upper bound.** `c5(x,y) = (x+2y) mod 5` is proper by the table. Hence
  `χ ≤ 5`.
- Therefore `χ = 5` exactly.

### Euclidean-norm reading: `χ = 3`

- **Lower bound.** The three points

  ```
  C3 = { (0,0), (1,0), (2,0) }
  ```

  form a clique: the pairwise differences are `(1,0), (2,0), (1,0)`, of
  Euclidean length `1, 2, 1`, all in `{1,2,4}`. Hence `χ ≥ 3`.
- **Upper bound.** `c3(x,y) = (x+y) mod 3` is proper: for `d ∈ Deuc` we have
  `dx+dy ≡ ±1, ±2, ±4 ≢ 0 (mod 3)`. Hence `χ ≤ 3`.
- Therefore `χ = 3` exactly.

### Union graph: `χ = 5`

`C5 ⊂ Dsq ⊂ D_union` gives `χ ≥ 5`, and `c5` gives `χ ≤ 5`; so the union graph
also has chromatic number exactly `5`.

Since `5 < 7` and `3 < 7`, the conjectured value `7` fails under **both**
readings.

## Caveats

- **Non-standard Manhattan reading.** If `D` is read as a set of Manhattan
  (taxicab) distances `|dx| + |dy| ∈ {1,2,4}`, the displacement set strictly
  contains the union above (it adds `(±1,±3), (±3,±1), (±2,±2)`). The nine
  points

  ```
  { (0,0), (1,±1), (2,0), (2,±2), (3,±1), (4,0) }
  ```

  are pairwise at Manhattan distance `1`, `2` or `4`, so they form a 9-clique
  and `χ ≥ 9 > 7`. Here `c5` is *not* proper: the displacement `(3,1)` has
  `3 + 2·1 = 5 ≡ 0 (mod 5)`. Thus `7` is false under this reading too.
- **The continuous plane `R²` is a different (open) problem.** The only way to
  rescue the value `7` is to reinterpret the vertex set `Z²` as the continuum
  `R²`. There, the chromatic number of the plane with forbidden distance set
  `{1,2,4}` is *not* settled by this argument; the Hadwiger–Nelson problem
  leaves the chromatic number of the plane in `{5,6,7}`, so `7` cannot be
  excluded in the continuum. This is **not** the conjecture as filed: it
  explicitly writes `G(Z², D)`, the integer lattice. A referee should read this
  submission as disproving the lattice statement, not the open continuum
  question.
- **"Planar distance graph" names a graph on lattice points, not a planar
  graph** in the graph-theoretic sense. `G(Z², D)` is far from planar.

## Files

| File | Description |
|:-----|:------------|
| `README.md` | This document: verdict, bilingual quote, the ambiguity and the witness, the 16-row residue table, exact values, caveats, file list, reproducibility, rule-3 status. |
| `main.tex` | LaTeX source of the disproof (standalone `article`), compiles with `tectonic --outdir build main.tex`. |
| `build/main.pdf` | PDF produced by `tectonic --outdir build main.tex`. |
| `reproduce.py` | Python 3 (standard library only): displacement sets for both readings, 16-residue check, brute-force properness of `c5` on `[-200,200]²` and `c3` on `[-100,100]²`, the 5-clique and 3-clique, the Manhattan 9-clique, exact chromatic numbers, `PASS`/`FAIL`, non-zero exit on failure. |
| `lean4/lean-toolchain` | Pins `leanprover/lean4:v4.33.1`. |
| `lean4/lakefile.toml` | Lake configuration; library name `tlmc1556`, no dependencies. |
| `lean4/Main.lean` | Lean 4 formalisation, core Lean only (`import Std`, no Mathlib, no `sorry`). |
| `lean4/Check.lean` | `#print axioms` audit for every theorem. |
| `lean4/README.md` | Statement table, proof strategy, axiom audit, scope note. |

## Reproducing

Python (dependency-free, runs in under a second):

```sh
python3 reproduce.py          # prints PASS, exits 0
```

It builds the displacement sets for both readings, checks all 16 residues
`(dx + 2dy) mod 5 ≠ 0`, brute-forces properness of `c5` on `[-200,200]²` for the
union graph and of `c3` on `[-100,100]²` for the Euclidean reading, exhibits the
5-clique `C5` and the 3-clique `C3`, verifies the Manhattan 9-clique, and prints
the exact chromatic numbers with the cliques as lower bounds. It exits non-zero
if any check fails.

LaTeX document:

```sh
tectonic --outdir build main.tex     # produces build/main.pdf
```

Lean 4 project:

```sh
cd lean4
lake build
lake env lean Check.lean
```

`lake build` exits `0`; `lake env lean Check.lean` prints `#print axioms` for
every theorem and reports no `sorryAx` (the `decide` computations depend on no
axioms; the properness theorems depend only on `propext` and `Quot.sound`).

## Status against the submission rules

Rule 3 requires each submission to contain the LaTeX source, a PDF document,
and a Lean 4 project.

- **LaTeX source** — present (`main.tex`), a standalone `article` using only
  `geometry`, `amsmath`, `amssymb`, `amsthm`, `array`, `parskip`, `booktabs`;
  compiles with `tectonic --outdir build main.tex`.
- **PDF document** — present at `build/main.pdf`.
- **Lean 4 project** — present under `lean4/`, with `lean-toolchain`
  (`leanprover/lean4:v4.33.1`), `lakefile.toml` (library `tlmc1556`),
  `Main.lean`, `Check.lean` (`#print axioms`), and `README.md`. It formalises,
  in core Lean only (no Mathlib), the 16-displacement residue check `D_ok`, the
  properness theorem `color_shift_ne` for **all** `(x,y) ∈ Z²` and **all**
  `d ∈ D`, the 5-clique certificate `C5_clique`, the Euclidean-reading
  properness `color3_shift_ne` and the 3-clique certificate `C3_clique`. It
  contains no `sorry`; the audit reports no `sorryAx`.
