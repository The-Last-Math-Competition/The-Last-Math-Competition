# Disproof of conjecture `00000008371`

**Verdict: FALSE.** The conjecture is a conjunction of four laws about the cells
of the tropical Grassmannian (the "space trees"). At least one conjunct fails for
every admissible `n`: the asserted count formula `(n-2)!(n-3)!/2` evaluates to
`1/2` at `n = 3` and so is not a count; and it never equals the vertex count
`C(n,2)` of the Johnson graph `J(n,2)` that the same conjecture asserts to be the
adjacency graph. The refutation needs no tropical geometry; the known
Speyer–Sturmfels count `(2n-5)!!` is cited only as context.

## The conjecture

> **Definition:** The Nielsen cells of the tropical Grassmannian: the count
> `space_tree` of cells of the tropicalization of `Gr(2,n)` (space trees).
> **Conjecture:** `space_tree` (the count of space trees) is the type count
> `(n-2)! (n-3)!/2` (a type counting law); the mod-2 pattern of the count (parity)
> follows the power law `2^{n-3}` (a power parity law); the adjacency graph of
> cells (shared faces of adjacent cells) is the Johnson graph `J(n,2)` (a Johnson
> adjacency law); and the complete spectrum of the adjacency graph (eigenvalues)
> is a difference set (a difference set spectrum law).

Original statement as filed in `conjectures/00000008371.md`:

> **English.** Definition: The Nielsen cells of the tropical Grassmannian: the count
> space_tree of cells of the tropicalization of Gr(2,n) (space trees). Conjecture:
> space_tree (the count of space trees) is the type count (n-2)! (n-3)!/2 (a type
> counting law); the mod-2 pattern of the count (parity) follows the power law
> 2^{n-3} (a power parity law); the adjacency graph of cells (shared faces of
> adjacent cells) is the Johnson graph J(n,2) (a Johnson adjacency law); and the
> complete spectrum of the adjacency graph (eigenvalues) is a difference set (a
> difference set spectrum law).
>
> **中文。** 定义：热带 Grassmannian 的 Nielsen 胞腔：Gr(2,n) 的热带化（空间树）的胞腔的计数
> space_tree。猜想：space_tree（空间树的计数）= (n-2)!·(n-3)!/2 的类型计数（类型计数律）；
> 且计数的模 2（奇偶）的规律为 2^{n-3} 的幂（幂奇偶律）；胞腔的邻接（相邻胞腔的共享面）的图
> 为 Johnson 图 J(n,2)（Johnson 邻接律）；邻接图的谱（特征值）的完全谱为差集（差集谱律）。

Because the conjecture is a conjunction `(A) ∧ (B) ∧ (C) ∧ (D)`, refuting one
conjunct refutes the whole. We give three independent failures.

## Why it is false

Write `F(n) = (n-2)!(n-3)!/2` and `J_n = C(n,2) = n(n-1)/2`.

### Failure 1 — the formula is not a count at `n = 3`

`F(3) = 1!·0!/2 = 1/2`, which is not an integer. A count of cells is a
non-negative integer, so it cannot equal `1/2`. The values are

`F(3) = 1/2`, `F(4) = 1`, `F(5) = 6`, `F(6) = 72`.

No cardinality can be `1/2`, so conjunct (A) fails at `n = 3`. (As a secondary
point, a half-integer also has no parity, so conjunct (B), the power parity law, is
likewise undefined there.)

### Failure 2 — the formula never equals the Johnson vertex count

The Johnson graph `J(n,2)` has as vertices the 2-subsets of an `n`-set, hence
`C(n,2) = n(n-1)/2` vertices: `3, 6, 10, 15, 21, 28` for `n = 3..8`. This never
equals `F(n)`:

| `n` | `n = 3` | `n = 4` | `n = 5` | `n = 6` | `n ≥ 6` |
|---|---|---|---|---|---|
| `F(n)` | `1/2` | `1` | `6` | `72` | `> C(n,2)` (proved by induction) |
| `C(n,2)` | `3` | `6` | `10` | `15` | `C(n,2)` |

For `n = 4,5,6` this is `1 ≠ 6`, `6 ≠ 10`, `72 ≠ 15`; and for all `n ≥ 6`,
`F(n) > C(n,2)` (the recurrence `F(n+1) = (n-1)(n-2)F(n)` makes `F` grow far
faster than the quadratic `C(n,2)`). So conjunct (A) and conjunct (C) are mutually
inconsistent for every `n ≥ 3`: at least one of them is false. This failure does
not use `n = 3`.

### Failure 3 — comparison with the known count (context)

It is a theorem of Speyer–Sturmfels (*The tropical Grassmannian*, Adv. Geom. 4
(2004), 389–411) that `Trop(Gr(2,n))` has exactly `(2n-5)!! = 1·3·5···(2n-5)`
maximal cones, equivalently the space of phylogenetic trees with `n` leaves has
`(2n-5)!!` vertices — these are the "space trees" of the conjecture. Values:
`1, 3, 15, 105, 945` for `n = 3..7`. For every `n ≥ 3` this differs from both the
formula and the Johnson count:

| `n` | `F(n)` | `C(n,2)` | `(2n-5)!!` |
|---|---|---|---|
| 3 | `1/2` | 3 | 1 |
| 4 | 1 | 6 | 3 |
| 5 | 6 | 10 | 15 |
| 6 | 72 | 15 | 105 |
| 7 | 1440 | 21 | 945 |
| 8 | 43200 | 28 | 10395 |

## The `n = 3` caveat, and why the refutation survives it

For `n = 3`, `Trop(Gr(2,3))` is a single point, so the true count is `1` and
`(2n-5)!! = 1`. If the author intended to exclude `n = 3`, then the `1/2`
objection (Failure 1) weakens: the formula would never be evaluated where it is
non-integral. We state this caveat explicitly.

The refutation survives, because it does not depend on `n = 3`:

- **Failure 2** holds for `n = 4, 5, 6` explicitly (`1 ≠ 6`, `6 ≠ 10`, `72 ≠ 15`)
  and for all `n ≥ 6` by the growth argument. Hence for every `n ≥ 4`, conjuncts
  (A) and (C) contradict each other.
- **Failure 3** holds for `n = 4,5,6,7` (`1 ≠ 3`, `6 ≠ 15`, `72 ≠ 105`,
  `1440 ≠ 945`), and `F` grows super-exponentially while `(2n-5)!!` does not, so
  agreement never resumes.

So even under the most generous reading — exclude `n = 3`, take the count formula
as a formula rather than a count — the conjunction is still false for every
`n ≥ 4`. The `n = 3` issue is offered as a first, simplest failure, not as the
sole basis of the disproof.

## Files

| file | purpose |
|---|---|
| `main.tex` | the disproof (LaTeX source) |
| `build/main.pdf` | compiled PDF, built with `tectonic --outdir build main.tex` (tectonic 0.17.0); checked-in build artifact |
| `reproduce.py` | computes `F(n)`, `C(n,2)`, `(2n-5)!!` for `n = 3..8`, asserts the two failures, prints PASS/FAIL; `python3 reproduce.py` exits 0 and prints `PASS` |
| `lean4/` | Lean 4 formalisation — core Lean only, no Mathlib, no `sorry`; built with `lake build` and axiom-checked with `lake env lean Check.lean` |
| `lean4/Main.lean` | the formalised statements and proofs |
| `lean4/Check.lean` | `#print axioms` audit |
| `lean4/README.md` | statement table, strategy, scope |

## Reproducing

Pure Python 3, standard library only, no dependencies:

```bash
python3 reproduce.py
```

Output: a table of `F(n)`, `C(n,2)` and `(2n-5)!!` for `n = 3..8`; a check that
`F(3) = 1/2` is non-integral; a check that `F(n) ≠ C(n,2)` for every `n` in the
range; and a check that `F(n) ≠ (2n-5)!!` throughout. It ends with `PASS` and
exits non-zero on `FAIL`.

The computation is a check, not a proof: the all-`n` mismatch is the induction of
Theorem `thm:mismatch` in `main.tex`.

## Status against the submission rules

Rule 3 requires a LaTeX source, a compiled PDF, and a Lean 4 project. All three
are present.

- **LaTeX source:** `main.tex`.
- **Compiled PDF:** `build/main.pdf`, built with
  `tectonic --outdir build main.tex` (tectonic 0.17.0) and checked in.
- **Lean 4 project:** `lean4/`. Core Lean only (`import Std`), no Mathlib
  dependency, no `sorry`. It defines `spaceTreeFormula`, proves `F(3) = 1/2`,
  proves that `1/2` is not a natural number (so no count can equal `F(3)`), and
  proves the explicit Johnson mismatches at `n = 4, 5, 6`, collected in
  `conjecture_00000008371_false`. It builds with `lake build` on
  `leanprover/lean4:v4.33.1` (exit 0, no errors), and `lake env lean Check.lean`
  reports dependencies on `[propext, Classical.choice, Quot.sound]` (some on
  none), with no `sorryAx` and no `Lean.ofReduceBool`.

See `lean4/README.md` for the statement table and the scope note.
