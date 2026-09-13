# Refutation of conjecture 00000001671

**Verdict: FALSE.**

Conjecture 00000001671 claims that the *basis number* of the complete graph
`K_n` equals `⌈(n+3)/2⌉`, where:

* a **cycle basis** of a graph is a basis of its cycle space over `GF(2)`;
* a cycle basis is **k-fold** if every edge lies in at most `k` of the basis
  cycles;
* the **basis number** `b(G)` is the least `k` admitting a `k`-fold cycle
  basis.

The true values are

| n | true `b(K_n)` | formula `⌈(n+3)/2⌉` |
|---|---|---|
| 3 | **1** | 3 |
| 4 | **2** | 4 |
| 5 | **3** | 4 |
| 6 | **3** | 5 |

so the claim fails for every `n = 3, 4, 5, 6` already.

## Why the formula is wrong

**`K_3`: `b = 1`, not `3`.** The cycle space has dimension `|E| − |V| + 1 =
3 − 3 + 1 = 1`, spanned by the single triangle `{0,1,2}`. Every edge lies in
exactly one basis cycle, so this is a 1-fold basis. Hence `b(K_3) = 1`,
whereas the formula gives `⌈6/2⌉ = 3`.

**`K_4`: `b = 2`, not `4`.** Here `|E| = 6`, `|V| = 4`, so the cycle space has
dimension `3`. No 1-fold basis exists: three independent cycles would need at
least `3 · 3 = 9` edge incidences, but `K_4` has only `6` edges. On the other
hand the three triangles `{0,1,2}`, `{0,1,3}`, `{0,2,3}` are linearly
independent (edges `12`, `13`, `23` each occur in exactly one of them) and
span the 3-dimensional cycle space; their edge multiplicities are
`2,2,2,1,1,1`, all at most two. So `b(K_4) = 2`, whereas the formula gives
`⌈7/2⌉ = 4`.

> **Caution.** It is *not* true that every edge of `K_4` lies in exactly two of
> those three triangles: the edges `12`, `13`, `23` of the omitted triangle
> `{1,2,3}` lie in only one. The correct statement is that every edge lies in
> **at most** two of them, which is all that is needed for `k = 2`.

**`K_5`: `b = 3`, not `4`.** Cycle-space dimension `10 − 5 + 1 = 6`.
A 1-fold basis is impossible because `3·6 = 18 > 1·10 = 10`. For `k = 2` the
length budget is `2·10 = 20`, so among six independent cycles of length `≥ 3`
the total excess `∑(|C|−3)` is at most `2`; a cycle of length `≥ 6` is already
excluded. The number of candidate 6-sets of cycles of lengths `3, 4, 5` with
total length at most `20` is exactly
`C(10,6) + C(10,5)·15 + C(10,5)·12 + C(10,4)·C(15,2) = 29 064`, and an
exhaustive check (in `reproduce.py`) shows none is independent with every edge
used at most twice. A 3-fold basis exists: for the centre `0`, the six
triangles `{0,i,j}` (`1 ≤ i < j ≤ 4`) are independent, and every spoke `0i`
occurs in three of them while every edge `ij` occurs once.

**`K_6`: `b = 3`, not `5`.** Cycle-space dimension `15 − 6 + 1 = 10`. For
`k = 1` the bound `3·10 = 30 > 15` rules it out. For `k = 2` the budget is
`2·15 = 30 = 3·10`, so a 2-fold basis would have to consist of ten triangles
with **every** edge of `K_6` used exactly twice — i.e. a Steiner triple system
on 6 points. But in such a system each point lies in `(6−1)/2 = 5/2` triples,
not an integer. Hence no 2-fold basis exists, and `b(K_6) ≥ 3`. A 3-fold basis
is given by the ten triangles
`{0,1,2}, {0,1,3}, {0,1,4}, {0,2,3}, {0,2,4}, {0,3,5}, {0,4,5}, {1,2,5},
{1,3,4}, {1,3,5}`, whose edge multiplicities are all at most `3`.

## Strongest objection: the "specific canonical basis" reading

If "basis number" were instead read as the maximum edge multiplicity of a
*specific* canonical basis — e.g. the **star basis** (centre `0`, fundamental
cycles `0–i–j–0` for all non-tree edges `ij`) — then its value is `n − 2`:
each spoke `0i` lies in exactly `n − 2` basis cycles and each edge `ij` in
exactly one.

For `n = 4, 5, 6` that gives `2, 3, 4`, while the formula `⌈(n+3)/2⌉` gives
`4, 4, 5`. So the formula is wrong under this reading too: the claim is false
whether "basis number" is the least admissible `k` (the conjecture's stated
definition) or the multiplicity of a fixed canonical basis. The two readings
coincide only at `n = 3`, and even there both give `1`, not `3`. The star basis
happens to be optimal for `K_4` and `K_5` (giving `2` and `3`) but is already
strictly suboptimal for `K_6`, where it gives `4` while the true value is `3`.

## Contents

| Path | Description |
|---|---|
| `main.tex` | Standalone article (amsmath/amssymb/amsthm): definitions, the `K_3` and `K_4` proofs, the `n = 5, 6` computations, and the fixed-canonical-basis objection. Build with `tectonic --outdir build main.tex`. |
| `reproduce.py` | Stdlib-only exact computation of `b(K_n)` for `n = 3..6` over `GF(2)`, printing the true-vs-formula table and `PASS`/`FAIL`; exits `0`. Also re-derives `K_3`, `K_4` by exhaustive enumeration of all bases. |
| `lean4/` | Core-Lean 4 (no Mathlib) machine-checked formalisation of `b(K_3) = 1` and `b(K_4) = 2` and the formula mismatches. |
| `build/main.pdf` | Compiled article. |

## Reproduce

```sh
python3 reproduce.py                    # exact table, PASS/FAIL (exit 0)
cd lean4 && lake build                  # builds the formalisation
lake env lean Check.lean                # prints the axiom audit
cd .. && tectonic --outdir build main.tex   # -> build/main.pdf
```

`reproduce.py` uses an exact backtracking search. It is exhaustive, not
heuristic: the length budget `∑|C| ≤ k|E|` and the fact that every simple cycle
has length `≥ 3` discard every cycle of length above `k|E| − 3(d−1)`, and the
search then enumerates all remaining candidate bases (checking `GF(2)` rank and
edge multiplicities).

## Lean formalisation

`lean4/Main.lean` represents an edge subset of `K_n` as a `Nat` bitmask and
computes the cycle space (even-degree edge sets), the predicate
`IsKFoldBasis n k basis`, and `minBasisNumber n` by pure structural recursion,
so the kernel itself reduces them. It proves, by `by decide` (no `sorry`, no
`axiom`, no `native_decide`):

* `minBasisNumber 3 = 1`, `minBasisNumber 4 = 2` (so `b(K_3)=1`, `b(K_4)=2`);
* `hasKFoldBasis 4 1 = false` (no 1-fold basis of `K_4`);
* explicit witnesses `IsKFoldBasis 3 1 [7] = true` and
  `IsKFoldBasis 4 2 [11,21,38] = true`;
* `formula 3 = 3`, `formula 4 = 4`, and the mismatches
  `formula 3 ≠ minBasisNumber 3`, `formula 4 ≠ minBasisNumber 4`;
* `conjecture_00000001671_false`, collecting the above.

`Check.lean` audits the axioms: **none** of the theorems depends on any axiom
(in particular there is no `sorryAx` and no `ofReduceBool`). Core `Nat.xor` is
opaque to the kernel reducer and would introduce `propext`, so the file
re-implements bitwise XOR (`xorBits`) by structural recursion; this is what
keeps the audit clean.
