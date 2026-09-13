# Disproof of conjecture `00000008234`

**Verdict: FALSE.**

This submission disproves conjecture `00000008234` as stated. The conjecture is
a conjunction; we refute its first conjunct, and therefore the conjunction. The
refutation is unconditional and elementary: with two agents, two goods and unit
(hence monotone) additive valuations, the EF1 exchange graph has exactly two
vertices and **no edges**, so it is disconnected, its diameter is infinite, and
the claimed bound `m(n-1) = 2` fails. The same phenomenon occurs for every
`n | m` with `n ≥ 2`, including the three-agent case `(n,m) = (3,3)`.

## The conjecture

Quoted verbatim from `conjectures/00000008234.md`:

> **English.** Definition: The exchange graph swap_graph of envy-free-up-to-one-good
> allocations when n agents divide m indivisible goods: vertices are EF1
> allocations and edges are single-good transfers. Conjecture: Under arbitrary
> monotone valuations swap_graph is connected with diameter at most m(n-1); an
> allocation that is simultaneously EF1 and Pareto optimal always exists and is
> reachable by a polynomial-time item-moving algorithm; and EFX allocations
> always exist for three agents, while a minimal counterexample, if one exists,
> must have exactly 4 agents and require a non-bimodal valuation profile.
> (EF1 swap graph diameter EFX four-agent threshold)
>
> **中文。** 定义：n 个代理分 m 件不可分物品时 envy-freeness up to one good
> 分配之间的交换图 swap_graph：顶点为 EF1 分配，边为单件物品的转移。猜想：任意
> 单调估值下 swap_graph 连通且直径不超过 m(n-1)；EF1 与 Pareto 最优的联合分配恒
> 存在且可由逐件移动的多项式算法达到；EFX 分配在三代理时恒存在而最小反例若出现
> 则代理数恰为 4 且需要非双峰估值剖面。

## Setup

An allocation is a map `a : goods → agents`. The **unit valuation** gives every
agent value `1` to every good, extended additively: the value of a bundle is its
cardinality. Unit valuations are additive, hence monotone, so they satisfy the
conjecture's "arbitrary monotone valuations" hypothesis.

An allocation is **EF1** if for every ordered pair of agents `(i,j)` there is a
good `g` in `j`'s bundle whose removal removes `i`'s envy:
`v_i(A_j \ {g}) ≤ v_i(A_i)`.

**Lemma (unit valuations).** EF1 is equivalent to: `max bundle size − min bundle
size ≤ 1`. *Proof.* If `|A_i| ≥ |A_j|` there is no envy; if `|A_j| = |A_i| + 1`,
removing any good from `A_j` leaves value `|A_i|`. Conversely, if
`|A_j| ≥ |A_i| + 2`, removing any one good still leaves value `≥ |A_i| + 1`, so
the envy of `i` towards `j` is not removed. ∎

## The counterexample: `n = 2` agents, `m = 2` goods

Goods `{g1,g2}`, agents `{A,B}`, unit valuations. Full enumeration of the
`2^2 = 4` allocations:

| allocation | bundles | sizes | EF1? |
|:-----------|:--------|:------|:----:|
| both goods to A | `({g1,g2}, ∅)` | `(2, 0)` | no — gap 2 |
| `g1→A, g2→B` | `({g1}, {g2})` | `(1, 1)` | **yes** |
| `g1→B, g2→A` | `({g2}, {g1})` | `(1, 1)` | **yes** |
| both goods to B | `(∅, {g1,g2})` | `(0, 2)` | no — gap 2 |

So the EF1 allocations are exactly the two diagonal allocations, and they differ
in **both** coordinates (Hamming distance `2`).

**No edge.** A single-good transfer out of either diagonal moves one good from
one agent to the other, producing the size pattern `(2, 0)` or `(0, 2)`. Neither
is EF1 (gap `2`), and neither diagonal is adjacent to the other (distance `2`,
not `1`). Hence `swap_graph` has **zero edges**.

**Disconnection.** A graph on two vertices with no edge has two connected
components: it is disconnected and its diameter is infinite (there is no path,
so no finite diameter bound holds). The conjectured bound `m(n-1) = 2` — indeed
any finite bound — fails, and the first conjunct of the conjecture is false.

## Strengthening: every `n | m`, including `n = m = 3`

For unit valuations, the lemma above says EF1 ⇔ all bundle sizes are within `1`
of one another. If `n` divides `m`, the sizes sum to a multiple of `n`, which
forces all sizes to be equal (if all sizes lie in `{k, k+1}` and their sum
`= nk + r` is divisible by `n`, then `r ∈ {0, n}`). So:

> If `n ≥ 2`, `m ≥ n` and `n | m`, every EF1 allocation gives each agent exactly
> `m/n` goods; any single-good transfer creates a size gap of `2`, so
> `swap_graph` has **no edges at all**. There are at least two balanced
> allocations, so `swap_graph` is disconnected.

In particular `(n,m) = (3,3)` is a three-agent counterexample (six EF1
permutations, one good each, zero edges, six components), so the `n = 2` case is
not a degenerate artifact. The family is checked by exhaustive enumeration:

| `n` | `m` | # EF1 allocations | # edges | # components |
|:---:|:---:|:-----------------:|:-------:|:------------:|
| 2 | 2 | 2 | 0 | 2 |
| 2 | 4 | 6 | 0 | 6 |
| 2 | 6 | 20 | 0 | 20 |
| 3 | 3 | 6 | 0 | 6 |
| 4 | 4 | 24 | 0 | 24 |

## Files

| File | Description |
|:-----|:------------|
| `README.md` | This document: verdict, conjecture, 2×2 table, the no-edge/disconnection argument, the `n | m` strengthening, reproduction commands. |
| `main.tex` | LaTeX source of the disproof. Standalone `article`, compiles with `tectonic main.tex`. |
| `build/main.pdf` | PDF produced by `tectonic` (non-empty; 66 KB). |
| `reproduce.py` | Python 3 (standard library only) enumeration of the allocations, the literal EF1 predicate, the swap graph and its components; asserts zero edges and disconnection; prints `PASS`/`FAIL` and exits non-zero on failure. |
| `lean4/lean-toolchain` | Pins `leanprover/lean4:v4.33.1`. |
| `lean4/lakefile.toml` | Lake configuration; library `Main`, no dependencies. |
| `lean4/Main.lean` | Lean 4 formalisation of the 2×2 refutation, core Lean only (`import Std`, no Mathlib, no `sorry`). |
| `lean4/Check.lean` | `#print axioms` audit for every theorem. |
| `lean4/README.md` | Statement table, proof strategy, and scope note for the formalisation. |
| `lean4/exploration/` | Minimal development scratch files; not part of the library, not built by `lake build`. |

## Reproducing

```sh
python3 reproduce.py                 # exhaustively checks EF1 / edges / components
tectonic -o build main.tex           # writes build/main.pdf
cd lean4 && lake build               # builds the Main library
cd lean4 && lake env lean Check.lean # prints the axioms of each theorem
```

`reproduce.py` enumerates all `n^m` allocations for `(n,m) = (2,2)` and `(3,3)`
(and the extra members `(2,4)`, `(2,6)`, `(4,4)`), computes EF1 straight from the
definition (for every ordered pair of agents, some good can be removed from the
envied bundle to remove the envy), builds the swap graph with edges = Hamming
distance `1`, and asserts zero edges and disconnection. A `FAIL` (non-zero exit
status) means a claimed contradiction did not verify; the script prints `PASS`
and exits `0` on success.

The Lean project pins the toolchain in `lean4/lean-toolchain` and imports only
`Std`; it does not depend on Mathlib.

## Status against the submission rules

- **LaTeX source** — present (`main.tex`), a standalone `article` using only
  `geometry`, `amsmath`, `amssymb`, `amsthm`, `array`, and `parskip`; it
  compiles with `tectonic main.tex` (verified, `tectonic 0.17.0`).
- **PDF document** — `build/main.pdf` exists and is non-empty (66 KB), generated
  from `main.tex` by `tectonic`.
- **Lean 4 project** — present under `lean4/` with `lean-toolchain`,
  `lakefile.toml`, `Main.lean`, and `Check.lean`. `lake build` exits `0`;
  `lake env lean Check.lean` reports only `propext` and `Quot.sound` for every
  theorem, with no `sorryAx`. All numerical facts are closed by `decide`, and
  function equality is handled pointwise via `funext` (there is no `Finset`,
  `SimpleGraph`, `ZMod`, or Mathlib dependency).
