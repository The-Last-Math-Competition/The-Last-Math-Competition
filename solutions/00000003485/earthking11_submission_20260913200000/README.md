# Disproof of conjecture `00000003485`

**Verdict: FALSE.**

This submission disproves conjecture `00000003485` as stated. The refutation is
unconditional and elementary. The witness is the directed `5`-cycle: its
out-degree is `1` everywhere, its directed girth is `5`, and it has no kernel.
The same failure occurs for every directed odd cycle, and it survives strongly
connected blow-ups, so it is not an artefact of out-degree `1`.

## The conjecture

> **Definition:** A kernel of a digraph is an independent out-stable set, with
> the existence criterion the core problem.
> **Conjecture:** Digraphs with bounded out-degree and girth at least five have
> kernels; the critical configuration of the condition is the directed odd cycle
> with a one-point source, and the bound is a tightening of Richardson's
> theorem. (kernel existence strengthened condition)

Original statement (English and Chinese) as filed in
`conjectures/00000003485.md`:

> **English.** Definition: A kernel of a digraph is an independent out-stable
> set, with the existence criterion the core problem. Conjecture: Digraphs with
> bounded out-degree and girth at least five have kernels; the critical
> configuration of the condition is the directed odd cycle with a one-point
> source, and the bound is a tightening of Richardson's theorem. (kernel
> existence strengthened condition)
>
> **中文。** 定义：有向图的核为独立外稳定集，其存在性判据是核心问题。猜想：出度有界且围长至少五的有向图存在核；条件的临界构型为有向奇圈加单点源且该界为
> Richardson 定理的紧化。（核存在强化条件）

## Kernels

For a digraph `D = (V, A)`, a **kernel** is a set `S ⊆ V` that is

1. **independent** — no arc joins two members of `S` in either direction: for
   all `u, v ∈ S`, neither `(u, v)` nor `(v, u)` lies in `A`; and
2. **out-stable** (absorbing) — every vertex outside `S` has an arc *into* `S`:
   for every `v ∈ V \ S` there is `s ∈ S` with `(v, s) ∈ A`.

## The witness: the directed 5-cycle `C_5`

Let `C_5` have vertices `0, 1, 2, 3, 4` and arcs `i → i + 1 (mod 5)`; it is the
cycle `0 → 1 → 2 → 3 → 4 → 0`.

**The conjectured hypotheses hold.** Every vertex has exactly one out-neighbour,
its cyclic successor, so the out-degree is `1` at every vertex — bounded in the
sharpest possible sense (and this is the minimum possible out-degree of a
digraph with a directed cycle). The directed girth is exactly `5`: the cycle
`0 → 1 → 2 → 3 → 4 → 0` has length `5`, and every arc raises the index by `1`
modulo `5`, so a closed walk of length `k` needs `k ≡ 0 (mod 5)`; no positive
`k < 5` qualifies. The underlying undirected graph is the ordinary `5`-cycle, so
its undirected girth is `5` as well.

**`C_5` has no kernel.** Brute force over all `2^5 = 32` subsets finds exactly
`0` kernels. In detail, exactly `11` of the `32` subsets are independent:
`∅`; the five singletons; and the five non-adjacent pairs `{0,2}`, `{1,3}`,
`{2,4}`, `{0,3}`, `{1,4}`. Each of these `11` fails out-stability, since the
successor of some vertex outside `S` also lies outside `S`:

| independent `S` | vertex outside `S` with no arc into `S` |
|:----------------|:----------------------------------------|
| `∅`             | `0` (its arc goes to `1 ∉ S`) |
| `{0}`           | `2` (its arc goes to `3 ∉ S`) |
| `{1}`           | `3` |
| `{2}`           | `4` |
| `{3}`           | `0` |
| `{4}`           | `1` |
| `{0,2}`         | `3` (its arc goes to `4 ∉ S`) |
| `{1,3}`         | `4` |
| `{2,4}`         | `0` |
| `{0,3}`         | `1` |
| `{1,4}`         | `2` |

The remaining `21` subsets are already not independent. So no subset is both
independent and out-stable: `C_5` has no kernel, while satisfying both
conjectured hypotheses. The implication asserted by the conjecture fails, and
the conjecture is false.

## The general odd-cycle family

The same argument characterises kernels of all directed cycles: the directed
`n`-cycle has a kernel **iff `n` is even** (then the even-indexed and the
odd-indexed vertices are the two kernels). Independence forbids two adjacent
vertices from both lying in `S`; out-stability forbids two adjacent vertices
from both lying outside `S`; together these force membership to alternate around
the cycle, which is consistent exactly when `n` is even. Hence `C_3`, `C_5`,
`C_7`, `C_9` all have no kernel — the minimum witness compatible with a girth
bound of `5` is `C_5`, not `C_7`.

## Blow-up strengthening

Fix `m ≥ 1` and replace each vertex `i` of `C_5` by an independent part
`P_i = {(i,k) : 0 ≤ k < m}` of size `m`, with an arc from every vertex of `P_i`
to every vertex of `P_{i+1 mod 5}`. This digraph has out-degree exactly `m`
(bounded by any `B ≥ m`), directed girth `5`, and still no kernel: writing
`b_i = 1` iff `S ∩ P_i ≠ ∅`, independence forbids consecutive `1`s, while
out-stability forces `b_{i+1} = 0 ⟹ S_i` to be the *full* part, which then
pushes a `1` to `b_{i+2}`; the `b_i` alternate and are consistent only for an
even number of parts. With `5` parts this is impossible. So the failure is not
specific to out-degree `1`: every bound `m` admits a kernel-free witness of
girth `5`.

**Robustness.** The underlying undirected graph of `C_5` is a `5`-cycle, so the
counterexample also refutes the conjecture under the undirected reading of
"girth". The obstruction is a parity/structural one, not a numerical edge case.
Richardson's theorem gives kernels for digraphs with no *odd directed cycle*;
"girth at least five" does not exclude odd directed cycles (`C_5` is one), so
the proposed condition is not a valid strengthening of it.

## Files

| File | Description |
|:-----|:------------|
| `README.md` | This document: verdict, kernel definition, the `C_5` witness, the odd-cycle family, the blow-up, file list, reproduction instructions, and the status note. |
| `main.tex` | LaTeX source of the disproof. Standalone `article`, compiles with `tectonic main.tex`; includes the English and Chinese conjecture quotes. |
| `build/main.pdf` | PDF produced by `tectonic -o build main.tex`. |
| `reproduce.py` | Python 3 (standard library only) brute force over all subsets of the directed `n`-cycle for `n = 3,5,7,9`, plus out-degree and girth of `C_5` and the blow-ups; asserts zero kernels and prints `PASS`/`FAIL`. |
| `lean4/lean-toolchain` | Pins `leanprover/lean4:v4.33.1`. |
| `lean4/lakefile.toml` | Lake configuration; library `Main`, name `tlmc3485`, no dependencies. |
| `lean4/Main.lean` | Lean 4 formalisation, core Lean only (`import Std`, no Mathlib, no `sorry`). |
| `lean4/Check.lean` | `#print axioms` audit for every theorem. |
| `lean4/Eval.lean` | Optional `#eval` demo of the computed facts. |
| `lean4/README.md` | Statement table, proof strategy, and scope note for the formalisation. |
| `build/cjk-font-probe.tex`, `build/cjk-font-probe.pdf` | Small probe used to confirm that `tectonic` renders the Chinese quote (via `ctex` with the Fandol font set). |

## Reproducing

The numerical checks are dependency-free and run in well under a second:

```sh
python3 reproduce.py
```

It enumerates all `2^n` subsets of the directed `n`-cycle for `n = 3, 5, 7, 9`
and confirms `0` kernels in every case, verifies that `C_5` has out-degree `1`
and directed and undirected girth `5`, and repeats the check for the blow-ups of
`C_5` with part sizes `m = 1, 2, 3`. It prints `PASS` and exits `0` when every
fact verifies, and exits non-zero otherwise.

The LaTeX document is built with:

```sh
tectonic -o build main.tex
```

The Lean 4 project is built with:

```sh
cd lean4
lake build
lake env lean Check.lean
```

The project uses the toolchain pinned in `lean4/lean-toolchain`
(`leanprover/lean4:v4.33.1`) and imports only `Std`; it does not depend on
Mathlib.

## Status against the submission rules

Rule 3 requires each submission to contain the LaTeX source code, a PDF
document, and a Lean 4 project.

- **LaTeX source** — present (`main.tex`), a standalone `article` using
  `ctex` (Fandol fonts, plain scheme), `geometry`, `amsmath`, `amssymb`,
  `amsthm`, `array`, and `parskip`; it compiles with `tectonic main.tex` and
  renders both the English and the Chinese statement of the conjecture.
- **PDF document** — `build/main.pdf`, produced by `tectonic -o build main.tex`
  (89 KB, verified non-empty and readable).
- **Lean 4 project** — present under `lean4/`, with `lean-toolchain`,
  `lakefile.toml` (library `Main`, name `tlmc3485`), `Main.lean`, `Check.lean`,
  `Eval.lean`, and `README.md`. It formalises the witness `C_5` with the arc
  predicate `arc5 i j = decide (j = i + 1)` on `Fin 5`, defines independence,
  out-stability, and kernels, and proves
  `no_kernel5 : ∀ S : Fin 5 → Bool, kernel5 S = false` by exhaustive case
  analysis over the `32` subsets. It also proves the out-degree and girth facts,
  the explicit `32`-subset enumeration (`kernelMasks5 = []`), and the odd-cycle
  instances `C_3` and `C_7`. It is core Lean only (no Mathlib) and contains no
  `sorry`; `Check.lean` reports only `propext` (never `sorryAx`).
- **All gates were actually run** in the assembly environment: `lake build`,
  `lake env lean Check.lean`, `tectonic -o build main.tex`, and
  `python3 reproduce.py` all succeeded (see the command/output summary in the
  accompanying report).
