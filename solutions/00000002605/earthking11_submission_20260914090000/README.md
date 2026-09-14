# Disproof of conjecture `00000002605`

**Verdict: FALSE.**

This submission disproves conjecture `00000002605` as stated. The refutation is
unconditional and completely elementary. The conjecture asserts that the rank
number sequences of **semimodular lattices** are strictly log-concave. A single
`5`-element lattice `L` lies in that class and has rank numbers
`W = [1, 2, 1, 1]`, for which
`W₂² = 1 < 2 = W₁·W₃` — so it fails even **weak** log-concavity, a fortiori the
filed strict log-concavity. The two additional clauses of the filing are
independently false as well.

## The geometric-lattice caveat (stated prominently)

This is the honest scope of the result, and it is the first thing a reviewer
should read.

> "Mason's conjecture" **in the literature** is about **geometric lattices**
> (equivalently, lattices of flats of simple matroids). There,
> **atomisticity is part of the hypothesis**, and the log-concavity of the
> Whitney numbers of the second kind is a known **theorem** (the strict
> log-concavity of the relevant `h`-vector / Whitney numbers of geometric
> lattices, in the lineage of Mason). The witness `L` below is **NOT
> atomistic**: the join of its two atoms is `a ⊔ b = c ≠ top`. Hence `L` is not
> geometric, so it refutes **only the filed wording "semimodular lattices"**
> — the class the filing names twice, with no atomisticity hypothesis. This
> submission **does not dispute the geometric-lattice theorem**.
>
> In short: the filing dropped a hypothesis (atomisticity) that the classical
> theorem needs. The witness is a clean exposure of this **class-broadening
> error** in the filing. It is a refutation of the conjecture *as literally
> worded*, not a counterexample to the classical geometric-lattice result.

This caveat is also stated in `main.tex` (Section "The geometric-lattice
caveat") and in `lean4/README.md` (scope note).

## The conjecture, quoted verbatim

From `conjectures/00000002605.md`:

> **English.** Definition: Whitney numbers of semimodular lattices: the
> coefficients of the rank generating function. Conjecture: The rank number
> sequences of semimodular lattices are strictly log-concave (the complete
> version of Mason's conjecture), and the deficit of concavity is controlled by
> the number of embedded N₅ sublattices; the minimal positive deficit example is
> exactly the fifth-layer embedding in the free Boolean lattice. (Whitney strict
> concavity)
>
> **中文。** 定义：半模格的 Whitney 数：秩生成函数的系数。猜想：半模格的秩数序列严格对数凹（Mason
> 猜想的完全版）且凹性的亏损由子格 N_5 的嵌入数控制。(Whitney 严格凹性)；且亏损极小正例恰为自由布尔格第五层嵌入。

Both versions are identical in content: the class named is **semimodular
lattices** (半模格), stated twice, with no atomisticity or geometricity
hypothesis.

## Definitions

**Whitney numbers of the second kind = the rank numbers.** Let `L` be a finite
graded lattice with rank function `ρ`. The Whitney numbers of the second kind
are the numbers of elements of each rank,

```
W_k = #{ x ∈ L : ρ(x) = k },
```

equivalently the coefficients of the rank generating function
`Σ_{x∈L} t^{ρ(x)} = Σ_k W_k t^k`. The filing explicitly defines them as "the
coefficients of the rank generating function", so the "rank number sequence" of
the conjecture is exactly `(W_0, W_1, …)` in this sense. (The *first*-kind
Whitney numbers are the characteristic-polynomial coefficients; they are the
Möbius transform of the second-kind numbers, and the witness's failure occurs
already in the counting sequence `[1,2,1,1]`, so the verdict is unchanged under
either reading.)

**Log-concavity and deficit.** A finite non-negative sequence `(W_0,…,W_r)` is
*weakly log-concave* if `W_k² ≥ W_{k-1}W_{k+1}` for all `1 ≤ k ≤ r−1`, and
*strictly log-concave* if every one of these inequalities is strict. Its
*deficit* is `Σ_k max(0, W_{k-1}W_{k+1} − W_k²)`.

**Semimodularity.** `L` is upper semimodular if `x ∧ y ⋖ x` implies
`y ⋖ x ∨ y` for all `x, y`; "semimodular" below means upper semimodular.
Distributive ⟹ modular ⟹ semimodular, and semimodular lattices are graded.

## The witness

Let `L = {0, a, b, c, top}` be the lattice with cover relations

```
(0,a), (0,b), (a,c), (b,c), (c,top),
```

so `a` and `b` are incomparable, `c = a ⊔ b`, and `0`, `top` are the bottom and
top. Equivalently, `L` is the lattice `J(P)` of order ideals of the poset `P`
with two incomparable minimal elements and a top, i.e. the poset with cover
relations `(0,2), (1,2)` on `{0,1,2}`. Concretely the order is

```
0 < a < c < top,   0 < b < c < top,   a ∥ b,
```

and the rank function (longest chain length) is

```
ρ(0) = 0,   ρ(a) = ρ(b) = 1,   ρ(c) = 2,   ρ(top) = 3.
```

Hence the Whitney numbers of the second kind are

```
W = (W_0, W_1, W_2, W_3) = (1, 2, 1, 1),
```

and log-concavity fails at the very first nontrivial index `k = 2`:

```
W_2² = 1   <   2 = W_1 · W_3        (deficit = W_1 W_3 − W_2² = 1 > 0).
```

So `L` is not weakly log-concave, hence not strictly log-concave.

`L` is **distributive** (`J(P)` for a poset `P`; meet = intersection, join =
union), therefore modular, therefore **upper semimodular**. It is therefore in
the class the filing names twice. It is **not** atomistic: its only atoms are
`a` and `b`, and `a ⊔ b = c ≠ top`; thus it is not geometric (see the caveat).

`reproduce.py` verifies every one of these claims from the covers alone:
partial-order axioms, existence of meet and join for all 25 pairs (lattice
axioms), upper semimodularity over all 25 pairs, the rank function and
`W = [1,2,1,1]`, the failing inequality, distributivity over all 125 triples,
and the order-ideal cross-check.

## The two extra clauses are independently false

**(i) "the deficit of concavity is controlled by the number of embedded N₅
sublattices" — FALSE.** `N₅` is the `5`-element non-modular lattice
(the pentagon). A lattice is distributive iff it contains no sublattice
isomorphic to `N₅` or `B₂` (the classical forbidden-sublattice
characterisation). The witness is distributive, so it contains **zero** `N₅`
sublattices — `reproduce.py` enumerates every `5`-element subset, keeps those
closed under the computed meet and join, and tests order-isomorphism with `N₅`,
obtaining count `0` (the count of `N₅` induced subposets is also `0`). Yet its
deficit is `1`. A positive deficit with zero `N₅` sublattices refutes the
asserted control: the clause predicts zero deficit whenever the `N₅` count is
zero.

**(ii) "the minimal positive deficit example is exactly the fifth-layer
embedding in the free Boolean lattice" — FALSE.** A free Boolean lattice `B_n`
is distributive and graded, and its rank-`k` elements are the `k`-subsets, so
its rank numbers are the binomial coefficients `C(n,k)`. Binomial rows are
**strictly** log-concave, because `C(n,k)/C(n,k−1) = (n−k+1)/k` is strictly
decreasing in `k`; hence `deficit(B_n) = 0` for every `n`. No free Boolean
lattice has any positive deficit at all, so none can contain the minimal
positive-deficit example; in particular no "fifth-layer embedding" in one does.
`reproduce.py` checks `deficit(B_n) = 0` and strict log-concavity for all
`n ≤ 20`. Meanwhile the `5`-element lattice `L` above is semimodular with
deficit `1`, and no semimodular lattice with a positive deficit has fewer than
`5` elements (a lattice of at most `4` elements is a chain or a chain times a
`2`-chain, hence distributive and log-concave), so `L` is a minimal
positive-deficit example that is not a Boolean layer.

**Degenerate note on strictness.** The `4`-element chain has `W = [1,1,1,1]`
with `W₁W₃ = W₂² = 1`: it violates *strict* log-concavity by equality but has
deficit `0`. It is recorded for completeness; the genuine positive-deficit
witness is `L`.

## Files

| File | Description |
|:-----|:------------|
| `README.md` | This document: verdict, bilingual quote, definitions, witness, the two false extra clauses, the geometric-lattice caveat, file list, reproducibility, rule-3 status. |
| `main.tex` | LaTeX source of the disproof (standalone `article`); compiles with `tectonic --outdir build main.tex`. |
| `build/main.pdf` | PDF produced by `tectonic --outdir build main.tex` (non-empty, 84 KB). |
| `reproduce.py` | Python 3 standard library only: builds `L` from its covers, computes the closure, verifies the lattice axioms and upper semimodularity, computes `W = [1,2,1,1]` and the failing inequality, verifies distributivity and zero `N₅` sublattices, cross-checks via order ideals of `P`, checks the Boolean-lattice clause, prints `PASS`/`FAIL`, non-zero exit on failure. |
| `lean4/lean-toolchain` | Pins `leanprover/lean4:v4.33.1`. |
| `lean4/lakefile.toml` | Lake configuration; project `tlmc2605`, library `Main`, no dependencies. |
| `lean4/Main.lean` | Lean 4 formalisation, core Lean only (no imports at all, no Mathlib, no `sorry`): derives order/meet/join/rank from the covers, proves the lattice and rank axioms, and proves `conjecture_00000002605_false`. |
| `lean4/Check.lean` | `#print axioms` audit for every theorem. |
| `lean4/README.md` | Statement table, proof strategy, axiom audit, scope/faithfulness note. |

## Reproducing

Python (dependency-free, runs in ~0.02 s):

```sh
python3 reproduce.py
```

It builds `L` from its cover relations, takes the transitive closure, checks the
partial-order and lattice axioms, upper semimodularity, the rank function and
`W = [1,2,1,1]`, the failing inequality `W₂² < W₁W₃`, distributivity, zero `N₅`
sublattices, the order-ideal cross-check for `W`, and the free-Boolean-lattice
clause, then prints `PASS` and exits `0` (non-zero on any failure).

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
and reports **only `propext`** for each (no `sorryAx`, no `Classical.choice`,
no Mathlib).

## Status against the submission rules

Rule 3 requires each submission to contain the LaTeX source, a PDF document,
and a Lean 4 project.

- **LaTeX source** — present (`main.tex`), a standalone `article` using only
  `geometry`, `amsmath`, `amssymb`, `amsthm`, `array`, `parskip`, `booktabs`;
  compiles with `tectonic --outdir build main.tex` with no warnings.
- **PDF document** — present at `build/main.pdf`, produced by the command
  above.
- **Lean 4 project** — present under `lean4/`, with `lean-toolchain` pinned to
  `leanprover/lean4:v4.33.1`, `lakefile.toml` (library `Main`, project
  `tlmc2605`, no dependencies), `Main.lean`, `Check.lean` (`#print axioms`), and
  a `README.md`. It is core Lean only (**no imports at all**, no Mathlib, no
  `sorry`); `lake build` exits `0` and the audit reports no `sorryAx` (each
  theorem depends only on the core axiom `propext`).
