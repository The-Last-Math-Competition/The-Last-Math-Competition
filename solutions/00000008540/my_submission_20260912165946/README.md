# Disproof of conjecture `00000008540`

**Verdict: FALSE.** The smallest counterexample is the three-element chain
`C3`, which has only three elements.

## The conjecture

> **Definition:** A congruence of a lattice is an order-preserving
> equivalence. **Conjecture:** The congruence lattice of a finite lattice is
> Boolean exactly when the lattice is of subdirectly irreducible type; the
> number of congruences is at most 2^{n−1}, and the bound is optimal.

## Reading used

"Subdirectly irreducible" is read in the standard sense: `L` is nontrivial and
admits no subdirect representation `L ≤ ∏ Lᵢ` in which every projection is
surjective but no projection is an isomorphism. For a finite lattice this is
equivalent to `Con(L)` having **exactly one atom**. "Exactly when" is read as a
genuine biconditional. We refute the "only if" direction.

The reading matters here, because subdirect irreducibility is strictly stronger
than direct indecomposability for lattices — and our witness sits precisely in
that gap.

## Why it is false

### The minimal counterexample: `C3`, the chain `0 < 1 < 2`

A partition of a chain is a congruence **iff** every block is an interval.
(If a block `B` is not an interval, take `x < z < y` with `x, y ∈ B`, `z ∉ B`;
then `x ∧ z = x` and `y ∧ z = z`, so `x ≡ z`, contradiction.) Hence
`|Con(Cₙ)| = 2^(n−1)`, and

```
Con(C3) = { {0,1,2},  {0,1}|{2},  {0}|{1,2},  {0}|{1}|{2} }
```

has four elements and forms a diamond, so `Con(C3) ≅ 2²` is **Boolean**.

But `C3` is **not** subdirectly irreducible. There is an explicit subdirect
embedding into `C2 × C2`:

```
φ(0) = (0,0)    φ(1) = (0,1)    φ(2) = (1,1)
```

Both coordinate projections are surjective onto `C2`, and neither is an
isomorphism (`|C3| = 3 ≠ 2 = |C2|`). Equivalently, `Con(C3)` has **two atoms**,
`{0,1}|{2}` and `{0}|{1,2}`, whereas subdirect irreducibility requires exactly
one.

So `Con(C3)` is Boolean while `C3` is not SI.

`C3` is directly indecomposable — a product of two nontrivial lattices has at
least four elements, and `C3` is a chain — so it is the classical illustration
that subdirect irreducibility is strictly stronger than direct
indecomposability.

### Minimality

The only two-element lattice is `C2`, whose congruence lattice has two elements
and exactly one atom, so `C2` is SI and consistent with the conjecture. Hence
`C3` is the smallest possible witness.

### A second witness: `2²`

The four-element Boolean lattice `2² = 2 × 2` also works, for a more
transparent reason: it is literally a direct product of two nontrivial
lattices, so it is subdirectly reducible on its face, and again `Con(2²)` has
two atoms. We give both, so that a reader has one witness whose non-SI-ness is
structural (`2²`) and one whose size is minimal (`C3`).

### Generalisation

For every `n ≥ 3` the chain `Cₙ` is a counterexample: `Con(Cₙ)` has `2^(n−1)`
elements and is Boolean, while it has `n − 1 ≥ 2` atoms.

## The counting clause is NOT refuted

`|Con(C3)| = 4 = 2^(3−1)` and `|Con(2²)| = 4 ≤ 2^(4−1) = 8`. The bound
`2^(n−1)` is attained by every chain, which is consistent with the
conjecture's own claim that the bound is optimal. **What fails is the
classification (the biconditional), not the counting bound.** We state this
explicitly so that the scope of the refutation is unambiguous.

## A note on brute force

Both enumerations were checked over *all* partitions of the underlying set,
using the full compatibility condition `x ≡ y ⟹ f(x,z) ≡ f(y,z)` for all `z`.
The relevant counts are the Bell numbers:

| `L` | `\|L\|` | partitions | wrong test | full condition | atoms | SI |
|---|---|---|---|---|---|---|
| `C2` | 2 | 2 | 2 | 2 | 1 | yes |
| `C3` | 3 | 5 | 5 | **4** | **2** | **no** |
| `2²` | 4 | 15 | 11 | **4** | **2** | **no** |

Two things worth recording, because a reviewer comparing implementations will
hit them:

1. **The number of partitions of a four-element set is 15, not 256.** `256` is
   neither the number of partitions of a 4-set (15) nor the number of
   equivalence relations on it (also 15 — the two notions are in bijection).
   This is a common slip and we flag it so that nobody re-derives it wrongly.
2. **Checking only that "each block is a sublattice" is insufficient** and
   overcounts: it reports 5 instead of 4 for `C3` (the spurious relation is
   `{0,2}|{1}`, whose block `{0,2}` is genuinely a sublattice of `C3` but which
   is not a congruence) and 11 instead of 4 for `2²`. The correct condition
   needs cross-block compatibility for all `z`, not just meet/join within a
   block.

## Files

| file | purpose |
|---|---|
| `main.tex` | the proof (LaTeX) |
| `main.pdf` | compiled PDF, built with `tectonic` |
| `reproduce.py` | brute-force verification of both witnesses and of minimality |
| `lean4/` | Lean 4 formalisation — **status: complete**, zero `sorry`, core Lean only |

## Reproducing

Pure Python 3, standard library only:

```bash
python3 reproduce.py
```

Output: the congruence analysis of `C3` and of `2²` (4 congruences each, 2
atoms, Boolean but not SI), the confirmation that `C2` is not a counterexample,
and both the correct and the incorrect counts.

## Status against the submission rules

Rule 3 requires LaTeX, a compiled PDF, and a Lean 4 project. All three are
present.

The Lean 4 project is in `lean4/` and formalises the combinatorial core of the
refutation — that `C3` has exactly four congruences, that they are order
isomorphic to `2²`, and that exactly two of them are atoms — with zero `sorry`
and **no Mathlib dependency**, so it builds in seconds:

```bash
cd lean4 && lake build && lake env lean Check.lean
```

`lean4/README.md` records the theorem inventory, the proof structure, and the
axiom dependency report (`propext` and `Quot.sound` only — no `sorryAx`, no
`Classical.choice`).

Two scope notes, stated so that the formalisation is not read as claiming more
than it does:

1. The formalisation covers the **combinatorial core**: the four congruences,
   their order, and the two atoms. It does not formalise the surrounding
   universal algebra — "finite lattice", "subdirect product", "subdirectly
   irreducible" are taken as the standard notions and are *not* themselves
   formalised. What is machine-checked is precisely the part that a reviewer
   would otherwise have to verify by hand, namely the enumeration and the atom
   count.
2. The counting clause (`|Con L| ≤ 2^(n−1)`) is not refuted and is not
   formalised here; see the section above.
