# Lean 4 formalisation — disproof of conjecture `00000002605`

Core Lean **only**: no Mathlib, no `import Std`, and in fact **no imports at
all** (only `Init`), no `sorry`. The project pins `lean-toolchain` to
`leanprover/lean4:v4.33.1` and defines the library `Main` (project name
`tlmc2605`) in `lakefile.toml`, with no dependencies, so `lake build` needs no
cache download.

## Build and audit

```sh
lake build
lake env lean Check.lean
```

`Check.lean` prints `#print axioms` for every theorem so a reviewer can confirm
the absence of `sorryAx` and of Mathlib dependencies.

## The witness

Elements `0,1,2,3,4` with `0` = bottom, `1` = `a`, `2` = `b`, `3` = `a ⊔ b`,
`4` = top, and cover relations `(0,1), (0,2), (1,3), (2,3), (3,4)`. The lattice
is distributive; its rank numbers are `W = [1,2,1,1]`; log-concavity fails at
`k = 2` because `W₂² = 1 < 2 = W₁·W₃`.

## What is formalised

Unlike a table-only encoding, this file **derives** the structure from the cover
relations and **proves** the lattice axioms:

| Definition / theorem | Kind | Statement |
|:---------------------|:-----|:----------|
| `covB` | input | the cover relation `x ⋖ y`, hardcoded (this is the lattice's definition) |
| `extend`, `closeIter`, `leB` | derived | `leB` is the reflexive-transitive closure of the covers (Bellman–Ford relaxation over `List (Fin 5)`) |
| `covLe` | derived | the covering relation re-derived from `leB` |
| `meetB`, `joinB` | derived | GLB / LUB computed by search through `elems` (fold starting at bottom / top) |
| `rankIter`, `rankB` | derived | rank as the longest cover-chain length (relaxation, 4 steps) |
| `W` | derived | Whitney numbers of the **second** kind: `# {x : rankB x = k}` |
| `upperSemimodular`, `distributive` | derived | Boolean checks over all pairs / triples |
| `atoms`, `joinAtoms`, `top` | derived | atoms, their join, and the top |
| `le_refl`, `le_antisymm`, `le_trans` | theorem | `leB` is a partial order |
| `le_decomp` | theorem | every relation is reflexive, a cover, or a cover followed by a relation (minimality: `leB` is exactly the closure) |
| `cover_derived_eq` | theorem | the re-derived covers equal the input covers |
| `meet_is_glb`, `join_is_lub` | theorem | the lattice axioms (GLB / LUB universal property) |
| `rank_zero`, `rank_cov`, `rank_mono` | theorem | rank vanishes at bottom, increases by one along every cover, is monotone in the order |
| `W_zero`, `W_one`, `W_two`, `W_three`, `W_four` | theorem | `W 0 = 1`, `W 1 = 2`, `W 2 = 1`, `W 3 = 1`, `W 4 = 0` |
| `logConcavity_fails` | theorem | **`W 2 * W 2 < W 1 * W 3`** |
| `strictLogConcavity_fails` | theorem | **`¬ (W 1 * W 3 ≤ W 2 * W 2)`** |
| `upperSemimodular_true` | theorem | the witness is upper semimodular |
| `distributive_true` | theorem | the witness is distributive (hence modular, hence semimodular) |
| `atoms_eq`, `joinAtoms_eq` | theorem | atoms are `[1,2]`, their join is `3` |
| `not_atomistic` | theorem | `joinAtoms ≠ top`: the lattice is not atomistic, hence not geometric |
| `conjecture_00000002605_false` | theorem | the conjunction: `W₂² < W₁W₃` **and** `¬ (W₁W₃ ≤ W₂²)` **and** `upperSemimodular = true` **and** `joinAtoms ≠ top` |

Every theorem is proved by `decide`, i.e. by kernel-checked evaluation of a
closed Boolean/arithmetic computation. The quantifications over `Fin 5` are
internalised as `List.all` over `elems`, so no quantifier decidability beyond
`Init` is needed.

## Axiom audit

`lake env lean Check.lean` reports, for every one of the 23 audited theorems,
exactly

```
'Tlmc2605.<name>' depends on axioms: [propext]
```

In particular **no `sorryAx`** appears, and there is no Mathlib and no
`Classical.choice`. (`propext` enters through `decide`'s use of decidable
equality / proof irrelevance on the `Fin 5` and `Bool` computations; it is a
core axiom.)

## Proof strategy

- **Order derived from covers.** `closeIter n` starts from equality together
  with `covB` and applies `n` relaxation steps `r ↦ r ∪ (covB ∘ r)`, each step
  appending at most one cover at the top. Since the longest cover-chain has four
  edges, `leB := closeIter 5` is the full reflexive-transitive closure; the
  decomposition theorem `le_decomp` is the minimality half of this statement.
- **Lattice axioms.** `meetB x y` folds over the elements below both `x` and
  `y`, starting at the bottom `0`; `joinB` is dual, starting at the top `4`.
  `meet_is_glb` checks (as a Boolean computation over all 25 pairs, with an
  inner `all` over all elements) that the result is a lower bound and dominates
  every lower bound; `join_is_lub` is the dual. These are precisely the lattice
  axioms.
- **Rank.** `rankIter` relaxes `d y := max { d x + 1 : x ⋖ y }` from `d ≡ 0`.
  Because the `if covB x y` branch guards the recursive call, this is cheap.
  `rank_zero`, `rank_cov` and `rank_mono` pin it as the rank function (the
  longest cover-chain length, normalised to `0` at the bottom). Since the
  lattice is graded and the bottom is below every element, these properties
  determine the rank function uniquely.
- **The refutation.** From `W 1 = 2`, `W 2 = 1`, `W 3 = 1`, `decide` closes
  `W 2 * W 2 < W 1 * W 3` and its negation. `upperSemimodular_true` checks the
  25 pairs `x ∧ y ⋖ x ⟹ y ⋖ x ∨ y`. `distributive_true` checks the 125
  triples of the distributive law. `not_atomistic` records that the join of the
  atoms is `c = 3`, not the top `4`.

## Scope note and faithfulness caveat

This is a faithful but deliberately minimal formalisation; the boundaries are:

- **One concrete witness, not a class theorem.** As a *disproof*, a single
  counterexample suffices, and that is what is formalised: the specific
  `5`-element lattice. The file does **not** formalise a general theorem about
  all semimodular lattices. That is not needed for a refutation.
- **"Zero N₅ sublattices" is argued, checked in Python, not formalised in
  Lean.** The Lean file proves `distributive_true`. The step
  "distributive ⟹ no N₅ sublattice" (N₅ is the forbidden non-modular
  sublattice) is a classical theorem that is *not* formalised here;
  `reproduce.py` instead **enumerates** every `5`-element subset, keeps the
  sublattices (closed under the computed meet/join), and checks
  order-isomorphism with `N₅`, obtaining count `0` directly.
- **The notion "geometric lattice" is not formalised.** The Lean file proves
  `joinAtoms ≠ top`, which is exactly non-atomisticity; the implication
  "geometric lattice ⟹ atomistic" and the geometric-lattice log-concavity
  theorem are not part of this project. See the caveat in the top-level
  `README.md` and in `main.tex`: this submission refutes the conjecture's
  literal wording over *semimodular* lattices and does **not** dispute the
  geometric-lattice theorem.
- **No physical Boolean-layer claim is formalised.** The second extra clause
  ("fifth-layer embedding in the free Boolean lattice") is refuted in prose and
  by `reproduce.py` (binomial rank numbers have deficit `0`); the Lean file does
  not contain a Boolean-lattice development.
- **Prototype vs. final.** An earlier prototype (in `/tmp`, not part of this
  submission) hardcoded the meet/join and rank **tables**. The present file
  improves on that: the order, meet, join, and rank are all **derived** from the
  cover relations, and the order/lattice/rank axioms are **proved**. The only
  remaining "input table" is `covB`, the definition of the lattice itself, plus
  the derived `decide` evaluations.

## Environment

Lean 4.33.1, Lake, no Mathlib, no dependencies. `lake build` needs no cache
download and exits `0`.
