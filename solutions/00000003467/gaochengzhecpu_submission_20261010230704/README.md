# Disproof of Conjecture 00000003467

On the fixed group Z/12Z, S1={1,11,3,9} and S2={1,11,2,10} are inverse-closed generating sets of size four. The corresponding connected Cayley graphs retract onto K2 and K3, which are their cores. The core edge counts are 1 and 3, so no function of generating-set size, and hence no claimed linear formula, can describe both.

## Scope

This refutes the abelian assertion while holding the entire group fixed. Both graphs are simple, undirected and connected, and both connection sets generate the group. The source imposes no minimal-generating-set condition. The contradiction is independent of the rank convention or a choice of intercept. No conclusion about the separate nonabelian assertion is needed.

## Formalization

Lean constructs actual ZMod 12 Cayley graphs and proves generation and connectedness. It builds the retractions and inclusions as graph homomorphisms, verifies left inverses, and proves complete graphs are cores. The standard endomorphism/retraction core predicate is linked to vertex minimality, induced-subgraph adjacency, uniqueness up to isomorphism and actual edge counts for any finite core. It then proves the fixed-group counterexample and failure of every function of generating-set cardinality. All finite checks are kernel checked.

## Reproduction

In `lean/`, run `lake exe cache get`, `lake build`, and
`lake env lean -DwarningAsError=true Main.lean`.
Lean 4.19.0 and Mathlib `c44e0c8ee63ca166450922a373c7409c5d26b00b`
are pinned in public-Git project metadata. Only verified official dependency
artifacts are reused; the submitted project is freshly rebuilt.
Run `tectonic main.tex` for the PDF. No auxiliary computation is required.

`SOURCE.md` preserves the exact bilingual source. `verification/` contains
provenance, actual build logs, hashes and review records. The author performed
a separate adversarial self-review; no independent reviewer or subagent was used.
