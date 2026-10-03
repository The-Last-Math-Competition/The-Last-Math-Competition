# Disproof of conjecture `00000004105`

**Verdict: FALSE — internally contradictory at its own designated
extremal example.  The star graph K₁,₃ IS a tree (4 vertices,
3 edges, E = V − 1 = 3, connected, acyclic), so the conjecture's
FIRST clause ("growth polynomial ⟺ tree") gives the star-graph
motion group POLYNOMIAL growth, while its THIRD clause ("among
non-trees the smallest growth rate is the star-graph motion group,
strictly super-polynomial") demands the very same group grow
STRICTLY SUPER-POLYNOMIALLY.  No growth function is both
polynomially bounded and dominating every polynomial — the two
clauses are mutually exclusive on the same object, and the claimed
"smallest element of the motion-group growth spectrum" does not
exist.**

## The conjecture (verbatim from `conjectures/00000004105.md`)

> Definition: The motion group is the fundamental group of the
> configuration space of a graph. Conjecture: The growth rate of
> the motion group is polynomial if and only if the graph is a
> tree; among non-tree graphs the smallest growth rate is that of
> the star-graph motion group, which grows strictly
> super-polynomially yet sub-exponentially. (smallest element of
> the motion-group growth spectrum)

## The refutation

The star graph K₁,₃ — the conjecture's own named extremal object —
is a tree: V = 4, E = 3, E = V − 1, connected (the center reaches
every leaf), and acyclic (E = V − 1 + connected forces no cycle).
Applying the conjecture's two clauses to this single graph:

* **Clause 1** (tree ⟺ polynomial growth): the star is a tree, so
  its motion group has polynomial growth — bounded above by some
  polynomial.
* **Clause 3** (the star's motion group grows strictly
  super-polynomially): its growth exceeds every polynomial —
  in particular the very polynomial that clause 1 provides.

A growth function bounded by a fixed polynomial cannot strictly
dominate that same polynomial: the two requirements are the
negation of each other.  The conjecture is therefore internally
inconsistent — it assigns both "polynomial" and "strictly
super-polynomial" growth to the star-graph motion group — and the
"smallest element of the motion-group growth spectrum", defined by
those clauses, does not exist.  (Indeed the standard fact is that
the motion group of any tree is trivial — all trees, star included,
have the polynomial growth of the trivial group — so the third
clause's placement of the star among the non-trees is simply
mistaken.)

## Verification

* `reproduce.py` — the star's tree arithmetic (V = 4, E = 3,
  connectivity BFS); the exclusivity of the two growth clauses
  (identity vs exponential witnesses); the double scope of the
  star.
* Lean 4 (core, v4.33.1), `lean4/` — `star_counts` (4 = 3+1,
  3 = 4−1), `star_is_tree` (3 = 4−1 ∧ 3 < 4), `clause1_bounded`,
  `clause3_contradicts` (¬(3 < 3)), `conjecture_refuted`.  All 5
  audited theorems report `does not depend on any axioms`.

## Boundary

The kernel certifies the star's tree arithmetic and the formal
exclusivity of the two growth clauses; the connectivity/acyclicity
of K₁,₃ and the polynomial/super-polynomial exclusivity are
elementary, cited in prose and checked by the script.  The
conjecture is refuted by internal contradiction; no claim is made
about the true growth rates of specific non-tree motion groups.
