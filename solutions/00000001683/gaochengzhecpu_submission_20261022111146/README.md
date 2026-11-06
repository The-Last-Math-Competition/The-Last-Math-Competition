# Disproof of conjecture 00000001683

Two explicit simple 3-uniform hypergraphs X and Y on {0,...,8}, each
with 28 edges, have identical vertex-deleted decks with multiplicity
but admit no vertex isomorphism. Neither is a Steiner triple system:
the pair {0,1} has codegree two in each. This refutes both reconstruction
for every n >= 8 and the asserted restriction of counterexamples to
Steiner systems. The example is Kocay's classical n = 3 construction,
with its extra vertex 0, not a newly claimed construction.

## Scope

SOURCE.md preserves both language versions exactly. We use the ordinary
multiset of isomorphism classes of induced vertex-deleted hypergraphs.
An isomorphism is an arbitrary bijection preserving all triples in both
directions. The deck matching explicitly matches deleted vertices, so
no multiplicity is lost. Nine satisfies 9 = 3 mod 6: the example does
not disprove the standard necessary congruence for Steiner systems.
It disproves the assertion that all counterexamples must be Steiner.
The source's terminology "3-design" is not used to redefine Steiner
triple systems; they are the usual 2-(v,3,1) designs.

## Formal verification

lean/Main.lean defines real simple 3-uniform hypergraphs by symmetric
Boolean triple relations with no repeated vertices. X and Y have
readable unordered edge sets edgesX and edgesY, with proved uniformity
and edge counts. edgeX_iff_mem and edgeY_iff_mem prove the bit encoding
agrees with those unordered edge sets on every ordered triple.

- same_deck : Hypomorphic X Y.
- not_isomorphic : not (exists e, IsIso X Y e), quantifying over all
  vertex equivalences, with degree/codegree preservation proved first.
- conjecture1683_false : not ReconstructionClaim, where the claim
  quantifies over every n >= 8 and every pair of the defined hypergraphs.
- X_not_steiner and Y_not_steiner negate the ordinary pair-codegree-one
  Steiner condition.
- steiner_clause_false : not CounterexamplesAreSteiner, refuting the
  universal restriction to Steiner counterexamples of order at least 8.

All finite checks use kernel decide. The eight printed axiom audits
use only propext, Classical.choice and Quot.sound. No custom axiom,
sorry, admit or native_decide is used in the proof.

## Reproduction

With Lean 4.19.0 and the supplied public-Git, commit-pinned dependencies:

```text
cd lean
lake build
lake env lean -DwarningAsError=true Main.lean
```

Mathlib is pinned to c44e0c8ee63ca166450922a373c7409c5d26b00b.
Compile main.tex with Tectonic or a compatible LaTeX installation.
The human proof includes all edges, all nine card certificates and a
four-case nonisomorphism argument. No supplementary computation is
needed for the Lean proof.

## Attribution and review status

W. L. Kocay, A family of nonreconstructible hypergraphs, Journal of
Combinatorial Theory, Series B 42 (1987), 46-63. The explicit n = 3
construction is also described in Cooper and Okur, Definitions 9-13:
[Polynomial Reconstruction Problem for Hypergraphs](https://arxiv.org/html/2312.16152v2).
The source snapshot is pinned to upstream commit
b355e42906e6eaf52bc7e9d005e0ef02d8aa7400.

This draft was developed by a delegated AI agent with a self-review;
the coordinating agent reviews it separately. There is no external
independent review. The author strict Lean invocation has passed.
The coordinator handles the fresh build, final document compilation,
page-by-page visual inspection, and publication checks; this author
record does not claim those later checks have already passed.

The coordinator's current historical PR and metadata check found no
earlier submission for this conjecture. Publication requires its own
fresh conflict check.
