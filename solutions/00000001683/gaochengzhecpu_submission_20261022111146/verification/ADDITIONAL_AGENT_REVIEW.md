# 00000001683 independent adversarial review

Reviewer: GPT-6.1 Sol / High, separate from the proof author. This is an AI review, not human or maintainer approval.

## Scope and result

Mathematical/semantic review: **PASS**. No blocking issue found in the source statement alignment, formal definitions, deck witness, or nonisomorphism argument. An independent strict compiler run against the frozen file also **passed**, exit code 0. All eight printed theorem axiom lists contain only `propext`, `Classical.choice`, and `Quot.sound`.

Source: `round5/source/00000001683.md`. Reviewed proof: `round5/drafts/00000001683/lean/Main.lean`. The exact reviewed source SHA-256 is recorded in `independent_result.json`.

## Definition audit

- `Hypergraph3.edge` is Boolean, hence it has no parallel edges. The two adjacent transpositions generate all six permutations. Together with `noRepeat`, they exclude all repeated-coordinate triples, not only repetitions in the first two coordinates. Thus this is exactly a simple 3-uniform hypergraph.
- `IsIso` uses a genuine vertex equivalence and an iff for every triple, so it preserves both edges and nonedges.
- `Hypomorphic` uses an outer equivalence on deleted vertices, preserving the multiplicity of isomorphic cards. For each card, the inner full vertex equivalence sends the deleted vertex to the matched deleted vertex; injectivity and surjectivity therefore restrict it to a bijection of the complements. Its edge iff is precisely induced vertex-deletion isomorphism. This agrees with Definition 1 of the cited paper.
- `doubleDegree` counts ordered pairs, precisely twice the usual degree. `codegree` counts the possible third vertex for a fixed distinct pair. Both preservation lemmas build the appropriate subtype equivalence; no equality of unrelated cardinalities is assumed.
- `ReconstructionClaim` says that every two finite simple 3-uniform hypergraphs with n >= 8 and equal vertex decks are isomorphic. The n = 9 witness negates that quantified claim directly.
- `IsSteinerTripleSystem` requires each distinct pair to have exactly one third vertex, the standard Steiner triple condition. Both examples have codegree(0,1) = 2, so neither is Steiner. `steiner_clause_false` separately negates the assertion that every counterexample is a Steiner pair. It does not refute the standard necessary congruence condition for actual Steiner systems; this example has 9 vertices.

## Independent data check actually run

`independent_check.py` was written for this review and run with the bundled Python runtime. It reads the Lean file directly rather than importing the author's generators or the root review script.

1. Decoded both exact Lean integer bitmasks. Checked all 729 ordered triples for each hypergraph, including repeated vertices, against simple unordered triples. Both have exactly 28 edges.
2. Compared the newly displayed 28-element unordered edge lists to the masks, including duplicate and edge-size checks.
3. Recomputed all degree and codegree entries and compared them to the literal Lean tables.
4. Read the five card permutations from Lean; checked all nine assigned cards, permutation bijectivity, the deleted vertex image, the exact complement image, and all ordered triples of each complement. All passed.
5. Exhausted all 576 degree-preserving vertex bijections, then checked every pair codegree. Exactly four survive. Each has an explicit triple with conflicting edge status, recorded in `independent_result.json`. This independently reproduces the mathematical obstruction without relying on the author's pruning generator.

## Exhaustiveness of the Lean nonisomorphism proof

The proof initially cases over all nine possible images of 0, then all nine images of 1. In each surviving branch it cases over every possible image of 2 and, when needed, 3 or 4. Each leaf uses a valid degree mismatch, codegree mismatch, injectivity contradiction, or edge/nonedge mismatch. The four edge leaves correspond to the four independently enumerated codegree-preserving bijections. No assumption that a permutation belongs to a smaller family is inserted.

No `sorry`, `admit`, `native_decide`, new axiom, unsafe declaration, external implementation hook, or proof-replacing metaprogram was found in Main.lean. `by decide` creates kernel-checkable proofs.

Independent strict command actually run after the author's freeze: `tools/lean-4.19.0-windows/bin/lake.exe env lean -DwarningAsError=true Main.lean`, with working directory `round5/drafts/00000001683/lean`. The first attempted bare `lake` command failed because Lake was absent from PATH; the absolute local executable above then succeeded. No install or dependency download was performed.

## Literature alignment

Opened https://arxiv.org/html/2312.16152v2 during review. Its Section 2 defines uniform hypergraphs as sets of fixed-size edges, Definition 1 defines hypomorphism with a permutation of the deleted vertices, and Theorem 2.1 states that rank-3 hypomorphic nonisomorphic pairs exist. The explicit counterexample should be credited as a known construction, without claiming a new discovery. None of the proof validity above depends on accepting that theorem as a formal axiom.
