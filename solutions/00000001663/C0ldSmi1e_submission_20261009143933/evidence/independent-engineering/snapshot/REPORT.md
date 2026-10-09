# Disproof of the literal strengthened conjunction in conjecture 00000001663

## Result and scope

The original submission target is **false as written**. Its added reconstruction-rigidity clause quantifies over two graphs with the same vertex-deleted deck and asserts that their edit distance is at least two. It does not assume that the graphs are distinct or nonisomorphic. Taking any admitted graph twice gives identical decks and edit distance zero. In particular, take the empty graph on three vertices twice.

The target has been formalized as the conjunction of the named Kelly–Ulam reconstruction assertion and the added rigidity assertion, and its negation has been proved. This result neither proves nor disproves the classical Kelly–Ulam reconstruction conjecture. No claim of a breakthrough on classical reconstruction is made. Its truth value is not needed at any point.

## Exact source and interpretation

The supplied source is preserved verbatim in `source/ORIGINAL.md`. Its English conjecture reads: “The reconstruction conjecture holds; strengthened (reconstruction rigidity): two graphs with the same deck have edit distance ≥ 2 — the reconstruction data are locally rigid.” The Chinese statement likewise contains no distinctness or nonisomorphism condition.

We use finite simple undirected graphs and the ordinary **unlabelled unit-cost edge-edit convention**: after a bijection between equal-sized vertex sets has been chosen, each unordered pair whose adjacency differs costs one; the distance is the minimum of this count over all bijections. Vertices are not inserted or removed in this equal-order edge-edit distance. Loops are absent, and the two orientations of an edge are counted only once.

The deck is a multiset of isomorphism classes of vertex-deleted graphs. Thus isomorphic cards are identified, but their multiplicities are retained. Reconstruction is up to graph isomorphism. No extra distinctness, connectedness, nonisomorphism, or edge hypothesis has been introduced.

The finite vertex set is `Fin (n + 1)` and the hypothesis is `2 ≤ n`. Therefore the actual order is `N = n + 1 ≥ 3`. Conversely, every integer order `N ≥ 3` is of this form. Every finite graph can be transported along a vertex enumeration to a graph on `Fin N`; graph isomorphism, the multiset deck, and the minimized edit distance remove the choice of labels. This representation does not restrict the graph class.

## Mathematical proof

For graphs `G,H` on a fixed vertex set of size `N` and a vertex bijection `f`, define

\[
 c_f(G,H)=\#\{(u,v):u<v,\ [u\sim_G v]\ne[f(u)\sim_H f(v)]\},
 \qquad d(G,H)=\min_f c_f(G,H).
\]

The order test chooses exactly one representative of each unordered pair. The finite set of bijections is nonempty, containing the identity. The Lean definition uses `Nat.find` on the nonempty set of attained costs. The two theorems `editDistance_attained` and `editDistance_le_cost` establish that the result is attained and is no greater than any bijection's cost, so it is an actual minimum.

For the identity bijection from `G` to itself, all adjacency comparisons agree. Consequently its cost is zero. Since costs are natural numbers, `d(G,G)=0`. The same argument works for any graph isomorphism. The identity of multisets gives `deck(G)=deck(G)`.

Choose `G=H` to be the empty graph on three vertices. Both hypotheses of the rigidity clause hold: order at least three, and equal decks. Its conclusion would say `2≤0`, a contradiction. Thus the rigidity assertion is false. If the complete conjunction were true, its second conjunct would be true, so the complete conjunction is false.

The argument is independent of the status of reconstruction. It does not use a pair of nonisomorphic graphs with equal decks. Such a hypothesis, if added, would define a different statement. Merely requiring unequal labelled adjacency relations would not rescue the given edge-edit clause: the formal challenge module exhibits the one-edge graphs with edges `{0,1}` and `{0,2}`, which are unequal as labelled graphs but isomorphic, have equal decks, and have distance zero.

## Source-to-theorem map

| Source component or convention | Lean declaration |
| --- | --- |
| Finite simple undirected graph, fixed order | `Conjecture1663.Graph` = `SimpleGraph (Fin n)` |
| Unlabelled graph card | `graphSetoid`, `Unlabelled`, `unlabelled` |
| Equality of unlabelled cards exactly means isomorphism | `unlabelled_eq_iff` |
| Vertex-deleted induced graph | `deleteVertex` |
| All surviving vertices, each exactly once | `deletion_vertices_exact`, `deletionInducedIso` |
| Deck with multiplicities | `deck`, `deck_card`, `empty_deck` |
| One unit per unordered differing edge under a bijection | `edgeEditCost` |
| Minimum over every vertex bijection | `editDistance`, `editDistance_attained`, `editDistance_le_cost` |
| Named Kelly–Ulam reconstruction assertion at all orders ≥3 | `Reconstruction` |
| Added rigidity assertion without extra hypotheses | `ReconstructionRigidity` |
| Entire original conjunction | `OriginalClaim` |
| Zero cost for an isomorphism, especially the identity | `edgeEditCost_iso`, `editDistance_iso`, `editDistance_self` |
| Universal diagonal obstruction | `every_graph_violates_rigidity` |
| Smallest admitted-order witness | `order_three_counterexample` |
| Negation of the added clause | `not_reconstructionRigidity` |
| Negation of the full original statement | `originalClaim_false` |
| Independently spelled out quantified conjunction | `Verification1663.exact_original_negation` |

The mathematical root is `Conjecture1663.lean`, importing `Definitions`, `Proof`, and `Challenges`. The second root is `Verification.lean` and is built after a fresh build of the mathematical root.

## Challenge coverage

These are proved in Lean, with kernel checking:

1. The deletion map is injective and its image is exactly the complement of the deleted vertex. Its card is isomorphic to the ordinary induced subgraph on that complement.
2. Every deck contains exactly as many cards as original vertices. The empty graph's deck contains precisely `n+1` copies of the empty card, rather than a singleton set.
3. An arbitrary graph isomorphism induces matching deleted-card isomorphisms and equal multiset decks.
4. Edit distance zero is equivalent to existence of a graph isomorphism. In particular, the definition does not silently enforce fixed labels.
5. Two unequal labelled one-edge graphs have equal decks and edit distance zero.
6. Inserting a single unordered edge costs exactly one and the resulting unlabelled distance is exactly one. This checks that orientations are not double-counted and the distance has not collapsed to the constant zero function.
7. The explicit counterexample has order three, and a separate theorem applies the diagonal obstruction to every finite simple graph.

An independent Python calculation additionally enumerates **all labelled simple graphs and all ordered pairs at orders 2, 3, and 4**. It constructs canonical unlabelled cards by testing all permutations and computes edge-edit distance by a minimum over all permutations. It checks deck length, repeated empty cards, all diagonal distances, symmetry, fixed-labelling upper bounds, and the equivalence of zero distance with isomorphism. At orders three and four it checks that all equal-deck pairs have distance zero. These finite calculations are sanity checks, not a substitute for the universal Lean proof. Order two is excluded by the original: the empty graph and the single edge have the same two singleton cards and distance one, which the calculation also detects.

## Proof dependencies, replay, and limitations

The final evidence and commands are recorded in `VERIFICATION.md`. `scripts/replay.py` verifies the supplied source hashes, local mathematical source bindings, package revisions and cleanliness, runtime binaries, and fingerprints of all imported compiled modules and available module sources. It creates a new workspace without any owned compiled objects, builds both roots with warnings treated as errors, executes the declaration audit afresh, and runs the finite computation afresh. A previous evidence file is not used to establish a new success.

`scripts/Audit.lean` identifies owned declarations by the originating module, rather than by a name prefix. This includes generated declarations. It runs Lean's axiom collector on every owned declaration, then recursively visits constants referenced by types and every available body. It rejects missing constants, unsafe definitions, partial definitions, and axioms outside `propext`, `Classical.choice`, and `Quot.sound`. It records all visited declarations and all imported module names. The audit is a metaprogram executed by Lean; it supplements rather than replaces the kernel checking of the mathematical and verification roots.

During development the all-declaration audit found Lean-generated compiler-stage declarations using the compiler's erased-proof axiom `lcProof`. The theorem proofs themselves did not depend on it. The initial audit failure was retained. The final mathematical definitions are explicitly marked noncomputable to suppress executable compiler stages; the mathematical definitions, proposition statements, and proof arguments are unchanged. The final audit therefore needs no axiom exemption for compiler stages. A section-level noncomputability marker alone was tested and was insufficient; that failed audit is also retained.

Dependency caches are reused from the explicitly allowed neutral package tree. The replay freshly compiles all owned mathematical and verification roots, but it does **not** rebuild the entire Lean runtime or all of Mathlib. Imported compiled objects and available source files are fingerprinted. Runtime source availability and any source-to-binary limitation are reported honestly in the evidence. The trust boundary includes the pinned Lean kernel, standard permitted logical axioms, dependency compiled objects, and the local execution environment. The finite Python program is not part of the trusted proof.

There is no `sorry`, `admit`, `native_decide`, custom axiom, unsafe definition, or partial definition in the mathematical or verification roots. Failed source attempts are plain text in `archive/`, never imported build roots. This directory is an author deliverable only: no publication, competition eligibility, maintainer acceptance, or independent review result is asserted here.

## Provenance

The author's problem inputs were only the supplied `ORIGINAL.md`, the English and Chinese rules, the supplied `lean-toolchain`, package manifest, and SHA-256 manifest in `/private/tmp/tlmc1663-author-input`. The input SHA-256 manifest itself has hash `6ae1b92afd1d1f78a64addf92af8cf8db6a645f05b3baae4a1f4330ee46a04a4`. Package definitions and APIs were read only from the allowed neutral pinned package tree `/private/tmp/tlmc-standard-library-419`. Runtime executables came from `/private/tmp/tlmc310-runtime/lean-4.19.0-darwin_aarch64/bin`.

No conjecture repository history, prior solution, prior agent proof, selector analysis, root review file, or external proof was consulted. No web search or outside mathematical source was used. All mathematical authoring took place in the fresh directory `/private/tmp/tlmc1663-author`. The parent agent coordinates independent review and any later publication separately. A source-only fidelity instruction required preserving the full conjunction, multiset decks, and unlabelled unit edge cost; it supplied no mathematical direction. The disproof and its proof were chosen independently by this author.
