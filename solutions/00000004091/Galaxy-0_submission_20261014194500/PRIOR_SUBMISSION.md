# Earlier submission and semantic repair

## Prior contribution and status

[orionsheep's PR 292](https://github.com/The-Last-Math-Competition/The-Last-Math-Competition/pull/292) was opened on 3 October 2026 and closed without merging later that day. Its head commit is `f444e65a6793129520e57dbd72982fa1e264f845` in `orionsheep/The-Last-Math-Competition`. The mathematical observation in that PR is correct: at n = 1, P4 and C4 have the same chromatic number 2 but first Betti numbers 0 and 1. We credit orionsheep for that earlier submitted counterexample and claim no novelty for the idea. The present choice K2/C4 merely shortens the acyclic witness.

The complete returned PR discussion contains one organizer review comment, by lidangzzz on 3 October 2026 at 11:57:50 UTC. [That comment](https://github.com/The-Last-Math-Competition/The-Last-Math-Competition/pull/292#issuecomment-5968931449) rejects the missing semantic connection between the Lean arithmetic, graph invariants, and conjecture. Direct inspection of all Lean source in the fetched PR diff confirms the issue. The fetched metadata, full diff, and review response are included in `evidence/eligibility-00000004091.json`.

## What the earlier Lean theorem did

The earlier Lean declarations have the following types:

- `b1_C4`: the natural-number identity 4 + 1 - 4 = 1
- `b1_P4`: the natural-number identity 3 + 1 - 4 = 0
- `betti_differ`: 1 != 0
- `same_chromatic`: (2 = 2) and (2 = 2)
- `conjecture_refuted`: the conjunction of those statements

Those are true arithmetic facts. However, no graph, coloring, chromatic minimum, homology, or configuration-space object appears in their types. Thus the Lean conclusion does not establish the conjecture's negation; names and comments cannot supply that missing mathematical content. The problem was incompleteness of the formal semantic connection, not an error in the elementary counterexample.

## Concrete repairs in the current project

1. Graphs are objects. `Graph` stores finitely many vertices, oriented edge endpoints, no-loop proofs, and uniqueness of undirected edges. `segment` and `square` are explicit K2/C4 instances.
2. Chromatic number is a minimum. `Coloring` is an actual vertex function satisfying the edge constraint. `HasChromaticNumber` requires both a proper coloring and exclusion of every smaller color count. The two-colorings and the lower bound from an edge are proved.
3. Homology is computed from incidence data. `boundary` sums incoming rational edge coefficients minus outgoing coefficients at each vertex. `IsCycle` is the kernel. There are no unexplained Betti labels or hard-coded graph rank assignments.
4. Betti values have genuine bases. `HasFirstBetti` supplies cycle vectors, spanning, and unique rational coefficients. `segment_cycle_iff` and `square_cycle_iff` characterize the full kernels; the basis theorems certify dimensions 0 and 1.
5. The conclusion is a universal refutation. `ChromaticDeterminesFirstBetti` asks for a function assigning every certified graph's Betti dimension from its certified chromatic minimum. `conjecture_00000004091_false` applies it to the two graph witnesses and derives a contradiction at input 2.
6. The topology bridge is explicit. Section 4.1 of the report constructs the finite one-dimensional CW realization, identifies chain coordinates and incidence boundaries, interprets the basis certificates, invokes Hatcher's cellular-to-singular comparison with rational coefficients, and uses the proven one-particle homeomorphism from Section 2. This connects the formal cellular calculation to the topological conjecture in the paper.

## Remaining formalization boundary

The CW realization, its topology, singular homology, the general comparison theorem, and the Conf_1 homeomorphism are not Lean definitions or theorems here. The report proves or cites them explicitly. They are not imported as extra Lean axioms. The kernel-checked result is the graph/chromatic/rational-cellular statement. Whether the resulting combination of complete paper proof and explicit finite algebraic formalization meets the competition's standard is for its reviewers to decide; this package does not represent itself as an organizer-approved or wholly Lean-topological proof.

The subdivision-invariance clause is true under the usual geometric configuration-space definition. Only the polynomial clause is refuted. The present proof uses the same-chromatic-number witnesses directly; it does not need any additional claimed conflict involving a change in chromatic number under subdivision.

## Publication requirement

Rule 2 requires any new PR description to give a complete account of the earlier failed submission and the correct replacement. Its body should link PR 292 and its rejection, credit the earlier counterexample, summarize the missing semantic connection and items 1–6 above, and state the remaining topology boundary. Do not say that no earlier PR exists.
