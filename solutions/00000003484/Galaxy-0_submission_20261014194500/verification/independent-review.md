# Independent review of Conjecture 00000003484

Review date: 14 October 2026, approximately 19:48–19:52 UTC.

## Recommendation

PASS for release within the expressly stated scope. I found no mathematical, formal-semantic, proof-integrity, or PDF-rendering defect that blocks this counterexample. This is a separate AI-assisted mathematical and build audit, not a human expert endorsement, organizer decision, acceptance, or guarantee of first-solver credit. No publication or external write was performed during this audit. Recheck live eligibility immediately before any submission.

The conclusion is that the source's bag-count equation and its zero-genus implication cannot both hold on the connected 3-sun under the source's maximal-clique-node definition. No definition or value of the unspecified Helly covering genus is invented.

## Exact files reviewed

I read the complete 465-line Main.lean, complete report.tex, exact bilingual source, source provenance, eligibility evidence, and verification records. I visually inspected all three rendered pages of the final report.pdf. The author files were not edited.

SHA-256 identities of the reviewed author files:

- Main.lean: `365283d228a56d63a3246747df5ae92c681ce3b8eb09e86b428c7180a2ea21ce`
- report.tex: `f7ae2187a4993a91a53a8b62d53555363913178e4886e302f6fa94898ccac31e`
- report.pdf: `e9d283399041647a584a110d1777534b1e0c66a808b2885e275c82cdd7fb6638`

The 692-byte source has SHA-256 `ee45b512bb8537d3d36add20f97d48f642e44331f76cd02ba30451c75d18daab`; I independently recomputed its Git blob identity as `6e8283ae36deff4684090880c4d608259201b28e` and matched it to a fresh pinned repository read.

## Mathematical and semantic checks

1. The adjacency expression really defines the six-vertex 3-sun: a central triangle on 0, 1, 2; outer vertex 3 adjacent exactly to 0, 1; vertex 4 to 1, 2; vertex 5 to 0, 2. There are nine undirected edges, no loops, and no outer-outer edges. Symmetry and irreflexivity are proved. The additional connectedness theorem constructs actual walks; it is not a Boolean label or an assumed hypothesis.

2. Chordality is the absence of induced simple cycles of length at least four. InducedCycle requires an injective map and adjacency if and only if cyclic consecutiveness. The proof treats all natural cycle lengths, uses actual neighbors of each cyclic index, excludes simplicial outer vertices from a long induced cycle, and then obtains a contradiction from four distinct vertices in a three-vertex core. It does not replace chordality with an unproved elimination-order equivalence or a bounded search.

3. MaximalClique quantifies over arbitrary subsets of the six vertices. The four displayed bags are proved to be cliques and inclusion-maximal; every clique is contained in one of them. The resulting maximal-clique classification is exhaustive, and bagSet is injective. The list counting maximal cliques is separately proved complete and without repetitions. Thus maximalCliqueCount = 4 is a count of the genuine maximal cliques.

4. CliqueTree requires irreflexive symmetric edges, actual connected walks, absence of simple cycles of every length, maximal bags, completeness, distinctness, and running intersection. The displayed four-node star satisfies every field. Its node list is complete and has no repetitions, independently of the maximal-clique list. Thus bagCount = 4 counts the nodes of an actual conventional clique tree. The definitions are graph-specific but semantically faithful, not result-shaped substitutes.

5. IntervalRepresentation uses nonempty closed intervals and an existential actual intersection point. The endpoint-overlap equivalence is proved from totality, transitivity, and nonemptiness. In particular, overlap is not merely asserted as an axiom. The universal obstruction applies to every total transitive relation, so it applies in particular to ordinary real order. Antisymmetry is unnecessary and its omission strengthens the result. IsInterval existentially quantifies the endpoint type, order relation, and endpoints, and its negation is genuinely proved. The written middle-outer-interval argument is correct in all three cases: use c when x is in the middle, a when y is in the middle, and b when z is in the middle.

6. The two concluding Lean theorems exclude any natural or integer h satisfying both 4 = 4 - h and h = 0 iff IsInterval. The natural-number theorem correctly handles truncated subtraction; positivity of four prevents the zero-cardinality exception. The integer theorem uses signed subtraction. The report accurately distinguishes these formal types from its elementary written cancellation argument for other ordinary numerical systems.

7. The report's finite normalization from arbitrary nonempty real intervals to closed bounded intervals is sound: choose points for vertices and edges, then take finite convex hulls inside each original interval. It is correctly identified as a written argument rather than a Lean theorem. No topology theorem or Mathlib real-analysis instantiation is claimed.

8. Both source languages entail the necessary implication from zero genus to interval representability. The possible Chinese scope ambiguity involving the trailing recursion does not remove that implication. Refuting the two necessary clauses suffices, so there is no need to invent or evaluate the unspecified recursion. The finite, simple, connected example avoids possible scope objections about disconnected or infinite graphs.

## Reproduced formal verification

I copied the exact final Main.lean into a separate audit-verify directory containing no pre-existing Main.olean. With the pinned toolchain on PATH, I ran:

```text
lean --version
sha256sum Main.lean
lean -DwarningAsError=true -o Main.olean Main.lean
LEAN_PATH=. leanchecker Main
LEAN_PATH=. lean -DwarningAsError=true Axioms.lean
```

The compiler reported Lean 4.31.0, commit `68218e876d2a38b1985b8590fff244a83c321783`. The strict source build and separate kernel replay both exited 0; the independently recorded verification.log includes explicit `STRICT_BUILD_EXIT=0` and `KERNEL_REPLAY_EXIT=0` markers. The final source hash matched before this build.

The 38-theorem axiom audit also completed successfully. Every printed dependency is among propext, Classical.choice, and Quot.sound; some theorems have no axioms. The source declares no custom axiom and contains no sorry, admit, native_decide, or unsafe declaration/tactic. I also inspected the definitions and proofs themselves, rather than relying only on this token scan. The packaged Lake configuration pins the same compiler and treats warnings as errors.

I read and reran the independent Python enumeration. It checks all subsets for maximal cliques and all 1,800 ordered injective candidate cycles of lengths four through six; it confirms exactly the four stated maximal cliques, no induced long cycle, and running intersection. This is a supplemental finite cross-check, not the justification for the universal Lean theorems.

## PDF verification

The final PDF has three A4 pages. All three page renders were opened and inspected. Text, mathematical symbols, equations, lists, page breaks, and page numbers are legible; there is no clipping, overlap, missing glyph, or misplaced mathematical content. The report correctly labels the limits of formalization and distinguishes internal review from organizer acceptance. All nine PDF fonts are embedded Type 1 fonts. The TeX log contains a default pdftex.map warning; the explicitly loaded maps produced the fully embedded, correctly rendered final PDF. This warning does not indicate a defect in the inspected artifact.

## Source and eligibility checks

Fresh checks during this audit still show main at `cce2d90cb298de9595798eb674d2c80712100532`. The exact source and metadata were read again at that commit. Metadata blob `ea8c9f6be73eecad1aa3b9e3b802a03a06072a86` contains:

```text
00000003484,,,,,,false,false,,false,
```

A fresh direct request for solutions/00000003484 returned 404. Separately, the saved complete, non-truncated solutions tree at `735647fb89aa45afc9a8490098b4add305d82792` contains 876 entries and no 3484 directory. The unchanged current main commit anchors that tree evidence.

I repeated raw GitHub all-state PR searches for the 11-digit ID, four-digit ID, and distinctive keywords. None uses an open-only filter. Results were: 00000003484 = 0; 3484 = 0; quoted Helly covering genus = 0; quoted clique tree = 3. All four responses report incomplete_results=false. The three phrase hits and the additional hyphenated-search hit in the original evidence are PRs 964, 983, 732, and 1007. I read their bodies and complete changed-filename listings. Their respective 8, 19, 15, and 16 files belong to other conjectures (3470, 4227, 1680, and 3996); none is a 3484 submission or a refutation of its bag-count/genus claim.

To avoid relying solely on potentially false-empty search-index responses, I additionally fetched the direct PR collection with state=all, sorted by creation, 100 records per page, through its final short page. The 11 pages contain 1,014 distinct PR records, with no duplicate record numbers. Their returned titles and bodies contain no full ID, standalone four-digit ID, Helly covering genus phrase, or clique-tree bag-count phrase. The public package records every request URL, timestamp, page count, and matching result in eligibility/all-state-pr-pagination-summary.json. The complete returned title/body/state listing is retained with the research records as live-pr-list-audit.json, with SHA-256 `49407c22d1de1142c69e3677cd384e1fefae015c91e85301a106fee3652d4d9b`; that digest is also recorded in the public summary. I checked that the summary matches the complete listing. The terminal page contains 14 records. This is a title/body screening of the full directly returned collection, not a claim to have semantically read every historical PR file or comment.

Supporting fresh records are in live-pr-searches.json and live-source-status.json. These observations support eligibility at the recorded time; they cannot rule out future submissions, unindexed language-only references, or organizer interpretations. They do not establish acceptance or priority.

## Release conditions

Keep the above Main.lean, report.tex, and report.pdf hashes unchanged, retain the exact source and verification evidence, and recheck repository eligibility before publishing. If any reviewed author file changes, this review must be updated for that revision. No blocking correction is requested for the reviewed revision.
