# Author self-review: conjecture 00000001679

Main.lean SHA-256: `bc70e8c2d89ef7ae717d00e2e24b01190593b8ed952392c684d5148e7c708b31`

main.tex SHA-256: `d7e0b048dcb202e144e374f6b2058b14664c1aa82369c2095d633ddf9911f2ec`

SOURCE.md SHA-256: `fc0157174b1a9134997ec41db297f3393c19947edbfdd4a09222f76423e8b15a`

1. The path is the actual Mathlib graph, with a proved connectedness theorem, so no graph-class assumption is evaded.
2. Every agent has an actual distinct position at every time, represented by an Equiv.Perm. AllMet uses the graph's adjacency relation.
3. The visible-pair map uses inverse position permutations and both edge orientations. Every real meeting is explicitly mapped into its finite image.
4. There are r+1 observations, including time zero. Repeated meetings can only reduce the union cardinality, and image cardinality correctly handles collisions.
5. The formal parameter n is the number of path edges; vertex count is N=n+1. The canceled edge count is strictly positive.
6. Arbitrary permutations form a superset of legal matching-swap schedules, so impossibility in that larger class is a valid lower bound for the stated game.
7. The witness size is obtained by an exact Archimedean existence proof, with natural logarithm comparisons verified in Lean; no giant floating-point computation is substituted.
8. The source states a universal bound without an expansion or random-graph restriction. Only that upper bound is refuted.

Formal and document verification: PASS. The final Lean sources passed fresh `lake build` and direct `lean -DwarningAsError=true Main.lean`. Only standard logical axioms occur. The final LaTeX source compiled successfully in the desktop compiler and Tectonic, and the final two-page PDF has zero TeX warnings. Both final rendered pages were visually inspected and passed. Exact source hashes and command evidence are in BUILD.json; PDF_REVIEW.json binds the page inspection to the final PDF and TeX hashes.
This is an author scope review, not an external review certificate.
