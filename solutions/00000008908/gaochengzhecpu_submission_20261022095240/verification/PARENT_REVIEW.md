# Parent adversarial review: 00000008908

Verdict: PASS

The parent read the exact bilingual source, the complete frozen Lean file,
the full author proof and self-review, the independent exact-arithmetic
verifier, actual author and fresh-build logs, and all three final rendered
PDF pages. This is internal parent review of an agent-developed proof;
no external independence is claimed.

The English source explicitly names the complement's CLIQUE number as an
endpoint. The actual simple five-cycle has Mathlib independence number two
and genuine complement maximum clique number two. Ordinary kernel decide
enumerates all finite subsets to certify the universal size bound; the
actual pair {0,2} attains it. The proof uses Mathlib cliqueNum/indepNum and
their complement identity, not numbers assigned to graph names.

The theta definition is the full standard PSD, trace-one, edge-zero real
matrix optimization. Parent opened Lovasz's original paper, Theorem4, and
Goemans' ICM survey and checked this edge convention. Feasible imposes no
circulant/rational/rank restriction. Actual Mathlib PosSemidef contains
symmetry and positivity of every real quadratic test, not an ad hoc cone.

The displayed integer circulant Gram factor is exact; the parent also
independently recomputed its entries. Gram diagonal2257, edge entries0,
remaining off-diagonal1392, normalization11285, objective5041/2257 and
positive gap527/2257 all agree between Lean, auxiliary code and paper.
The real Gram matrix gives genuine PSD for all vectors, so there is no
floating-point eigensolver or assumed numerical semidefiniteness.

The sup is the actual supremum over ALL feasible objective values, not
the witness's value renamed theta. Nonemptiness is witnessed explicitly.
For every PSD matrix, testing e_i-e_j proves 2Xij<=Xii+Xjj; summing all25
pairs gives objective<=5 under trace1. Thus the whole feasible set is
bounded above. The proof then validly compares its actual real supremum
to the witness. No empty/unbounded conditional-complete-order convention
or unproved optimizer attainment is used.

Both endpoint values are two while theta is strictly greater than two,
so a monotone chain between those endpoints fails in either orientation.
The paper correctly distinguishes the standard valid CHROMATIC endpoint
sandwich. It claims neither exact theta=sqrt(5) nor optimality of this
rational certificate. Those stronger conclusions are not needed.

The supplementary verifier reconstructs the Gram factor and enumerates
actual graph cliques using exact Fractions. Its finite computations are
not trusted by Lean. Fresh complete lake build, strict Main and verifier
all exited zero. Official dependency revisions and source cleanliness were
checked; printed axioms contain only the three standard foundational ones.
The exact current TeX passed native compilation, Tectonic has zero warnings,
and all three final PDF pages are complete and legible, with clean matrix
displays and references and no clipping or overlap.


Reviewed artifact hashes:

- Main.lean: `36281b8a4e00b73151244703a2b595d124b5389445a9f502d7bfed21d03c71b2`
- main.tex: `7a574c0e87e1d2819ed7960e3639ac34625f3275a946aacf997e16286a3f6e01`
- main.pdf: `83fb9398e705234b96e419b5b568489982717d7fd0bec70c5187fa37162d90ba`
- SOURCE.md: `5940d1502259e2fea00b10d0484a0a5dbd71304db7f4ec45c0d2f40c76a5d4e5`
