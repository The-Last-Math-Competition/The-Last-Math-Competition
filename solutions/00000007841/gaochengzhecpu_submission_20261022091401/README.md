# Disproof of Conjecture 00000007841

For every simple connected cycle C_n, n>=3, the actual uniform-edge Karger contraction algorithm returns some minimum cut with probability one. The claimed cycle-sharp expression 2(1-epsilon(n))/n^2 tends to zero for epsilon(n)=O(1/n), and its gap from the actual success probability tends to one.

## Scope

Refutes the explicit tight-on-cycles conjunct (the Chinese source asserts equality), hence the full conjunction. It treats success as returning ANY minimum cut, exactly as the source defines p(G). No formal assertion about the infimum ratio rho(n), its actual extremizers, or failure of the lower-bound inequality itself is claimed.

## Formalization

Lean starts with actual Mathlib simple connected cycle graphs of every order at least three. It identifies their actual undirected edge sets with cycle labels, proves exact quotient fibers for arbitrary-edge contraction, deletes exactly the selected loop and preserves every remaining edge and parallel multiplicity. Actual returned bipartitions are pulled back through these same quotient maps. Every proper cut has size at least two and every history returns a proper cut of size two. Actual successive uniform-edge weights are proved nonnegative and sum to one; success probability is their sum over the actual minimum-cut event, not defined as one. The final theorems prove probability one, an arbitrary-cutoff contradiction under any eventual O(1/n) correction, and gap tending to one rather than zero under the weaker epsilon->0 assumption. The auxiliary exact-arithmetic enumerator independently checks cycles and complete graphs and is not an oracle for Lean.

## Reproduction

Inside lean/: `lake exe cache get`, `lake build`, and
`lake env lean -DwarningAsError=true Main.lean`.
Lean 4.19.0 and Mathlib c44e0c8ee63ca166450922a373c7409c5d26b00b are pinned.
Run `python verify.py` for supplementary exact finite enumeration and
`tectonic main.tex` for the paper. The complete cycle-family proof is in Lean.
The exact bilingual source, provenance, actual fresh-build logs, axiom audit,
artifact hashes and PDF review are included. An author agent supplied a
self-review; the parent separately reviewed the complete proof and final
artifacts. No external independent review or novelty of the standard cycle
contraction facts is claimed. Karger and Stein's author-hosted paper is cited
for the algorithm and the distinction from a prescribed-cut survival bound.
