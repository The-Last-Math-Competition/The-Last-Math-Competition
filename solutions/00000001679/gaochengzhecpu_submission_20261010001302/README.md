# Conjecture 00000001679: connected paths violate the claimed acquaintance-time upper bound

For a path with N vertices, r rounds expose at most (r+1)(N-1) unordered pairs, even if arbitrary rearrangements are allowed between rounds. Complete acquaintance therefore requires r>=N/2-1. For N>=4 with log N>4096, this exceeds 1024N/log N, disproving the universal upper bound.

## Scope

The graph family consists of ordinary finite connected paths; no disconnected-graph edge case is used. Time zero is included among the observed configurations. The lower bound applies to all position permutations, so it includes every legal matching-swap schedule. The submission refutes the claimed universal upper bound and does not claim a sharp formula for restricted random graph families.

## Formalization

Lean uses Mathlib's actual SimpleGraph.pathGraph and proves connectedness. AllMet is defined by actual path adjacency between the agents' positions. A finite map enumerates time, path edge, and orientation; every actual meeting is proved to occur in its image. Finset cardinalities give the lower bound. Real logarithm inequalities and the Archimedean property then produce a natural vertex count for which no schedule satisfying the proposed bound can complete acquaintance. No large graph is evaluated numerically.

## Reproduction

In `lean/`, run:

```text
lake build
lake env lean -DwarningAsError=true Main.lean
```

The project pins Lean 4.19.0 and Mathlib commit
`c44e0c8ee63ca166450922a373c7409c5d26b00b`, including exact public Git revisions
for its dependencies. On a new machine, fetch official dependency artifacts
with `lake exe cache get`. Run `tectonic main.tex` from the submission directory
to regenerate the PDF. No auxiliary numerical script is required.

`SOURCE.md` is a byte-for-byte copy of the exact current bilingual conjecture.
`SOURCE_PROVENANCE.json` records its immutable upstream commit, Git blob, and
SHA-256. The current source was checked against both the fresh source snapshot
and the upstream tree. `verification/BUILD.json` and its logs record fresh local
Lean builds, direct warnings-as-errors checking, the axiom audit, PDF export,
hashes, and visual inspection. The project's own compiled artifacts are rebuilt;
only official commit-pinned dependency artifacts are reused.

`verification/SELF_REVIEW.md` is the author's semantic review. Parent-agent
adversarial review is a separate step; no external independent review is claimed.
