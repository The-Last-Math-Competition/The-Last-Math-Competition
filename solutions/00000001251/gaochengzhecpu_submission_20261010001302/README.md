# Conjecture 00000001251: capacity-two exclusion has nondegenerate product stationary laws

On the three-site cycle, capacity-two partial exclusion with jump rates eta_i(2-eta_j) has the product Binomial(2,1/2) stationary law. All 27 states have positive mass, and the three-site factorization deficit is zero. The alternative convention of unit-rate legal jumps also has a full-support product stationary law, namely the product of three uniform laws on {0,1,2}.

## Scope

Both examples use actual legal single-particle capacity-two moves on a three-site cycle. They cover both common rate conventions because the source specifies capacity but no jump-rate convention. These are nondegenerate grand-canonical product stationary laws; the source does not restrict to fixed particle-number sectors or extremal laws. Stationarity is certified by the standard finite-chain generator equation pi Q=0, with nonnegative off-diagonal entries and zero row sums.

## Formalization

Lean defines the 27 actual occupancy states, legal moves, and both generator matrices. It proves the capacity bound, positivity and normalization of all state probabilities, exact detailed balance, zero generator row sums, and both stationary equations. It constructs actual Mathlib PMFs and verifies their real probabilities against the corresponding generators. The binomial marginals, product formula, means, and three-point factorization deficit are computed exactly. It does not construct a separate continuous-time sample-path space; the checked statement is the exact finite-generator stationarity criterion.

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
