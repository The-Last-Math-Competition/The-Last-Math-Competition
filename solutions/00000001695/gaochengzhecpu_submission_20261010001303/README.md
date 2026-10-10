# Conjecture 00000001695: the stated prime-time normalization fails on the constant observable

Rotate the unit circle by sqrt(2), whose bad-approximation bound 1/(5q^2) is proved explicitly, and take f=1. The actual source average is primeCounting(N)/N while its actual Haar integral is one. An elementary parity sieve gives an error at least 1/4 for N>=16. Every proposed nonnegative constant fails at arbitrarily large N, at every starting point.

## Scope

This uses the source's explicit 1/N normalization and a genuine measure-preserving linear polynomial phase with badly approximable coefficient. The source does not require a zero-mean observable. The argument treats every nonnegative error-bound constant and every eventual threshold. It does not refute averages normalized by the number of primes, or weighted prime ergodic theorems with different definitions.

## Formalization

Lean proves sqrt(2) is badly approximable with the displayed uniform rational-approximation constant, defines its actual rotation on UnitAddCircle, proves Haar measure preservation, and computes the iterates as the linear phase. It computes the genuine prime finset sum and Bochner integral. The elementary prime-counting bound uses Mathlib's sieve with modulus two. Real square-root and logarithm estimates then produce arbitrarily large natural counterexample indices for every nonnegative constant and starting point.

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
