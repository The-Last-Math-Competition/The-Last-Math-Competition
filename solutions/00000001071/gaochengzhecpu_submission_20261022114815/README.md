# Conjecture 00000001071 — Disproof

The standard Paley graph at prime order p = 1 (mod 4) has smallest adjacency
eigenvalue at least -(1 + sqrt(p))/2. Its discrepancy from -2 sqrt(p) is
therefore at least (3 sqrt(p) - 1)/2 and is unbounded on those primes.
The source's literal difference-±1 reading gives the cycle graph, with
discrepancy at least 2 sqrt(p) - 2. Both readings contradict the claimed
error even with an arbitrary Big-O constant and an arbitrary starting point.

## Files and reproduction

- `SOURCE.md`: unchanged bilingual upstream source.
- `lean/Main.lean`: all formal mathematics in one file; Lean 4.19.0 and pinned Mathlib.
- `main.tex`: complete proof covering both graph interpretations.
- `author-strict.log`: successful author warning-as-error build and axiom output.
- `verification/SELF_REVIEW.md`: numbered adversarial self-review.
- `verification/SOURCE_PROVENANCE.md`: source commit and digest.

Run `lake env lean -DwarningAsError=true Main.lean` from `lean/`.
The coordinating agent performs a separate fresh validation and PDF review.

## Exact formal scope

`Conjecture1071.Paley.graph` is an actual Mathlib simple graph over the finite
field, with adjacency proved equivalent to a nonzero square difference.
The adjacency matrix is `SimpleGraph.adjMatrix`. The proof derives the
character correlation and Q² = p I - J from Mathlib's quadratic character
and Jacobi sum, proves the graph's column sums, and derives the lower bound
for every actual real eigenvalue. The smallest value is the minimum of the
complete Hermitian eigenvalue list and has a nonzero eigenvector.

`Conjecture1071.Paley.prime_deviation_unbounded` quantifies over every real
bound and every natural cutoff. `Conjecture1071.Paley.not_spectralClaim`
negates the universally quantified estimate over all admissible primes.
Its epsilon witness is 1/8. The parallel cycle results use Mathlib's
`cycleGraph`, not a substituted matrix with the desired numbers.

Both principal graph readings are formalized. The paper does not assume an
exact Paley spectrum, claim a new eigenvalue formula, or resolve the source's
separate spectral-gap clause. No prior submission on this conjecture was
identified by the coordinating agent's complete upstream history check.

Review mode: agent development with parent adversarial review; no external independent review.
Developed by a delegated AI agent with a self-review; the coordinating agent reviews it separately.
