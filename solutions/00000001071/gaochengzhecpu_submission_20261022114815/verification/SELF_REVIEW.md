# Adversarial self-review — 00000001071

Verdict: PASS

Developed by a delegated AI agent with a self-review; the coordinating agent reviews it separately.
Review mode: agent development with parent adversarial review; no external independent review.

1. **Source ambiguity is material and covered.** The name quadratic-residue graph
   suggests the standard Paley graph; the explicit difference-±1 reading suggests
   a cycle. The paper and Lean contain both actual graph families. The Paley
   argument is fully formalized, rather than being a paper-only bridge.
2. **The Paley object is genuine.** Vertices are `ZMod p`; primality supplies its
   field structure. Adjacency is quadratic character equal to one, formally
   equivalent to distinct vertices with `IsSquare` difference. The condition
   p = 1 (mod 4) proves χ(-1) = 1 and hence symmetry. The graph has no loops.
3. **No spectrum was inserted as an assumption.** The character's inverse and
   Jacobi-sum theorem establish the basic correlation. An explicit affine
   bijection gives off-diagonal sums -1; the diagonal sum is p - 1. These yield
   Q² = p I - J for the actual quadratic-character matrix.
4. **The matrix bridge is discharged for the actual graph.** Q = 2 A + I - J
   and column sums (p - 1)/2 are proved from the entrywise definition and the
   zero character sum. The generic conference-matrix spectral lemma is applied
   to these proved identities, not treated as a replacement conjecture.
5. **The eigenvalue is real and attached to its graph.** Both minima are taken
   over Mathlib's complete Hermitian adjacency eigenvalue list. The orthonormal
   eigenvector basis supplies a nonzero eigenvector for the minimizing entry.
   The lower-bound proofs apply to every real eigenvalue, so no occurrence or
   multiplicity assertion about a proposed explicit spectrum is required.
6. **The asymptotic assertion is actually contradicted.** For every real B and
   every cutoff N, there is an admissible prime beyond N with discrepancy > B.
   Paley uses arbitrarily large primes 1 (mod 4), not one isolated example. The
   final claim allows arbitrary nonnegative constants C and arbitrary N and is
   negated at epsilon = 1/8, strictly between zero and 1/4.
7. **Quantifier and coercion audit.** The Paley claim quantifies over the subtype
   of primes 1 (mod 4); the cycle claim quantifies over all prime orders at least
   three via n + 3. The displayed p in each discrepancy is the actual vertex
   count. Finite initial exceptions therefore cannot repair the estimate.
8. **Paper proof checked independently by hand.** Summing Ax = lambda x gives
   (k - lambda) sum(x) = 0. When lambda != k, Jx = 0 and Qx = (2 lambda + 1)x;
   Q²x = p x forces (2 lambda + 1)² = p. This gives the stated lower bound with
   the correct factor 1/2. The resulting discrepancy is (3 sqrt(p) - 1)/2,
   not (sqrt(p) - 1)/2. The cycle maximum-coordinate argument gives |lambda| <= 2.
9. **Claim boundary is honest.** Failure of the spectral error clause disproves
   the source's conjunction. No separate result about uniform spectral gaps or
   an unspecified alternative graph or normalization is claimed. All bridges
   needed for the two graph interpretations are formalized.
10. **Trusted-proof audit.** Author strict compilation and printed axiom reports
    pass with only propext, Classical.choice and Quot.sound. There are no sorry,
    admit, native_decide, custom axioms or opaque declarations. Parent fresh
    validation, adversarial review and PDF inspection are separate pending steps
    when this self-review is first written.


Reviewed artifact hashes:

- Main.lean: `0e1f23ca09ca6d4dcf9b0a97b2134cdd92772dea79260c04ded3e22ce45de43b`
- main.tex: `9ae1d40d5836209f4144e281645957fbcafdba503ac728389dac07f36ba1f194`
- main.pdf: `0fb1fe581cac8dc1f9a86eeb3a9c77563edeb35e1836ef6fa82119e9f5ba5f24`
- SOURCE.md: `f4496985aea07c458f67cae6a3bf9dbb3baeccd918c6915fc3c59b4817fc0fb3`
