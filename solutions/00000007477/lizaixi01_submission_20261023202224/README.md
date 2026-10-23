# Problem 00000007477

A counterexample under the source's unrestricted bounded-positive-operator reading: the half-line adjacency operator on the genuine real Banach lattice c0(N) is ideal irreducible, has complexified spectral radius 2, and has no nonzero eigenvector at 2.

The standard meaning of ideal irreducibility is used: every closed solid invariant linear subspace is zero or whole. The source does not state a finite-dimensional or compactness condition. No finite-dimensional Perron–Frobenius or compact-operator theorem is refuted. The complete original bilingual source appears in SOURCE.md.

## Complete proof

- The actual complete normed sequence space and its pointwise lattice are constructed. The norm is solid; addition and nonnegative scalar multiplication respect the order.
- The actual continuous linear operator has coordinates (Ax)0=x1 and (Ax)(n+1)=xn+x(n+2), is positive, and has norm at most 2.
- Every nonzero closed solid invariant real submodule contains a coordinate vector. Adjacent-coordinate propagation gives all coordinate vectors, and actual finite truncations converge in sup norm to every sequence, proving irreducibility.
- The actual complex sequence-space extension preserves the real inclusion, scalar operations and norm; every complex vector has a real/imaginary decomposition.
- 2I−A has no e0 preimage. Taking real parts excludes a complex preimage too. This proves genuine complex spectrum membership, and the norm bound yields spectral radius exactly 2.
- The eigenvector recurrence forces x(n)=(n+1)x0, so convergence to zero forces x=0. The final theorem uses the actual spectralRadius of the complex extension.

report.tex/report.pdf contain the mathematical argument. lean/Main.lean contains the full proof. All 66 declarations (42 theorems, 16 definitions, 2 abbreviations, 6 instances) are audited by lean/Check.lean. There are no extra axioms, sorry, or native_decide.

## Reproduction

Lean 4.33.0 and Mathlib db584cd6d46c92f209a44c0f1c829460d327499d are pinned, together with dependency revisions. From lean/:

    ./verify.sh

The four gates are lean --version, lake build +Main, lake env lean -DwarningAsError=true Check.lean, and lake env leanchecker --fresh Main. See VERIFICATION.md and evidence/ for exact source-bound commands, exits, log hashes, all declared axiom dependencies and actual execution records. This is the official fresh kernel replay, not an independent kernel implementation.

Primary convention reference: Gao–Troitsky, https://arxiv.org/pdf/1208.3498, Introduction pp. 1–2. It defines ideal irreducibility by closed invariant order ideals. The proof does not rely on the paper for the example. No earlier same-ID PR was found at initial qualification; final eligibility is refreshed before submission. Organizer acceptance is pending. This production work is not a controlled efficiency experiment.

