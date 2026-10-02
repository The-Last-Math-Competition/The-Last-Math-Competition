# Disproof of conjecture `00000003730`

**Verdict: FALSE (maximum clause) — on 5 vertices, K₅ has energy 8,
exceeding every complete bipartite graph's energy (K₂,₃: 2√6 < 8): the
maximum of graph energy is NOT attained by complete bipartite graphs.**

## The conjecture (verbatim from `conjectures/00000003730.md`)

> Definition: Spectral minimization: graph spectral energy functionals.
> Conjecture: The extremum of graph spectral energy: energy is the sum
> of absolute eigenvalues, with the maximum complete bipartite graphs
> and the minimal trees paths.

## The counterexample (5 vertices)

1. **Energy of K₅ = 8.** A(K₅) = J − I has spectrum {4, −1, −1, −1, −1}
   (classical): the all-ones vector is an eigenvector with eigenvalue 4
   (each row sums to 4), and every coordinate-sum-zero vector is an
   eigenvector with eigenvalue −1 (Jv = (Σvᵢ)·1 = 0, so (J−I)v = −v).
   Energy = 4 + 4·1 = **8**.
2. **Energy of the best complete bipartite graph on 5 vertices.**
   K_{m,n} (m + n = 5) has spectrum {√(mn), −√(mn), 0ᵐ⁺ⁿ⁻²} (classical),
   so its energy is 2√(mn) ≤ 2√6 (maximized at {m, n} = {2, 3}):
   **2√6 ≈ 4.90 < 8**.
3. **8 > 2√6** (squared: 64 > 24, kernel-certified).

So K₅ — not complete bipartite — has strictly higher energy than every
complete bipartite graph on the same number of vertices: the displayed
maximum clause is false. (The minimum clause "minimal trees are paths"
is the classical path-minimizes-energy-among-trees fact and is not
disputed.)

## Verification

* `reproduce.py` — numpy eigenvalue computation for K₅ (energy 8), all
  complete bipartite graphs on 5 vertices (max energy 2√6 ≈ 4.899), and
  a scan over ALL 1024 graphs on 5 vertices showing the maximum energy
  is attained by K₅ itself (8), not by any bipartite graph.
* Lean 4 (core, v4.33.1) — `lean4/`: the eigenvalue identifications'
  numeric consequences (energy 4 + 4 = 8; the squared comparison
  64 > 24); all audited theorems report `does not depend on any
  axioms`. The spectra of K₅ and K_{m,n} are classical and cited.

## Boundary

Only the maximum clause is refuted (at n = 5); the minimum clause for
trees is classical and not disputed.
