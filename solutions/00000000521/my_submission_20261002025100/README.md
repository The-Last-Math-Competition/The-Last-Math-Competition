# Disproof of TLMC Conjecture 00000000521

**Verdict: FALSE.**

## The conjecture

For a monomial ideal `I` let `A_j = sum_i (-1)^i beta_{i,j}(I)` be the
alternating Betti sums. The conjecture claims that for every edge ideal the
sign of the sequence `{A_j}` changes **exactly once** as `j` crosses
`reg(I)`, and that `|A_j|` is monotonically nondecreasing up to that point;
this was proposed as a combinatorial characterization of the graded
Lefschetz property for edge ideals.

## The counterexample (confirmed queue attack, indices corrected)

Take the triangle graph `C3` and its edge ideal

    I = (xy, xz, yz)  in  k[x,y,z].

The minimal free resolution of `R/I` is

    0 -> R(-3)^2 -> R(-2)^3 -> R -> R/I -> 0,

i.e. the graded Betti numbers of the standard Betti table of `I` are

    beta_{0,0} = 1,   beta_{1,2} = 3,   beta_{2,3} = 2,

(the resolution is exact by the Hilbert-series check
`Hilb_{R/I}(t) = (1 - 3t^2 + 2t^3)/(1-t)^3 = 1 + 3t/(1-t)`, and the syzygy
module on the three Koszul syzygies `(z,-y,0), (z,0,-x), (0,y,-x)` is generated
by their single relation). Hence

    A_0 = 1,  A_1 = 0,  A_2 = -3,  A_3 = 2,  A_j = 0 for j >= 4,
    reg(I) = 2   (beta_{0,2}(I) = 3, beta_{1,3}(I) = 2).

The nonzero entries of `{A_j}` are `+, -, +`, so the sign changes **twice**,
not exactly once. Moreover `|A_0|, |A_2|, |A_3| = 1, 3, 2` is not
nondecreasing. The conjecture fails.

*Index correction.* The original queue entry listed the attack numbers as
`A_2 = 3, A_4 = -3, A_6 = 1`, which used wrong indices. The recomputation
confirms the corrected numbers `A_0 = 1, A_2 = -3, A_3 = 2` (as in the verify
verdict); the falsification conclusion is unchanged.

## Boundary (from `reproduce.py`, all Hilbert-series cross-checked)

* The failure is not special to `C3`. Under the standard reading
  (`beta_{i,j}` = the Betti table of `R/I`, as displayed by Macaulay2/Singular),
  **any** path of two adjacent edges already fails:
  `I = (xy, yz)` gives `A = (1, 0, -2, 1)` — two sign changes.
* A scan over all 63 labeled graphs on 4 vertices with at least one edge:
  **57 of 63** violate the "exactly one sign change" condition
  (e.g. `2K2`: `A = (1, 0, -2, 0, 1)`; `P4`: `A = (1, 0, -3, 2, 0)`;
  `C4`: `A = (1, 0, -4, 4, -1)` — three changes).
* The conjecture also fails under the alternative reading where
  `beta_{i,j}(I)` means the Betti numbers of the module `I`
  (`A_j(I) = beta_{0,j}(R/I) - A_j(R/I)`): for `C4`
  `A(I) = (0, 0, 4, -4, 1)` and for the star `K_{1,3}`
  `A(I) = (0, 0, 3, -3, 1)` — two sign changes each; for a single edge
  `A(I) = (0, 0, 1)` never changes sign at all.
  No reading of the convention rescues the conjecture.
* The only graphs consistent with reading 1 in the scan are those whose
  `R/I`-resolution has a single homological step beyond degree 0
  (single edge, and `P3`... not even that: see above) — in practice only
  ideals with `A` having at most one nonzero entry beyond `A_0`.

## Verification

* `reproduce.py` — self-contained (stdlib only) independent recomputation:
  builds the Taylor resolution of `R/I`, tensors it with `k = GF(1000000007)`,
  computes homology dimensions per bidegree to obtain `beta_{i,j}`, and
  cross-checks `A_j` against `(1-t)^n * Hilb_{R/I}(t)` obtained by direct
  monomial enumeration. Run: `python3 reproduce.py`.
* `lean4/` — Lean 4 (v4.33.1, no Mathlib) formalization of the numeric
  attack: the Betti table, the alternating sums, the two sign changes and the
  monotonicity failure are all proved by `decide`. Zero axioms, zero
  `sorry`:

      cd lean4 && lake build && lake env lean Check.lean

  every `#print axioms` reports "does not depend on any axioms".
* `build/main.pdf` — the write-up (`main.tex`, compiled with tectonic).
