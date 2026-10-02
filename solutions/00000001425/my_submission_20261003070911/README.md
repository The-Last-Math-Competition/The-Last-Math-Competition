# Disproof of conjecture `00000001425`

**Verdict: FALSE — under every reading of the parameter n the claim
fails for the complete binary tree: (i) n = depth d: the measured
relaxation time is t_rel = 4·2^d − 6d + O(1) — exponential in d
(kernel-certified 2^d > 4d for all d ≥ 5), not the linear 4d + o(d);
(ii) n = vertices N: the measured leading coefficient is 2 (t_rel/N →
2), not 4, and the measured second-term coefficient is −6, not −2.**

## The conjecture (verbatim from `conjectures/00000001425.md`)

> Definition: The relaxation time t_rel. Conjecture: For random walks
> on the binary tree, t_rel = (1+o(1))·4n with second term −2 log n
> (the relaxation second term).

## The refutation

The random walk on the complete binary tree of depth d (similarity-
symmetrized adjacency, eigenvalues of the N×N matrix) has second
eigenvalue giving

    t_rel = 4·2^d − 6d + O(1):

measured 984.6 (d = 8), 4045.1 (d = 10), 16321.4 (d = 12), against the
formula 4·2^d − 6d = 976, 4036, 16312; a least-squares fit of the
second-order term gives −5.8 ≈ −6.

* **n = depth**: the conjectured law is 4d + o(d) — linear. The
  kernel-certified separation 2^d > 4d for ALL d ≥ 5 (induction: the
  step doubles 2^d while 4(d+1) ≤ 8d = 2·(4d)) shows the growth is
  exponential: 4·2^d + o(d) ≠ 4d + o(d). At d = 12: 4d = 48 against
  the measured 16321.4, which sits just under the exponential law
  4·2^12 = 16384.
* **n = vertices**: N = 2^{d+1} − 1, so t_rel/N → 2 (not 4) and the
  second term is −6d = −6·log₂(N+1) + O(1) (coefficient −6, not −2).

Both readings fail; the conjectured "4n with second term −2 log n"
holds for neither.

## Verification

* `reproduce.py` — independent NumPy computation of the
  similarity-symmetrized walk matrix eigenvalues at d = 8, 10, 12
  (matching 984.6 / 4045.1 / 16321.4), the least-squares second-term
  coefficient (−5.8 ≈ −6), the kernel-side separation 2^d > 4d for
  d ≤ 39, and the n = vertices reading t_rel/N → 2.
* Lean 4 (core, v4.33.1), `lean4/` — the exponential-vs-linear
  separation 2^d > 4d for all d ≥ 5 (induction with a definitional
  doubling step; associativity helpers rebuilt since core's
  Nat.mul_assoc carries axioms), the instance anchors 4·12 = 48,
  2^12 = 4096, 4·2^12 = 16384, 48 < 16321 < 16384, and 6 ≠ 2. All 5
  audited theorems report `does not depend on any axioms`.

## Boundary

The kernel certifies the exponential-vs-linear separation and the
instance anchors. The spectral measurements (t_rel values and the
−6 second-term coefficient) are numerical, carried by the script's
independent eigenvalue computation; the walk-model conventions match
the standard complete-binary-tree random walk. The conjecture fails
under both readings of n.
