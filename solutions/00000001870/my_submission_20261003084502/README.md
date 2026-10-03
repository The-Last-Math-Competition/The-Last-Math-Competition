# Disproof of conjecture `00000001870`

**Verdict: FALSE — the third cumulant of Tr U under Haar measure on
U(N) is EXACTLY 0 for every N (Haar invariance under U → i·U rotates
the trace by i, forcing every odd moment to vanish), so it does not
decay like c₃/N with c₃ = 2πi/3 (a nonzero imaginary constant, |c₃| =
2π/3 ≈ 2.094).  The "decay exponent 1" claim concerns a cumulant that
is identically zero.**

## The conjecture (verbatim from `conjectures/00000001870.md`)

> Definition: The CLT for the trace distribution of random unitary
> matrices (known).  Conjecture: The third cumulant decays as
> N⁻¹·c₃ with c₃ = (2πi)/3 (from the series expansion of the
> cumulant-generating function); the decay exponent 1 is exact.

## The refutation

Haar invariance under multiplication by i (U → iU is measure-
preserving) maps Tr U to i·Tr U, so the third moment
m = E[(Tr U)³] satisfies m = E[(i·Tr U)³] = −i·m.  Working in the
Gaussian integers ℤ[i] (pairs (a, b) = a + bi), the rotated moment is
(b, −a) (multiplication by −i), and invariance (b, −a) = (a, b) forces
b = a and −a = b, whence a = −a, so a = 0 and b = 0: **m = 0
exactly** (kernel-certified: the torsion-freeness of ℤ[i] collapses
the invariance equation).  The mean is 0 by the same invariance, so
the third cumulant equals the third moment: kappa₃ = 0 for every N.

Since c₃ = 2πi/3 is nonzero-imaginary (2π/3 > 0), kappa₃ = 0 cannot
equal c₃/N at any N: the conjectured decay law and its "exact exponent
1" concern a cumulant that is identically zero.

## Verification

* `reproduce.py` — Monte Carlo Haar samples via QR of complex Ginibre
  matrices (60000 trials each at N = 2, 3): E[(Tr U)³] vanishes within
  noise (|E| < 0.02), E[|Tr U|²] = 1 (the known CLT normalization ✓),
  E[Tr] = 0; the claimed kappa₃ ≈ 1.047i (N = 2), 0.698i (N = 3) are
  more than 10× the observed magnitudes.
* Lean 4 (core, v4.33.1), `lean4/` — the rotation map negI (×(−i)) in
  ℤ[i], its order-4 property, the collapse `rot_inv_collapse`
  (invariance m = negI m forces m = (0,0), via `eq_neg_self` by
  Int.noConfusion — no omega/Int-lemma taint), the non-identity check
  of the rotation, and the nonzero-imaginary comparison of the claimed
  constant.  All 5 audited theorems report `does not depend on any
  axioms`.

## Boundary

The kernel certifies the rotational-symmetry collapse (the
mathematical core) universally over the ℤ[i]-valued moment; the Haar
invariance of U → iU and the classical CLT normalization
E[|Tr U|²] = 1 are cited in prose and re-verified by the Monte Carlo
script.
