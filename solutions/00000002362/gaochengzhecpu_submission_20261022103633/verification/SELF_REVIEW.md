# Author-agent adversarial self-review: 00000002362

Verdict: PASS

# Conjecture 2362: a fixed-angle obstruction to a universal calculus bound

Status: formally complete, awaiting parent semantic review and publication decision. No PR, TeX or PDF created by this agent.

## Exact source and mathematical claim

Source: `round5/source/00000002362.md`. The conjecture asserts that the bound constant of the sectorial H-infinity calculus is an explicit function of the sector angle, with a singularity as that angle tends to pi.

The result disproves a finite bound depending **only** on the angle. Both the operator class angle pi/3 and the calculus domain angle pi/2 are fixed. No limiting-angle argument is needed. The first assertion already fails, so the appended assertion about the proposed function cannot rescue the conjecture.

This does not deny estimates involving an operator's resolvent constants, similarity constant or additional hypotheses. The operators below have changing resolvent constants. No numerical-range angle is substituted for the genuine spectral/resolvent sectorial angle.

## Actual construction and proof

On the fixed complex Hilbert space C^2 with its Euclidean norm, let

- E = [[0,1],[0,0]], so E^2=0 and its Euclidean operator norm is exactly 1;
- A_N = I + N E for real N>=0;
- g(z)=z/(1+z)^3.

The elementary identities, including all inverses, are proved in Lean over actual complex matrices, and transferred by Mathlib's star algebra equivalence `Matrix.toEuclideanCLM` to actual bounded complex-linear operators on `EuclideanSpace C (Fin 2)`.

### Genuine sectoriality

The formal predicate uses the standard definition: spectral containment in the closed sector, and for every larger angle theta<pi a finite bound on ||z(z-A)^(-1)|| outside the closed theta-sector. It is generic over complex normed algebras; no finite-matrix proxy spectrum is introduced.

For z!=1, the genuine Mathlib resolvent is

(z-A_N)^(-1) = (z-1)^(-1) I + N (z-1)^(-2) E.

Hence sigma(A_N) is contained in {1}. For any 0<theta<pi put delta=min(1,1-cos(theta))>0. Outside the theta-sector, elementary geometry gives |z-1|>=delta. Indeed, Re z<=|z|cos(theta), and |z-1|^2=|z|^2+1-2 Re z. If cos(theta)>=0, completing a square gives |z-1|>=1-cos(theta); if cos(theta)<0, |z-1|>=1.

Using |z|<=|z-1|+1 gives the explicit uniform-in-z bound

||z(z-A_N)^(-1)|| <= (1+1/delta)(1+N/delta).

Therefore every A_N is sectorial of angle 0, and also belongs to the same class Sect(pi/3). The least sectorial angle is not asserted to be pi/3; the stronger angle-0 membership is what is proved. Norm, spectrum, units and resolvent are all explicitly transferred to the genuine bounded-operator algebra.

### An actual H0-infinity rational test on a fixed domain

The open sector Sigma_(pi/2) is proved equal to the open right half-plane, with zero excluded. The scalar function g is genuinely complex differentiable there. On the closed right half-plane, |1+z|>=1 and |1+z|>=|z|, so

|g(z)| <= |z|/(1+|z|^2) <= 1.

Lean additionally proves the conventional two-sided H0-infinity decay form

|g(z)| <= 2 |z|/(1+|z|)^2.

Thus g is an admissible bounded holomorphic rational test and belongs to the usual decaying elementary sectorial calculus class. This avoids relying on whether a particular author's H-infinity construction initially includes constants or the Cayley transform.

### Actual rational calculus, not a replacement definition of H-infinity calculus

The denominator is genuinely invertible:

(I+A_N)^(-1) = I/2 - N E/4.

Consequently the ordinary rational functional calculus evaluates g as

g(A_N) = A_N (I+A_N)^(-3) = I/8 - N E/16.

The Lean matrix expression uses the actual nonsingular matrix inverse, and its operator counterpart uses `Ring.inverse`, with invertibility proved and the two expressions identified under the star algebra equivalence. It follows from the triangle inequality that

||g(A_N)|| >= N/16 - 1/8.

For any proposed real constant C, take N=16(max(C,0)+1). Then ||g(A_N)||>C although |g(z)|<=1 throughout the same domain Sigma_(pi/2). Therefore no finite uniform rational-test bound exists for all operators in Sect(pi/3), even on the fixed Hilbert space C^2.

Any genuine bounded H-infinity calculus extends its ordinary rational calculus and satisfies ||f(A)||<=K||f||_infinity. Its bound K must therefore dominate ||g(A_N)||. A universal K determined only by these fixed angles is impossible.

The formal theorem intentionally refutes this **necessary rational-test consequence**. It does not define a substitute H-infinity calculus and does not claim to formalize construction of the whole contour-integral calculus. The rational consistency and definition of the calculus bound are the standard mathematical bridge, spelled out here. For these finite Jordan matrices the usual full holomorphic calculus is explicitly f(A_N)=f(1)I+N f'(1)E, and Cauchy's estimate on the radius-1/2 circle around 1 also shows an individual finite bound 1+2N; the obstruction is uniformity across N.

## Main formal statements

File: `round5/drafts/00000002362/lean/Main.lean`.

- `E_norm`: actual Euclidean matrix operator norm is one.
- `resolvent_formula`, `spectrum_subset`: genuine Mathlib spectrum and resolvent identities.
- `jordan_sectorial_zero`: complete all-larger-sectors resolvent definition.
- `g_holomorphic`, `g_decay`, `g_standard_decay`, `g_bounded`, `g_is_H0_infty_test`: actual scalar holomorphy and uniform/decay inequalities.
- `plus_isUnit`, `rationalValue_formula`, `rationalValue_lower`: genuine inverse, rational identity and growing norm.
- `Phi_norm`, `Phi_resolvent`, `Phi_sectorial`, `Phi_rationalValue`, `Phi_plus_isUnit` (the source spells Phi with the Greek capital letter): actual B(C^2) bridges.
- `fixed_positive_angle_counterexample`: for every C there is an actual bounded operator sectorial of angle pi/3 with the rational value norm>C.
- `no_fixed_positive_angle_bound`: there is no constant bounding this test throughout that fixed sectorial class.

## Adversarial author review

1. Matrix norm: `open scoped Matrix.L2OpNorm` is active. Norm equality with actual Euclidean continuous-linear-map norm is proved by `Matrix.cstar_norm_def`. No entrywise or Frobenius norm is used.
2. Operator angle versus numerical range: sectoriality is proved from the true spectrum and resolvent for every larger angle. The argument makes no numerical-range assumption. Numerical ranges may grow with N.
3. Class angle versus minimum angle: all matrices have angle-0 sectorial membership, then monotonicity puts them in Sect(pi/3). The report does not call pi/3 their least angle.
4. Correct domain ordering: the fixed calculus half-angle pi/2 is strictly larger than the class half-angle pi/3. Both are fixed, so even a proposed function of both angles would fail without further operator data.
5. Actual admissible function: g is holomorphic and bounded on the full open right half-plane, has its pole only at -1, and decays at both zero and infinity. No non-admissible boundary function is used.
6. Denominator: I+A_N is proved a unit. No totalized inverse at a singular matrix is used to obtain the claimed rational value.
7. Rational consistency: the proved object is the ordinary rational expression A(I+A)^(-3), exactly the rational functional calculus for g. The report explicitly uses its standard consistency with H-infinity calculus and does not relabel a proxy calculus as the full object.
8. Uniformity: each N has its own legitimate finite resolvent bound. Only an angle-only bound uniform over the fixed class is refuted. The proof does not mistakenly infer a universal bound from pointwise sectoriality.
9. Quantifiers: the construction works for any proposed real C, including negative C. N=16(max C 0+1) is nonnegative and the lower bound exceeds C with a strict margin. No floating-point evidence is used.
10. Scope: the claimed divergence as angle tends to pi is not separately analyzed because the prior assertion of an angle-only bound already fails at fixed angles. Estimates containing additional resolvent/geometry data remain outside this refutation.
11. Infinite-dimensional escape: no such issue arises; C^2 is a valid fixed complex Hilbert space and its genuine bounded-operator algebra is explicitly used in the final theorem.
12. Trust: all final printed axiom dependencies are only propext, Classical.choice and Quot.sound. There are no sorry/admit/native_decide/custom axioms; no numerical computation is trusted by Lean.

## Verified primary reference

Charles Batty, Markus Haase and Junaid Mubeen, *The Holomorphic Functional Calculus Approach to Operator Semigroups*, author PDF dated September 20, 2012:
https://fa.ewi.tudelft.nl/~haase/files/bahamu20-09-2012.pdf

Actually opened and read. Section 2.1 (PDF page 7) gives the sectorial definition using true spectral containment and all larger sector resolvent constants. Proposition 2.8 records compatibility with the sectorial calculus. Section 5, equation (5.1) (PDF page 11), specifies the operator-norm versus scalar sup-norm bound. Example 7.4 (PDF page 20) explicitly uses rational function tests. These references support standard definitions/consistency, while the counterexample's identities and bounds are proved directly.

## Reproducibility

See `round14/quantum/2362-status.json`, `2362-strict.log`, `2362-lake-build.log` for actual complete commands, exit codes, timings, and final Main SHA256. Lean version 4.19.0; Mathlib commit c44e0c8ee63ca166450922a373c7409c5d26b00b. Full default Lake target is Main with warningAsError enabled in lakefile.toml. No auxiliary computation is required: all matrix, scalar, spectrum, operator and growth claims above are checked by the Lean kernel.

Final frozen Main SHA256: `fce8c54edd9bb93ca9f1f27eb6f47b790ad771838b09b766b36068abaca92b1d`. Strict pass: 18.437 seconds. Full Lake build pass: 19.266 seconds.


Reviewed artifact hashes:

- Main.lean: `fce8c54edd9bb93ca9f1f27eb6f47b790ad771838b09b766b36068abaca92b1d`
- main.tex: `a2c2ec70c35dbdebee456b703bdd49fd82c9f92dca154df91e5adc992a20487b`
- main.pdf: `179a6f31a58b4d0d604d9685b838bb4e7397338600c5bd757e55c313087d07ae`
- SOURCE.md: `8553ea0727bb80969fb77cd741be8834ec6d58d03efd0ba70d20b49b6f24f5a0`
