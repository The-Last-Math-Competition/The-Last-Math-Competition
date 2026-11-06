# Disproof of 00000001491 for its explicit printed map

Both original languages print H_ab(x,y)=(1-a*x^2+y,b), with constant second coordinate b. This differs from the usual Henon map whose second coordinate is b*x. The proof concerns the printed map only; it does not assert a dimension result for the usual map or independently settle the box-dimension or Kaplan-Yorke clauses.

Lean works on the actual Euclidean plane, proves the printed polynomial map is continuous, and proves every positive iterate lies in the closed horizontal line y=b. The actual Mathlib forward omegaLimit of every actual initial set, and the closure of the union of all actual singleton omegaLimits, lie in that line. An actual real-line isometry proves the line has true Hausdorff dimension one. Any actual compact fully invariant set H''A=A also has dimension at most one; merely forward-invariant trapping regions are not substituted for attractors.

All real parameters are covered, then a=7/5 and b=3/10 are instantiated. True extended Hausdorff dimensions are bounded by one and shown finite before the real toReal bounds, so the required real lower bound 1.26=63/50 is impossible for these actual dynamical limiting sets or a fully invariant compact attractor. No general Milnor-attractor classification, actual usual-Henon dimension computation, or infinite-dimension conversion default is used.

The original bilingual source is included. The distinction from the usual map is checked against the original abstract of M. Henon, Communications in Mathematical Physics50(1976),69-77, DOI10.1007/BF01608556, available on the official Springer article page. No claim to have read an unavailable complete PDF is made.

## Reproduce

From lean/ with elan installed:

```sh
lake exe cache get
bash verify.sh
```

Lean4.33.0 and Mathlib db584cd6d46c92f209a44c0f1c829460d327499d are pinned. A new root build, all21 theorem transitive axiom audits and full official leanchecker --fresh Main replay are required. Complete LaTeX/PDF, source-bound logs/receipts and SHA256 manifest accompany the proof. No sorry, native_decide or additional axiom. Worker and separate supervising AI agent review source/report/PDF; organizer acceptance is pending.
