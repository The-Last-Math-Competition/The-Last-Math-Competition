# Disproof of Conjecture 00000007986

**Verdict: FALSE**

## Conjecture (under test)

The main inequality of conjecture 00000007986 asserts:

> rho(C) <= n - sqrt(n * d) for codes with nontrivial 2-transitive automorphism group.

## Summary of the disproof

Both the primary and the secondary counterexample satisfy every hypothesis of the
conjecture (nontrivial 2-transitive automorphism group), yet violate the inequality.

### Primary counterexample: binary repetition code C4 = {0000, 1111} in F_2^4

- Length n = 4, minimum distance d = 4.
- Automorphism group: the coordinate-permutation group S_4 acts on F_2^4, preserves
  Hamming distance, and maps the code set {0000, 1111} to itself (all 24 permutations
  stabilize the set). It is nontrivial and 2-transitive on {1,2,3,4}.
- Covering radius by exhaustive enumeration over all 16 vectors of F_2^4:
  rho(C4) = max_x min(d(x, 0000), d(x, 1111)) = 2
  (e.g. weight-2 vectors such as 0011 are at distance 2 from both codewords; every
  x has min-distance <= 2 by the pigeonhole principle on bit counts).
- Right-hand side: 4 - sqrt(4 * 4) = 4 - 4 = 0.
- Claimed inequality: 2 <= 0 — FALSE.

### Secondary counterexample: binary repetition code C2 = {00, 11} in F_2^2

- Length n = 2, minimum distance d = 2; automorphism group S_2, nontrivial and
  2-transitive.
- rho(C2) = 1 (exhaustive enumeration over all 4 vectors of F_2^2).
- Right-hand side: 2 - sqrt(2 * 2) = 2 - 2 = 0.
- Claimed inequality: 1 <= 0 — FALSE.

### Counterexample tables

C4 = {0000, 1111} subset F_2^4, n = 4, d = 4:

| x (weight) | d(x, 0000) | d(x, 1111) | min |
|---|---|---|---|
| 0000 (0) | 0 | 4 | 0 |
| 0001, 0010, 0100, 1000 (1) | 1 | 3 | 1 |
| 0011, 0101, 0110, 1001, 1010, 1100 (2) | 2 | 2 | 2 |
| 0111, 1011, 1101, 1110 (3) | 3 | 1 | 1 |
| 1111 (4) | 4 | 0 | 0 |

max of min column = **2**; RHS = 4 - sqrt(16) = **0**; 2 <= 0 fails.

C2 = {00, 11} subset F_2^2, n = 2, d = 2:

| x (weight) | d(x, 00) | d(x, 11) | min |
|---|---|---|---|
| 00 (0) | 0 | 2 | 0 |
| 01, 10 (1) | 1 | 1 | 1 |
| 11 (2) | 2 | 0 | 0 |

max of min column = **1**; RHS = 2 - sqrt(4) = **0**; 1 <= 0 fails.

## Scope / boundary of the disproof

We refute the *literal statement of the main inequality* rho(C) <= n - sqrt(n d)
under its own hypothesis (nontrivial 2-transitive automorphism group of the code).
The ancillary clauses of the conjecture (equality for Reed-Solomon type affine group
codes; orbit-rank correspondence; transitivity criterion for design strength) are
**not** the target of this disproof.

Note that in both counterexamples the gap is extreme: the RHS is 0 while the true
covering radius is n/2, so no rounding or interpretation of sqrt rescues the
inequality.

## Contents

- `reproduce.py` — standalone script: exhaustive enumeration verifying
  rho(C4) = 2, rho(C2) = 1, RHS values 0 and 0; asserts the counterexamples.
- `main.tex`, `build/main.pdf`, `build/log.txt` — formal write-up with the full
  16-point enumeration table.
- `lean4/` — Lean 4 (v4.33.1, core only) machine-checked verification, zero
  axioms, no `sorry`: the covering radii are evaluated by the kernel
  (`rho_C4 : coverRad4 = 2`, `rho_C2 : coverRad2 = 1`) and the numeric
  refutations are proved by `decide`
  (`refute_bound_4 : ¬ ((2:Int) ≤ (4:Int) - 4)`,
  `refute_bound_2 : ¬ ((1:Int) ≤ (2:Int) - 2)`; the bound values are exact
  integers since `n*d` is a perfect square). `Check.lean` prints
  `#print axioms` for every theorem.

## Reproducing

```bash
python3 reproduce.py
cd lean4 && lake build && lake env lean Check.lean
tectonic main.tex --outdir build   # or: tectonic -X compile main.tex --outdir build
```
