# Lean 4 verification for the disproof of TLMC conjecture 00000000521

Pure Lean 4 core (v4.33.1), no Mathlib.

Contents of `Main.lean`:

* `beta i j` — the graded Betti numbers of `R/(xy,xz,yz)` over `k[x,y,z]`
  (Betti table of the ideal): `β_{0,0} = 1`, `β_{1,2} = 3`, `β_{2,3} = 2`,
  i.e. the minimal resolution `0 → R(−3)² → R(−2)³ → R → R/I → 0`;
* `A j` — the alternating Betti sums: `A_0 = 1, A_1 = 0, A_2 = −3, A_3 = 2`;
* `conjecture_00000000521_false` — the sign of `{A_j}` changes **twice**
  (`+ → − → +`), while the conjecture demands exactly one change;
* `abs_not_monotone` — `|A_j|` is not nondecreasing.

Build and audit:

    lake build
    lake env lean Check.lean

`Check.lean` prints `#print axioms` for every theorem; each reports
**"does not depend on any axioms"**. No `sorry`, no `native_decide`,
no additional axioms — all proofs are `decide`/`rfl` on closed integer data.

The numeric inputs are independently recomputed by `../reproduce.py`
(Taylor resolution tensored with k, cross-checked against the Hilbert
series (1 − 3t² + 2t³)/(1−t)³).
