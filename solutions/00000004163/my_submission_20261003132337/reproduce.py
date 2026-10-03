#!/usr/bin/env python3
"""
Independent reproduction for TLMC conjecture 00000004163 (REFUTED).

Conjecture: for seven cubic powers of primes the local obstruction
classes mod 9 are exactly three non-representable classes; adding
one variable removes all obstructions.

Refutation: prime cubes mod 9 ∈ {0, 1, 8}; SEVEN-term sums already
cover ALL NINE classes (no obstruction at all); and the genuine
obstruction belongs to THREE variables, which miss exactly TWO
classes {4, 5}, not three.
"""

from itertools import product

primes = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43]
cubes = sorted({p ** 3 % 9 for p in primes})
assert cubes == [0, 1, 8], cubes
print(f"prime cubes mod 9: {cubes} (3^3 = 0; p not div by 3: p^3 = ±1)")

# ---------- gate 1: seven variables cover all 9 classes ----------
reps7 = {sum(c) % 9 for c in product(cubes, repeat=7)}
assert reps7 == set(range(9)), sorted(reps7)
print("7-term sums cover all 9 residue classes — ZERO obstruction classes (claimed: 3) — REFUTED")

# ---------- gate 2: the true obstruction table ----------
for s in (3, 4, 5, 6, 7):
    reps = {sum(c) % 9 for c in product(cubes, repeat=s)}
    missing = sorted(set(range(9)) - reps)
    print(f"{s}-term sums: missing classes = {missing}")
assert sorted(set(range(9)) - {sum(c) % 9 for c in product(cubes, repeat=3)}) == [4, 5]
assert sorted(set(range(9)) - {sum(c) % 9 for c in product(cubes, repeat=4)}) == []
print("genuine obstruction: 3 variables miss exactly {4, 5} (TWO classes); 4 variables already suffice — OK")

print("\nALL CHECKS PASSED: conjecture 00000004163 REFUTED "
      "(7 variables: no obstruction; 3 variables: exactly 2 missing classes)")
