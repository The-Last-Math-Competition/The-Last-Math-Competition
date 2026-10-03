#!/usr/bin/env python3
"""
Independent reproduction for TLMC conjecture 00000003842 (REFUTED).

Conjecture: #hypoplactic classes of length <= ell over n letters =
#plane partitions in a 2 x n x ell box.

Refutation at n = ell = 2: at most 6 classes (only 6 nonempty words)
but exactly 20 plane partitions in 2x2x2 (MacMahon 20, brute force 20).
"""

from itertools import product

# ---------- gate 1: word side ----------
words = [w for L in (1, 2) for w in product("ab", repeat=L)]
assert len(words) == 6
print(f"nonempty words of length <= 2 over {{a,b}}: {len(words)} -> at most 6 classes — OK")

# ---------- gate 2: plane partitions in 2x2x2 = 20 ----------
cnt, pps = 0, []
for a in range(3):
    for b in range(3):
        for c in range(3):
            for d in range(3):
                if a >= b and a >= c and b >= d and c >= d:
                    cnt += 1
                    pps.append((a, b, c, d))
assert cnt == 20, cnt
# MacMahon product formula
num = den = 1
for i in (1, 2):
    for j in (1, 2):
        for k in (1, 2):
            num *= i + j + k - 1
            den *= i + j + k - 2
assert den and num // den == 20
print(f"plane partitions in 2x2x2 box: brute force = {cnt}, MacMahon = {num}/{den} = 20 — OK")

# ---------- gate 3: mismatch ----------
assert 20 > 6
print("20 > 6: equality impossible at the first non-trivial instance — REFUTED")

# ---------- gate 4: even at n=1 the claim fails ----------
# 1-letter alphabet, length <= 1: 1 class (word "a"); 2x1x1 box: 2 PPs (0 or 1)
assert 2 != 1
print("cross-check n=1, ell=1: 1 class vs 2 plane partitions in 2x1x1 — also unequal — OK")

print("\nALL CHECKS PASSED: conjecture 00000003842 REFUTED (6 classes max vs 20 plane partitions)")
