#!/usr/bin/env python3
"""
Independent reproduction for TLMC conjecture 00000002692 (REFUTED).

Conjecture: the measure of the attracting basin of a p-adic
contraction is an explicit fraction of the ball volume; the
denominator of the fraction is the order of the multiplier mod p;
the boundary of the basin is the closure of periodic points.

Refutation at f(x) = 5x + x^2 on Z_5: the multiplier mod p is 0
(no order exists); the basin is exactly 5Z_5, measure 1/5
(denominator p, not an order); and the basin-boundary shell
5Z_5 \\ 25Z_5 maps straight to 0, so it is not made of periodic
points -- the boundary is not the closure of periodic points.
"""

q_max = 625

def f(x, q):
    return (5 * x + x * x) % q

# ---------- gate 1: the multiplier has no order mod p ----------
mult = 5 % 5
assert mult == 0
assert all(pow(0, k, 5) != 1 for k in range(1, 100))
print("multiplier f'(0) = 5 ≡ 0 (mod 5); 0^k mod 5 never 1 — no order — OK")

# ---------- gate 2: basin is exactly 5Z_5, fraction 1/5 at all depths ----------
for q in (25, 125, 625):
    basin = []
    for x in range(q):
        z = x
        for _ in range(300):
            if z == 0:
                basin.append(x)
                break
            z = f(z, q)
    mults5 = set(range(0, q, 5))
    assert set(basin) == mults5, (q, len(basin))
    assert len(basin) * 5 == q
print("basin of 0 = exactly 5Z_5: a 1/5-fraction of the ball at depths 2, 3, 4 — OK")
print("(denominator 5 = p, NOT the order of the multiplier, which does not exist)")

# ---------- gate 3: boundary shell is not periodic ----------
q = 25
periodic = set()
for x in range(q):
    z = x
    for k in range(1, 40):
        z = f(z, q)
        if z == x:
            periodic.add(x)
            break
shell = [x for x in range(q) if x % 5 == 0 and x % 25 != 0]
assert shell == [5, 10, 15, 20]
assert all(f(x, q) == 0 for x in shell)
assert not (set(shell) & periodic)
print(f"periodic points mod 25: {sorted(periodic)} (0; -4=21; 4-cycle 1,6,11,16)")
print(f"basin-boundary shell {shell}: f(x) = 0 != x for all — none periodic — OK")
print("boundary of the basin != closure of periodic points — OK")

print("\nALL CHECKS PASSED: conjecture 00000002692 REFUTED "
      "(no multiplier order; fraction denominator = p; boundary not periodic closure)")
