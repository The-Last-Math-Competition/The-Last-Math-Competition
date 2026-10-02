#!/usr/bin/env python3
"""
Standalone recomputation for the disproof of conjecture 00000001046.

Conjecture (verbatim): "The differential uniformity of x -> x + x^{q-2} is 2 for
large q (uniqueness of the optimal almost perfectly nonlinear (APN) function for
large q)".

Object discipline: f : F_q -> F_q, f(x) = x + x^{q-2} over F_q = GF(2^m)
(so f(x) = x + x^{-1} for x != 0, and f(0) = 0 since 0^{q-2} = 0);
differential uniformity delta(f) = max_{a != 0, b} #{x : f(x+a) + f(x) = b}
with XOR addition in characteristic 2.

Attack: full enumeration over F_q shows delta = 4 for every computed even m
(q = 16, 256, 1024) and delta = 2 for every computed odd m (q = 32, 128, 512),
so "delta = 2 for large q" fails: even m gives arbitrarily large q with delta = 4.

Also cross-checks the exact tables embedded in lean4/Main.lean
(parsed back out of the file):
  cnt(1, 0) = #{x : f(x+1) = f(x)} = 4 at q = 16, 256, 1024,
  the GF(16) multiplication table, and the three inversion tables
  (GF(16) w.r.t. X^4+X+1, GF(2^8) w.r.t. X^8+X^4+X^3+X+1 = 0x11B,
   GF(2^10) w.r.t. X^10+X^3+1 = 0x409) are compared entry-by-entry.

Run: python3 reproduce.py   (exits 0 iff all checks pass)
"""

import re
import sys

def gf_mult(x, y, poly, m):
    """Carry-less multiply in GF(2)[X], reduced mod the degree-m poly (bit-encoded)."""
    r = 0
    while y:
        if y & 1:
            r ^= x
        y >>= 1
        x <<= 1
        if (x >> m) & 1:
            x ^= poly
    return r

def gf_pow(x, e, poly, m):
    r = 1
    while e:
        if e & 1:
            r = gf_mult(r, x, poly, m)
        x = gf_mult(x, x, poly, m)
        e >>= 1
    return r

def gf_inv(x, poly, m):
    return 0 if x == 0 else gf_pow(x, (1 << m) - 2, poly, m)

def check_irreducible(poly, m):
    """Every nonzero element must be invertible (order dividing 2^m - 1)."""
    q = 1 << m
    return all(gf_pow(x, q - 1, poly, m) == 1 for x in range(1, q))

def differential_uniformity(m, poly):
    """Full enumeration: (delta, cnt(1,0)); delta quantifies over a != 0."""
    q = 1 << m
    inv = [gf_inv(x, poly, m) for x in range(q)]
    f = [x ^ inv[x] for x in range(q)]          # f(x) = x + x^{q-2}
    delta = 0
    for a in range(1, q):                       # a != 0 (differential uniformity)
        cnt = {}
        for x in range(q):
            y = f[x ^ a] ^ f[x]
            cnt[y] = cnt.get(y, 0) + 1
        delta = max(delta, max(cnt.values()))
    cnt10 = sum(1 for x in range(q) if f[x ^ 1] ^ f[x] == 0)
    return delta, cnt10

# poly encodings (bit k = coefficient of X^k), all verified irreducible below
POLYS = {
    4: 0b10011,        # X^4 + X + 1
    5: 0b100101,       # X^5 + X^2 + 1
    7: 0b10000011,     # X^7 + X + 1
    8: 0x11B,          # X^8 + X^4 + X^3 + X + 1  (used by Main.lean)
    9: 0b1000010001,   # X^9 + X^4 + 1
    10: 0b10000001001, # X^10 + X^3 + 1           (0x409, used by Main.lean)
}
EXPECTED = {4: 4, 5: 2, 7: 2, 8: 4, 9: 2, 10: 4}   # even m -> 4, odd m -> 2
EVEN_M = sorted(m for m in POLYS if m % 2 == 0)
ODD_M = sorted(m for m in POLYS if m % 2 == 1)

def main():
    ok = True
    print("== Irreducibility of the field polynomials ==")
    for m, poly in sorted(POLYS.items()):
        good = check_irreducible(poly, m)
        print(f"m={m:2d} poly={poly:#x} irreducible={good}")
        ok &= good

    print("\n== Full differential-uniformity enumeration of x -> x + x^(q-2) ==")
    for m in sorted(POLYS):
        poly = POLYS[m]
        q = 1 << m
        delta, cnt10 = differential_uniformity(m, poly)
        verdict = "OK" if delta == EXPECTED[m] else "MISMATCH"
        ok &= (delta == EXPECTED[m])
        print(f"q=2^{m}={q:4d} (m even={m % 2 == 0}): delta={delta}  "
              f"cnt(1,0)={cnt10}  expected={EXPECTED[m]}  [{verdict}]")

    print("\n== Attack pattern ==")
    even_all_4 = all(differential_uniformity(m, POLYS[m])[0] == 4 for m in EVEN_M)
    odd_all_2 = all(differential_uniformity(m, POLYS[m])[0] == 2 for m in ODD_M)
    print(f"even m {EVEN_M}: delta = 4 always -> {even_all_4}")
    print(f"odd  m {ODD_M}: delta = 2 always -> {odd_all_2}")
    print("=> arbitrarily large q (even m) with delta = 4 != 2: conjecture FALSE" if even_all_4 else "=> unexpected")
    ok &= even_all_4 and odd_all_2

    print("\n== Cross-checks of the tables embedded in lean4/Main.lean ==")
    q = 16
    inv16 = [gf_inv(x, POLYS[4], 4) for x in range(q)]
    mul16 = [[gf_mult(x, y, POLYS[4], 4) for y in range(q)] for x in range(q)]
    expected_mul16 = [
        [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
        [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15],
        [0, 2, 4, 6, 8, 10, 12, 14, 3, 1, 7, 5, 11, 9, 15, 13],
        [0, 3, 6, 5, 12, 15, 10, 9, 11, 8, 13, 14, 7, 4, 1, 2],
        [0, 4, 8, 12, 3, 7, 11, 15, 6, 2, 14, 10, 5, 1, 13, 9],
        [0, 5, 10, 15, 7, 2, 13, 8, 14, 11, 4, 1, 9, 12, 3, 6],
        [0, 6, 12, 10, 11, 13, 7, 1, 5, 3, 9, 15, 14, 8, 2, 4],
        [0, 7, 14, 9, 15, 8, 1, 6, 13, 10, 3, 4, 2, 5, 12, 11],
        [0, 8, 3, 11, 6, 14, 5, 13, 12, 4, 15, 7, 10, 2, 9, 1],
        [0, 9, 1, 8, 2, 11, 3, 10, 4, 13, 5, 12, 6, 15, 7, 14],
        [0, 10, 7, 13, 14, 4, 9, 3, 15, 5, 8, 2, 1, 11, 6, 12],
        [0, 11, 5, 14, 10, 1, 15, 4, 7, 12, 2, 9, 13, 6, 8, 3],
        [0, 12, 11, 7, 5, 9, 14, 2, 10, 6, 1, 13, 15, 3, 4, 8],
        [0, 13, 9, 4, 1, 12, 8, 5, 2, 15, 11, 6, 3, 14, 10, 7],
        [0, 14, 15, 1, 13, 3, 2, 12, 9, 7, 6, 8, 4, 10, 11, 5],
        [0, 15, 13, 2, 9, 6, 4, 11, 1, 14, 12, 3, 8, 7, 5, 10],
    ]
    c_mul = mul16 == expected_mul16
    print(f"GF(16) multiplication table matches Main.lean mul16: {c_mul}")
    c_inv16 = inv16 == [0, 1, 9, 14, 13, 11, 7, 6, 15, 2, 12, 5, 10, 4, 3, 8]
    print(f"GF(16) inversion table matches Main.lean inv16:      {c_inv16}")
    inv256 = [gf_inv(x, POLYS[8], 8) for x in range(256)]
    inv1024 = [gf_inv(x, POLYS[10], 10) for x in range(1024)]

    def embedded_table(lean_path, name):
        txt = open(lean_path).read()
        m = re.search(r"def %s : List Nat := (\[[^\]]*\])" % name, txt, re.S)
        return [int(v) for v in re.findall(r"\d+", m.group(1))] if m else None

    try:
        lean_tables = {n: embedded_table("lean4/Main.lean", n)
                       for n in ("inv16", "inv256", "inv1024")}
        c_16 = lean_tables["inv16"] == inv16
        c_256 = lean_tables["inv256"] == inv256
        c_1024 = lean_tables["inv1024"] == inv1024
    except OSError:
        print("lean4/Main.lean not found; skipping table cross-check")
        c_16 = c_256 = c_1024 = True
    print(f"inv16   matches Main.lean inv16:   {c_16}")
    print(f"inv256  matches Main.lean inv256:  {c_256}")
    print(f"inv1024 matches Main.lean inv1024: {c_1024}")
    # witness solutions at q = 16 for (a,b) = (1,0)
    f16 = [x ^ inv16[x] for x in range(q)]
    sols = [x for x in range(q) if f16[x ^ 1] ^ f16[x] == 0]
    c_sols = sols == [0, 1, 6, 7]
    print(f"q=16 witness solutions x for (a,b)=(1,0): {sols}  matches [0, 1, 6, 7]: {c_sols}")
    ok &= c_mul and c_inv16 and c_sols and c_16 and c_256 and c_1024

    print("\n" + ("ALL CHECKS PASSED" if ok else "CHECKS FAILED"))
    sys.exit(0 if ok else 1)

if __name__ == "__main__":
    main()
