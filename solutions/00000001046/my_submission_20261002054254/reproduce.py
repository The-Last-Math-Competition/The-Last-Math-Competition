#!/usr/bin/env python3
"""
Independent recomputation for TLMC conjecture 00000001046.

Conjecture: the differential uniformity of F: x -> x + x^(q-2) over F_q is 2
for large q.  We take q = 2^m (the natural family F_{2^m}) and compute
delta(F) by exhaustive enumeration for m = 4..12.

Method:
  * GF(2^m) = GF(2)[x]/(f), f a primitive polynomial found and verified by
    checking ord(x) = 2^m - 1 via square-and-multiply with carry-less mult.
  * inverse table inv (representing x^(q-2)), verified elementwise with an
    independent carry-less multiplication: clmul(v, inv[v]) == 1 for v != 0.
  * F(x) = x XOR inv[x]  (characteristic-2 addition = XOR); F(0) = 0 since
    0^(q-2) = 0.
  * delta(F) = max_{a != 0, b} #{x in F_q : F(x+a) + F(x) = b}
    computed by full enumeration (numpy bincount when available, with a
    pure-Python fallback).

Expected / claimed by the attack:  even m -> delta = 4, odd m -> delta = 2.
"""
from itertools import combinations
from collections import Counter


def clmul(a, b, m, poly):
    """Carry-less multiplication in GF(2)[x]/(poly), basis x^i -> bit i."""
    r = 0
    while b:
        if b & 1:
            r ^= a
        b >>= 1
        a <<= 1
        if (a >> m) & 1:
            a ^= poly
    return r


def gfpow(a, e, m, poly):
    r = 1
    while e:
        if e & 1:
            r = clmul(r, a, m, poly)
        a = clmul(a, a, m, poly)
        e >>= 1
    return r


def find_primitive_poly(m):
    """Smallest primitive poly of degree m with <= 4 middle terms; verified."""
    full = (1 << m) - 1
    divs = [p for p in range(2, full + 1) if full % p == 0]
    for w in range(1, 5):
        for mid in combinations(range(1, m), w):
            poly = (1 << m) | 1
            for k in mid:
                poly |= 1 << k
            # primitivity: x^full = 1 and x^(full/p) != 1 for all divisors p>1
            if gfpow(2, full, m, poly) != 1:
                continue
            if any(gfpow(2, full // p, m, poly) == 1 for p in divs):
                continue
            return poly
    raise RuntimeError(f"no primitive polynomial found for m={m}")


def inverse_table(m, poly):
    q = 1 << m
    # exp/log tables; exp doubled so wrap-around indexing stays in range
    exp = [0] * (2 * (q - 1))
    log = [0] * q
    x = 1
    for i in range(2 * (q - 1)):
        exp[i] = x
        if i < q - 1:
            log[x] = i
        x = clmul(x, 2, m, poly)
    assert x == 1
    assert sorted(log[1:]) == list(range(q - 1))
    inv = [0] * q
    for v in range(1, q):
        inv[v] = exp[(q - 1) - log[v]]
    # elementwise verification with independent carry-less multiplication
    for v in range(1, q):
        assert clmul(v, inv[v], m, poly) == 1, f"bad inverse at m={m}, v={v}"
    return inv


def differential_uniformity(m, poly, inv, report=False):
    q = 1 << m
    F = [v ^ inv[v] for v in range(q)]          # F(x) = x + x^(q-2)

    best, arg = 0, None
    try:
        import numpy as np
        xs = np.arange(q)
        Fn = np.array(F)
        for a in range(1, q):
            cnt = np.bincount(Fn[xs ^ a] ^ Fn[xs], minlength=q)
            c = int(cnt.max())
            if c > best:
                best, arg = c, (a, int(cnt.argmax()))
    except ImportError:
        for a in range(1, q):
            cnt = Counter(F[x ^ a] ^ F[x] for x in range(q))
            c, b = max((v, k) for k, v in cnt.items())
            if c > best:
                best, arg = c, (a, b)

    if report:
        a, b = arg
        sols = [x for x in range(q) if F[x ^ a] ^ F[x] == b]
        print(f"    attack instance for q=2^{m}: a={a}, b={b}, "
              f"solutions={sols} ({len(sols)} solutions)")
    return best


def main():
    print("delta of F(x) = x + x^(q-2) over GF(2^m), exhaustive enumeration:")
    for m in range(4, 13):
        poly = find_primitive_poly(m)
        inv = inverse_table(m, poly)
        d = differential_uniformity(m, poly, inv, report=(m <= 8))
        tag = "even m" if m % 2 == 0 else "odd m "
        print(f"  m={m:2d}  q=2^{m:<2d}={1 << m:5d}  {tag}  delta = {d}")
        assert d == (4 if m % 2 == 0 else 2), "UNEXPECTED RESULT"
    print("Conclusion: even m -> delta = 4 (q = 16, 64, 256, 1024, 4096); "
          "odd m -> delta = 2 (q = 32, 128, 512, 2048).")
    print("=> The conjecture 'delta = 2 for large q' is FALSE: "
          "for arbitrarily large q with even m, delta = 4 != 2.")


if __name__ == "__main__":
    main()
