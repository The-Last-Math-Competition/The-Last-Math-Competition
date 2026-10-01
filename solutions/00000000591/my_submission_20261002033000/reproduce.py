#!/usr/bin/env python3
"""Independent recomputation for the disproof of TLMC conjecture 00000000591.

Conjecture (new direction on Wilf): for embedding-dimension-3 numerical
semigroups S,  (3*n(S) - g(S) - 3)/g(S) -> 0  as g(S) -> infinity,
where n(S) = #{s in S : 0 <= s <= g(S)}.

Verdict: FALSE. This script recomputes every number claimed in the package:
the Frobenius number g, the nongap count n, the surplus 3n-g-3 and the ratio,
for the four Lean-verified instances, checks the exact formulas of the
symmetric complete-intersection family <pq,pr,qr>, pushes one instance to
g ~ 2.2 million, sweeps a generic family, and cross-checks the DP against the
exhaustive triple search used in the Lean formalization.

Run:  python3 reproduce.py
"""

from itertools import combinations
from math import gcd


def analyze(gens):
    """Frobenius number, nongap count up to g, surplus, ratio for <a,b,c>.

    Sieve bound is doubled until completeness is certified: a run of
    `min(gens)` consecutive representable integers right after the largest
    gap, so closure under addition makes every larger integer representable.
    """
    a, b, c = sorted(gens)
    assert gcd(gcd(a, b), c) == 1, "semigroup must be numerical"
    N = 4 * max(gens)
    while True:
        rep = bytearray(N + 1)
        rep[0] = 1
        for gen in (a, b, c):
            for i in range(gen, N + 1):
                if rep[i - gen]:
                    rep[i] = 1
        gF = max(i for i in range(N + 1) if not rep[i])
        if gF + a <= N and all(rep[i] for i in range(gF + 1, gF + 1 + a)):
            n = sum(rep[i] for i in range(gF + 1))           # nongaps <= g
            surplus = 3 * n - gF - 3
            return gF, n, surplus, surplus / gF
        N *= 2


def rep_triple_search(a, b, c, n):
    """Membership by exhaustive bounded triple search (mirrors Lean's `rep`)."""
    for y in range(n // b + 1):
        for z in range(n // c + 1):
            s = y * b + z * c
            if s <= n and (n - s) % a == 0:
                return True
    return False


def check(label, gens, g_exp, n_exp, s_exp):
    g, n, s, r = analyze(gens)
    ok = (g, n, s) == (g_exp, n_exp, s_exp)
    print(f"{'PASS' if ok else 'FAIL'}  [{label}] S=<{','.join(map(str, gens))}>: "
          f"g={g} n={n} surplus={s} ratio={r:.4f}  "
          f"(expected g={g_exp} n={n_exp} surplus={s_exp})")
    return ok


def main():
    all_ok = True

    print("== 1. Lean-verified instances ==")
    all_ok &= check("a", (17, 23, 29), 215, 104, 94)
    all_ok &= check("b", (9, 13, 101), 95, 48, 46)
    all_ok &= check("c", (15, 33, 55), 227, 114, 112)
    all_ok &= check("d", (35, 55, 77), 603, 302, 300)
    all_ok &= check("e", (15, 39, 65), 271, 136, 134)
    bound_ok = all(5 * s > 2 * g for g, n, s in
                   [(215, 104, 94), (95, 48, 46), (227, 114, 112), (603, 302, 300)])
    print("PASS  all four Lean instances have surplus/g > 2/5" if bound_ok else
          "FAIL  ratio bound")
    all_ok &= bound_ok

    print("\n== 2. Symmetric complete-intersection family <pq,pr,qr>, p,q,r distinct primes ==")
    print("      exact: g = 2pqr-pq-pr-qr, n = (g+1)/2, surplus = (g-3)/2, ratio -> 1/2")
    primes = [p for p in range(2, 200) if all(p % d for d in range(2, int(p ** 0.5) + 1))]
    fam_ok = True
    shown = 0
    tested = 0
    for p, q, r in combinations(primes, 3):
        g_formula = 2 * p * q * r - p * q - p * r - q * r
        if not (200 <= g_formula <= 5000):
            continue
        tested += 1
        g, n, s, ratio = analyze((p * q, p * r, q * r))
        ok = (g == g_formula and n == (g + 1) // 2 and s == (g - 3) // 2
              and abs(ratio - (g - 3) / (2 * g)) < 1e-12)
        fam_ok &= ok
        if shown < 6:
            print(f"  ({p},{q},{r}) S=<{p*q},{p*r},{q*r}>: g={g} n={n} surplus={s} "
                  f"ratio={ratio:.4f}  formulas_ok={ok}")
            shown += 1
    print(f"PASS  family formulas hold on all {tested} instances tested" if fam_ok else
          "FAIL  family formulas")
    all_ok &= fam_ok

    print("\n== 3. One huge instance: p,q,r = 101,103,107 ==")
    p, q, r = 101, 103, 107
    gens = (p * q, p * r, q * r)
    g, n, s, ratio = analyze(gens)
    ok = (g == 2 * p * q * r - p * q - p * r - q * r and n == (g + 1) // 2
          and s == (g - 3) // 2)
    print(f"{'PASS' if ok else 'FAIL'}  S=<{gens}>: g={g} n={n} surplus={s} "
          f"ratio={ratio:.7f}  (g ~ 2.2e6, ratio -> 1/2, nowhere near 0)")
    all_ok &= ok

    print("\n== 4. Generic family <2k+1, 2k+3, 2k+5> (ratio grows toward 1/2) ==")
    for k in (10, 25, 50, 100, 200):
        gens = (2 * k + 1, 2 * k + 3, 2 * k + 5)
        g, n, s, ratio = analyze(gens)
        print(f"  k={k:<4} S=<{gens}>: g={g:<7} n={n:<7} ratio={ratio:.4f}")
        all_ok &= (ratio > 0.42)

    print("\n== 5. Sweep generic triples 6 <= a < b < c <= 30 with g >= 200 ==")
    tot = cnt = 0
    for a, b, c in combinations(range(6, 31), 3):
        if gcd(gcd(a, b), c) != 1:
            continue
        g, n, s, ratio = analyze((a, b, c))
        if g >= 200:
            tot += 1
            if 0.40 <= ratio <= 0.505:
                cnt += 1
    print(f"  {tot} admissible triples with g>=200; {cnt} have surplus/g in [0.40,0.505]")
    all_ok &= (cnt >= 90 * tot // 100)

    print("\n== 6. Cross-check DP membership vs exhaustive triple search (n <= 800) ==")
    xs_ok = True
    for gens in ((17, 23, 29), (9, 13, 101), (35, 55, 77)):
        a, b, c = sorted(gens)
        N = 800
        rep = bytearray(N + 1)
        rep[0] = 1
        for gen in (a, b, c):
            for i in range(gen, N + 1):
                if rep[i - gen]:
                    rep[i] = 1
        for m in range(N + 1):
            if bool(rep[m]) != rep_triple_search(a, b, c, m):
                xs_ok = False
    print("PASS  DP and triple search agree on every n tested" if xs_ok else
          "FAIL  DP vs triple search")
    all_ok &= xs_ok

    print("\nALL CHECKS PASSED" if all_ok else "\nSOME CHECKS FAILED")
    return 0 if all_ok else 1


if __name__ == "__main__":
    raise SystemExit(main())
