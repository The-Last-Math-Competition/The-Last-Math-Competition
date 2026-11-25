#!/usr/bin/env python3
"""
Standalone exact verification suite for Conjecture 00000004764:
  "Boolean convolution is the simplified convolution without a composition condition.
   Conjecture: The conversion of Boolean to free convolution is an explicit power of two,
   the exponent is controlled by the partition structure of the moment order, and it is
   exact at the generating function level."

Verifies:
  1. Exact generating-function equations with vs without composition:
     - Boolean: (1 - B(z)) * M(z) = 1  <=>  M(z) - 1 = B_tilde(z) * (z * M(z))
     - Free:    M(z) = C(z * M(z))     <=>  M(z) - 1 = R(z * M(z)) * (z * M(z))
  2. Combinatorial partition lattices Int(n), NC(n), NC_irr(n) for n = 1..7,
     confirming |Int(n)| = 2^(n-1), |NC(n)| = C_n, |NC_irr(n)| = C_{n-1}, and
     exact agreement with generating-function expansions.
  3. Reading I (Bercovici-Pata / Kreweras partition-type moment conversion):
     - Closed-form ratio N_NC(lambda) / N_Int(lambda) = n! / (k! * (n - k + 1)!)
     - Low-order Fermat-prime mirage at n in {1, 2, 4} (ratios in {1, 2})
     - Exact obstructions at n = 3 (3/2), n = 5 (5/2), n = 6 (3 and 5), and
       concrete witness mu_Bern -> B_1(mu_Bern) = mu_sc at order 6 (5 vs 1).
  4. Reading II (Same-measure cumulant conversion beta_n <-> kappa_n):
     - Lagrange-Burmann closed forms beta_n = [w^n] C(w)^(n-1) / (n-1) and
       kappa_n = -[z^n] (1 - B(z))^(n-1) / (n-1) for n = 2..8
     - Symmetric low-order mirage up to n = 6 (coeffs 1, 1, 1, 4, 2)
     - Exact obstructions: nonlinearity at n = 4 (beta_4(mu_sc) = 1 vs kappa_4 = 0),
       negativity at n = 4 (kappa_4(mu_Bern) = -1), odd-order coeff 3 at n = 5,
       and symmetric Catalan collapse at n = 8 (coeffs 6, 3, 15, 5; beta_8(mu_sc) = 5).
  5. Reading III (Direct two-measure convolution mu uplus nu vs mu boxplus nu):
     - Centered order-4 mirage (mixed ratio 4 / 2 = 2^1)
     - Centered order-5 failure (5 / 2) and symmetric order-6 failure (factor 3)
     - Concrete Bernoulli self-convolution vs arcsine law: m_4 (6 vs 4) and m_6 (20 vs 8).
  6. Reading IV (Partition-lattice counts |NC(n)| / |Int(n)|):
     - Agreement at n = 1, 2 and failure at n = 3 (5 / 4).

Uses only the Python 3.12 standard library (fractions, math, collections).
"""

from __future__ import annotations
import math
import sys
from collections import Counter, defaultdict
from fractions import Fraction


def is_signed_pow2(r: Fraction) -> bool:
    """Return True iff r in {2^k : k in Z}."""
    if r <= 0:
        return False
    num, den = r.numerator, r.denominator
    return (num == 1 and (den & (den - 1)) == 0) or (den == 1 and (num & (num - 1)) == 0)


# ---------------------------------------------------------------------------
# 1. Exact Multivariate Polynomial Algebra over Q
# ---------------------------------------------------------------------------
Poly = dict[tuple[tuple[str, int], ...], Fraction]


def p_const(c: int | Fraction) -> Poly:
    fc = Fraction(c)
    return {(): fc} if fc != 0 else {}


def p_var(name: str) -> Poly:
    return {((name, 1),): Fraction(1)}


def p_add(a: Poly, b: Poly, scale: Fraction = Fraction(1)) -> Poly:
    out = dict(a)
    for m, c in b.items():
        nv = out.get(m, Fraction(0)) + scale * c
        if nv == 0:
            out.pop(m, None)
        else:
            out[m] = nv
    return out


def p_mul(a: Poly, b: Poly) -> Poly:
    acc: dict[tuple[tuple[str, int], ...], Fraction] = defaultdict(Fraction)
    for m1, c1 in a.items():
        for m2, c2 in b.items():
            d: dict[str, int] = defaultdict(int)
            for v, e in m1:
                d[v] += e
            for v, e in m2:
                d[v] += e
            key = tuple(sorted((v, e) for v, e in d.items() if e != 0))
            acc[key] += c1 * c2
    return {m: c for m, c in acc.items() if c != 0}


# ---------------------------------------------------------------------------
# 2. Formal Power Series Operations (Exact Truncation to Degree N)
# ---------------------------------------------------------------------------
def series_mul(f: list[Poly], g: list[Poly], deg: int) -> list[Poly]:
    res = [p_const(0) for _ in range(deg + 1)]
    for i in range(deg + 1):
        if not f[i]:
            continue
        for j in range(deg + 1 - i):
            if g[j]:
                res[i + j] = p_add(res[i + j], p_mul(f[i], g[j]))
    return res


def series_pow(f: list[Poly], exp: int, deg: int) -> list[Poly]:
    res = [p_const(1)] + [p_const(0) for _ in range(deg)]
    base = f[:]
    e = exp
    while e > 0:
        if e & 1:
            res = series_mul(res, base, deg)
        e >>= 1
        if e > 0:
            base = series_mul(base, base, deg)
    return res


def moments_from_bool(b: list[Poly], deg: int) -> list[Poly]:
    m = [p_const(1)] + [p_const(0) for _ in range(deg)]
    for n in range(1, deg + 1):
        acc = p_const(0)
        for j in range(1, n + 1):
            acc = p_add(acc, p_mul(b[j], m[n - j]))
        m[n] = acc
    return m


def bool_from_moments(m: list[Poly], deg: int) -> list[Poly]:
    b = [p_const(0) for _ in range(deg + 1)]
    for n in range(1, deg + 1):
        acc = m[n]
        for j in range(1, n):
            acc = p_add(acc, p_mul(b[j], m[n - j]), scale=Fraction(-1))
        b[n] = acc
    return b


def moments_from_free(k: list[Poly], deg: int) -> list[Poly]:
    m = [p_const(1)] + [p_const(0) for _ in range(deg)]
    for n in range(1, deg + 1):
        acc = p_const(0)
        for j in range(1, n + 1):
            mj = series_pow(m[: n - j + 1], j, n - j)
            acc = p_add(acc, p_mul(k[j], mj[n - j]))
        m[n] = acc
    return m


def free_from_moments(m: list[Poly], deg: int) -> list[Poly]:
    k = [p_const(0) for _ in range(deg + 1)]
    for n in range(1, deg + 1):
        acc = m[n]
        for j in range(1, n):
            mj = series_pow(m[: n - j + 1], j, n - j)
            acc = p_add(acc, p_mul(k[j], mj[n - j]), scale=Fraction(-1))
        k[n] = acc
    return k


# ---------------------------------------------------------------------------
# 3. Combinatorial Partition Lattices via Restricted Growth Strings (RGS)
# ---------------------------------------------------------------------------
def all_rgs(n: int) -> list[tuple[int, ...]]:
    if n == 0:
        return [()]
    res = [(0,)]
    for _ in range(1, n):
        nxt = []
        for p in res:
            mx = max(p)
            for lbl in range(mx + 2):
                nxt.append(p + (lbl,))
        res = nxt
    return res


def is_interval_rgs(p: tuple[int, ...]) -> bool:
    return all(p[i] <= p[i + 1] for i in range(len(p) - 1))


def is_nc_rgs(p: tuple[int, ...]) -> bool:
    n = len(p)
    for a in range(n):
        pa = p[a]
        for b in range(a + 1, n):
            pb = p[b]
            if pa == pb:
                continue
            for c in range(b + 1, n):
                if p[c] != pa:
                    continue
                for d in range(c + 1, n):
                    if p[d] == pb:
                        return False
    return True


def is_irr_nc_rgs(p: tuple[int, ...]) -> bool:
    return len(p) > 0 and p[0] == p[-1] and is_nc_rgs(p)


def partition_type(p: tuple[int, ...]) -> tuple[int, ...]:
    counts = Counter(p)
    return tuple(sorted(counts.values(), reverse=True))


def partition_poly(parts: list[tuple[int, ...]], prefix: str) -> Poly:
    total = p_const(0)
    for p in parts:
        mon = p_const(1)
        for sz in Counter(p).values():
            mon = p_mul(mon, p_var(f"{prefix}{sz}"))
        total = p_add(total, mon)
    return total


def catalan(n: int) -> int:
    return math.comb(2 * n, n) // (n + 1)


def main() -> int:
    print("=" * 74)
    print("Verification Suite for Conjecture 00000004764")
    print("=" * 74)

    # -----------------------------------------------------------------------
    # Check 1: Generating-function equations & bijections up to degree 8
    # -----------------------------------------------------------------------
    N = 8
    b_sym = [p_const(0)] + [p_var(f"b{i}") for i in range(1, N + 1)]
    k_sym = [p_const(0)] + [p_var(f"k{i}") for i in range(1, N + 1)]

    M_bool = moments_from_bool(b_sym, N)
    M_free = moments_from_free(k_sym, N)

    # Verify (1 - B(z)) * M_bool(z) == 1 up to z^8
    one_minus_B = [p_const(1)] + [p_add(p_const(0), b_sym[i], Fraction(-1)) for i in range(1, N + 1)]
    prod_bool = series_mul(one_minus_B, M_bool, N)
    assert prod_bool[0] == p_const(1) and all(prod_bool[i] == {} for i in range(1, N + 1))

    # Verify M_free(z) == C(z * M_free(z)) up to z^8
    zM = [p_const(0)] + M_free[:N]
    comp_C = [p_const(1)] + [p_const(0) for _ in range(N)]
    for j in range(1, N + 1):
        zM_pow = series_pow(zM, j, N)
        for n in range(j, N + 1):
            comp_C[n] = p_add(comp_C[n], p_mul(k_sym[j], zM_pow[n]))
    assert comp_C == M_free

    # Verify round-trip bijections
    assert bool_from_moments(M_bool, N) == b_sym
    assert free_from_moments(M_free, N) == k_sym
    print("[PASS] Check 1: Exact generating-function equations (1 - B)M = 1 and M = C(zM) verified (deg <= 8).")

    # -----------------------------------------------------------------------
    # Check 2: Combinatorial partition lattices & Reading IV (n = 1..7)
    # -----------------------------------------------------------------------
    beta_of_k = bool_from_moments(M_free, N)
    kappa_of_b = free_from_moments(M_bool, N)

    for n in range(1, 8):
        rgs = all_rgs(n)
        int_p = [p for p in rgs if is_interval_rgs(p)]
        nc_p = [p for p in rgs if is_nc_rgs(p)]
        irr_p = [p for p in rgs if is_irr_nc_rgs(p)]

        assert len(int_p) == 2 ** (n - 1), f"Failed |Int({n})|"
        assert len(nc_p) == catalan(n), f"Failed |NC({n})|"
        assert len(irr_p) == catalan(n - 1), f"Failed |NC_irr({n})|"

        if n <= 6:
            assert partition_poly(int_p, "b") == M_bool[n]
            assert partition_poly(nc_p, "k") == M_free[n]
            assert partition_poly(irr_p, "k") == beta_of_k[n]

    ratio_n3 = Fraction(catalan(3), 2 ** 2)
    assert ratio_n3 == Fraction(5, 4) and not is_signed_pow2(ratio_n3)
    print(f"[PASS] Check 2: Partition lattices verified (n=1..7); |NC(3)|/|Int(3)| = {ratio_n3} (not 2^e).")

    # -----------------------------------------------------------------------
    # Check 3: Reading I — Kreweras ratios & Bercovici-Pata bijection B_1
    # -----------------------------------------------------------------------
    for n in range(1, 7):
        rgs = all_rgs(n)
        int_counts = Counter(partition_type(p) for p in rgs if is_interval_rgs(p))
        nc_counts = Counter(partition_type(p) for p in rgs if is_nc_rgs(p))
        for lam, c_int in int_counts.items():
            k_len = len(lam)
            mult_counts = Counter(lam)
            denom_mult = math.prod(math.factorial(r) for r in mult_counts.values())
            assert c_int == math.factorial(k_len) // denom_mult
            assert nc_counts[lam] == math.factorial(n) // (math.factorial(n - k_len + 1) * denom_mult)
            ratio = Fraction(nc_counts[lam], c_int)
            assert ratio == Fraction(math.factorial(n), math.factorial(k_len) * math.factorial(n - k_len + 1))
            if n in (1, 2, 4):
                assert is_signed_pow2(ratio)

    assert Fraction(math.factorial(3), math.factorial(2) * math.factorial(2)) == Fraction(3, 2)
    assert Fraction(math.factorial(5), math.factorial(2) * math.factorial(4)) == Fraction(5, 2)
    assert Fraction(math.factorial(6), math.factorial(2) * math.factorial(5)) == Fraction(3, 1)
    assert Fraction(math.factorial(6), math.factorial(3) * math.factorial(4)) == Fraction(5, 1)

    # Concrete witness: symmetric Bernoulli -> Wigner semicircle under B_1
    b_bern = [p_const(1 if i == 2 else 0) for i in range(N + 1)]
    m_bern = moments_from_bool(b_bern, N)
    m_wigner = moments_from_free(b_bern, N)
    bern_vals = [m_bern[i].get((), Fraction(0)) for i in range(0, N + 1, 2)]
    wigner_vals = [m_wigner[i].get((), Fraction(0)) for i in range(0, N + 1, 2)]
    assert bern_vals == [1, 1, 1, 1, 1]
    assert wigner_vals == [1, 1, 2, 5, 14]
    assert not is_signed_pow2(wigner_vals[3] / bern_vals[3])  # 5 / 1 = 5
    print("[PASS] Check 3: Reading I (Kreweras & Bercovici-Pata) verified; fails at n=3 (3/2), n=5 (5/2), n=6 (3, 5).")

    # -----------------------------------------------------------------------
    # Check 4: Reading II — Lagrange-Burmann cumulant conversion (n = 2..8)
    # -----------------------------------------------------------------------
    C_series = [p_const(1)] + k_sym[1:]
    one_minus_B_sym = [p_const(1)] + [p_add(p_const(0), b_sym[i], Fraction(-1)) for i in range(1, N + 1)]
    for n in range(2, N + 1):
        cn = series_pow(C_series, n - 1, n)[n]
        lagrange_beta = {m: c * Fraction(1, n - 1) for m, c in cn.items()}
        assert lagrange_beta == beta_of_k[n], f"Lagrange beta failed at n={n}"

        bn = series_pow(one_minus_B_sym, n - 1, n)[n]
        lagrange_kappa = {m: c * Fraction(-1, n - 1) for m, c in bn.items()}
        assert lagrange_kappa == kappa_of_b[n], f"Lagrange kappa failed at n={n}"

    # Verify symmetric n=6 power-of-two mirage and n=8 collapse
    even_beta6 = {m: c for m, c in beta_of_k[6].items() if all(int(v[1:]) % 2 == 0 for v, _ in m)}
    assert all(is_signed_pow2(c) for c in even_beta6.values())  # {1, 4, 2}
    even_beta8 = {m: c for m, c in beta_of_k[8].items() if all(int(v[1:]) % 2 == 0 for v, _ in m)}
    non_pow2_beta8 = {m: c for m, c in even_beta8.items() if not is_signed_pow2(c)}
    assert sorted(non_pow2_beta8.values()) == [Fraction(3), Fraction(5), Fraction(6), Fraction(15)]

    beta_wigner = bool_from_moments(m_wigner, N)
    kappa_bern = free_from_moments(m_bern, N)
    assert [beta_wigner[i].get((), Fraction(0)) for i in (2, 4, 6, 8)] == [1, 1, 2, 5]
    assert [kappa_bern[i].get((), Fraction(0)) for i in (2, 4, 6, 8)] == [1, -1, 2, -5]
    print("[PASS] Check 4: Reading II (Lagrange-Burmann beta <-> kappa) verified; symmetric n=8 coeffs {3, 5, 6, 15}.")

    # -----------------------------------------------------------------------
    # Check 5: Reading III — Direct two-measure convolution mu uplus nu vs mu boxplus nu
    # -----------------------------------------------------------------------
    N2 = 6
    a_cent = [p_const(1), p_const(0)] + [p_var(f"a{i}") for i in range(2, N2 + 1)]
    c_cent = [p_const(1), p_const(0)] + [p_var(f"c{i}") for i in range(2, N2 + 1)]
    b_ac = [p_add(bool_from_moments(a_cent, N2)[i], bool_from_moments(c_cent, N2)[i]) for i in range(N2 + 1)]
    k_ac = [p_add(free_from_moments(a_cent, N2)[i], free_from_moments(c_cent, N2)[i]) for i in range(N2 + 1)]
    m_uplus = moments_from_bool(b_ac, N2)
    m_boxplus = moments_from_free(k_ac, N2)

    assert m_uplus[4][(("a2", 1), ("c2", 1))] == Fraction(2)
    assert m_boxplus[4][(("a2", 1), ("c2", 1))] == Fraction(4)
    assert m_uplus[5][(("a2", 1), ("c3", 1))] == Fraction(2)
    assert m_boxplus[5][(("a2", 1), ("c3", 1))] == Fraction(5)
    assert m_uplus[6][(("a2", 1), ("c4", 1))] == Fraction(2)
    assert m_boxplus[6][(("a2", 1), ("c4", 1))] == Fraction(6)
    assert m_uplus[6][(("a2", 2), ("c2", 1))] == Fraction(1)
    assert m_boxplus[6][(("a2", 2), ("c2", 1))] == Fraction(3)

    # Bernoulli self-convolution vs arcsine law
    b_bern2 = [p_add(b_bern[i], b_bern[i]) for i in range(N + 1)]
    k_bern2 = [p_add(kappa_bern[i], kappa_bern[i]) for i in range(N + 1)]
    m_bern_uplus2 = moments_from_bool(b_bern2, N)
    m_bern_boxplus2 = moments_from_free(k_bern2, N)
    uplus_even = [m_bern_uplus2[2 * k].get((), Fraction(0)) for k in range(1, 5)]
    boxplus_even = [m_bern_boxplus2[2 * k].get((), Fraction(0)) for k in range(1, 5)]
    assert uplus_even == [2, 4, 8, 16]
    assert boxplus_even == [2, 6, 20, 70]  # C(2k, k)
    assert not is_signed_pow2(boxplus_even[1] / uplus_even[1])  # 6 / 4 = 3 / 2
    assert not is_signed_pow2(boxplus_even[2] / uplus_even[2])  # 20 / 8 = 5 / 2
    print("[PASS] Check 5: Reading III (Direct convolution uplus vs boxplus) verified; Bernoulli^2 ratios 3/2, 5/2.")

    print("=" * 74)
    print("ALL VERIFICATION CHECKS PASSED: Conjecture 00000004764 is FALSE.")
    print("=" * 74)
    return 0


if __name__ == "__main__":
    sys.exit(main())
