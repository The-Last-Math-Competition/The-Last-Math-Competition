#!/usr/bin/env python3
"""
Verification script for Conjecture 00000007675:
"Carry formula for Gaussian binomial valuations and alternative LCM-expression"

Verifies:
  1. Equivalence of three definitions of Gaussian binomial coefficients [n choose k]_q
     (q-Pascal recurrence, q-factorial quotient, and multiplicative cross-product).
  2. Congruence [n choose k]_q == 1 (mod q) for all q >= 2 and 0 <= k <= n, hence
     v_p([n choose k]_{p^r}) == 0 identically for all primes p, r >= 1, and 0 <= k <= n.
  3. Equivalence of residue and ripple-carry definitions of base-p carries, Kummer's
     termwise identity (making Clause 1 a tautological 0 = 0 under 1-indexed carries),
     and failure of Clause 1 under 0-indexed carries at (p, n, k) = (2, 2, 1).
  4. Refutation of Clause 2 ("alternative LCM-expression holds only when p <= n - k")
     in BOTH directions (necessary, sufficient, and biconditional) across all eight
     natural parsings LCM_1 .. LCM_8, and for every individual prime p.
"""

from fractions import Fraction
import math
import sys


def q_int(q: int, m: int) -> int:
    """Standard q-integer [m]_q = 1 + q + ... + q^(m-1) for m >= 0."""
    return sum(q ** i for i in range(m))


def q_fact(q: int, m: int) -> int:
    """Standard q-factorial [m]_q! = prod_{i=1}^m [i]_q."""
    res = 1
    for i in range(1, m + 1):
        res *= q_int(q, i)
    return res


def q_binom_pascal(q: int, n: int, k: int) -> int:
    """Gaussian binomial coefficient [n choose k]_q via q-Pascal recurrence."""
    if k < 0 or k > n:
        return 0
    dp = [[0] * (n + 1) for _ in range(n + 1)]
    for m in range(n + 1):
        dp[m][0] = 1
    for m in range(1, n + 1):
        for j in range(1, m + 1):
            dp[m][j] = dp[m - 1][j] + (q ** (m - j)) * dp[m - 1][j - 1]
    return dp[n][k]


def q_binom_qfact(q: int, n: int, k: int) -> int:
    """Gaussian binomial coefficient via [n]_q! / ([k]_q! [n-k]_q!) for q >= 1."""
    if k < 0 or k > n:
        return 0
    num = q_fact(q, n)
    den = q_fact(q, k) * q_fact(q, n - k)
    assert num % den == 0
    return num // den


def q_binom_prod(q: int, n: int, k: int) -> int:
    """Gaussian binomial coefficient via prod_{i=1}^k (q^(n-k+i)-1)/(q^i-1) for q >= 2."""
    if k < 0 or k > n:
        return 0
    num = 1
    den = 1
    for i in range(1, k + 1):
        num *= (q ** (n - k + i) - 1)
        den *= (q ** i - 1)
    assert num % den == 0
    return num // den


def padic_val(x: int, p: int) -> int:
    """Exact p-adic valuation v_p(x) for positive integer x and prime p."""
    assert x > 0 and p >= 2
    v = 0
    while x % p == 0:
        x //= p
        v += 1
    return v


def carry_residue(p: int, a: int, b: int, j: int) -> int:
    """1-indexed base-p carry into p^j via residues modulo p^j (j >= 1)."""
    assert p >= 2 and j >= 1
    pj = p ** j
    return 1 if (a % pj) + (b % pj) >= pj else 0


def carry_ripple(p: int, a: int, b: int, j: int) -> int:
    """1-indexed base-p carry into p^j via digit-by-digit ripple addition (j >= 1)."""
    assert p >= 2 and j >= 1
    c = 0
    for idx in range(j):
        da = (a // (p ** idx)) % p
        db = (b // (p ** idx)) % p
        c = (da + db + c) // p
    return c


def lcm_interval(lo: int, hi: int) -> int:
    """Least common multiple of integers in [lo, hi] (1 if empty)."""
    res = 1
    for m in range(lo, hi + 1):
        res = math.lcm(res, m)
    return res


def floor_log_p_q(p: int, num: int, den: int) -> int:
    """
    Exact integer e = floor(log_p(num / den)) for p >= 2, num >= 1, den >= 1,
    characterized uniquely by p^e <= num / den < p^(e + 1).
    """
    assert p >= 2 and num >= 1 and den >= 1
    q = Fraction(num, den)
    if q >= 1:
        e = 0
        while Fraction(p ** (e + 1), 1) <= q:
            e += 1
        assert Fraction(p ** e, 1) <= q < Fraction(p ** (e + 1), 1)
        return e
    else:
        e = -1
        while q < Fraction(1, p ** (-e)):
            e -= 1
        assert Fraction(1, p ** (-e)) <= q < Fraction(1, p ** (-e - 1))
        return e


def all_lcm_parsings(p: int, n: int, k: int) -> dict[str, int]:
    """Evaluate all 8 natural parsings of the Clause 2 LCM-expression."""
    L = lcm_interval(k + 1, n)
    fk = math.factorial(k)
    fnk = math.factorial(n - k)
    denom = fk * fnk
    fl_L = floor_log_p_q(p, L, 1)
    return {
        "LCM_1_floor_log_Q": floor_log_p_q(p, L, denom),
        "LCM_2_floor_logL_over_denom": fl_L // denom,
        "LCM_3_floor_log_over_nkfact": floor_log_p_q(p, L, fnk),
        "LCM_4_vp_L_minus_vp_denom": padic_val(L, p) - padic_val(denom, p),
        "LCM_5_vp_L_minus_vp_nkfact": padic_val(L, p) - padic_val(fnk, p),
        "LCM_6_fllogL_minus_vp_denom": fl_L - padic_val(denom, p),
        "LCM_7_fllogL_minus_vp_nkfact": fl_L - padic_val(fnk, p),
        "LCM_8_vp_classic_binom": padic_val(math.comb(n, k), p),
    }


def main() -> int:
    print("=== Verification for Conjecture 00000007675 ===")

    # 1. Verify equivalence of Gaussian binomial definitions and [n choose k]_q == 1 (mod q)
    print("\n[Check 1] Gaussian binomial definitions & congruence mod q...")
    for n in range(16):
        for k in range(n + 1):
            assert q_binom_pascal(1, n, k) == q_binom_qfact(1, n, k) == math.comb(n, k)
    for q in [2, 3, 4, 5, 7, 8, 9, 11, 13]:
        dp_table = [[0] * 16 for _ in range(16)]
        for m in range(16):
            dp_table[m][0] = 1
        for m in range(1, 16):
            for j in range(1, m + 1):
                dp_table[m][j] = dp_table[m - 1][j] + (q ** (m - j)) * dp_table[m - 1][j - 1]
        for n in range(16):
            for k in range(n + 1):
                v1 = dp_table[n][k]
                v2 = q_binom_qfact(q, n, k)
                v3 = q_binom_prod(q, n, k)
                assert v1 == v2 == v3, f"Mismatch at q={q}, n={n}, k={k}"
                assert v1 % q == 1, f"Mod q != 1 at q={q}, n={n}, k={k}: got {v1}"

    primes = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31]
    for p in primes[:6]:
        for r in [1, 2, 3]:
            q = p ** r
            for n in range(13):
                for k in range(n + 1):
                    val = q_binom_prod(q, n, k)
                    assert padic_val(val, p) == 0
    print("  PASS: [n choose k]_q matches all 3 definitions; [n choose k]_{p^r} == 1 (mod p^r),")
    print("        so v_p([n choose k]_{p^r}) = 0 identically for all p, r >= 1, 0 <= k <= n.")

    # 2. Verify Clause 1 (Kummer's termwise carry cancellation & 0-indexed carry failure)
    print("\n[Check 2] Clause 1 carry conventions & Kummer's termwise identity...")
    for p in [2, 3, 5, 7]:
        for n in range(26):
            for k in range(n + 1):
                a, b = k, n - k
                for j in range(1, 10):
                    c_res = carry_residue(p, a, b, j)
                    c_rip = carry_ripple(p, a, b, j)
                    diff = (n // (p ** j)) - (a // (p ** j)) - (b // (p ** j))
                    assert c_res == c_rip == diff
    # Shifted 0-indexed carry (carry out of p^j into p^(j+1), summed over j >= 1) at (2, 2, 1):
    shifted_sum_2_2_1 = sum(
        (2 // (2 ** j)) - (1 // (2 ** j)) - (1 // (2 ** j)) - carry_residue(2, 1, 1, j + 1)
        for j in range(1, 8)
    )
    assert padic_val(q_binom_prod(2, 2, 1), 2) == 0 and shifted_sum_2_2_1 == 1
    print("  PASS: Under 1-indexed carries, each summand floor(n/p^j) - floor(k/p^j)")
    print("        - floor((n-k)/p^j) - carry_j(k, n-k) == 0 identically.")
    print(f"        Under 0-indexed carries, at (p,n,k)=(2,2,1) the sum is {shifted_sum_2_2_1} != 0.")

    # 3. Verify Clause 2 refutation: "holds ONLY WHEN p <= n - k" fails!
    print("\n[Check 3] Refuting 'LCM-expression holds ONLY WHEN p <= n - k' (p > n - k cases)...")
    # Case A: Fixed p = 2 at (n, k) = (3, 2), where 0 < k < n and n - k = 1 < 2 = p:
    p2_3_2 = all_lcm_parsings(2, 3, 2)
    assert padic_val(q_binom_prod(2, 3, 2), 2) == 0
    assert p2_3_2["LCM_1_floor_log_Q"] == 0
    assert p2_3_2["LCM_2_floor_logL_over_denom"] == 0
    assert p2_3_2["LCM_5_vp_L_minus_vp_nkfact"] == 0
    assert p2_3_2["LCM_6_fllogL_minus_vp_denom"] == 0
    assert p2_3_2["LCM_8_vp_classic_binom"] == 0
    print(f"  (p, n, k) = (2, 3, 2) [n-k = 1 < p = 2]: v_2([3 choose 2]_2) = 0,")
    print(f"    LCM_1 = {p2_3_2['LCM_1_floor_log_Q']}, LCM_2 = {p2_3_2['LCM_2_floor_logL_over_denom']} (both equal 0 despite p > n - k!).")

    # Case B: Infinite family (p, n, k) = (p, 2, 1) for every odd prime p >= 3:
    for p in primes[1:]:  # all odd primes in list: 3, 5, ..., 31
        assert not (p <= 2 - 1)
        assert padic_val(q_binom_prod(p, 2, 1), p) == 0
        vals = all_lcm_parsings(p, 2, 1)
        for name, val in vals.items():
            assert val == 0, f"Unexpected nonzero for {name} at p={p}: {val}"
    print(f"  Infinite family (p, 2, 1) tested for odd primes {primes[1:]}:")
    print("    0 < k < n, n - k = 1 < p (so p <= n - k is FALSE), yet ALL 8 parsings")
    print("    LCM_1 .. LCM_8 equal 0 == v_p([2 choose 1]_p)!")

    # 4. Verify converse failure: even WHEN p <= n - k (with 0 < k < n), LCM-expression != 0!
    print("\n[Check 4] Refuting converse 'LCM-expression holds WHEN p <= n - k' (p <= n - k cases)...")
    c_2_3_1 = all_lcm_parsings(2, 3, 1)
    c_2_4_1 = all_lcm_parsings(2, 4, 1)
    assert c_2_3_1["LCM_2_floor_logL_over_denom"] == 1 != 0
    for key in [
        "LCM_1_floor_log_Q",
        "LCM_3_floor_log_over_nkfact",
        "LCM_4_vp_L_minus_vp_denom",
        "LCM_5_vp_L_minus_vp_nkfact",
        "LCM_6_fllogL_minus_vp_denom",
        "LCM_7_fllogL_minus_vp_nkfact",
        "LCM_8_vp_classic_binom",
    ]:
        assert c_2_4_1[key] != 0, f"Expected nonzero for {key} at (2,4,1)"
    print(f"  (p, n, k) = (2, 3, 1) [p=2 <= n-k=2]: {c_2_3_1}")
    print(f"  (p, n, k) = (2, 4, 1) [p=2 <= n-k=3]: {c_2_4_1}")

    # Infinite family (p, 2p, 1) for odd primes p >= 3:
    for p in primes[1:8]:
        n, k = 2 * p, 1
        assert p <= n - k
        L = lcm_interval(2, 2 * p)
        denom = math.factorial(2 * p - 1)
        assert L <= denom // 2 < denom
        vals = all_lcm_parsings(p, n, k)
        assert vals["LCM_1_floor_log_Q"] <= -1 < 0
    print(f"  Infinite family (p, 2p, 1) tested for odd primes {primes[1:8]}:")
    print("    p <= 2p - 1 = n - k holds, yet LCM(2..2p) <= (2p-1)!/2 < 1!(2p-1)!,")
    print("    so LCM_1(p, 2p, 1) <= -1 != 0 == v_p([2p choose 1]_p).")

    print("\nALL VERIFICATION CHECKS PASSED.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
