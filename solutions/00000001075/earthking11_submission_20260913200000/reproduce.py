#!/usr/bin/env python3
"""Reproduce the disproof of conjecture 00000001075.

    Definition: the entropic uncertainty principle for the finite-field
                Fourier transform states #supp(f) + #supp(f_hat) >= q + 1.
    Conjecture: equality holds exactly for Fourier translates of affine
                functions a*x + b (support pairs of q and 1), and no other
                equality configurations exist.

Counterexample (q = 5): f = delta_0 - delta_1 on Z/5, i.e. f = (1,-1,0,0,0).

  * #supp(f) = 2.
  * f_hat(xi) = sum_x f(x) omega^(xi*x) = 1 - omega^xi.  Since omega has order
    5, 1 - omega^xi = 0 only for xi = 0, so #supp(f_hat) = 4.
  * Therefore #supp(f) + #supp(f_hat) = 6 = 5 + 1: this is an equality
    configuration, with support pair (2,4), not the claimed (5,1).
  * f is not a time-frequency translate of any affine function: a nonzero
    affine function a*x+b with a != 0 on Z/5 has exactly one zero, a nonzero
    constant has none, and f has three zeros (x = 2,3,4); translation permutes
    the domain and modulation multiplies by a unit, so both preserve the zero
    set.  Exhaustive check over all 5^4 = 625 tuples (a,b,alpha,beta).
  * Enumerating all f : Z/5 -> {0,+-1} (3^5 = 243 functions) there are exactly
    32 equality configurations: 10 of type (1,5), 20 of type (2,4) and 2 of
    type (5,1).  None of the 20 of type (2,4) is a time-frequency translate of
    an affine function, so the clause "no other equality configurations exist"
    fails, and so does the parenthetical "(support pairs of q and 1)".

Context: the premise #supp(f) + #supp(f_hat) >= q + 1 is false in general (it
fails for q = 4 and q = 6; a subgroup indicator of size p^(k-1) in F_{p^k}
gives p^(k-1) + p < p^k + 1 for k >= 2).  It holds for prime q, which is why
the counterexample is taken over F_5 = Z/5.

Exact arithmetic in Z[omega] = Z[x]/(x^4+x^3+x^2+x+1).  Elements are integer
4-tuples (c0,c1,c2,c3) standing for c0 + c1*omega + c2*omega^2 + c3*omega^3,
with omega^4 = -(1 + omega + omega^2 + omega^3).  Standard library only, no
sympy, no floating point.  Prints PASS/FAIL and exits non-zero on failure.
"""

from itertools import product


# ---------------------------------------------------------------------------
# exact arithmetic in Z[omega]
# ---------------------------------------------------------------------------

ZERO = (0, 0, 0, 0)
ONE = (1, 0, 0, 0)
W = (0, 1, 0, 0)          # omega


def add(a, b):
    return (a[0] + b[0], a[1] + b[1], a[2] + b[2], a[3] + b[3])


def neg(a):
    return (-a[0], -a[1], -a[2], -a[3])


def mul(a, b):
    """Multiplication in Z[omega], reduced with omega^4 = -1-w-w^2-w^3.

    With r0..r6 the plain convolution coefficients, omega^4 = -(1+w+w^2+w^3)
    gives omega^5 = 1 and omega^6 = omega, so the reduced tuple is
    (r0 - r4 + r5, r1 - r4 + r6, r2 - r4, r3 - r4).
    """
    r = [0] * 7
    for i, ai in enumerate(a):
        for j, bj in enumerate(b):
            r[i + j] += ai * bj
    r0, r1, r2, r3, r4, r5, r6 = r
    return (r0 - r4 + r5, r1 - r4 + r6, r2 - r4, r3 - r4)


def scalar(n):
    return (n, 0, 0, 0)


def wpow(k):
    """omega^k for k >= 0, using the order-5 relation."""
    k %= 5
    if k == 0:
        return ONE
    if k == 1:
        return W
    if k == 2:
        return mul(W, W)
    if k == 3:
        return mul(W, mul(W, W))
    return (-1, -1, -1, -1)     # omega^4 = -(1+w+w^2+w^3)


def sum_q4(terms):
    acc = ZERO
    for t in terms:
        acc = add(acc, t)
    return acc


def dft_int(f):
    """DFT of an integer-valued f : Z/5 -> Z, returned as five Z[omega] values."""
    return tuple(
        sum_q4(mul(scalar(f[x]), wpow(xi * x)) for x in range(5))
        for xi in range(5)
    )


def dft_q4(f):
    """DFT of a Z[omega]-valued f, returned as five Z[omega] values."""
    return tuple(
        sum_q4(mul(f[x], wpow(xi * x)) for x in range(5))
        for xi in range(5)
    )


# ---------------------------------------------------------------------------
# supports
# ---------------------------------------------------------------------------

def supp_int(f):
    return sum(1 for v in f if v != 0)


def supp_q4(g):
    return sum(1 for v in g if v != ZERO)


# ---------------------------------------------------------------------------
# the witness and the affine family
# ---------------------------------------------------------------------------

WITNESS = (1, -1, 0, 0, 0)                       # delta_0 - delta_1


def affine_q4(a, b):
    """x |-> a*x + b on Z/5, embedded in Z[omega]."""
    return tuple(scalar((a * x + b) % 5) for x in range(5))


def tf_trans(h, alpha, beta):
    """Time-frequency translate x |-> omega^(beta*x) * h(x + alpha)."""
    return tuple(mul(wpow(beta * x), h[(x + alpha) % 5]) for x in range(5))


def is_scalar_of(v, f):
    """True if the Z[omega] vector v is scalar*(f), i.e. v[i] = scalar(f[i])."""
    return all(v[i] == scalar(f[i]) for i in range(5))


# ---------------------------------------------------------------------------
# context: the premise fails for q = p^k, k >= 2 (worked out over F_4)
# ---------------------------------------------------------------------------

# F_4 = F_2[t]/(t^2+t+1), encoded 0,1,2,3 for 0,1,t,t+1.  Addition is xor;
# multiplication from t^2 = t+1.
F4_MUL = {
    (0, 0): 0, (0, 1): 0, (0, 2): 0, (0, 3): 0,
    (1, 0): 0, (1, 1): 1, (1, 2): 2, (1, 3): 3,
    (2, 0): 0, (2, 1): 2, (2, 2): 3, (2, 3): 1,
    (3, 0): 0, (3, 1): 3, (3, 2): 1, (3, 3): 2,
}


def f4_trace(z):
    """Trace F_4 -> F_2, tr(z) = z + z^2."""
    z2 = F4_MUL[(z, z)]
    return z ^ z2


def f4_character(xi, x):
    """Additive character x |-> (-1)^tr(xi*x), integer valued."""
    return -1 if f4_trace(F4_MUL[(xi, x)]) else 1


def context_q4():
    """Indicator of the subgroup {0,1} of F_4 has #supp + #supp(f_hat) = 4 < 5."""
    f = tuple(1 if x in (0, 1) else 0 for x in range(4))
    fhat = tuple(
        sum(f4_character(xi, x) * f[x] for x in range(4))
        for xi in range(4)
    )
    return supp_int(f), supp_int(fhat)


# ---------------------------------------------------------------------------
# checks
# ---------------------------------------------------------------------------

def main():
    checks = []

    def check(name, ok, detail):
        checks.append((name, ok, detail))

    # --- the witness ------------------------------------------------------
    fhat = dft_int(WITNESS)
    s_f = supp_int(WITNESS)
    s_fh = supp_q4(fhat)

    check("witness #supp(f) == 2", s_f == 2,
          "f = (1,-1,0,0,0) = delta_0 - delta_1")
    check("witness #supp(f_hat) == 4", s_fh == 4,
          "f_hat(xi) = 1 - omega^xi vanishes only at xi = 0")
    check("witness attains equality #supp(f) + #supp(f_hat) == 6 == q + 1",
          s_f + s_fh == 6, f"{s_f} + {s_fh} = {s_f + s_fh} = 5 + 1")
    check("witness support pair is (2,4), not the claimed (5,1)",
          (s_f, s_fh) == (2, 4),
          f"observed pair ({s_f},{s_fh})")
    check("explicit transform values f_hat = (0, 1-w, 1-w^2, 1-w^3, 1-w^4)",
          fhat == (ZERO, (1, -1, 0, 0), (1, 0, -1, 0), (1, 0, 0, -1),
                   (2, 1, 1, 1)),
          f"f_hat = {fhat}")

    # --- the witness is not a time-frequency translate of an affine map ----
    affine_hit = None
    affine_dft_hit = None
    for a in range(5):
        for b in range(5):
            h = affine_q4(a, b)
            for alpha in range(5):
                for beta in range(5):
                    t = tf_trans(h, alpha, beta)
                    if is_scalar_of(t, WITNESS):
                        affine_hit = (a, b, alpha, beta)
                    # DFT of the translate, pointwise against the witness
                    if is_scalar_of(dft_q4(t), WITNESS):
                        affine_dft_hit = (a, b, alpha, beta)
    check("no time-frequency translate of any affine function equals the witness",
          affine_hit is None,
          "exhaustive over 5^4 = 625 tuples (a,b,alpha,beta)")
    check("no DFT of a time-frequency translate of an affine function equals the witness",
          affine_dft_hit is None,
          "exhaustive over 5^4 = 625 tuples (a,b,alpha,beta)")

    # zero-count reason, made concrete
    zero_sets = {}
    for a in range(5):
        for b in range(5):
            zs = tuple(sorted(x for x in range(5) if (a * x + b) % 5 == 0))
            zero_sets.setdefault(len(zs), 0)
            zero_sets[len(zs)] = zero_sets[len(zs)] + 1
    check("affine functions on Z/5 have 1 zero (a != 0), 0 zeros (a = 0, b != 0),"
          " or 5 zeros (the zero map)",
          zero_sets == {0: 4, 1: 20, 5: 1},
          f"zero-count histogram over 25 affine maps: {zero_sets}")
    check("the witness has 3 zeros", supp_int(WITNESS) == 2,
          "zeros at x = 2,3,4, a count no affine function can have")

    # --- enumeration of all 243 functions Z/5 -> {0,+-1} -------------------
    by_pair = {}
    all_functions = list(product((-1, 0, 1), repeat=5))
    min_sum = None
    min_sum_nonzero = None
    for g in all_functions:
        total = supp_int(g) + supp_q4(dft_int(g))
        min_sum = total if min_sum is None else min(min_sum, total)
        if supp_int(g) != 0:
            min_sum_nonzero = (
                total if min_sum_nonzero is None else min(min_sum_nonzero, total)
            )
        if total == 6:
            by_pair.setdefault((supp_int(g), supp_q4(dft_int(g))), []).append(g)

    expected_pairs = {(1, 5): 10, (2, 4): 20, (5, 1): 2}
    observed_pairs = {k: len(v) for k, v in by_pair.items()}
    total_eq = sum(observed_pairs.values())

    check("there are 3^5 = 243 functions Z/5 -> {0,+-1}",
          len(all_functions) == 243, f"enumerated {len(all_functions)}")
    check("uncertainty bound #supp(f) + #supp(f_hat) >= 6 holds for every nonzero f",
          min_sum_nonzero == 6,
          f"minimum over the 242 nonzero functions is {min_sum_nonzero} "
          f"(the zero function gives {min_sum})")
    check("exactly 32 equality configurations", total_eq == 32,
          f"found {total_eq}")
    check("equality configurations split 10/20/2 by support pair (1,5)/(2,4)/(5,1)",
          observed_pairs == expected_pairs,
          f"observed {dict(sorted(observed_pairs.items()))}")

    # the 20 of type (2,4) are exactly +-(delta_p - delta_q) and not affine
    twenty = by_pair.get((2, 4), [])
    pair_forms = set()
    for g in twenty:
        zeros = [x for x in range(5) if g[x] == 0]
        pair_forms.add(tuple(zeros))
    not_affine = []
    for g in twenty:
        is_affine = False
        for a in range(5):
            for b in range(5):
                h = affine_q4(a, b)
                for alpha in range(5):
                    for beta in range(5):
                        if is_scalar_of(tf_trans(h, alpha, beta), g):
                            is_affine = True
        if not is_affine:
            not_affine.append(g)
    check("the 20 type-(2,4) configurations are +-(delta_p - delta_q), p != q",
          len(twenty) == 20
          and len(pair_forms) == 5 * 4 // 2
          and all(len(z) == 3 for z in pair_forms),
          f"10 unordered zero pairs {sorted(pair_forms)}, 2 signs each")
    check("none of the 20 type-(2,4) configurations is an affine translate",
          len(not_affine) == 20,
          f"{len(not_affine)} of {len(twenty)} are non-affine")

    # the other pairs are the affine family and its Fourier duals
    five_one = by_pair.get((5, 1), [])
    one_five = by_pair.get((1, 5), [])
    check("type (5,1) is the two nonzero constant functions (+-1)",
          set(five_one) == {(1, 1, 1, 1, 1), (-1, -1, -1, -1, -1)},
          f"{sorted(five_one)}")
    check("type (1,5) is the ten functions +-delta_p (Fourier duals of (5,1))",
          len(one_five) == 10
          and all(supp_int(g) == 1 for g in one_five),
          "5 points times 2 signs")

    # --- context: the premise itself fails for q = 4 ----------------------
    s_f4, s_fh4 = context_q4()
    check("context: for q = 4 a subgroup indicator gives 2 + 2 = 4 < 5 = q + 1",
          s_f4 + s_fh4 == 4 and s_f4 + s_fh4 < 5,
          f"#supp = {s_f4}, #supp(f_hat) = {s_fh4}, sum = {s_f4 + s_fh4}")

    # --- report -----------------------------------------------------------
    line = "=" * 74
    print(line)
    print("Disproof of conjecture 00000001075 -- reproduction")
    print(line)
    print()
    print("[1] The witness f = delta_0 - delta_1 on Z/5 and its transform")
    print(f"    f            = {WITNESS}")
    print(f"    f_hat        = {fhat}")
    print(f"    #supp(f)     = {s_f}")
    print(f"    #supp(f_hat) = {s_fh}")
    print(f"    sum          = {s_f + s_fh} = q + 1 with q = 5")
    print("    f_hat(xi) = 1 - omega^xi, nonzero for xi = 1,2,3,4.")
    print()
    print("[2] Not a Fourier translate of an affine function")
    print("    exhaustive over a,b,alpha,beta in Z/5 (625 tuples each) for")
    print("    the direct translate and for its transform: no match.")
    print("    zero counts: nonzero affine -> 1 zero; constant -> 0 zeros;")
    print("    witness -> 3 zeros (x = 2,3,4); translates preserve zeros.")
    print()
    print("[3] Enumeration of all 243 functions Z/5 -> {0,+-1}")
    print(f"    equality configurations (#supp + #supp(f_hat) = 6): {total_eq}")
    for k in sorted(observed_pairs):
        print(f"      support pair {k}: {observed_pairs[k]}")
    print("    the 20 of type (2,4) are +-(delta_p - delta_q) and none is")
    print("    an affine Fourier translate -> the conjecture's 'no other")
    print("    equality configurations exist' and '(support pairs of q and 1)'")
    print("    both fail.")
    print()
    print("[4] Checks")
    all_ok = True
    for name, ok, detail in checks:
        mark = "ok  " if ok else "FAIL"
        print(f"    [{mark}] {name}")
        print(f"           {detail}")
        all_ok = all_ok and ok
    print()
    print(line)
    if all_ok:
        print("PASS: the witness disproves conjecture 00000001075 as stated.")
        print("  eps: on F_5, #supp(f) + #supp(f_hat) = 2 + 4 = 6 = q + 1, and f")
        print("  is not a Fourier translate of any affine function; 32 equality")
        print("  configurations exist, 20 with support pair (2,4).")
        print(line)
        return 0
    print("FAIL: at least one claimed fact did not verify.")
    print(line)
    return 1


if __name__ == "__main__":
    raise SystemExit(main())
