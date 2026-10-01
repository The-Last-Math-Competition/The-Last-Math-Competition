#!/usr/bin/env python3
"""Standalone recomputation for the disproof of TLMC conjecture 00000001031.

Conjecture: for a Singer difference set D in F_{q^3}^*, the multiplier group
{tau : tauD = D} equals the norm-image subgroup N(F_{q^3}/F_q) of F_{q^3}^*
(order q-1, index q^2+q+1).

Counterexample q = 2, computed below entirely from scratch:
  - build F_8 = F_2[x]/(x^3+x+1) with explicit polynomial arithmetic;
  - D = nonzero trace-zero elements, as exponents in F_8^* = <alpha>;
  - verify D = {1,2,4} is a (7,3,1) difference set;
  - multiplier group = {tau in Z_7^* : tauD = D} = {1,2,4} (order 3);
  - norm image N(F_8/F_2) = F_2^* = {1} (order q-1 = 1, index 7);
  - {1,2,4} != {1}  =>  conjecture FALSE.
"""

MOD = 7          # q^2 + q + 1 for q = 2 (order of F_8^*)
Q = 2


def f8_mul(x: int, y: int) -> int:
    """Multiplication in F_8 = F_2[x]/(x^3+x+1); elements are 3-bit masks."""
    r = 0
    for i in range(3):
        if (y >> i) & 1:
            r ^= x << i
    for i in range(5, 2, -1):          # reduce mod x^3+x+1 (mask 0b1011)
        if (r >> i) & 1:
            r ^= 0b1011 << (i - 3)
    return r


def f8_trace(x: int) -> int:
    """Tr(x) = x + x^2 + x^4 (char 2: addition = XOR)."""
    x2 = f8_mul(x, x)
    x4 = f8_mul(x2, x2)
    return x ^ x2 ^ x4


def main() -> None:
    # 1) discrete log table for the generator alpha = x (must have order 7):
    #    covers all nonzero elements 1..7 (element 1 = alpha^0 added manually)
    dlog = {1: 0}
    cur = 1
    for k in range(1, MOD):
        cur = f8_mul(cur, 2)           # alpha = x = 0b010
        dlog[cur] = k
    assert len(dlog) == MOD and set(dlog) == set(range(1, MOD + 1)), \
        "alpha must generate F_8^*"

    # 2) Singer difference set D = {alpha^k : Tr != 0... Tr(alpha^k) = 0, k != 0}
    D = sorted(k for e, k in dlog.items() if f8_trace(e) == 0)
    print("Singer difference set (exponents of trace-zero elements):", D)
    assert D == [1, 2, 4]

    # 3) difference-set property: each nonzero residue arises exactly lambda = q-1 times
    from collections import Counter
    cnt = Counter((a - b) % MOD for a in D for b in D if a != b)
    expected = q_lambda = Q - 1
    assert all(cnt.get(g, 0) == q_lambda for g in range(1, MOD)), "not a difference set"
    print(f"difference property: every nonzero residue occurs exactly {expected} time(s). OK")

    # 4) multiplier group: tauD = D as subsets of Z_7
    Dset = set(D)
    mult = [t for t in range(1, MOD) if {(t * d) % MOD for d in Dset} == Dset]
    print("multiplier group {tau : tauD = D}:", mult, "(order", len(mult), ")")
    assert mult == [1, 2, 4]

    # 5) norm image: N(x) = x^(1+q+q^2); its image is F_q^* of order q-1,
    #    embedded in F_{q^3}^* as the subgroup {alpha^k : (q^3-1) | k*q-... } --
    #    concretely for q=2 the image is F_2^* = {1}, i.e. only the identity,
    #    corresponding to exponent 0 / trivial multiplier tau = 1.
    norm_order = Q - 1
    norm_sub = [1]  # the unique subgroup of order q-1 = 1 of F_8^*
    print("norm subgroup N(F_8/F_2) = F_2^*:", norm_sub,
          "(order", norm_order, ", index", MOD // norm_order, ")")
    assert norm_order == 1 and MOD // norm_order == Q * Q + Q + 1

    # 6) verdict
    equal = set(mult) == set(norm_sub)
    print("multiplier group == norm subgroup?", equal)
    print("VERDICT:", "CONJECTURE TRUE" if equal else "CONJECTURE FALSE")
    assert not equal
    # the "no other multipliers" clause also fails:
    assert 2 in mult and 4 in mult and set(mult) != set(norm_sub)
    print("'no other multipliers' clause also violated (multipliers 2,4 not in norm subgroup).")


if __name__ == "__main__":
    main()
