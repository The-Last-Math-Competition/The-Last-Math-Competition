#!/usr/bin/env python3
# Robustness check: same exact moment recursion with an alternative toll t(n) for C_n (n>=2).
# Variants: toll n-1 (main model), n+1 (Knuth-style), n (pivot counted once more).
from fractions import Fraction as F
import math


def run(tollfn, N=12):
    M = [(F(0),) * 3, (F(0),) * 3]
    for n in range(2, N + 1):
        a = tollfn(n)
        s = [F(0)] * 3
        for j in range(n):
            x1, x2, x3 = M[j]
            y1, y2, y3 = M[n - 1 - j]
            z1 = x1 + y1
            z2 = x2 + 2 * x1 * y1 + y2
            z3 = x3 + 3 * x2 * y1 + 3 * x1 * y2 + y3
            s[0] += a + z1
            s[1] += a * a + 2 * a * z1 + z2
            s[2] += a ** 3 + 3 * a * a * z1 + 3 * a * z2 + z3
        M.append(tuple(v / n for v in s))
    return [m3 - 3 * m1 * m2 + 2 * m1 ** 3 for m1, m2, m3 in M]


L = math.log
for name, t in [("n-1", lambda n: n - 1), ("n+1", lambda n: n + 1), ("n", lambda n: n)]:
    k = run(t)
    f2 = float(k[2]) - 4 + 6 * L(2)
    f3 = float(k[3]) - 6 + 6 * L(3)
    print(name, "k2=", k[2], "k3=", k[3], "k4=%.6f" % float(k[4]),
          "| natlog C2=%.6f C3=%.6f differ=%s" % (f2, f3, abs(f2 - f3) > 1e-9),
          "| f(12)=%.3f" % (float(k[12]) - (24 - 6 * L(12))))
