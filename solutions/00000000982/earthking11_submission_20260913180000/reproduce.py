#!/usr/bin/env python3
"""Numerical verification for the disproof of conjecture 00000000982.

Conjecture: "Fixed points of the Berezin transform on Fock space are radial
functions, and the cardinality of the fixed-point set is at most 2."

On the Fock space with the Gaussian measure (1/pi) e^{-|w|^2} dA(w), the
(diagonal) Berezin transform is the Gaussian convolution

    B f(z) = (1/pi) * integral_C f(w) e^{-|w-z|^2} dA(w)
           = (1/pi) * integral_C f(z+u) e^{-|u|^2} dA(u)          (u = w - z)

which equals e^{Delta/4} f(z).  In particular it fixes every harmonic function,
hence every holomorphic function in F^2.

We evaluate the two-dimensional integral by tensor Gauss-Hermite quadrature,
which is exact for polynomials of degree <= 2n-1 in each variable.  For an
entire f the Taylor expansion plus the Gaussian moments

    (1/pi) * integral u^m conj(u)^k e^{-|u|^2} dA(u) = m! * delta_{m,k}

gives  B f(z) = sum_m (d_z^m d_zbar^m f)(z) / m!  = e^{Delta/4} f(z).

Checks:
  (i)   B(1)   = 1,
  (ii)  B(z)   = z,
  (iii) B(z^2) = z^2  and B(z^3) = z^3,
  (iv)  z is not radial: |1| = |i| = 1 but z(1) = 1 != i = z(i),
plus cross-checks that a non-holomorphic harmonic function (z + zbar) is fixed
and that a non-harmonic function (|z|^2) is not fixed.

Standard library only; numpy is not required (a pure-Python Gauss-Hermite
routine is included).  Exits 0 regardless of the verdict.
"""

import cmath
import math
import sys

# ---------------------------------------------------------------------------
# Gauss-Hermite quadrature nodes/weights for the weight e^{-x^2} on (-inf,inf)
# ---------------------------------------------------------------------------

def _hermite_pair(n, x):
    """Return (H_n(x), H_{n-1}(x)) for the physicists' Hermite polynomials."""
    if n == 0:
        return 1.0, 0.0
    h_prev, h = 1.0, 2.0 * x  # H_0, H_1
    for k in range(1, n):
        h_prev, h = h, 2.0 * x * h - 2.0 * k * h_prev
    return h, h_prev


def gauss_hermite(n):
    """Nodes x_i and weights w_i with sum_i w_i g(x_i) ~ integral g e^{-x^2}.

    The roots of H_n are located by scanning for sign changes and bisecting;
    this is robust (unlike naive Newton from the crude edge asymptotics) and
    keeps the script pure standard library.
    """
    reach = math.sqrt(2.0 * n + 1.0) + 1.5
    step = 0.01
    nodes = []
    x = -reach
    _, _ = _hermite_pair(n, x)
    prev_h, _ = _hermite_pair(n, x)
    while x < reach:
        x_new = min(x + step, reach)
        h_new, _ = _hermite_pair(n, x_new)
        if (prev_h < 0.0) != (h_new < 0.0):
            lo, hi, hlo = x, x_new, prev_h
            for _ in range(100):
                mid = 0.5 * (lo + hi)
                hm, _ = _hermite_pair(n, mid)
                if (hm < 0.0) == (hlo < 0.0):
                    lo = mid
                else:
                    hi = mid
            nodes.append(0.5 * (lo + hi))
        x, prev_h = x_new, h_new

    weights = []
    for r in nodes:
        _, hn1 = _hermite_pair(n, r)
        w = (2.0 ** (n - 1) * math.factorial(n) * math.sqrt(math.pi)
             / (n * n * hn1 * hn1))
        weights.append(w)
    return nodes, weights


NQ = 40  # exact for polynomials of degree <= 79 in each variable
NODES, WEIGHTS = gauss_hermite(NQ)


def berezin(f, z):
    """B f(z) = (1/pi) * integral f(z+u) e^{-|u|^2} dA(u) by tensor quadrature."""
    total = 0j
    for xi, wi in zip(NODES, WEIGHTS):
        for xj, wj in zip(NODES, WEIGHTS):
            total += wi * wj * f(z + complex(xi, xj))
    return total / math.pi


# ---------------------------------------------------------------------------
# Checks
# ---------------------------------------------------------------------------

def main():
    points = [0 + 0j, 1 + 0j, 1 + 1j, 0.5 - 0.7j, -1.3 + 0.9j]

    # (i)-(iii): B fixes 1, z, z^2, z^3 (all holomorphic, hence harmonic).
    fixed = [
        (r"B(1) = 1", lambda w: 1 + 0j, lambda z: 1 + 0j),
        (r"B(z) = z", lambda w: w, lambda z: z),
        (r"B(z^2) = z^2", lambda w: w * w, lambda z: z * z),
        (r"B(z^3) = z^3", lambda w: w ** 3, lambda z: z ** 3),
        (r"B(z+zbar) = z+zbar  [harmonic, non-holomorphic]",
         lambda w: w + w.conjugate(), lambda z: z + z.conjugate()),
    ]

    print("Berezin transform B f(z) = (1/pi) * integral f(z+u) e^{-|u|^2} dA(u)")
    print("Gauss-Hermite quadrature: %d nodes per dimension (tensor grid %d points)"
          % (NQ, NQ * NQ))
    print("Test points z:", ", ".join("%g%+gi" % (z.real, z.imag) for z in points))
    print()

    max_err = 0.0
    all_ok = True
    for name, f, fref in fixed:
        err = 0.0
        for z in points:
            err = max(err, abs(berezin(f, z) - fref(z)))
        max_err = max(max_err, err)
        ok = err < 1e-10
        all_ok = all_ok and ok
        print("  %-46s max |B f(z) - f(z)| = %.3e  %s"
              % (name, err, "PASS" if ok else "FAIL"))

    # Cross-check: |z|^2 = z zbar is NOT harmonic, and B(|w|^2) = |z|^2 + 1.
    err_nonfixed = 0.0
    for z in points:
        err_nonfixed = max(err_nonfixed,
                           abs(berezin(lambda w: abs(w) ** 2, z) - (abs(z) ** 2 + 1)))
    ok_nonfixed = err_nonfixed < 1e-10
    all_ok = all_ok and ok_nonfixed
    print("  %-46s max |B|z|^2 - (|z|^2+1)| = %.3e  %s"
          % (r"B(|z|^2) = |z|^2 + 1  [not fixed: non-harmonic]",
             err_nonfixed, "PASS" if ok_nonfixed else "FAIL"))

    # (iv): z is not radial.
    print()
    p, q = 1 + 0j, 0 + 1j
    same_modulus = abs(abs(p) - abs(q)) < 1e-15
    values_differ = (p != q)
    ok_radial = same_modulus and values_differ
    all_ok = all_ok and ok_radial
    print("Non-radiality of z (f(z) = z):")
    print("  |1| = %.15g, |i| = %.15g, equal: %s" % (abs(p), abs(q), same_modulus))
    print("  z(1) = %g, z(i) = %gi, differ: %s" % (p.real, q.imag, values_differ))
    print("  ==> z is NOT radial (equal modulus, unequal values): %s"
          % ("PASS" if ok_radial else "FAIL"))

    print()
    print("Maximum error over all fixed-point checks: %.3e" % max_err)
    print("Threshold: 1e-10")
    if all_ok:
        print("PASS: B fixes every holomorphic function tested; z is a non-radial")
        print("      fixed point, so the fixed set is neither radial nor of size <= 2.")
    else:
        print("FAIL: a numerical check exceeded its threshold.")

    # The conjecture is refuted; exit 0 either way as required.
    return 0


if __name__ == "__main__":
    sys.exit(main())
