#!/usr/bin/env python3
"""
Numerical refutation of TLMC conjecture 00000004412.

Claim (verbatim):
  "The characteristic function of the expected spectral measure is given
   explicitly by the logarithm of the Fredholm determinant of the kernel,
   and the determinant series converges iff the kernel is square integrable."

We model a graphon integral operator on a finite probability space of size m
as a real symmetric matrix K/m (uniform counting measure). For such an
operator:

  * the expected spectral measure is the empirical eigenvalue distribution
        mu = (1/m) sum_j delta_{lambda_j},
    whose characteristic function is
        phi(t) = (1/m) sum_j exp(i t lambda_j);
        in particular  phi(0) = 1   (probability normalization).

  * the Fredholm determinant is
        det(I - z T) = prod_j (1 - z lambda_j),
    and its logarithm is
        log det(I - z T) = -sum_{n>=1} z^n Tr(T^n)/n = sum_j log(1 - z lambda_j);
        in particular  log det(I - 0*T) = log 1 = 0.

Refutation A (normalization / value at zero):
  The conjectured identity  phi(t) = log det(I - t T)  fails already at
  t = 0: phi(0) = 1 but log det(I) = 0.  A characteristic function is
  always 1 at 0; a log-determinant is always 0 there.  No kernel can fix
  this -- the identity is false for every nonzero example.

Refutation B (boundedness):
  Any characteristic function satisfies |phi(t)| <= 1 for all real t,
  whereas Re log det(I - tT) = log|prod(1 - t lambda_j)| is unbounded
  above as |t| -> infinity when T has a nonzero eigenvalue.  So the two
  sides cannot be equal as functions even after the normalization issue.

Refutation C (the "iff square integrable" direction):
  The Fredholm series needs only the coefficient integrals
      a_n = (1/n!) int det[K(x_i,x_j)] dx_1..dx_n .
  For a rank-one kernel K(x,y) = u(x) v(y) every n x n determinant with
  n >= 2 vanishes, so the series collapses to the polynomial
      det(I - zT) = 1 - z ∫ u(x) v(x) dx,
  which converges (for all z) even when K is NOT square integrable.
  Concrete example on [0,1]:  u(x)=1, v(y)=y^{-3/4}.  Then
      ∫∫ K^2 = (∫1^2)(∫ y^{-3/2} dy) = +infinity   (not square integrable),
  yet the Fredholm series is the finite polynomial 1 - 4z.
  Hence "converges => square integrable" is false.
"""

import math
import cmath

def spectral_charfn(eig, t):
    """phi(t) = (1/m) sum exp(i t lambda_j) for the empirical spectral measure."""
    m = len(eig)
    return sum(cmath.exp(1j * t * lam) for lam in eig) / m

def fredholm_det(eig, z):
    """det(I - zT) = prod_j (1 - z lambda_j)."""
    out = 1.0 + 0j
    for lam in eig:
        out *= (1 - z * lam)
    return out

def fredholm_logdet_series(traces, z, N=None):
    """log det(I - zT) = -sum_{n>=1} z^n Tr(T^n)/n (first N terms)."""
    if N is None: N = len(traces)
    return -sum(z**n * traces[n-1] / n for n in range(1, N+1))

def main():
    print("=" * 70)
    print("TLMC 00000004412 -- numerical refutation")
    print("=" * 70)

    # A concrete finite graphon: block matrix of a 4-node weighted graph,
    # i.e. the integral operator on a 4-point probability space.
    # K/m acts on R^4; take a symmetric K.
    import random
    random.seed(4412)
    m = 4
    K = [[0.0]*m for _ in range(m)]
    for i in range(m):
        for j in range(i, m):
            K[i][j] = K[j][i] = random.uniform(-1.0, 1.0)
    # eigenvalues of T = K/m via characteristic polynomial power sums:
    # use Newton identities on power sums p_n = Tr(T^n).
    def matmul(A, B):
        return [[sum(A[i][k]*B[k][j] for k in range(m)) for j in range(m)] for i in range(m)]
    T = [[K[i][j]/m for j in range(m)] for i in range(m)]
    Tn = [[1.0 if i==j else 0.0 for j in range(m)] for i in range(m)]
    powers = []          # p_n = Tr T^n, n = 1..4
    for n in range(1, m+1):
        Tn = matmul(Tn, T)
        powers.append(sum(Tn[i][i] for i in range(m)))
    # Newton: e_1 = p1; 2e2 = e1 p1 - p2; 3e3 = e2 p1 - e1 p2 + p3; ...
    e = [0.0]*(m+1); e[0] = 1.0
    for n in range(1, m+1):
        s = sum(((-1)**(k-1)) * e[n-k] * powers[k-1] for k in range(1, n+1))
        e[n] = s / n
    # eigenvalues = roots of lambda^4 - e1 lambda^3 + e2 lambda^2 - e3 lambda + e4
    # (numeric, via numpy if present else Durand-Kerner)
    try:
        import numpy as np
        eig = list(np.roots([1, -e[1], e[2], -e[3], e[4]]).real)
    except Exception:
        # Durand-Kerner fallback
        coeffs = [1, -e[1], e[2], -e[3], e[4]]
        roots = [cmath.exp(2*cmath.pi*1j*k/m)*0.5 for k in range(m)]
        for _ in range(200):
            for i in range(m):
                denom = 1+0j
                for j in range(m):
                    if i != j:
                        denom *= roots[i]-roots[j]
                if denom == 0: denom = 1e-9
                val = coeffs[0]*roots[i]**4 + coeffs[1]*roots[i]**3 + coeffs[2]*roots[i]**2 + coeffs[3]*roots[i] + coeffs[4]
                roots[i] -= val/denom
        eig = [r.real for r in roots]
    print("kernel K (symmetric 4x4) eigenvalues of T=K/4:")
    print("   lambda =", [round(l,6) for l in eig])
    print("   Tr T   =", round(sum(eig),6), "   check Tr K/m =", round(sum(K[i][i] for i in range(m))/m,6))

    # ---- Refutation A: value at t = 0 --------------------------------------
    phi0 = spectral_charfn(eig, 0.0)
    logdet0 = cmath.log(fredholm_det(eig, 0.0))
    print("\n[A] t = 0:")
    print("   characteristic function phi(0) =", phi0)
    print("   log Fredholm determinant  log det(I - 0*T) =", logdet0)
    assert abs(phi0 - 1) < 1e-12, "phi(0) must equal 1"
    assert abs(logdet0 - 0) < 1e-12, "log det(I) must equal 0"
    print("   phi(0) = 1  !=  0 = log det(I)  => identity fails at t=0")

    # ---- Refutation B: boundedness vs unboundedness ------------------------
    print("\n[B] boundedness: |phi(t)| <= 1 always; Re log det grows")
    for t in [1.0, 5.0, 20.0]:
        phi = spectral_charfn(eig, t)
        ld  = cmath.log(fredholm_det(eig, t))
        print(f"   t={t:5.1f}:  |phi(t)| = {abs(phi):.4f}   "
              f"Re log det(I-tT) = {ld.real:+.4f}   "
              f"phi={phi.real:+.3f}{phi.imag:+.3f}i")
    # compare to log-det series
    ld_series = fredholm_logdet_series(powers, 0.3)
    ld_exact  = cmath.log(fredholm_det(eig, 0.3))
    print(f"   check: log det series at z=0.3 = {ld_series:.6f}, "
          f"exact = {ld_exact:.6f}  (series converges for small z)")

    # ---- Refutation C: non-L2 kernel with convergent Fredholm series --------
    print("\n[C] rank-one kernel K(x,y)=y^{-3/4} on [0,1]:")
    # numeric quadrature
    # v(y) = y^-3/4;  ∫v = 4 exactly, ∫v^2 = ∫y^-3/2 dy = +inf
    # midpoint-rule quadrature on 2e6 points
    steps = 2_000_000
    sv = sv2 = 0.0
    for i in range(steps):
        y = (i+0.5)/steps
        sv  += y**-0.75
        sv2 += y**-1.5
    sv *= 1.0/steps; sv2 *= 1.0/steps
    print(f"   ∫_0^1 v(y) dy     ≈ {sv:.4f}   (exact = 4)")
    print(f"   ∫_0^1 v(y)^2 dy   ≈ {sv2:.1f}   (grows like 2/sqrt(h), diverges)")
    print(f"   ∫∫ |K|^2 = ∫u^2 ∫v^2 = 1 * inf = +inf  => kernel NOT square integrable")
    print(f"   but rank-one => det[K(x_i,x_j)] = 0 for n>=2,")
    print(f"   Fredholm series = 1 - z*∫∫K = 1 - {4}z  -- a polynomial, converges")
    print(f"   => 'converges => square integrable' is FALSE")

    print("\n" + "=" * 70)
    print("REFUTED: part (a) fails at t=0 (phi=1 vs log det=0) and by")
    print("boundedness; part (b) 'only if' fails on a rank-one non-L2 kernel.")
    print("VERDICT:REFUTED")
    print("=" * 70)

if __name__ == "__main__":
    main()
