#!/usr/bin/env python3
"""
Target E: 00000001619
  "The Fredholm determinant det(I - tK) of the kernel K(x,y) = e^{-xy} is
   defined on L^2(0,inf); conjecture det(I - tK) = e^{-t^2/4}."

Target F: 00000001668
  "chi_c(G(n,k)) = 3 when n = 0 mod 3 and k = 1 mod 3, and 4 otherwise."
"""
import numpy as np

print("=" * 74)
print("E. 00000001619 - Fredholm determinant of the kernel e^{-xy}")
print("=" * 74)

print("  K(x,y) = e^{-xy} on L^2(0,inf), symmetric and bounded (it is the")
print("  Laplace transform, of norm sqrt(pi) = 1.7725).")
print()
print("  The Fredholm determinant det(I - tK) exists only for a trace-class")
print("  operator. Trace class implies Hilbert-Schmidt, which requires")
print("  int int |K|^2 < inf. Compute:")
print()
print("      int_0^inf int_0^inf e^{-2xy} dx dy")
print("        = int_0^inf [ 1/(2y) ] dy")
print("        = +inf")
print()
print("  The divergence comes from y -> 0: the kernel is unbounded on the")
print("  diagonal. Truncating to [0,L]^2 makes the integral finite but it")
print("  diverges like ln L:")
print()
print(f"  {'L':>6} {'int_[0,L]^2 |K|^2':>18} {'ln L + 0.7':>12}")
for L in (5, 10, 20, 40, 80, 160, 320):
    y = np.linspace(1e-13, L, 800001)
    val = np.trapezoid((1 - np.exp(-2 * L * y)) / (2 * y), y)
    print(f"  {L:>6} {val:>18.4f} {np.log(L) + 0.7:>12.4f}")
print("  (each doubling of L adds about ln 2 = 0.693)")
print()
print("  So K is not Hilbert-Schmidt, hence not trace class, hence")
print("  det(I - tK) is not defined. The asserted value e^{-t^2/4} is not a")
print("  quantity that exists.")
print()
print("  Independent corroboration that the operator has no eigenvalues:")
print("  applying K twice gives")
print("      (K^2 f)(x) = int_0^inf f(y) [ int_0^inf e^{-z(x+y)} dz ] dy")
print("                 = int_0^inf f(y)/(x+y) dy,")
print("  i.e. K^2 is the Carleman operator with kernel 1/(x+y), whose spectrum")
print("  on L^2(0,inf) is the purely continuous interval [0,pi]. K^2 therefore")
print("  has no eigenvalues, so neither does K.")
print()
print("  NOTE ON METHOD: a naive discretisation of K does NOT demonstrate this")
print("  reliably - the kernel is unbounded on the diagonal and the matrix is")
print("  severely ill-conditioned, so finite-matrix eigenvalues are not")
print("  trustworthy here. The argument above is analytic, not numerical.")

print()
print("=" * 74)
print("F. 00000001668 - circular chromatic number of G(n,k)")
print("=" * 74)


def petersen(n, k):
    """Generalized Petersen graph G(n,k): outer n-cycle, inner step-k cycle,
    spokes joining i to i'."""
    adj = {i: set() for i in range(2 * n)}
    for i in range(n):
        adj[i].add((i + 1) % n)
        adj[(i + 1) % n].add(i)
        adj[n + i].add(n + (i + k) % n)
        adj[n + (i + k) % n].add(n + i)
        adj[i].add(n + i)
        adj[n + i].add(i)
    return adj


def chromatic(adj):
    verts = sorted(adj, key=lambda v: -len(adj[v]))
    col = {}

    def rec(i, k):
        if i == len(verts):
            return True
        v = verts[i]
        banned = {col[u] for u in adj[v] if u in col}
        for c in range(k):
            if c not in banned:
                col[v] = c
                if rec(i + 1, k):
                    return True
                del col[v]
        return False

    k = 1
    while not rec(0, k):
        k += 1
    return k


def pq_colorable(adj, p, q, budget=[0]):
    """A (p,q)-colouring maps V -> Z_p with circular edge distance in [q,p-q]."""
    verts = sorted(adj, key=lambda v: -len(adj[v]))
    col = {}

    def ok(cu, cv):
        d = abs(cu - cv)
        d = min(d, p - d)
        return q <= d <= p - q

    def rec(i):
        budget[0] += 1
        if budget[0] > 3_000_000:
            raise TimeoutError
        if i == len(verts):
            return True
        v = verts[i]
        for c in range(p):
            if all(ok(c, col[u]) for u in adj[v] if u in col):
                col[v] = c
                if rec(i + 1):
                    return True
                del col[v]
        return False

    return rec(0)


def circ_chromatic(adj, chi, qmax=6):
    best = float(chi)
    for q in range(1, qmax + 1):
        for p in range(q * (chi - 1) + 1, q * chi + 1):
            if p <= 0 or p / q >= best:
                continue
            budget = [0]
            try:
                if pq_colorable(adj, p, q, budget):
                    best = p / q
            except TimeoutError:
                pass
    return best


# Phase 1: ordinary chromatic number over a wide range. Since chi_c <= chi
# always, any case with chi <= 3 and "conjecture says 4" is already refuted.
print("  Phase 1 - ordinary chromatic number (chi_c <= chi, so chi <= 3 < 4")
print("  refutes every 'conjecture says 4' case).")
print()
print(f"  {'n':>3} {'k':>3} {'|V|':>4} {'chi':>4} {'conj says':>10}  verdict")
refuted = []
for n in range(5, 21):
    for k in range(1, n // 2 + 1):
        adj = petersen(n, k)
        chi = chromatic(adj)
        predicted = 3 if (n % 3 == 0 and k % 3 == 1) else 4
        # chi_c <= chi, so a prediction of 4 needs chi >= 4, and a prediction
        # of 3 needs chi >= 3.
        verdict = "ok" if chi >= predicted else "REFUTED"
        if verdict == "REFUTED":
            refuted.append((n, k, chi, predicted))
        print(f"  {n:>3} {k:>3} {len(adj):>4} {chi:>4} {predicted:>10}  {verdict}")

print()
print(f"  refuted cases: {len(refuted)}")
print()

# Phase 2: exact circular chromatic number for a few small graphs.
print("  Phase 2 - exact circular chromatic number for small G(n,k):")
print()
print(f"  {'n':>3} {'k':>3} {'|V|':>4} {'chi':>4} {'chi_c':>7} {'conj says':>10}  verdict")
for (n, k) in [(5, 1), (5, 2), (6, 1), (7, 1), (7, 2), (7, 3)]:
    adj = petersen(n, k)
    chi = chromatic(adj)
    cc = circ_chromatic(adj, chi)
    predicted = 3 if (n % 3 == 0 and k % 3 == 1) else 4
    verdict = "ok" if abs(cc - predicted) < 1e-9 else "REFUTED"
    print(f"  {n:>3} {k:>3} {len(adj):>4} {chi:>4} {cc:>7.3f} "
          f"{predicted:>10}  {verdict}")

print()
print("  The failure is structural, not incidental. G(n,k) is 3-regular, so by")
print("  Brooks' theorem chi <= 3 unless G(n,k) is K_4. Since chi_c <= chi")
print("  always, chi_c <= 3 < 4 for every G(n,k) other than K_4, so the")
print("  'chi_c = 4 otherwise' branch can never hold.")
print()
print("  Smallest counterexample: G(5,1), the pentagonal prism, has chi_c = 5/2.")
print("  Here n = 5 is not divisible by 3, so the conjecture predicts chi_c = 4.")
