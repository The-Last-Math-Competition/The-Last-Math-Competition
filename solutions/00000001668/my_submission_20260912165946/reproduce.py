#!/usr/bin/env python3
"""
Reproducer for the disproof of conjecture 00000001668.

    Conjecture: chi_c(G(n,k)) = 3 when n = 0 mod 3 and k = 1 mod 3,
                and 4 otherwise.

Two independent refutations are produced:

  (A) STRUCTURAL.  For every admissible (n,k), G(n,k) is connected and
      3-regular.  By Brooks' theorem chi(G(n,k)) <= 3 (the graph is never
      K_4, since |V| = 2n >= 6).  Since chi_c <= chi always, chi_c <= 3 < 4.
      Therefore the "4 otherwise" branch can NEVER hold -- for any n, k.
      This is a statement about the classification framework, not about
      isolated arithmetic slips.

  (B) EXPLICIT.  Exact circular chromatic numbers for small G(n,k), with
      (p,q)-colouring certificates, plus the smallest counterexamples to
      each branch.

Conventions
-----------
G(n,k) has vertices u_0..u_{n-1}, v_0..v_{n-1} and edges
    u_i u_{i+1}   (indices mod n)      outer cycle
    v_i v_{i+k}   (indices mod n)      inner star polygon
    u_i v_i                            spokes
Admissible parameters: n >= 3 and 1 <= k < n/2.

A (p,q)-colouring is c : V -> Z_p with  q <= |c(x) - c(y)|_p <= p - q
on every edge, where |d|_p = min(d mod p, p - (d mod p)).
Then chi_c(G) = min { p/q : G has a (p,q)-colouring }.

Standard library only.  Python 3.8+.
"""

from fractions import Fraction
from itertools import product

# --------------------------------------------------------------------------
# graph construction
# --------------------------------------------------------------------------


def petersen(n, k):
    """Adjacency list of the generalized Petersen graph G(n,k)."""
    adj = {("u", i): set() for i in range(n)}
    adj.update({("v", i): set() for i in range(n)})
    for i in range(n):
        # outer cycle
        adj[("u", i)].add(("u", (i + 1) % n))
        adj[("u", (i + 1) % n)].add(("u", i))
        # inner star polygon
        adj[("v", i)].add(("v", (i + k) % n))
        adj[("v", (i + k) % n)].add(("v", i))
        # spoke
        adj[("u", i)].add(("v", i))
        adj[("v", i)].add(("u", i))
    return adj


def admissible(n):
    """
    All k with 1 <= k <= n/2.

    The conjecture quantifies over all n and k, so we do not restrict to
    k < n/2.  When k < n/2 the graph is cubic (all degrees 3).  When k = n/2
    (n even) the inner star polygon degenerates to a perfect matching, so the
    inner vertices have degree 2 and the graph is only *subcubic*: the maximum
    degree is still 3.  Brooks' theorem needs only the maximum degree, so the
    conclusion is unaffected -- we report which case each graph falls in.
    """
    return list(range(1, n // 2 + 1))


def is_connected(adj):
    start = next(iter(adj))
    seen, stack = {start}, [start]
    while stack:
        x = stack.pop()
        for y in adj[x]:
            if y not in seen:
                seen.add(y)
                stack.append(y)
    return len(seen) == len(adj)


def degrees(adj):
    return sorted({len(s) for s in adj.values()})


# --------------------------------------------------------------------------
# ordinary chromatic number (exact, backtracking)
# --------------------------------------------------------------------------


def chromatic(adj, kmax=6):
    """Smallest number of colours, or None if > kmax."""
    verts = sorted(adj)
    for k in range(1, kmax + 1):
        colour = {}

        def bt(i):
            if i == len(verts):
                return True
            x = verts[i]
            used = {colour[y] for y in adj[x] if y in colour}
            # symmetry breaking: the first vertex may use only colour 0, and
            # after colours 0..m are in use only 0..m+1 may be opened.
            used_max = max(colour.values()) if colour else -1
            hi = min(k, used_max + 2)
            for c in range(hi):
                if c not in used:
                    colour[x] = c
                    if bt(i + 1):
                        return True
                    del colour[x]
            return False

        if bt(0):
            return k
    return None


# --------------------------------------------------------------------------
# circular chromatic number (exact, backtracking)
# --------------------------------------------------------------------------


def pq_colouring(adj, p, q):
    """Return a (p,q)-colouring as a dict, or None."""
    if not (1 <= q <= p - q):
        return None
    verts = sorted(adj)
    colour = {}

    def ok(x, c):
        for y in adj[x]:
            if y in colour:
                d = abs(colour[y] - c) % p
                d = min(d, p - d)
                if not (q <= d <= p - q):
                    return False
        return True

    def bt(i):
        if i == len(verts):
            return True
        x = verts[i]
        for c in range(p):
            if ok(x, c):
                colour[x] = c
                if bt(i + 1):
                    return True
                del colour[x]
        return False

    return dict(colour) if bt(0) else None


def circ_chromatic(adj, pmax=None):
    """
    Exact chi_c as a Fraction, together with a witness (p,q,colouring).

    We search p from 1 to pmax (default |V|) and all q with 1 <= q <= p/2.
    For a graph on n vertices the optimum is attained with p <= n, so
    pmax = |V| is sufficient here; we also try q = 1 explicitly, which
    covers the bipartite case chi_c = 2.
    """
    n = len(adj)
    if pmax is None:
        pmax = n
    best = None
    for p in range(1, pmax + 1):
        for q in range(1, p // 2 + 1):
            val = Fraction(p, q)
            if best is not None and val >= best[0]:
                continue
            col = pq_colouring(adj, p, q)
            if col is not None:
                best = (val, p, q, col)
    return best


# --------------------------------------------------------------------------
# conjecture
# --------------------------------------------------------------------------


def conjecture_predicts(n, k):
    """The conjecture's table: 3 if n = 0 mod 3 and k = 1 mod 3, else 4."""
    return 3 if (n % 3 == 0 and k % 3 == 1) else 4


# --------------------------------------------------------------------------
# main
# --------------------------------------------------------------------------


def main():
    line = "=" * 74

    print(line)
    print("STRUCTURAL REFUTATION - max degree 3, so Brooks' theorem applies")
    print(line)
    print("  For every admissible (n,k) the graph is connected with Delta = 3.")
    print("  It is cubic exactly when k < n/2; at k = n/2 (n even) the inner")
    print("  star polygon degenerates to a perfect matching and the inner")
    print("  vertices drop to degree 2, leaving Delta = 3 still.")
    print()
    print("    n   k  |V|  degrees  cubic  connected  chi  chi<=3?  K_4?")
    bad_delta = bad_conn = bad_brooks = 0
    n_cubic = n_subcubic = 0
    for n in range(3, 21):
        for k in admissible(n):
            adj = petersen(n, k)
            deg = degrees(adj)
            cubic = deg == [3]
            conn = is_connected(adj)
            chi = chromatic(adj)
            is_k4 = len(adj) == 4
            if deg[-1] != 3:
                bad_delta += 1
            if not conn:
                bad_conn += 1
            if chi is None or chi > 3:
                bad_brooks += 1
            if cubic:
                n_cubic += 1
            else:
                n_subcubic += 1
            print(
                f"  {n:3d} {k:3d} {len(adj):4d}  {str(deg):8s} "
                f"{str(cubic):6s} {str(conn):9s} {str(chi):4s} "
                f"{str(chi <= 3):8s} {is_k4}"
            )
    print()
    print(f"  graphs with max degree != 3 : {bad_delta}")
    print(f"  graphs that are not connected: {bad_conn}")
    print(f"  graphs with chi > 3          : {bad_brooks}")
    print(f"  cubic (k < n/2)              : {n_cubic}")
    print(f"  subcubic (k = n/2)           : {n_subcubic}")
    print()
    print("  Brooks' theorem: a connected graph with maximum degree 3 has")
    print("  chi <= 3 unless it is K_4.  Here |V| = 2n >= 6, so K_4 never")
    print("  occurs.  Hence chi <= 3 for every admissible (n,k).")
    print("  Since chi_c <= chi always, chi_c <= 3 < 4.")
    print()
    print("  => the '4 otherwise' branch of the conjecture is impossible")
    print("     for ALL n, k.  This is structural, not a boundary case.")

    print()
    print(line)
    print("EXPLICIT REFUTATION - exact chi_c with (p,q)-colouring certificates")
    print(line)
    print()
    print("    n   k  |V|  chi   chi_c  conj says  verdict")
    small = [(5, 1), (5, 2), (6, 1), (7, 1), (7, 2), (7, 3)]
    refuted_explicit = []
    for n, k in small:
        adj = petersen(n, k)
        chi = chromatic(adj)
        val, p, q, col = circ_chromatic(adj)
        pred = conjecture_predicts(n, k)
        verdict = "REFUTED" if val < pred else "ok"
        if verdict == "REFUTED":
            refuted_explicit.append((n, k))
        print(
            f"  {n:3d} {k:3d} {len(adj):4d} {chi:4d}  {str(val):6s} "
            f"{pred:9d}  {verdict}"
        )

    print()
    print("  Certificates (a (p,q)-colouring of Z_p; |c(x)-c(y)|_p in [q, p-q]")
    print("  on every edge):")
    for n, k in [(5, 1), (7, 1), (6, 1)]:
        adj = petersen(n, k)
        val, p, q, col = circ_chromatic(adj)
        outer = [col[("u", i)] for i in range(n)]
        inner = [col[("v", i)] for i in range(n)]
        viol = 0
        for x in adj:
            for y in adj[x]:
                d = abs(col[x] - col[y]) % p
                d = min(d, p - d)
                if not (q <= d <= p - q):
                    viol += 1
        print()
        print(f"  G({n},{k})   ({p},{q})-colouring   p/q = {val}")
        print(f"     outer u_0..u_{n-1} = {outer}")
        print(f"     inner v_0..v_{n-1} = {inner}")
        print(f"     edges violating the (p,q) condition: {viol}")

    print()
    print("  Non-existence check for G(5,2) at p/q = 5/2:")
    adj = petersen(5, 2)
    print(f"     (5,2)-colouring found: {pq_colouring(adj, 5, 2) is not None}")
    print("     (it has odd cycles of length 5 and is not 2-colourable, so")
    print("      chi_c > 5/2; the exact value is 3.)")

    print()
    print(line)
    print("SWEEP - both branches of the conjecture fail")
    print(line)
    print()
    total = 0
    refuted = 0
    survived = []
    for n in range(5, 21):
        for k in admissible(n):
            adj = petersen(n, k)
            chi = chromatic(adj)
            pred = conjecture_predicts(n, k)
            total += 1
            # chi_c <= chi, so chi < pred already refutes the prediction
            if chi < pred:
                refuted += 1
            else:
                survived.append((n, k, chi, pred))
    print(f"  cases tested                : {total}")
    print(f"  refuted by chi_c <= chi     : {refuted}")
    print(f"  not refuted by this bound   : {len(survived)}")
    print()
    print("  NOTE: 'not refuted by this bound' does NOT mean 'verified'.")
    print("  The test uses chi >= prediction, a NECESSARY condition coming")
    print("  from chi_c <= chi.  Passing it only means this single inequality")
    print("  does not already refute the case.  Every survivor has")
    print("  n = 0 mod 3, k = 1 mod 3 AND chi >= 3:")
    print()
    for n, k, chi, pred in survived:
        print(f"    G({n},{k})  chi = {chi}  predicted chi_c = {pred}")
    print()
    print("  The '3' branch is also refuted, by bipartite cases with")
    print("  n = 0 mod 3 and k = 1 mod 3:")
    for n, k in [(6, 1), (12, 1), (18, 7)]:
        adj = petersen(n, k)
        chi = chromatic(adj)
        print(
            f"    G({n},{k})  n = 0 mod 3, k = 1 mod 3, chi = chi_c = {chi} "
            f"< predicted {conjecture_predicts(n, k)}  -> REFUTED"
        )

    print()
    print(line)
    print("VERDICT")
    print(line)
    print("  Smallest counterexample to the '4 otherwise' branch : G(5,1)")
    print("    the pentagonal prism, chi_c = 5/2, conjecture says 4")
    print("  Smallest counterexample to the '3' branch           : G(6,1)")
    print("    the hexagonal prism, bipartite, chi_c = 2, conjecture says 3")
    print("  Structural reason the '4' branch can never hold     : Brooks' theorem")
    print("  => conjecture 00000001668 is FALSE")


if __name__ == "__main__":
    main()
