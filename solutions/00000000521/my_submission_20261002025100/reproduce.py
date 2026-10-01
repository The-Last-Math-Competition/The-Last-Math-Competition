#!/usr/bin/env python3
"""
TLMC conjecture 00000000521 - independent recomputation (falsification package).

Conjecture. For every edge ideal I of a simple graph, the alternating Betti
sums  A_j = sum_i (-1)^i beta_{i,j}  satisfy: the sign of the sequence {A_j}
changes exactly once as j crosses reg(I), and |A_j| is monotonically
nondecreasing up to that point.

Attack (TLMC falsification queue, verdict line corrected): the triangle graph
C3 with I = (xy, xz, yz) in k[x,y,z].

Fully independent method (no reliance on the original pipeline's numbers):
  1. Build the Taylor resolution of R/I (explicit standard free resolution).
  2. Tensor with k = GF(P) and compute homology dimensions per bidegree
     -> graded Betti numbers beta_{i,j}(R/I).  This is legitimate because
     Tor can be computed from ANY free resolution; after tensoring with k
     only the constant (=1) entries of the Taylor differentials survive.
     (For monomial ideals Betti numbers are field independent; all entries
     here are 0,+1,-1 and P = 10^9+7, so no mod-P rank degeneration.)
  3. Cross-check: A_j must equal the coefficient of t^j in
     (1-t)^n * Hilb_{R/I}(t), computed by direct monomial enumeration.
  4. Form A_j, count sign changes (zeros skipped), test monotonicity of |A_j|.

Also scans all labeled graphs on <= 4 vertices (and, with --scan5, on 5
vertices), and evaluates the alternative reading where beta_{i,j}(I) means
the Betti numbers of the module I (then A_j(I) = beta_{0,j}(R/I) - A_j(R/I),
from the long exact Tor sequence of 0 -> I -> R -> R/I -> 0).

Standard library only.  python3 reproduce.py   (exit code 0 = recomputation OK)
"""

from itertools import combinations
from math import comb
import sys

P = 1_000_000_007


# ---------------- linear algebra over GF(P) ----------------

def rank(rows, ncols):
    """Rank of a matrix given as a list of rows of ints, mod P."""
    M = [r[:] for r in rows]
    rk = 0
    for col in range(ncols):
        piv = None
        for i in range(rk, len(M)):
            if M[i][col] % P:
                piv = i
                break
        if piv is None:
            continue
        M[rk], M[piv] = M[piv], M[rk]
        inv = pow(M[rk][col], P - 2, P)
        M[rk] = [(v * inv) % P for v in M[rk]]
        for i in range(len(M)):
            if i != rk and M[i][col] % P:
                f = M[i][col]
                M[i] = [(M[i][j] - f * M[rk][j]) % P for j in range(ncols)]
        rk += 1
    return rk


# ---------------- Betti numbers via Taylor resolution (x) k ----------------

def lcm_m(a, b):
    return tuple(max(x, y) for x, y in zip(a, b))


def bits(mask):
    i = 0
    out = []
    while mask:
        if mask & 1:
            out.append(i)
        mask >>= 1
        i += 1
    return out


def betti_table_RI(gens):
    """
    gens: list of exponent tuples = minimal monomial generators of I.
    Returns (dims, maxdeg) where dims[(i, j)] = beta_{i,j}(R/I).
    """
    nvars = len(gens[0])
    r = len(gens)
    deg = {}
    for mask in range(1 << r):
        d = (0,) * nvars
        for s in bits(mask):
            d = lcm_m(d, gens[s])
        deg[mask] = (sum(d), d)
    maxdeg = max(d for (d, _) in deg.values())

    groups = {}
    for mask, (dj, dv) in deg.items():
        groups.setdefault((bin(mask).count("1"), dj), []).append(mask)

    # rank_r[(i,j)] = rank of d_i : C_i(j) -> C_{i-1}(j)  (0-map for i = 0)
    rank_r = {}
    n_i = {}
    for (i, j), src in groups.items():
        n_i[(i, j)] = len(src)
        tgt = groups.get((i - 1, j), []) if i > 0 else []
        tcol = {m: c for c, m in enumerate(tgt)}
        rows = []
        for S in src:
            row = [0] * len(tgt)
            for pos, s in enumerate(bits(S)):
                S2 = S & ~(1 << s)
                if deg[S][1] == deg[S2][1]:  # lcm unchanged -> constant entry survives (x)k
                    row[tcol[S2]] = 1 if pos % 2 == 0 else P - 1
            rows.append(row)
        rank_r[(i, j)] = rank(rows, len(tgt)) if rows else 0

    dims = {}
    for (i, j), src in list(groups.items()):
        ker = len(src) - rank_r.get((i, j), 0)
        im_next = rank_r.get((i + 1, j), 0)  # im d_{i+1} lives in C_i(j)
        dims[(i, j)] = ker - im_next
    # explicit zero entries
    for i in range(r + 1):
        for j in range(maxdeg + 1):
            dims.setdefault((i, j), 0)
    return dims, maxdeg


def hilbert_num_RI(gens, nvars, D):
    """
    Coefficients c_j of (1-t)^n * Hilb_{R/I}(t) for j = 0..D,
    obtained by enumerating monomials of R/I of degree <= D.
    A monomial survives iff its support is independent (contains no edge).
    """
    edges = [ (a, b) for a in range(nvars) for b in range(a + 1, nvars)
              if any(g[a] > 0 and g[b] > 0 for g in gens) ]
    # (reconstruct the graph's edges from the generators for the independence test)
    h = [0] * (D + 1)
    exp = [0] * nvars

    def rec(v, total):
        if v == nvars:
            supp = [i for i in range(nvars) if exp[i] > 0]
            for (a, b) in edges:
                if a in supp and b in supp:
                    return
            h[total] += 1
            return
        for e in range(D - total + 1):
            exp[v] = e
            rec(v + 1, total + e)
        exp[v] = 0

    rec(0, 0)
    c = []
    for j in range(D + 1):
        c.append(sum(h[d] * ((-1) ** (j - d)) * comb(nvars, j - d)
                     for d in range(j + 1)))
    return c


def analyze(gens, nvars, label):
    dims, maxdeg = betti_table_RI(gens)
    A = [sum(((-1) ** i) * dims.get((i, j), 0) for i in range(len(gens) + 1))
         for j in range(maxdeg + 2)]
    # Hilbert-series cross-check
    c = hilbert_num_RI(gens, nvars, maxdeg + 2)
    ok = all(A[j] == c[j] for j in range(min(len(A), len(c)))) and all(v == 0 for v in c[len(A):])
    # regularities (standard: reg M = max{j - i} over beta_{i,j}(M))
    reg_RI = max(((j - i) for (i, j), d in dims.items() if d), default=0)
    reg_I = max(((j - i + 1) for (i, j), d in dims.items() if d and i >= 1), default=0)

    def sc(seq):
        nz = [x for x in seq if x != 0]
        return sum(1 for a, b in zip(nz, nz[1:]) if (a > 0) != (b > 0))

    res = {
        "label": label, "dims": dims, "A": A, "maxdeg": maxdeg,
        "hilbert_ok": ok, "reg_RI": reg_RI, "reg_I": reg_I,
        "changes_RI": sc(A),
        # reading 2: Betti numbers of the module I:  A_j(I) = beta_{0,j}(R/I) - A_j(R/I)
        "A_modI": [dims.get((0, j), 0) - A[j] for j in range(len(A))],
    }
    res["changes_modI"] = sc(res["A_modI"])
    return res


def edge_ideal(nvars, edges):
    gens = []
    for (a, b) in edges:
        t = [0] * nvars
        t[a] = 1
        t[b] = 1
        gens.append(tuple(t))
    return gens


def nondecreasing(seq):
    return all(a <= b for a, b in zip(seq, seq[1:]))


def main():
    print("=" * 72)
    print("TLMC 00000000521 falsification - independent recomputation")
    print("=" * 72)

    # ---------- the confirmed attack: triangle C3 ----------
    tri = edge_ideal(3, [(0, 1), (1, 2), (0, 2)])  # (xy, xz, yz)
    t = analyze(tri, 3, "C3 triangle, I=(xy,xz,yz) in k[x,y,z]")
    print(f"\n[{t['label']}]")
    print("  graded Betti numbers beta_{i,j}(R/I):")
    for (i, j), d in sorted(t["dims"].items()):
        if d:
            print(f"    beta_{i},{j} = {d}")
    print(f"  A_j (j=0..{t['maxdeg']+1}) = {t['A']}")
    print(f"  Hilbert-series cross-check (1-t)^3*Hilb == A : {t['hilbert_ok']}")
    print(f"  reg(R/I) = {t['reg_RI']},  reg(I) = {t['reg_I']}")
    print(f"  nonzero sign sequence: {[x for x in t['A'] if x]} -> "
          f"{t['changes_RI']} sign changes (conjecture demands exactly 1)")
    print(f"  |A_j| = {[abs(x) for x in t['A']]} : not nondecreasing "
          f"(1>0 at j=1; 3>2 at j=3)")
    # reading 2 (module I)
    print(f"  alternative reading (Betti numbers of the module I): "
          f"A_j(I) = {t['A_modI']}, sign changes = {t['changes_modI']}")

    assert t["hilbert_ok"], "Hilbert-series cross-check FAILED"
    assert t["dims"][(0, 0)] == 1 and t["dims"][(1, 2)] == 3 and t["dims"][(2, 3)] == 2
    assert t["A"][:4] == [1, 0, -3, 2], t["A"]
    assert t["changes_RI"] == 2, "expected 2 sign changes"
    print("  -> conjecture FALSIFIED for C3 (verdict numbers A_0=1, A_2=-3, A_3=2 reproduced)")

    # ---------- further counterexamples / boundary ----------
    print("\nBoundary examples (reading 1: beta of R/I | reading 2: beta of module I):")
    named = [
        ("single edge K2",            2, [(0, 1)]),
        ("P3 = (xy,yz) two adjacent", 3, [(0, 1), (1, 2)]),
        ("C3 = (xy,xz,yz)",           3, [(0, 1), (1, 2), (0, 2)]),
        ("2K2 = (xy,zt)",             4, [(0, 1), (2, 3)]),
        ("P4",                        4, [(0, 1), (1, 2), (2, 3)]),
        ("star K1,3",                 4, [(0, 1), (0, 2), (0, 3)]),
        ("C4",                        4, [(0, 1), (1, 2), (2, 3), (0, 3)]),
        ("paw",                       4, [(0, 1), (1, 2), (0, 2), (2, 3)]),
        ("diamond",                   4, [(0, 1), (0, 2), (0, 3), (1, 2), (2, 3)]),
        ("K4",                        4, [(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3)]),
    ]
    for label, nv, es in named:
        r = analyze(edge_ideal(nv, es), nv, label)
        assert r["hilbert_ok"], f"Hilbert cross-check failed for {label}"
        print(f"  {label:28s} A(R/I)={r['A']}  changes={r['changes_RI']} "
              f"| A(I)={r['A_modI']}  changes={r['changes_modI']}")

    # ---------- exhaustive scans ----------
    for nvars, flag in [(4, None), (5, "--scan5")]:
        if flag and flag not in sys.argv[1:]:
            continue
        pairs = list(combinations(range(nvars), 2))
        total = viol1 = viol2 = both = 0
        first_examples = []
        for mask in range(1 << len(pairs)):
            es = [pairs[k] for k in range(len(pairs)) if mask >> k & 1]
            if not es:
                continue
            total += 1
            r = analyze(edge_ideal(nvars, es), nvars, "")
            bad1 = r["changes_RI"] != 1
            # monotonicity of |A_j| over nonzero entries up to reg(I)
            upto = [abs(r["A"][j]) for j in range(len(r["A"]))
                    if j <= r["reg_I"] and r["A"][j] != 0]
            bad2 = not nondecreasing(upto)
            if bad1:
                viol1 += 1
            if bad2:
                viol2 += 1
            if bad1 and bad2:
                both += 1
            if bad1 and len(first_examples) < 5:
                first_examples.append((es, r["A"], r["changes_RI"]))
        print(f"\nScan: all labeled graphs on {nvars} vertices with >=1 edge")
        print(f"  graphs checked                 : {total}")
        print(f"  violating 'exactly one sign change' : {viol1}")
        print(f"  violating '|A| nondecreasing up to reg(I)' : {viol2}")
        print(f"  violating both                 : {both}")
        for es, A, ch in first_examples:
            print(f"    example {es}: A = {A}, sign changes = {ch}")

    print("\nAll recomputations and cross-checks PASSED.")
    print("Conclusion: conjecture 00000000521 is FALSE; recomputation reproduces the")
    print("verdict numbers for C3 (A_0=1, A_2=-3, A_3=2, two sign changes).")


if __name__ == "__main__":
    main()
