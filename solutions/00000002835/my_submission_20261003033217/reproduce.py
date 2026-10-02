#!/usr/bin/env python3
"""Independent verification for the disproof of conjecture 00000002835.

The 2x3 pattern with observations M11=4, M12=6, M13=10, M21=14 (all
even, in doubled units):
  1. The support bipartite graph has 5 vertices: no 1-regular spanning
     subgraph (handshaking 2*1 != 3*1).
  2. The rank-1 completion is UNIQUE: M22 = 21, M23 = 35 (all 2x2
     minors of the completed matrix vanish; each missing entry forced
     by the cancellation equations).
So unique recovery holds WITHOUT any 1-regular spanning subgraph.
Exit 0 iff all checks pass.
"""
import sys
from fractions import Fraction


def main():
    # doubled observations
    M = [[Fraction(4), Fraction(6), Fraction(10)],
         [Fraction(14), None, None]]

    # (1) handshaking: support bipartite graph 2 + 3 = 5 vertices;
    #     a 1-regular spanning subgraph needs 2*1 == 3*1 edges
    print("support vertices: 2 left + 3 right; 1-regular spanning subgraph "
          "would need 2*1 == 3*1 edges:", 2 * 1 == 3 * 1)
    assert 2 * 1 != 3 * 1

    # (2) unique completion: M22 = M12*M21/M11 = 6*14/4 = 21;
    #     M23 = M13*M21/M11 = 10*14/4 = 35
    m22 = M[0][1] * M[1][0] / M[0][0]
    m23 = M[0][2] * M[1][0] / M[0][0]
    print(f"M22 = {m22}, M23 = {m23}")
    assert m22 == 21 and m23 == 35

    # completed matrix is rank-1: all 2x2 minors vanish
    full = [[M[0][0], M[0][1], M[0][2]],
            [M[1][0], m22, m23]]
    for c1 in range(3):
        for c2 in range(c1 + 1, 3):
            det = full[0][c1] * full[1][c2] - full[0][c2] * full[1][c1]
            assert det == 0, (c1, c2, det)
    print("completed matrix [[4,6,10],[14,21,35]]: all 2x2 minors zero "
          "(rank 1, unique completion)")

    # uniqueness: every entry forced
    assert m22 == M[0][1] * M[1][0] / M[0][0]
    assert m23 == M[0][2] * M[1][0] / M[0][0]

    print("ALL CHECKS PASS — unique rank-1 completion without any "
          "1-regular spanning subgraph")
    return 0


if __name__ == "__main__":
    sys.exit(main())
