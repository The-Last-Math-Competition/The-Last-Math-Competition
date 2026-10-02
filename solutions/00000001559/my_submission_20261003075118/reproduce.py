#!/usr/bin/env python3
"""Independent verification for the disproof of conjecture 00000001559.

The conjecture's displayed expression (1+sqrt(3))/2 * (sqrt(3)-1)
equals exactly 1 (difference of squares).  But six disks of radius
0.62 centered at the vertices of the inscribed hexagon (radius 1/2)
already cover the unit disk: the sector-convexity argument reduces the
check to the sector corners, and all corner squared-distances are
< 0.62^2.  Hence r_6 <= 0.62 < 1 = the claimed value.  Also brute-force
grid check on a fine grid.
Exit 0 iff all checks pass.
"""
import math
import sys


def main():
    # 1. the claimed value is exactly 1 (difference of squares)
    s = math.sqrt(3)
    val = (1 + s) / 2 * (s - 1)
    assert abs(val - 1) < 1e-12, val
    print(f"(1+sqrt3)/2 * (sqrt3-1) = {val:.15f} = 1 exactly (alg.) — OK")

    # 2. the covering: six centers at hexagon vertices, radius 0.62
    R = 0.5
    r = 0.62
    centers = [(R * math.cos(math.pi / 3 * i + math.pi / 6),
                R * math.sin(math.pi / 3 * i + math.pi / 6))
               for i in range(6)]

    def dist2(p, c):
        return (p[0] - c[0]) ** 2 + (p[1] - c[1]) ** 2

    # sector-convexity certificate: for each sector (60 degrees around
    # a center), the squared distance is convex, max at corners
    corners = [(1.0, 0.0), (0.0, 0.0),
               (math.cos(math.pi / 6), math.sin(math.pi / 6)),
               (math.cos(math.pi / 2), math.sin(math.pi / 2))]
    r2 = r * r
    for i in range(6):
        c = centers[i]
        # sector i spans angles [i*60, (i+1)*60]; its corners are the
        # origin and the two unit-boundary points at those rays
        worst = 0.0
        for ang in (i * math.pi / 3, (i + 1) * math.pi / 3):
            for rad in (0.0, 1.0):
                p = (rad * math.cos(ang), rad * math.sin(ang))
                worst = max(worst, dist2(p, c))
        assert worst <= r2 + 1e-15, (i, worst)
    print("sector-convexity certificate: every sector corner within "
          "0.62 of its center (max sqdist < 0.3844) — OK")

    # fine grid brute-force cross-check
    step = 2000
    worst = 0.0
    for i in range(step + 1):
        x = -1 + 2 * i / step
        h = math.sqrt(max(0.0, 1 - x * x))
        steps = max(1, int(2 * h * step / 2))
        for j in range(steps + 1):
            y = -h + 2 * h * j / steps
            d2 = min((x - c[0]) ** 2 + (y - c[1]) ** 2 for c in centers)
            worst = max(worst, d2)
    assert worst <= r2 + 1e-12, worst
    print(f"fine-grid check (2000x~2000): max sqdist {worst:.6f} "
          f"<= {r2} — covered — OK")

    # 3. hence r_6 <= 0.62 < 1 = claimed value; also known optimum ~0.5559
    assert 0.62 < 1
    print("r_6 <= 0.62 < 1 = claimed value (and literature r_6 ~ 0.5559)")

    print("ALL CHECKS PASS — the claimed quadratic value 1 is wrong")
    return 0


if __name__ == "__main__":
    sys.exit(main())
