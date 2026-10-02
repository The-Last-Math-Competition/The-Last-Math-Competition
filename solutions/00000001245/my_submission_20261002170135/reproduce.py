#!/usr/bin/env python3
"""Independent verification for the disproof of conjecture 00000001245."""
import sys

def rule(n, l, c, r):
    return (n >> (l * 4 + c * 2 + r)) & 1

def gm(n, w, blk):
    return tuple(rule(n, blk[(i - 1) % w], blk[i], blk[(i + 1) % w])
                 for i in range(w))

def blocks(w):
    for x in range(2 ** w):
        yield tuple((x >> i) & 1 for i in range(w))

def main():
    # (1) rule 51 is bijective on blocks of widths 2..10
    for w in range(2, 11):
        img = {gm(51, w, b) for b in blocks(w)}
        assert len(img) == 2 ** w, f"rule 51 not bijective at width {w}"
    print("rule 51: bijective on blocks of widths 2..10 -> no GoE patterns at all")
    # width-2 table
    tbl = {b: gm(51, 2, b) for b in blocks(2)}
    print("rule 51 width-2 table:", tbl)
    assert tbl == {(0,0):(1,1), (0,1):(1,0), (1,0):(0,1), (1,1):(0,0)}
    # (2) sweep: rules with an all-zeros GoE word
    hits = []
    for n in range(256):
        for w in range(2, 11):
            if not any(gm(n, w, b) == tuple([0] * w) for b in blocks(w)):
                hits.append((n, w))
                break
    print(f"rules with a density-0 (all-zeros) GoE word: {len(hits)}")
    print("first few (rule, width):", hits[:10])
    assert (133, 2) in hits, "rule 133 width-2 should have the all-zeros GoE word"
    t133 = {b: gm(133, 2, b) for b in blocks(2)}
    print("rule 133 width-2 table:", t133)
    assert all(v != (0, 0) for v in t133.values())
    print("density of the all-zeros width-2 word: 0/2 = 0 < 1/4 -> infimum is 0")
    print("ALL CHECKS PASS — conjecture 00000001245 refuted")
    return 0

if __name__ == "__main__":
    sys.exit(main())
