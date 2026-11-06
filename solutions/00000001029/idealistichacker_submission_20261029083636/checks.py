"""Independent bounded GF(2) diagnostics, not a generic design-existence proof."""
from itertools import product


def _dimension_bound(n):
    if not isinstance(n, int) or isinstance(n, bool) or not 0 <= n <= 3:
        raise ValueError("This diagnostic supports only integer dimensions 0..3")


def carrier_members(code, n):
    _dimension_bound(n)
    if not isinstance(code, int) or isinstance(code, bool) or not 0 <= code < (1 << (1 << n)):
        raise ValueError("Invalid finite-vector carrier bit mask")
    return tuple(x for x in range(1 << n) if code & (1 << x))


def subspace_gf2(code, n):
    members = carrier_members(code, n)
    return 0 in members and all((x ^ y) in members for x in members for y in members)


def subspaces_gf2(n, d):
    _dimension_bound(n)
    if not isinstance(d, int) or isinstance(d, bool) or not 0 <= d <= n:
        return ()
    return tuple(code for code in range(1 << (1 << n))
                 if code.bit_count() == (1 << d) and subspace_gf2(code, n))


def actual_design_gf2(n, k, family):
    _dimension_bound(n)
    if not isinstance(k, int) or isinstance(k, bool) or not 2 <= k <= n:
        return False
    family = tuple(family)
    if len(set(family)) != len(family):
        return False
    blocks = set(subspaces_gf2(n, k))
    if any(block not in blocks for block in family):
        return False
    return all(sum((u & block) == u for block in family) == 1 for u in subspaces_gf2(n, 2))


def catalogue_gf2(n, k):
    _dimension_bound(n)
    if not isinstance(k, int) or isinstance(k, bool) or not 2 <= k <= n:
        return ()
    blocks = subspaces_gf2(n, k)
    result = []
    for mask in range(1 << len(blocks)):
        family = tuple(block for i, block in enumerate(blocks) if mask & (1 << i))
        if actual_design_gf2(n, k, family):
            result.append(family)
    return tuple(result)


def valid_two_label_tables():
    """Enumerate raw constants and binary tables independently of the Lean order."""
    labels = (0, 1)
    valid = []
    for zero, one in product(labels, repeat=2):
        if zero == one:
            continue
        for add_table in product(labels, repeat=4):
            add = lambda a, b: add_table[2 * a + b]
            if not all(add(add(a, b), c) == add(a, add(b, c)) for a, b, c in product(labels, repeat=3)):
                continue
            if not all(add(zero, a) == a and any(add(b, a) == zero for b in labels) for a in labels):
                continue
            for mul_table in product(labels, repeat=4):
                mul = lambda a, b: mul_table[2 * a + b]
                if not all(mul(mul(a, b), c) == mul(a, mul(b, c)) for a, b, c in product(labels, repeat=3)):
                    continue
                if not all(mul(a, b) == mul(b, a) for a, b in product(labels, repeat=2)):
                    continue
                if not all(mul(one, a) == a for a in labels):
                    continue
                if not all(mul(a, add(b, c)) == add(mul(a, b), mul(a, c))
                           for a, b, c in product(labels, repeat=3)):
                    continue
                if not all(a == zero or any(mul(a, b) == one for b in labels) for a in labels):
                    continue
                valid.append((zero, one, add_table, mul_table))
    return tuple(valid)


if __name__ == "__main__":
    import json
    print(json.dumps({"scope": "Bounded GF(2) diagnostics only", "raw_two_label_fields": len(valid_two_label_tables()),
                      "catalogues": {f"n{n}k{k}": catalogue_gf2(n, k)
                                     for n, k in ((2, 2), (3, 2), (3, 3), (3, 1), (0, 0))}}, indent=2))
