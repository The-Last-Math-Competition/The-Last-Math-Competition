#!/usr/bin/env python3
"""Independent finite sanity checks; universal claims are proved in Lean."""
import itertools
import json


def edges(n):
    return tuple(itertools.combinations(range(n), 2))


def edge_set(n, mask):
    return frozenset(e for k, e in enumerate(edges(n)) if mask & (1 << k))


def renamed(edge, perm):
    return frozenset(tuple(sorted((perm[a], perm[b]))) for a, b in edge)


def canonical(n, edge):
    return min(tuple(sorted(renamed(edge, p))) for p in itertools.permutations(range(n)))


def deck(n, edge):
    cards = []
    for deleted in range(n):
        survivors = [v for v in range(n) if v != deleted]
        pos = {v: i for i, v in enumerate(survivors)}
        card = frozenset((pos[a], pos[b]) for a, b in edge if deleted not in (a, b))
        cards.append(canonical(n - 1, card))
    return tuple(sorted(cards))


def distance(n, left, right):
    return min(len(left ^ renamed(right, p)) for p in itertools.permutations(range(n)))


def run():
    rows = []
    for n in (2, 3, 4):
        graphs = [edge_set(n, m) for m in range(1 << len(edges(n)))]
        canons = [canonical(n, g) for g in graphs]
        decks = [deck(n, g) for g in graphs]
        equal_deck_pairs = 0
        noniso_equal_deck_pairs = 0
        for i, g in enumerate(graphs):
            assert len(decks[i]) == n
            assert distance(n, g, g) == 0
            for j, h in enumerate(graphs):
                d = distance(n, g, h)
                assert (d == 0) == (canons[i] == canons[j])
                assert d == distance(n, h, g)
                assert d <= len(g ^ h)
                if decks[i] == decks[j]:
                    equal_deck_pairs += 1
                    noniso_equal_deck_pairs += canons[i] != canons[j]
                    if n >= 3:
                        assert d == 0
        assert decks[0] == tuple(() for _ in range(n))
        assert distance(n, graphs[0], graphs[1]) == 1
        rows.append(dict(order=n, labelled_graphs=len(graphs),
                         unlabelled_graphs=len(set(canons)), ordered_pairs=len(graphs)**2,
                         equal_deck_ordered_pairs=equal_deck_pairs,
                         nonisomorphic_equal_deck_ordered_pairs=noniso_equal_deck_pairs))
    g = frozenset({(0, 1)})
    h = frozenset({(0, 2)})
    assert g != h and deck(3, g) == deck(3, h) and distance(3, g, h) == 0
    print(json.dumps(dict(status='FINITE_CHECKS_OK', scope='All simple labelled graphs and ordered pairs at orders 2, 3, 4 only', results=rows), indent=2))


if __name__ == '__main__':
    run()
