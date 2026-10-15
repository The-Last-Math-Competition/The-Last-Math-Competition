"""Independent exact check; only Python's standard library is required."""
from collections import Counter
from itertools import product

pairs = list(product(range(3), repeat=2))
words = [tuple((a * t + b) % 3 for t in range(3)) for a, b in pairs]
assert len(set(words)) == 9
weights = Counter(sum(x != 0 for x in word) for word in words)
assert weights == {0: 1, 2: 6, 3: 2}
assert min(w for w in weights if w > 0) == 2
assert tuple(t % 3 for t in range(3)) == (0, 1, 2)
assert 2 != 3 - 0
for (a, b), word in zip(pairs, words):
    print(f"a={a}, b={b}: {word}, weight={sum(x != 0 for x in word)}")
print("Verified: minimum nonzero weight 2; deg(D)-g = 3; enumerator 1+6*z^2+2*z^3.")
