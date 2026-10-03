#!/usr/bin/env python3
"""
Independent reproduction for TLMC conjecture 00000004172 (REFUTED).

Conjecture: boundary density for the dense circle method is 5/8;
sets of density below 5/8 can completely avoid nontrivial sums.

Refutation under both readings: (a) the interval {1..60} in [1,100]
has density 0.6 < 0.625 but is full of sums; (b) sum-free sets cap
at density 1/2 (odds), so no set of density in (1/2, 5/8) can avoid
sums — the true boundary is 1/2, not 5/8.
"""

# ---------- gate 1: reading (a) — dense interval with sums ----------
N = 100
A = set(range(1, 61))
density = len(A) / N
assert density == 0.6 < 0.625
sums_in_A = sum(1 for a in A for b in A if a + b in A)
assert sums_in_A >= 60  # 1+1..1+59, 2+1.. etc: thousands
print(f"reading (a): A = {{1..60}} in [1,100]: density {density} < 5/8, "
      f"but {sums_in_A} ordered nontrivial sum pairs land in A — REFUTED")

# ---------- gate 2: reading (b) — sum-free ceiling is 1/2 ----------
odds = set(range(1, N + 1, 2))
assert all(a + b not in odds for a in odds for b in odds)
assert len(odds) == 50
print(f"reading (b): odds are sum-free of size 50 (density 1/2); "
      f"max sum-free size = ceil(N/2) = 50 < 60: no density-0.6 sum-free set — REFUTED")

# ---------- gate 3: exhaustive confirmation for small N ----------
def max_sumfree_bruteforce(N):
    # brute force over all subsets for tiny N
    best = 0
    for mask in range(2 ** N):
        S = {i + 1 for i in range(N) if mask >> i & 1}
        if all(a + b not in S for a in S for b in S):
            best = max(best, len(S))
    return best

for N in (6, 8, 10):
    m = max_sumfree_bruteforce(N)
    assert m == (N + 1) // 2, (N, m)
    print(f"N={N}: brute-force max sum-free size = {m} = ceil(N/2) (density 1/2) — OK")

print("\nALL CHECKS PASSED: conjecture 00000004172 REFUTED "
      "(true boundary density is 1/2, not 5/8)")
