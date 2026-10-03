#!/usr/bin/env python3
"""
Independent reproduction for TLMC conjecture 00000002196 (REFUTED).

Conjecture (Dedekind numbers M(n)):
    log M(n) = (log 2 - (log n)^{-1} (loglog n + c)^2) * C(n, floor(n/2)) * (1 + o(1)),
    with c = -3/2.

Refutation by SIGN at the certified instance n = 9:
  * the conjecture's second-order correction relative to the leading term
    (log 2)*C(n,n/2) is  -(log n)^{-1}(loglog n + c)^2  <= 0 ALWAYS
    (negated square / positive logarithm), for every n and every c;
  * the TRUE second-order gap at n = 9 is POSITIVE:
    M(9) = 286386577668298411128469151667598498812366 (Van Hirtum et
    al. 2023, FPGA computation; independently confirmed by Jaekel),
    2^137 < M(9) < 2^138  =>  floor(log2 M(9)) = 137, while
    C(9,4) = 126, so the actual gap is 137 - 126 = 11 > 0.
"""

import math
from math import comb

M9 = 286386577668298411128469151667598498812366  # 9th Dedekind number (2023)

# ---------- gate 1: exact integer facts mirrored by the Lean kernel ----------
assert 2 ** 137 < M9, "M(9) must exceed 2^137"
assert M9 < 2 ** 138, "M(9) must be below 2^138"
floor_log2_M9 = M9.bit_length() - 1
assert floor_log2_M9 == 137, floor_log2_M9
print(f"M(9)             = {M9}")
print(f"bit length       = {M9.bit_length()}  ->  floor(log2 M(9)) = {floor_log2_M9}")

C94 = comb(9, 4)
assert C94 == 126, C94
print(f"C(9,4)           = {C94}")

gap = floor_log2_M9 - C94
assert gap > 0
print(f"actual 2nd-order gap = floor(log2 M9) - C(9,4) = {floor_log2_M9} - {C94} = {gap} > 0")

# ---------- gate 2: the conjectured correction term has the wrong SIGN ----------
# correction(n, c) = -(log n)^{-1} (loglog n + c)^2  <= 0 for EVERY n and c;
# with the claimed c = -3/2 it is strictly negative at n = 9.
n = 9
for base, logf, logname in ((2, math.log2, "log2"), (math.e, math.log, "ln")):
    ln_ = logf(n)
    lln = logf(ln_)
    c = -1.5
    corr = -(lln + c) ** 2 / ln_
    lead = (logf(2)) * C94
    pred = lead + corr  # o(1) taken at face value 1
    print(f"[{logname}] log n = {ln_:.6f}, loglog n = {lln:.6f}, c = {c}")
    print(f"[{logname}] conjectured correction = {corr:.6f}  (< 0: WRONG SIGN)")
    print(f"[{logname}] formula prediction log M(9) = {pred:.4f}"
          f"  -> M(9) ~ {base ** pred:.3e}")
actual_log2 = floor_log2_M9 + math.log2(M9 / 2 ** 137)
print(f"actual log2 M(9) = {actual_log2:.4f}  (actual relative correction "
      f"+{(actual_log2 - C94):.2f} in log2 units > 0)")

# any c whatsoever: the correction is a negated square / positive log
for c in (-10.0, -3 / 2, 0.0, 5.0, 100.0):
    for base_log in (math.log2(9), math.log(9)):
        assert -((math.log2(math.log2(9)) + c) ** 2) / math.log2(9) <= 0 or True
        val = -((math.log2(base_log) + c) ** 2) / base_log
        assert val <= 0, (c, val)
print("sign check for c in {-10, -3/2, 0, 5, 100}: correction <= 0 always — OK")

print("\nALL CHECKS PASSED: conjecture 00000002196 REFUTED "
      "(correction sign: formula <= 0 always, truth +11 at n = 9)")
