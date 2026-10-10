# Infinite periodic counts for a polynomial identity system

Conjecture 00000005401 omits any finiteness or isolation condition on periodic points. The genuine two-variable polynomial identity map on the real plane fixes every point under every positive iterate. Its fixed-point counts are infinite, so the proposed finite zero/constant, linear, exponential growth classification fails. The invariant compact unit square has the same problem. The report distinguishes points fixed by the n-th iterate from points of least period n.

The Lean project verifies the coordinate polynomials, true function iterates, explicit injections into fixed-point sets, infinitude, the negation of finite counting, exact-period-one infinitude and the invariant-square version.

Reproduce with Lean 4.19.0: run lake update then lake build inside lean. Public Mathlib requirement and manifest pin c44e0c8ee63ca166450922a373c7409c5d26b00b. Printed final theorem audits use only standard axioms. No sorry/admit/native_decide/custom axioms/unsafe; ignored local package junctions are conveniences only.
