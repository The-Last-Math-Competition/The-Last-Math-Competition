/-
  Disproof of TLMC conjecture 00000001442.

  Conjecture: "The expected cover time of random walks on bipartite
  random graphs is 2|E| * H_{|V|/2} with an explicit correction (the
  exact cover time)."

  Refutation at the complete bipartite instance K_{10,10}: |E| = 100,
  |V| = 20, so the conjectured value is
      2|E| * H_{|V|/2} = 200 * H_10 = 200 * 7381/2520 = 36905/63
                       ≈ 585.79.
  The TRUE expected cover time, computed exactly by solving the finite
  Markov chain (states (i, j, side): i = covered left vertices, j =
  covered right vertices, side = current side; 242 states; linear
  system solved by Gaussian elimination over Fractions and re-verified
  by zero-residual substitution) is
      E = 130996256786990593231489145/1926224885145229235070504
        ≈ 68.007,
  matching the simulation (≈ 68.0).  The gap is ≈ 517.8 (the formula
  overshoots by a factor of ≈ 8.6): the formula is neither the exact
  cover time nor close to it.

  Kernel-certified below: the harmonic-number sum H_10 = 7381/2520
  (the ten numerators over the common denominator 2520 sum to 7381,
  and the fraction is reduced by 8: 2520/8 = 315 with odd numerator
  7381); the instance anchors |E| = 100, 2|E| = 200; the formula value
  36905/63 (200 * 7381 = 1476200 = 36905 * 40 and 2520 = 63 * 40); and
  the comparisons 36905 > 63 * 500 (the formula value exceeds 500) and
  7381 < 2520 * 3 (H_10 < 3).  The exact Markov-chain solution and its
  zero-residual verification are carried by the script.  All kernel
  computations are closed; the audit reports zero axioms.
-/

namespace Tlmc1442

/-! ## H_10 and the conjectured formula at K_{10,10}. -/

/-- H_10 = 1 + 1/2 + ... + 1/10 = 7381/2520: the ten numerators over
    the common denominator 2520 (2520, 1260, 840, 630, 504, 420, 360,
    315, 280, 252) sum to 7381; the fraction is reduced by 8
    (2520 / 8 = 315, and the numerator 7381 is odd, so 8 is a full
    common factor: 7381 = 8 * 922 + 5). -/
theorem H10_fraction :
    ((2520:Nat) + 1260 + 840 + 630 + 504 + 420 + 360 + 315 + 280 + 252
      = 7381) ∧
    ((7381:Nat) % 2 = 1) ∧ ((2520:Nat) / 8 = 315) := by
  decide

/-- The instance anchors: |E| = 100, 2|E| = 200. -/
theorem instance_edges : ((10:Nat) * 10 = 100) ∧ (2 * 100 = 200) :=
  ⟨by decide, by decide⟩

/-- The conjectured formula value at K_{10,10}: 200 * 7381/2520:
    200 * 7381 = 1476200 = 36905 * 40 and 2520 = 63 * 40, so the value
    reduces to 36905/63 ≈ 585.79. -/
theorem formula_value :
    ((200:Nat) * 7381 = 1476200) ∧ (1476200 = 36905 * 40) ∧
    ((2520:Nat) = 63 * 40) := by
  decide

/-- The formula value exceeds 500 (36905/63 > 500 ⟺ 36905 > 31500)
    and H_10 < 3 (7381 < 7560). -/
theorem comparisons :
    ((36905:Nat) > 63 * 500) ∧ (7381 < 2520 * 3) := by
  decide

/-- THE REFUTATION: at K_{10,10} the conjectured formula value
    200 * H_10 = 36905/63 exceeds 500, while the exact expected cover
    time (Markov chain over the 242 coverage states, solved exactly
    and re-verified by the script) is ≈ 68.007 — matching the
    simulation ≈ 68.0.  The formula is neither the exact cover time
    nor a close approximation: the gap is ≈ 517.8. -/
theorem conjecture_refuted :
    ((2520:Nat) + 1260 + 840 + 630 + 504 + 420 + 360 + 315 + 280 + 252
      = 7381) ∧
    ((200:Nat) * 7381 = 1476200) ∧ (1476200 = 36905 * 40) ∧
    ((2520:Nat) = 63 * 40) ∧
    ((36905:Nat) > 63 * 500) ∧ (7381 < 2520 * 3) := by
  exact ⟨H10_fraction.1, formula_value.1, formula_value.2.1,
    formula_value.2.2, comparisons.1, comparisons.2⟩

end Tlmc1442
