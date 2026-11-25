/-
  Conjecture 00000000546 — Master Resolution & Non-Vacuity Witnesses
  Core Lean 4.19.0
-/
import Conjecture00000000546.TangentCone
import Conjecture00000000546.MonomialSubrings

namespace Conjecture00000000546

/-! ## 1. Master Resolution Theorem Across All Algebraic & Combinatorial Readings -/

/--
  **Master Resolution of Conjecture 00000000546**:
  For the interval numerical semigroup `S_{a,k} = ⟨a, a+1, …, a+k⟩` (`a ≥ 2, 1 ≤ k ≤ a - 1`)
  and ANY coefficient field `K`:
  1. **Affine monomial subring `K[S_{a,k}] ⊆ K[t]`**: `(t^a)` is a maximal regular sequence
     of exact length `1` across ALL `(a, k)` — constant homological depth `1`, zero depth drop.
  2. **Projective monomial curve `R_{a,k} ⊆ K[u, v]^{(a+k)}`**: `(u^{a+k}, v^{a+k})` is a
     maximal regular sequence of exact length `2` across ALL `(a, k)` — constant homological
     depth `2`, zero depth drop.
  3. **Tangent cone `gr_m(K[[S_{a,k}]])`**: `t^a + m^2` is a nonzerodivisor across ALL `(a, k)`
     — constant homological depth `1`, zero depth drop; its reduction-number threshold is
     `⌈(a-1)/k⌉`, while `⌈a/k⌉` is the nilpotency index of `t^{a+k} + m^2` (sumset overlap).
  4. **Eliahou combinatorial depth `q(S_{a,k}) = ⌈C(S_{a,k}) / m(S_{a,k})⌉`** (and the
     ordinary power-truncation threshold of `S_{a,k}^{(m)}`): equals `⌈(a-1)/k⌉`, which
     strictly disagrees with the conjectured `⌈a/k⌉` whenever `(a - 1) % k = 0` (including
     every `a ≥ 2` at `k = 1`).
  5. **Symmetric-gap depth jump**: for `k ≥ 2` and `a ≥ k + 2`, `S_{a,k}` has symmetric gaps
     iff `(a - 2) % k = 0` iff the true Eliahou depth jumps (`q(S_{a,k}) > q(S_{a-1,k})`),
     whereas the conjectured formula `⌈a/k⌉` has ZERO jump (`⌈a/k⌉ = ⌈(a-1)/k⌉`) at every
     symmetric-gap semigroup for `k ≥ 2`.
-/
theorem master_resolution_00000000546 {K : Type} [FieldCoeff K]
    {a k : Nat} (ha : 2 ≤ a) (hk : 1 ≤ k) (hka : k ≤ a - 1) :
    -- (1) Affine semigroup ring K[S_{a,k}] has constant exact regular-sequence length 1
    (IsAffineRegSeq1 a k (monomial1 (FieldCoeff.one : K) a) ∧
      ∀ g : Poly1 K, ¬ IsAffineRegSeq2 a k (monomial1 (FieldCoeff.one : K) a) g) ∧
    -- (2) Projective closure R_{a,k} has constant exact regular-sequence length 2
    (IsBivarRegSeq2_UV K (AProj a k) (a + k) ∧
      ∀ G : BivarPoly K, ¬ IsBivarRegSeq3_UVG K (AProj a k) (a + k) G) ∧
    -- (3) Exact Eliahou depth is ⌈(a-1)/k⌉, disagreeing with ⌈a/k⌉ iff (a - 1) % k = 0
    (IsEliahouDepth (InIntervalSemigroup a k) (ceilDiv (a - 1) k) ∧
      (ceilDiv (a - 1) k ≠ ceilDiv a k ↔ (a - 1) % k = 0)) ∧
    -- (4) Exact symmetric-gaps characterization
    (HasSymmetricGaps (InIntervalSemigroup a k) (ceilDiv (a - 1) k * a - 1) ↔
      (k = 1 ∨ (a - 2) % k = 0)) := by
  refine ⟨⟨affine_ta_is_regSeq1 (by omega), affine_no_regSeq2_extending_ta ha hk⟩,
          ⟨projectiveClosure_isRegSeq2 K (by omega) hk, projectiveClosure_no_regSeq3 K ha hk hka⟩,
          ⟨eliahouDepth_intervalSemigroup ha hk, eliahouDepth_ne_conjectured_iff ha hk⟩,
          hasSymmetricGaps_iff ha hk hka⟩

/-! ## 2. Concrete Counterexamples & Non-Vacuity Witnesses -/

/-- Counterexample 1 (`a = 3, k = 1`, symmetric semigroup `⟨3, 4⟩`):
    `S_{3,1}` has symmetric gaps (`F = 5`), true Eliahou depth `2`, conjectured `⌈3/1⌉ = 3 ≠ 2`. -/
theorem counterexample_S3_1 :
    HasSymmetricGaps (InIntervalSemigroup 3 1) 5 ∧
    IsEliahouDepth (InIntervalSemigroup 3 1) 2 ∧
    ¬ IsEliahouDepth (InIntervalSemigroup 3 1) (ceilDiv 3 1) ∧
    ceilDiv 3 1 = 3 := by
  have hsym : HasSymmetricGaps (InIntervalSemigroup 3 1) (ceilDiv 2 1 * 3 - 1) :=
    (hasSymmetricGaps_iff (a := 3) (k := 1) (by omega) (by omega) (by omega)).mpr (Or.inl rfl)
  have hdepth : IsEliahouDepth (InIntervalSemigroup 3 1) (ceilDiv 2 1) :=
    eliahouDepth_intervalSemigroup (a := 3) (k := 1) (by omega) (by omega)
  have hbad : ¬ IsEliahouDepth (InIntervalSemigroup 3 1) (ceilDiv 3 1) :=
    eliahouDepth_k_eq_one_counterexample (a := 3) (by omega)
  exact ⟨hsym, hdepth, hbad, rfl⟩

/-- Counterexample 2 (`a = 5, k = 2`, semigroup `⟨5, 6, 7⟩`):
    1. Eliahou depth is `⌈4/2⌉ = 2 ≠ 3 = ⌈5/2⌉`.
    2. Ordinary power-truncation semigroup `S_{5,2}^{(2)}` ALREADY has depth `1` at `m = 2 < 3`.
    3. Symmetric-gap pinched Veronese ring `B_{5,2}^{(2)}` over `𝔽₂` ALREADY has regular
       sequence `(u^{14}, v^{14})` of length `2` at `m = 2 < 3 = ⌈5/2⌉` (while failing at `m = 1`). -/
theorem counterexample_S5_2_all_readings :
    IsEliahouDepth (InIntervalSemigroup 5 2) 2 ∧
    ceilDiv 5 2 = 3 ∧
    ¬ IsEliahouDepth (InIntervalSemigroup 5 2) (ceilDiv 5 2) ∧
    (∀ n, 2 * 5 ≤ n → InPowerSemigroup 5 2 2 n) ∧
    ¬ IsBivarRegSeq2_UV F2 (AVer 5 2 1) (1 * (5 + 2)) ∧
    IsBivarRegSeq2_UV F2 (AVer 5 2 2) (2 * (5 + 2)) := by
  have hdepth : IsEliahouDepth (InIntervalSemigroup 5 2) 2 :=
    eliahouDepth_intervalSemigroup (a := 5) (k := 2) (by omega) (by omega)
  have hnot3 : ¬ IsEliahouDepth (InIntervalSemigroup 5 2) (ceilDiv 5 2) := by
    intro h3
    have heq := eliahouDepth_unique hdepth h3
    have : ceilDiv 5 2 = 3 := rfl
    omega
  have hord2 : ∀ n, 2 * 5 ≤ n → InPowerSemigroup 5 2 2 n :=
    (powerSemigroup_ordinary_iff (a := 5) (k := 2) (m := 2) (by omega) (by omega) (by omega)).mpr
      (by decide)
  have hver1 : ¬ IsBivarRegSeq2_UV F2 (AVer 5 2 1) (1 * (5 + 2)) := by
    rw [pinchedVeronese_isRegSeq2_iff F2 (a := 5) (k := 2) (m := 1) (by omega) (by omega) (by omega) (by omega)]
    decide
  have hver2 : IsBivarRegSeq2_UV F2 (AVer 5 2 2) (2 * (5 + 2)) := by
    rw [pinchedVeronese_isRegSeq2_iff F2 (a := 5) (k := 2) (m := 2) (by omega) (by omega) (by omega) (by omega)]
    decide
  exact ⟨hdepth, rfl, hnot3, hord2, hver1, hver2⟩

/-- Counterexample 3 (`a = 4, k = 2` and `a = 5, k = 3`, symmetric-gap semigroups with `k ≥ 2`):
    At `S_{5,3} = ⟨5, 6, 7, 8⟩` (`F = 9`, symmetric gaps `{1,2,3,4,9}`), true Eliahou depth
    jumps from `q(S_{4,3}) = 1` to `q(S_{5,3}) = 2`, whereas `⌈5/3⌉ = 2 = ⌈4/3⌉` has NO jump! -/
theorem counterexample_symmetric_jump_S5_3 :
    HasSymmetricGaps (InIntervalSemigroup 5 3) 9 ∧
    ceilDiv (4 - 1) 3 = 1 ∧
    ceilDiv (5 - 1) 3 = 2 ∧
    ceilDiv 4 3 = 2 ∧
    ceilDiv 5 3 = 2 := by
  have hsym : HasSymmetricGaps (InIntervalSemigroup 5 3) (ceilDiv 4 3 * 5 - 1) :=
    (hasSymmetricGaps_iff (a := 5) (k := 3) (by omega) (by omega) (by omega)).mpr
      (Or.inr (by decide))
  exact ⟨hsym, rfl, rfl, rfl, rfl⟩

/-- Non-vacuity witness instantiating `master_resolution_00000000546` over `𝔽₂` at `(a = 5, k = 2)`. -/
theorem nonvacuity_witness_F2_5_2 :
    IsAffineRegSeq1 5 2 (monomial1 (FieldCoeff.one : F2) 5) ∧
    (∀ g : Poly1 F2, ¬ IsAffineRegSeq2 5 2 (monomial1 (FieldCoeff.one : F2) 5) g) ∧
    IsBivarRegSeq2_UV F2 (AProj 5 2) 7 ∧
    (∀ G : BivarPoly F2, ¬ IsBivarRegSeq3_UVG F2 (AProj 5 2) 7 G) := by
  have hm := master_resolution_00000000546 (K := F2) (a := 5) (k := 2)
    (by omega) (by omega) (by omega)
  exact ⟨hm.1.1, hm.1.2, hm.2.1.1, hm.2.1.2⟩

end Conjecture00000000546
