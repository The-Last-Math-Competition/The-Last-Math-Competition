import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Data.Fintype.Perm
import Mathlib.Logic.Equiv.Sum
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

noncomputable section
open Filter Asymptotics
open scoped BigOperators Topology

namespace Conjecture4157

def Collision {A B : Type*} (f : A → B) := {v : A × A // f v.1 = f v.2}

def collisionEquiv {A B : Type*} (f : A → B) :
    Collision f ≃ Σ b : B, {x : A // f x = b} × {x : A // f x = b} where
  toFun v := ⟨f v.val.1, ⟨v.val.1, rfl⟩, ⟨v.val.2, v.property.symm⟩⟩
  invFun v := ⟨(v.2.1.val, v.2.2.val), v.2.1.property.trans v.2.2.property.symm⟩
  left_inv v := by rfl
  right_inv v := by
    rcases v with ⟨b, ⟨x, hx⟩, ⟨y, hy⟩⟩
    cases hx
    rfl

/-- Cauchy-Schwarz applied to the actual fibers of a finite map. -/
theorem collision_lower_bound {A B : Type*} [Fintype A] [Fintype B] (f : A → B) :
    Nat.card A ^ 2 ≤ Nat.card B * Nat.card (Collision f) := by
  classical
  let r (b : B) := Nat.card {x : A // f x = b}
  have hs : ∑ b, r b = Nat.card A := by
    rw [← Nat.card_sigma]
    exact Nat.card_congr (Equiv.sigmaFiberEquiv f)
  have hss : ∑ b, r b ^ 2 = Nat.card (Collision f) := by
    rw [Nat.card_congr (collisionEquiv f), Nat.card_sigma]
    simp [r, Nat.card_prod, pow_two]
  have h := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset B) (fun _ => (1 : ℕ)) r
  simpa only [one_mul, one_pow, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    mul_one, hs, hss, ← Nat.card_eq_fintype_card] using h

abbrev Tuple (N : ℕ) := Fin 6 → Fin N
abbrev MomentBox (N : ℕ) := Fin (6 * N + 1) × Fin (6 * N ^ 2 + 1)

/-- The two genuine power sums of six integers in {1,...,N}. -/
def momentMap (N : ℕ) (x : Tuple N) : MomentBox N :=
  (⟨∑ i, ((x i).val + 1), by
      have h : (∑ i, ((x i).val + 1)) ≤ 6 * N := by
        calc
          _ ≤ ∑ _i : Fin 6, N := Finset.sum_le_sum fun i _ => by omega
          _ = 6 * N := by simp
      omega⟩,
   ⟨∑ i, ((x i).val + 1) ^ 2, by
      have h : (∑ i, ((x i).val + 1) ^ 2) ≤ 6 * N ^ 2 := by
        calc
          _ ≤ ∑ _i : Fin 6, N ^ 2 := Finset.sum_le_sum fun i _ =>
            Nat.pow_le_pow_left (by omega) 2
          _ = 6 * N ^ 2 := by simp
      omega⟩)

theorem momentMap_eq_iff (N : ℕ) (x y : Tuple N) :
    momentMap N x = momentMap N y ↔
      (∑ i, ((x i).val + 1)) = (∑ i, ((y i).val + 1)) ∧
      (∑ i, ((x i).val + 1) ^ 2) = (∑ i, ((y i).val + 1) ^ 2) := by
  simp only [momentMap, Prod.mk.injEq, Fin.mk.injEq]

/-- Exactly the ordered solutions defining J_{6,2}(N). -/
abbrev VMVTSolutions (N : ℕ) := Collision (momentMap N)
def J (N : ℕ) : ℕ := Nat.card (VMVTSolutions N)

theorem vmvt_count_lower_bound (N : ℕ) :
    N ^ 12 ≤ ((6 * N + 1) * (6 * N ^ 2 + 1)) * J N := by
  have h := collision_lower_bound (momentMap N)
  simpa [J, Tuple, MomentBox, Nat.card_fun, Nat.card_prod, Nat.card_eq_fintype_card,
    ← pow_mul] using h

theorem ninth_power_lower_bound {N : ℕ} (hN : 1 ≤ N) : N ^ 9 ≤ 49 * J N := by
  have hN2 : 1 ≤ N ^ 2 := by nlinarith
  have hb : (6 * N + 1) * (6 * N ^ 2 + 1) ≤ 49 * N ^ 3 := by
    calc
      _ ≤ (7 * N) * (7 * N ^ 2) := Nat.mul_le_mul (by omega) (by omega)
      _ = 49 * N ^ 3 := by ring
  have h : N ^ 3 * N ^ 9 ≤ N ^ 3 * (49 * J N) := by
    calc
      _ = N ^ 12 := by ring
      _ ≤ _ := vmvt_count_lower_bound N
      _ ≤ (49 * N ^ 3) * J N := Nat.mul_le_mul_right _ hb
      _ = _ := by ring
  exact le_of_mul_le_mul_left h (by positivity : 0 < N ^ 3)

theorem not_bigO_diagonal_order :
    ¬ (fun N : ℕ => (J N : ℝ)) =O[atTop] (fun N : ℕ => (N : ℝ) ^ 6) := by
  intro h
  obtain ⟨C, hC⟩ := isBigO_iff.mp h
  obtain ⟨M, hM⟩ := eventually_atTop.mp hC
  obtain ⟨N, hN⟩ := exists_nat_gt (max (M : ℝ) (49 * |C| + 1))
  have hNM : M ≤ N := by exact_mod_cast (le_of_lt ((le_max_left _ _).trans_lt hN))
  have hlarge : 49 * |C| + 1 < (N : ℝ) := (le_max_right _ _).trans_lt hN
  have hN1 : 1 ≤ N := by
    have : (1 : ℝ) < N := by linarith [abs_nonneg C]
    exact_mod_cast this.le
  have hpos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hu : (J N : ℝ) ≤ C * (N : ℝ) ^ 6 := by
    simpa [Real.norm_eq_abs, abs_of_nonneg (show (0 : ℝ) ≤ (J N : ℝ) from Nat.cast_nonneg _),
      abs_of_nonneg (pow_nonneg hpos.le 6)] using hM N hNM
  have hl : (N : ℝ) ^ 9 ≤ 49 * (J N : ℝ) := by
    exact_mod_cast ninth_power_lower_bound hN1
  have hc : (N : ℝ) ^ 3 ≤ 49 * C := by
    apply (mul_le_mul_right (pow_pos hpos 6)).mp
    calc
      (N : ℝ) ^ 3 * (N : ℝ) ^ 6 = (N : ℝ) ^ 9 := by ring
      _ ≤ 49 * (J N : ℝ) := hl
      _ ≤ (49 * C) * (N : ℝ) ^ 6 := by nlinarith
  have hp : (N : ℝ) ≤ (N : ℝ) ^ 3 :=
    le_self_pow₀ (by exact_mod_cast hN1) (by decide)
  linarith [le_abs_self C]

/-- Genuine diagonal tuples: the right tuple is a permutation of the left. -/
def Diagonal (N : ℕ) := {v : Tuple N × Tuple N //
  ∃ σ : Equiv.Perm (Fin 6), ∀ i, v.2 i = v.1 (σ i)}

def D (N : ℕ) : ℕ := Nat.card (Diagonal N)

def diagonalParameter (N : ℕ) (v : Tuple N × Equiv.Perm (Fin 6)) : Diagonal N :=
  ⟨(v.1, fun i => v.1 (v.2 i)), v.2, fun _ => rfl⟩

theorem diagonalParameter_surjective (N : ℕ) : Function.Surjective (diagonalParameter N) := by
  rintro ⟨⟨x, y⟩, σ, hσ⟩
  refine ⟨(x, σ), ?_⟩
  apply Subtype.ext
  change (x, fun i => x (σ i)) = (x, y)
  exact Prod.ext rfl (funext fun i => (hσ i).symm)

theorem diagonal_satisfies_system (N : ℕ) (v : Diagonal N) :
    momentMap N v.val.1 = momentMap N v.val.2 := by
  obtain ⟨σ, hσ⟩ := v.property
  apply (momentMap_eq_iff _ _ _).mpr
  constructor
  · simp_rw [hσ]
    exact (Equiv.sum_comp σ (fun i => (v.val.1 i).val + 1)).symm
  · simp_rw [hσ]
    exact (Equiv.sum_comp σ (fun i => ((v.val.1 i).val + 1) ^ 2)).symm

theorem diagonal_count_bound (N : ℕ) : D N ≤ 720 * N ^ 6 := by
  calc
    D N ≤ Nat.card (Tuple N × Equiv.Perm (Fin 6)) :=
      Nat.card_le_card_of_surjective _ (diagonalParameter_surjective N)
    _ = 720 * N ^ 6 := by
      simp [Tuple, Nat.card_prod, Nat.card_fun, Nat.card_eq_fintype_card,
        Fintype.card_perm, Nat.factorial, Nat.mul_comm]

theorem diagonal_isBigO :
    (fun N : ℕ => (D N : ℝ)) =O[atTop] (fun N : ℕ => (N : ℝ) ^ 6) := by
  apply isBigO_iff.mpr
  refine ⟨720, Eventually.of_forall fun N => ?_⟩
  simpa [Real.norm_eq_abs, abs_of_nonneg (show (0 : ℝ) ≤ (D N : ℝ) from Nat.cast_nonneg _),
    abs_of_nonneg (pow_nonneg (Nat.cast_nonneg N : (0 : ℝ) ≤ N) 6)] using
    (show (D N : ℝ) ≤ 720 * (N : ℝ) ^ 6 by exact_mod_cast diagonal_count_bound N)

theorem diagonal_not_main_term :
    ¬ (fun N : ℕ => (J N : ℝ)) ~[atTop] (fun N : ℕ => (D N : ℝ)) := by
  intro h
  exact not_bigO_diagonal_order (h.isBigO.trans diagonal_isBigO)

theorem conjecture_range_contains_counterexample : (6 : ℕ) ≤ 2 * (2 + 1) := by decide

/-- The exact solution set for J_{2,1}(N), using entries 0,...,N-1.
Adding 1 to every entry gives the standard interval 1,...,N. -/
def LinearSolutions (N : ℕ) := {v : (Fin N × Fin N) × (Fin N × Fin N) //
  v.1.1.val + v.1.2.val = v.2.1.val + v.2.2.val}

/-- Translation by one identifies this condition with the standard VMVT interval. -/
theorem linear_equation_iff_standard (N : ℕ)
    (v : (Fin N × Fin N) × (Fin N × Fin N)) :
    v.1.1.val + v.1.2.val = v.2.1.val + v.2.2.val ↔
      (v.1.1.val + 1) + (v.1.2.val + 1) =
        (v.2.1.val + 1) + (v.2.2.val + 1) := by omega

abbrev OffsetParameters (N : ℕ) := Σ m : Fin N, Fin m.val × Fin m.val
abbrev LinearParameters (N : ℕ) := (Fin N × Fin N) ⊕
  (OffsetParameters N ⊕ OffsetParameters N)

def offsetSolution (N : ℕ) (p : OffsetParameters N) : LinearSolutions N := by
  rcases p with ⟨m, a, b⟩
  have hm := m.isLt
  have ha := a.isLt
  have hb := b.isLt
  exact ⟨((⟨a.val + (N - m.val), by omega⟩, ⟨b.val, by omega⟩),
    (⟨a.val, by omega⟩, ⟨b.val + (N - m.val), by omega⟩)), by dsimp; omega⟩

def swapLinear (N : ℕ) (v : LinearSolutions N) : LinearSolutions N :=
  ⟨(v.val.2, v.val.1), v.property.symm⟩

def encodeLinear (N : ℕ) : LinearParameters N → LinearSolutions N
  | .inl v => ⟨(v, v), rfl⟩
  | .inr (.inl p) => offsetSolution N p
  | .inr (.inr p) => swapLinear N (offsetSolution N p)

theorem offset_first_gt (N : ℕ) (p : OffsetParameters N) :
    (offsetSolution N p).val.2.1.val < (offsetSolution N p).val.1.1.val := by
  rcases p with ⟨m, a, b⟩
  have hm := m.isLt
  dsimp [offsetSolution]
  omega

theorem offsetSolution_injective (N : ℕ) : Function.Injective (offsetSolution N) := by
  rintro ⟨m, a, b⟩ ⟨n, c, d⟩ h
  have h1 := congrArg (fun v : LinearSolutions N => v.val.1.1.val) h
  have h2 := congrArg (fun v : LinearSolutions N => v.val.1.2.val) h
  have h3 := congrArg (fun v : LinearSolutions N => v.val.2.1.val) h
  dsimp [offsetSolution] at h1 h2 h3
  have hm := m.isLt
  have hn := n.isLt
  have heq : m = n := Fin.ext (by omega)
  subst n
  have hac : a = c := Fin.ext h3
  have hbd : b = d := Fin.ext h2
  subst c
  subst d
  rfl

theorem encodeLinear_injective (N : ℕ) : Function.Injective (encodeLinear N) := by
  intro v w h
  rcases v with v | v | v <;> rcases w with w | w | w
  · have hh := congrArg (fun x : LinearSolutions N => x.val.1) h
    exact congrArg Sum.inl hh
  · have hh := congrArg (fun x : LinearSolutions N =>
      x.val.2.1.val < x.val.1.1.val) h
    have hg := offset_first_gt N w
    simp only [encodeLinear] at hh
    change (v.1.val < v.1.val) = _ at hh
    rw [← hh] at hg
    exact (Nat.lt_irrefl _ hg).elim
  · have hh := congrArg (fun x : LinearSolutions N =>
      x.val.1.1.val < x.val.2.1.val) h
    have hg := offset_first_gt N w
    simp only [encodeLinear, swapLinear] at hh
    change (v.1.val < v.1.val) = _ at hh
    rw [← hh] at hg
    exact (Nat.lt_irrefl _ hg).elim
  · have hh := congrArg (fun x : LinearSolutions N =>
      x.val.2.1.val < x.val.1.1.val) h
    have hg := offset_first_gt N v
    simp only [encodeLinear] at hh
    change _ = (w.1.val < w.1.val) at hh
    rw [hh] at hg
    exact (Nat.lt_irrefl _ hg).elim
  · exact congrArg (fun p => Sum.inr (Sum.inl p)) (offsetSolution_injective N h)
  · have hh1 := congrArg (fun x : LinearSolutions N => x.val.1.1.val) h
    have hh2 := congrArg (fun x : LinearSolutions N => x.val.2.1.val) h
    have hv := offset_first_gt N v
    have hw := offset_first_gt N w
    simp only [encodeLinear, swapLinear] at hh1 hh2
    omega
  · have hh := congrArg (fun x : LinearSolutions N =>
      x.val.1.1.val < x.val.2.1.val) h
    have hg := offset_first_gt N v
    simp only [encodeLinear, swapLinear] at hh
    change _ = (w.1.val < w.1.val) at hh
    rw [hh] at hg
    exact (Nat.lt_irrefl _ hg).elim
  · have hh1 := congrArg (fun x : LinearSolutions N => x.val.1.1.val) h
    have hh2 := congrArg (fun x : LinearSolutions N => x.val.2.1.val) h
    have hv := offset_first_gt N v
    have hw := offset_first_gt N w
    simp only [encodeLinear, swapLinear] at hh1 hh2
    omega
  · have hh := congrArg (swapLinear N) h
    change offsetSolution N v = offsetSolution N w at hh
    exact congrArg (fun p => Sum.inr (Sum.inr p)) (offsetSolution_injective N hh)

theorem encodeLinear_surjective (N : ℕ) : Function.Surjective (encodeLinear N) := by
  rintro ⟨⟨⟨a,b⟩,⟨c,d⟩⟩, h⟩
  have ha := a.isLt
  have hb := b.isLt
  have hc := c.isLt
  have hd := d.isLt
  dsimp at h
  by_cases heq : a.val = c.val
  · have hac : a = c := Fin.ext heq
    have hbd : b = d := Fin.ext (by omega)
    subst c
    subst d
    exact ⟨Sum.inl (a,b), rfl⟩
  · by_cases hgt : c.val < a.val
    · refine ⟨Sum.inr (Sum.inl ⟨⟨N - (a.val - c.val), by omega⟩,
        ⟨c.val, by dsimp; omega⟩, ⟨b.val, by dsimp; omega⟩⟩), ?_⟩
      apply Subtype.ext
      ext <;> dsimp [encodeLinear, offsetSolution] <;> omega
    · refine ⟨Sum.inr (Sum.inr ⟨⟨N - (c.val - a.val), by omega⟩,
        ⟨a.val, by dsimp; omega⟩, ⟨d.val, by dsimp; omega⟩⟩), ?_⟩
      apply Subtype.ext
      ext <;> dsimp [encodeLinear, offsetSolution, swapLinear] <;> omega

def J21 (N : ℕ) : ℕ := Nat.card (LinearSolutions N)

theorem J21_count (N : ℕ) : J21 N = N ^ 2 + 2 * ∑ m : Fin N, m.val ^ 2 := by
  rw [J21, ← Nat.card_eq_of_bijective _ ⟨encodeLinear_injective N, encodeLinear_surjective N⟩]
  simp [Nat.card_sum, Nat.card_prod, Nat.card_sigma, Nat.card_eq_fintype_card, pow_two]
  ring

theorem sum_squares_identity (N : ℕ) :
    6 * (∑ m : Fin N, (m.val : ℝ) ^ 2) = (N : ℝ) * (N - 1) * (2 * N - 1) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Fin.sum_univ_castSucc]
    push_cast
    simp only [Fin.coe_castSucc, Fin.val_last]
    nlinarith

theorem J21_exact (N : ℕ) : (J21 N : ℝ) = (2 * (N : ℝ) ^ 3 + N) / 3 := by
  rw [J21_count]
  push_cast
  have h := sum_squares_identity N
  nlinarith

def samePairs (N : ℕ) : Finset ((Fin N × Fin N) × (Fin N × Fin N)) :=
  Finset.univ.image fun p => (p, p)

def reversedPairs (N : ℕ) : Finset ((Fin N × Fin N) × (Fin N × Fin N)) :=
  Finset.univ.image fun p => (p, (p.2, p.1))

/-- Both permutations of the two coordinates: the exact diagonal solution set. -/
def diagonal21 (N : ℕ) := samePairs N ∪ reversedPairs N
def D21 (N : ℕ) : ℕ := (diagonal21 N).card

theorem diagonal21_mem_iff (N : ℕ) (v : (Fin N × Fin N) × (Fin N × Fin N)) :
    v ∈ diagonal21 N ↔ v.2 = v.1 ∨ v.2 = (v.1.2, v.1.1) := by
  classical
  rcases v with ⟨⟨a,b⟩,⟨c,d⟩⟩
  simp [diagonal21, samePairs, reversedPairs, Prod.mk.injEq]
  aesop

theorem diagonal21_satisfies (N : ℕ) (v : (Fin N × Fin N) × (Fin N × Fin N))
    (h : v ∈ diagonal21 N) : v.1.1.val + v.1.2.val = v.2.1.val + v.2.2.val := by
  rcases (diagonal21_mem_iff N v).mp h with h | h
  · rw [h]
  · rw [h]
    exact Nat.add_comm _ _

theorem pair_intersection (N : ℕ) : samePairs N ∩ reversedPairs N =
    Finset.univ.image (fun a : Fin N => ((a,a),(a,a))) := by
  classical
  ext v
  rcases v with ⟨⟨a,b⟩,⟨c,d⟩⟩
  simp only [samePairs, reversedPairs, Finset.mem_inter, Finset.mem_image,
    Finset.mem_univ, true_and, Prod.mk.injEq]
  aesop

theorem D21_count (N : ℕ) : D21 N + N = 2 * N ^ 2 := by
  classical
  have h1 : (samePairs N).card = N ^ 2 := by
    rw [samePairs, Finset.card_image_of_injective]
    · simp [pow_two]
    · exact fun _ _ h => congrArg Prod.fst h
  have h2 : (reversedPairs N).card = N ^ 2 := by
    rw [reversedPairs, Finset.card_image_of_injective]
    · simp [pow_two]
    · exact fun _ _ h => congrArg Prod.fst h
  have hi : (samePairs N ∩ reversedPairs N).card = N := by
    rw [pair_intersection, Finset.card_image_of_injective]
    · simp
    · exact fun _ _ h => congrArg (fun v => v.1.1) h
  have h := Finset.card_union_add_card_inter (samePairs N) (reversedPairs N)
  rw [h1, h2, hi] at h
  simpa [D21, diagonal21, two_mul] using h

theorem D21_exact (N : ℕ) : (D21 N : ℝ) = 2 * (N : ℝ) ^ 2 - N := by
  have h : (D21 N : ℝ) + N = 2 * (N : ℝ) ^ 2 := by exact_mod_cast D21_count N
  linarith

theorem reciprocal_tends_zero :
    Tendsto (fun N : ℕ => (N : ℝ)⁻¹) atTop (𝓝 0) :=
  tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop

theorem J21_leading_coefficient :
    Tendsto (fun N : ℕ => (J21 N : ℝ) / (N : ℝ) ^ 3) atTop (𝓝 (2 / 3 : ℝ)) := by
  have h : Tendsto (fun N : ℕ => (2/3 : ℝ) + (1/3 : ℝ) * ((N : ℝ)⁻¹) ^ 2)
      atTop (𝓝 (2/3 : ℝ)) := by
    convert tendsto_const_nhds.add (tendsto_const_nhds.mul (reciprocal_tends_zero.pow 2)) using 1
    norm_num
  apply h.congr'
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hne : (N : ℝ) ≠ 0 := by exact_mod_cast (by omega : N ≠ 0)
  rw [J21_exact]
  field_simp [hne]
  ring

theorem D21_leading_coefficient :
    Tendsto (fun N : ℕ => (D21 N : ℝ) / (N : ℝ) ^ 2) atTop (𝓝 (2 : ℝ)) := by
  have h : Tendsto (fun N : ℕ => (2 : ℝ) - (N : ℝ)⁻¹) atTop (𝓝 (2 : ℝ)) := by
    simpa using tendsto_const_nhds.sub reciprocal_tends_zero
  apply h.congr'
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hne : (N : ℝ) ≠ 0 := by exact_mod_cast (by omega : N ≠ 0)
  rw [D21_exact]
  field_simp [hne]
  ring

/-- On the actual cubic scale of J_{2,1}, the diagonal contribution is zero. -/
theorem D21_cubic_coefficient :
    Tendsto (fun N : ℕ => (D21 N : ℝ) / (N : ℝ) ^ 3) atTop (𝓝 (0 : ℝ)) := by
  have h : Tendsto (fun N : ℕ => ((D21 N : ℝ) / (N : ℝ) ^ 2) * (N : ℝ)⁻¹)
      atTop (𝓝 (0 : ℝ)) := by
    simpa using D21_leading_coefficient.mul reciprocal_tends_zero
  apply h.congr'
  exact Eventually.of_forall fun N => by
    simp only [div_eq_mul_inv, inv_pow]
    ring

theorem explicit_coefficient_counterexample :
    (2 : ℕ) ≤ 1 * (1 + 1) ∧ (2 / 3 : ℝ) ≠ 2 ∧
      Tendsto (fun N : ℕ => (J21 N : ℝ) / (N : ℝ) ^ 3) atTop (𝓝 (2 / 3 : ℝ)) ∧
      Tendsto (fun N : ℕ => (D21 N : ℝ) / (N : ℝ) ^ 2) atTop (𝓝 (2 : ℝ)) ∧
      Tendsto (fun N : ℕ => (D21 N : ℝ) / (N : ℝ) ^ 3) atTop (𝓝 (0 : ℝ)) := by
  exact ⟨by decide, by norm_num, J21_leading_coefficient,
    D21_leading_coefficient, D21_cubic_coefficient⟩

end Conjecture4157

#print axioms Conjecture4157.collision_lower_bound
#print axioms Conjecture4157.momentMap_eq_iff
#print axioms Conjecture4157.ninth_power_lower_bound
#print axioms Conjecture4157.not_bigO_diagonal_order
#print axioms Conjecture4157.diagonal_satisfies_system
#print axioms Conjecture4157.diagonal_count_bound
#print axioms Conjecture4157.diagonal_not_main_term
#print axioms Conjecture4157.J21_exact
#print axioms Conjecture4157.linear_equation_iff_standard
#print axioms Conjecture4157.D21_exact
#print axioms Conjecture4157.D21_cubic_coefficient
#print axioms Conjecture4157.explicit_coefficient_counterexample
