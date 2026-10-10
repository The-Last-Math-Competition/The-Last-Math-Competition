import Mathlib.Data.Real.Irrational
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Data.Finset.Order
import Mathlib.Tactic
import WordCombinatorics

noncomputable section

namespace SturmianCF

abbrev Slope := { t : ℝ // 0 < t ∧ t < 1 ∧ Irrational t }

def rawStep (t : ℝ) (j : ℕ) : ℤ := ⌊(j+1 : ℕ) * t⌋ - ⌊(j : ℝ) * t⌋

theorem rawStep_bounds (t : Slope) (j : ℕ) : 0 ≤ rawStep t j ∧ rawStep t j ≤ 1 := by
  have hlo : (j : ℝ) * t ≤ (j+1 : ℕ) * t := by
    push_cast; nlinarith [t.2.1]
  have hhi : (j+1 : ℕ) * (t : ℝ) < j*t+1 := by
    push_cast; nlinarith [t.2.2.1]
  have hfloor := Int.floor_mono hlo
  have hupper : ⌊(j+1 : ℕ) * (t : ℝ)⌋ < ⌊j*(t : ℝ)⌋+2 := by
    apply Int.floor_lt.mpr
    push_cast
    push_cast at hhi
    linarith [Int.lt_floor_add_one ((j:ℝ)*t)]
  dsimp [rawStep]
  omega

def mechanical (t : Slope) (j : ℕ) : Fin 2 :=
  ⟨(rawStep t j).toNat, (Int.toNat_lt (rawStep_bounds t j).1).2 (by have := (rawStep_bounds t j).2; omega)⟩

theorem mechanical_val (t : Slope) (j : ℕ) : ((mechanical t j).val : ℤ) = rawStep t j :=
  Int.toNat_of_nonneg (rawStep_bounds t j).1

/-- Number of ones in a factor, expressed without a summation. -/
def cumul (t : ℝ) (j k : ℕ) : ℤ := ⌊((j+k : ℕ) : ℝ)*t⌋ - ⌊(j : ℝ)*t⌋

theorem cumul_fract (t : ℝ) (j k : ℕ) :
    cumul t j k = ⌊(k : ℝ)*t + Int.fract ((j : ℝ)*t)⌋ := by
  rw [cumul, ← Int.floor_sub_intCast]
  congr 1
  rw [Int.fract]
  push_cast
  ring

theorem cumul_zero (t : ℝ) (j : ℕ) : cumul t j 0 = 0 := by simp [cumul]

theorem cumul_succ_sub (t : ℝ) (j k : ℕ) :
    cumul t j (k+1) - cumul t j k = rawStep t (j+k) := by
  simp only [cumul, rawStep, Nat.add_assoc]
  ring

def gap (t : ℝ) (j k : ℕ) : ℤ := cumul t j k - ⌊(k : ℝ)*t⌋

theorem gap_bounds (t : ℝ) (j k : ℕ) : 0 ≤ gap t j k ∧ gap t j k ≤ 1 := by
  rw [gap, cumul_fract]
  have hlo := Int.floor_mono (show (k:ℝ)*t ≤ (k:ℝ)*t+Int.fract (j*t) by
    linarith [Int.fract_nonneg ((j:ℝ)*t)])
  have hhi : ⌊(k:ℝ)*t+Int.fract ((j:ℝ)*t)⌋ < ⌊(k:ℝ)*t⌋+2 := by
    apply Int.floor_lt.mpr
    push_cast
    linarith [Int.fract_lt_one ((j:ℝ)*t), Int.lt_floor_add_one ((k:ℝ)*t)]
  omega

theorem gap_mono (t : ℝ) (j l k : ℕ)
    (h : Int.fract ((j:ℝ)*t) ≤ Int.fract ((l:ℝ)*t)) : gap t j k ≤ gap t l k := by
  simp only [gap, cumul_fract]
  exact sub_le_sub_right (Int.floor_mono (add_le_add_left h _)) _

def rank (t : ℝ) (n j : ℕ) : ℤ := ∑ i : Fin n, gap t j (i.val+1)

theorem rank_bounds (t : ℝ) (n j : ℕ) : 0 ≤ rank t n j ∧ rank t n j ≤ n := by
  constructor
  · exact Finset.sum_nonneg (fun i _ => (gap_bounds t j (i.val+1)).1)
  · calc rank t n j ≤ ∑ _i : Fin n, (1 : ℤ) :=
          Finset.sum_le_sum (fun i _ => (gap_bounds t j (i.val+1)).2)
         _ = n := by simp

theorem rank_eq_implies_block_eq (t : Slope) (n j l : ℕ)
    (heq : rank t n j = rank t n l) : block (mechanical t) n j = block (mechanical t) n l := by
  have hgap : ∀ i : Fin n, gap t j (i.val+1) = gap t l (i.val+1) := by
    rcases le_total (Int.fract ((j:ℝ)*t)) (Int.fract ((l:ℝ)*t)) with h | h
    · exact fun i => (Finset.sum_eq_sum_iff_of_le (fun i _ => gap_mono t j l (i.val+1) h)).1 heq i (Finset.mem_univ i)
    · exact fun i => ((Finset.sum_eq_sum_iff_of_le (fun i _ => gap_mono t l j (i.val+1) h)).1 heq.symm i (Finset.mem_univ i)).symm
  have hc : ∀ k ≤ n, cumul t j k = cumul t l k := by
    intro k hk
    cases k with
    | zero => simp [cumul_zero]
    | succ k => have hg := hgap ⟨k, by omega⟩; dsimp [gap] at hg; omega
  funext i
  apply Fin.ext
  apply Int.ofNat_inj.mp
  change ((mechanical t (j+i)).val : ℤ) = ((mechanical t (l+i)).val : ℤ)
  rw [mechanical_val, mechanical_val, ← cumul_succ_sub, ← cumul_succ_sub,
    hc (i.val+1) (by omega), hc i.val (by omega)]

noncomputable def factorRank (t : Slope) (n : ℕ) (u : Factor (mechanical t) n) : Fin (n+1) :=
  let j := Classical.choose u.2
  ⟨(rank t n j).toNat, (Int.toNat_lt (rank_bounds t n j).1).2 (by have := (rank_bounds t n j).2; omega)⟩

theorem factorRank_injective (t : Slope) (n : ℕ) : Function.Injective (factorRank t n) := by
  intro u v h
  apply Subtype.ext
  rw [← Classical.choose_spec u.2, ← Classical.choose_spec v.2]
  apply rank_eq_implies_block_eq
  have hv := congrArg (fun x : Fin (n+1) => (x.val : ℤ)) h
  dsimp [factorRank] at hv
  simpa only [Int.toNat_of_nonneg (rank_bounds _ _ _).1] using hv

theorem complexity_le_length_add_one (t : Slope) (n : ℕ) : complexity (mechanical t) n ≤ n+1 := by
  simpa using Fintype.card_le_of_injective (factorRank t n) (factorRank_injective t n)

/-- An elementary Archimedean bound: a positive slope cannot stay bounded. -/
theorem nonpos_of_nat_mul_le (x C : ℝ) (h : ∀ n : ℕ, (n:ℝ)*x ≤ C) : x ≤ 0 := by
  by_contra! hx
  obtain ⟨n, hn⟩ := exists_nat_gt (C/x)
  have hg := (div_lt_iff₀ hx).1 hn
  linarith [h n]

theorem cumul_eq_of_tail_eq (t s : Slope) (j l : ℕ)
    (h : ∀ k, mechanical t (j+k) = mechanical s (l+k)) :
    ∀ k, cumul t j k = cumul s l k := by
  intro k
  induction k with
  | zero => simp [cumul_zero]
  | succ k ih =>
    have hh := congrArg (fun x : Fin 2 => (x.val : ℤ)) (h k)
    dsimp only at hh
    rw [mechanical_val, mechanical_val] at hh
    have ht := cumul_succ_sub t j k
    have hs := cumul_succ_sub s l k
    omega

theorem mechanical_injective : Function.Injective mechanical := by
  intro t s h
  apply Subtype.ext
  have hc (k : ℕ) : ⌊(k:ℝ)*(t:ℝ)⌋ = ⌊(k:ℝ)*(s:ℝ)⌋ := by
    have := cumul_eq_of_tail_eq t s 0 0 (fun k => by simpa using congrFun h k) k
    simpa [cumul] using this
  have hle : (t:ℝ) ≤ s := by
    have hn : (t:ℝ)-(s:ℝ) ≤ 0 := nonpos_of_nat_mul_le _ 1 (fun k => by
      have ht := Int.lt_floor_add_one ((k:ℝ)*(t:ℝ))
      have hs := Int.floor_le ((k:ℝ)*(s:ℝ))
      rw [hc k] at ht
      nlinarith)
    linarith
  have hge : (s:ℝ) ≤ t := by
    have hn : (s:ℝ)-(t:ℝ) ≤ 0 := nonpos_of_nat_mul_le _ 1 (fun k => by
      have ht := Int.floor_le ((k:ℝ)*(t:ℝ))
      have hs := Int.lt_floor_add_one ((k:ℝ)*(s:ℝ))
      rw [← hc k] at hs
      nlinarith)
    linarith
  exact le_antisymm hle hge

theorem mechanical_aperiodic (t : Slope) : Aperiodic (mechanical t) := by
  intro j l hjl
  by_contra! heq
  have hc := cumul_eq_of_tail_eq t t j l heq
  let q := l-j
  have hq : 0 < q := by dsimp [q]; omega
  have hl : l = j+q := by dsimp [q]; omega
  let c : ℤ := ⌊(l:ℝ)*(t:ℝ)⌋ - ⌊(j:ℝ)*(t:ℝ)⌋
  have hs (k : ℕ) : ⌊((l+k:ℕ):ℝ)*(t:ℝ)⌋ = ⌊((j+k:ℕ):ℝ)*(t:ℝ)⌋ + c := by
    have := hc k
    dsimp [cumul, c] at *
    omega
  have hp (m : ℕ) : ⌊((j+m*q:ℕ):ℝ)*(t:ℝ)⌋ = ⌊(j:ℝ)*(t:ℝ)⌋ + (m:ℤ)*c := by
    induction m with
    | zero => simp
    | succ m ih =>
      have hh := hs (m*q)
      have hid : l+m*q = j+(m+1)*q := by rw [hl]; ring
      rw [hid, ih] at hh
      rw [hh]
      push_cast
      ring
  have hd : (q:ℝ)*(t:ℝ) = (c:ℝ) := by
    have hle : (q:ℝ)*(t:ℝ)-(c:ℝ) ≤ 0 :=
      nonpos_of_nat_mul_le _ ((⌊(j:ℝ)*(t:ℝ)⌋:ℝ)+1-(j:ℝ)*(t:ℝ)) (fun m => by
        have hf := Int.lt_floor_add_one (((j+m*q:ℕ):ℝ)*(t:ℝ))
        rw [hp m] at hf
        push_cast at hf
        nlinarith)
    have hge : (c:ℝ)-(q:ℝ)*(t:ℝ) ≤ 0 :=
      nonpos_of_nat_mul_le _ ((j:ℝ)*(t:ℝ)-(⌊(j:ℝ)*(t:ℝ)⌋:ℝ)) (fun m => by
        have hf := Int.floor_le (((j+m*q:ℕ):ℝ)*(t:ℝ))
        rw [hp m] at hf
        push_cast at hf
        nlinarith)
    linarith
  have hrat : (t:ℝ) = (c:ℝ)/(q:ℝ) := by
    apply (eq_div_iff (by exact_mod_cast Nat.ne_of_gt hq)).2
    nlinarith [hd]
  exact (irrational_iff_ne_rational (t:ℝ)).1 t.2.2.2 c (q:ℤ) (by simpa using hrat)

theorem mechanical_complexity (t : Slope) (n : ℕ) : complexity (mechanical t) n = n+1 :=
  le_antisymm (complexity_le_length_add_one t n)
    (length_add_one_le_complexity (mechanical t) (mechanical_aperiodic t) n)

end SturmianCF
