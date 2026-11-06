import Mathlib.Logic.Function.Iterate
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! Actual positive inverse fibers, with either standard normalization of Collatz.
The finite-depth unfolded tree permits cyclic-root labels at different depths. -/
namespace TLMC1294
open Function Filter
open scoped Topology

def step (shortcut : Bool) (n : ℕ) : ℕ :=
  if n % 2 = 0 then n / 2 else if shortcut then (3*n+1)/2 else 3*n+1

def Good (n : ℕ) : Prop := 0 < n ∧ n % 3 ≠ 0

theorem step_double (b : Bool) (n : ℕ) : step b (2*n) = n := by
  simp [step]

theorem double_iterate (b : Bool) (k n : ℕ) : (step b)^[k] (2^k*n) = n := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply, show 2^(k+1)*n = 2*(2^k*n) by ring,
      step_double, ih]

theorem route (b : Bool) (p k x n : ℕ) (h : step b x = 2^k*n) :
    (step b)^[k+1+p] (2^p*x) = n := by
  rw [Function.iterate_add_apply, double_iterate]
  rw [Function.iterate_succ_apply, h, double_iterate]

theorem odd_block (b : Bool) (x n k : ℕ) (hk : 1 ≤ k ∧ k ≤ 6)
    (hx : x % 2 = 1) (heq : 3*x+1 = 2^k*n) :
    (step b)^[7] ((if b then 2 else 1)*2^(6-k)*x) = n := by
  cases b with
  | false =>
    have hs : step false x = 2^k*n := by simp [step, hx, heq]
    have he : k+1+(6-k)=7 := by omega
    simpa [he] using route false (6-k) k x n hs
  | true =>
    have hp : 2^k = 2 * 2^(k-1) := by
      conv_lhs => rw [show k = (k-1)+1 by omega]
      rw [pow_succ]; omega
    have hs : step true x = 2^(k-1)*n := by
      simp [step, hx, heq, hp, Nat.mul_assoc]
    have he : (k-1)+1+(7-k)=7 := by omega
    have hp' : 2^(7-k)=2*2^(6-k) := by
      rw [show 7-k=(6-k)+1 by omega, pow_succ]; omega
    simpa [he, hp', Nat.mul_assoc] using route true (7-k) (k-1) x n hs

def oddX (r q : ℕ) (j : Fin 2) : ℕ :=
  match r with
  | 1 => if j=0 then 12*q+1 else 48*q+5
  | 2 => if j=0 then 6*q+1 else 24*q+5
  | 4 => if j=0 then 12*q+5 else 192*q+85
  | 5 => if j=0 then 24*q+13 else 96*q+53
  | 7 => if j=0 then 48*q+37 else 192*q+149
  | 8 => if j=0 then 6*q+5 else 96*q+85
  | _ => 0

def oddK (r : ℕ) (j : Fin 2) : ℕ :=
  match r with
  | 1 => if j=0 then 2 else 4
  | 2 => if j=0 then 1 else 3
  | 4 => if j=0 then 2 else 6
  | 5 => if j=0 then 3 else 5
  | 7 => if j=0 then 4 else 6
  | 8 => if j=0 then 1 else 5
  | _ => 1

def child (b : Bool) (n : ℕ) (j : Fin 3) : ℕ :=
  if h : j.val = 0 then 128*n else
    (if b then 2 else 1)*2^(6-oddK (n%9) ⟨j.val-1, by omega⟩)*
      oddX (n%9) (n/9) ⟨j.val-1, by omega⟩

theorem good_residue (n : ℕ) (hn : Good n) :
    n%9=1 ∨ n%9=2 ∨ n%9=4 ∨ n%9=5 ∨ n%9=7 ∨ n%9=8 := by
  have h9 := Nat.mod_lt n (by decide : 0<9)
  have h3 : n%9%3 = n%3 := by omega
  unfold Good at hn
  omega

theorem child_spec (b : Bool) (n : ℕ) (hn : Good n) (j : Fin 3) :
    (step b)^[7] (child b n j) = n := by
  have hdiv : n = 9*(n/9)+n%9 := by omega
  fin_cases j
  · simpa [child] using double_iterate b 7 n
  all_goals
    rcases good_residue n hn with hr|hr|hr|hr|hr|hr
    all_goals
      simp only [child, Fin.isValue, Nat.reduceEqDiff, ↓reduceDIte, hr, oddK, oddX]
      apply odd_block
      · norm_num
      · norm_num; omega
      · norm_num; omega

theorem child_good (b : Bool) (n : ℕ) (hn : Good n) (j : Fin 3) :
    Good (child b n j) := by
  have hdiv : n = 9*(n/9)+n%9 := by omega
  fin_cases j <;> cases b <;>
    rcases good_residue n hn with hr|hr|hr|hr|hr|hr <;>
    norm_num [child, hr, oddK, oddX, Good] <;> omega

theorem child_injective (b : Bool) (n : ℕ) (hn : Good n) :
    Function.Injective (child b n) := by
  have hdiv : n = 9*(n/9)+n%9 := by omega
  intro i j hij
  fin_cases i <;> fin_cases j <;> cases b <;>
    rcases good_residue n hn with hr|hr|hr|hr|hr|hr <;>
    norm_num [child, hr, oddK, oddX] at hij ⊢ <;> omega

theorem step_good (b : Bool) (n : ℕ) (hn : Good n) : Good (step b n) := by
  unfold Good at hn ⊢
  unfold step
  split_ifs <;> omega

theorem iterate_good (b : Bool) (n k : ℕ) (hn : Good n) :
    Good ((step b)^[k] n) := by
  induction k with
  | zero => simpa using hn
  | succ k ih => simpa [Function.iterate_succ_apply'] using step_good b _ ih

theorem one_le_twice_step (b : Bool) (x : ℕ) : x ≤ 2*step b x := by
  unfold step
  split_ifs <;> omega

theorem iterate_bound (b : Bool) (N x : ℕ) : x ≤ 2^N*(step b)^[N] x := by
  induction N generalizing x with
  | zero => simp
  | succ N ih =>
    have h := (one_le_twice_step b x).trans (Nat.mul_le_mul_left 2 (ih (step b x)))
    simpa [Function.iterate_succ_apply, pow_succ, Nat.mul_assoc,
      Nat.mul_comm, Nat.mul_left_comm] using h

def level (b : Bool) (N : ℕ) : Finset ℕ :=
  (Finset.range (2^N+1)).filter (fun x => 0<x ∧ (step b)^[N] x=1)

def prunedLevel (b : Bool) (N : ℕ) : Finset ℕ :=
  (level b N).filter (fun x => x%3≠0)

theorem mem_level (b : Bool) (N x : ℕ) :
    x ∈ level b N ↔ 0<x ∧ (step b)^[N] x=1 := by
  simp only [level, Finset.mem_filter, Finset.mem_range]
  constructor
  · exact fun h => h.2
  · intro h
    have hb := iterate_bound b N x
    rw [h.2, Nat.mul_one] at hb
    exact ⟨by omega,h⟩

theorem mem_prunedLevel (b : Bool) (N x : ℕ) :
    x ∈ prunedLevel b N ↔ Good x ∧ (step b)^[N] x=1 := by
  simp [prunedLevel, mem_level, Good, and_assoc, and_left_comm, and_comm]

theorem pruned_path (b : Bool) (N x : ℕ) (hx : x∈prunedLevel b N) (i : ℕ) :
    Good ((step b)^[i] x) :=
  iterate_good b x i ((mem_prunedLevel b N x).mp hx).1

def node (b : Bool) : (m : ℕ) → (Fin m → Fin 3) → ℕ
  | 0, _ => 1
  | m+1, w => child b (node b m (fun i => w i.succ)) (w 0)

theorem node_good (b : Bool) (m : ℕ) (w : Fin m → Fin 3) : Good (node b m w) := by
  induction m with
  | zero => norm_num [node,Good]
  | succ m ih => exact child_good b _ (ih _) _

theorem node_iterate (b : Bool) (m : ℕ) (w : Fin m → Fin 3) :
    (step b)^[7*m] (node b m w)=1 := by
  induction m with
  | zero => simp [node]
  | succ m ih =>
    rw [show 7*(m+1)=7*m+7 by omega, Function.iterate_add_apply]
    rw [node, child_spec b _ (node_good b m _)]; exact ih _

theorem node_injective (b : Bool) (m : ℕ) : Function.Injective (node b m) := by
  induction m with
  | zero => intro u v _; exact Subsingleton.elim _ _
  | succ m ih =>
    intro u v huv
    have hp := congrArg ((step b)^[7]) huv
    simp only [node, child_spec b _ (node_good b m _)] at hp
    have ht := ih hp
    have hz : u 0 = v 0 := by
      apply child_injective b _ (node_good b m _)
      simpa only [node, ht] using huv
    funext i
    refine Fin.cases hz (fun j => congrFun ht j) i

theorem exponential_lower_bound (b : Bool) (m : ℕ) :
    3^m ≤ (prunedLevel b (7*m)).card := by
  let f : (Fin m → Fin 3) → {x // x∈prunedLevel b (7*m)} :=
    fun w => ⟨node b m w, (mem_prunedLevel b _ _).mpr
      ⟨node_good b m w,node_iterate b m w⟩⟩
  have hf : Function.Injective f := by
    intro u v huv
    exact node_injective b m (congrArg Subtype.val huv)
  simpa using Fintype.card_le_of_injective f hf

theorem unpruned_lower_bound (b : Bool) (m : ℕ) :
    3^m ≤ (level b (7*m)).card :=
  (exponential_lower_bound b m).trans (Finset.card_le_card (Finset.filter_subset _ _))

noncomputable def claimedBase : ℝ := Real.sqrt (4/3)

theorem claimedBase_properties : 0 < claimedBase ∧ claimedBase^7 < 3 := by
  have hpos : 0 < claimedBase := Real.sqrt_pos.mpr (by norm_num)
  have hsq : claimedBase^2 = (4/3:ℝ) := Real.sq_sqrt (by norm_num)
  have he : (claimedBase^7)^2 = (4/3:ℝ)^7 := by
    rw [← pow_mul, Nat.mul_comm 7 2, pow_mul, hsq]
  have hh : (claimedBase^7)^2 < (3:ℝ)^2 := by rw [he]; norm_num
  exact ⟨hpos, by nlinarith [pow_pos hpos 7]⟩

theorem violates_every_bound (b : Bool) (C : ℝ) (N : ℕ) :
    ∃ n ≥ N, C*claimedBase^n < ((prunedLevel b n).card:ℝ) := by
  have hc := claimedBase_properties
  have hr0 : 0 ≤ claimedBase^7/3 := div_nonneg (pow_nonneg hc.1.le _) (by norm_num)
  have hr1 : claimedBase^7/3 < 1 := by linarith
  have hlim : Tendsto (fun m : ℕ => C*(claimedBase^7/3)^m) atTop (𝓝 0) := by
    simpa using tendsto_const_nhds.mul
      (tendsto_pow_atTop_nhds_zero_of_lt_one hr0 hr1)
  have hsmall : ∀ᶠ m : ℕ in atTop, C*(claimedBase^7/3)^m < 1 :=
    (tendsto_order.mp hlim).2 1 (by norm_num)
  obtain ⟨m,hmN,hm⟩ := ((eventually_ge_atTop N).and hsmall).exists
  refine ⟨7*m,by omega,?_⟩
  have hp : 0 < (3:ℝ)^m := by positivity
  have he : (claimedBase^7/3)^m = claimedBase^(7*m)/(3:ℝ)^m := by
    rw [div_pow, ← pow_mul]
  rw [he, ← mul_div_assoc] at hm
  have hh : C*claimedBase^(7*m) < (3:ℝ)^m := by
    simpa using (div_lt_iff₀ hp).mp hm
  have hl : (3:ℝ)^m ≤ ((prunedLevel b (7*m)).card:ℝ) := by
    exact_mod_cast exponential_lower_bound b m
  exact hh.trans_le hl

theorem pruned_not_bigO (b : Bool) :
    ¬ Asymptotics.IsBigO atTop (fun n => ((prunedLevel b n).card:ℝ))
      (fun n => claimedBase^n) := by
  intro h
  obtain ⟨C,hC⟩ := h.bound
  obtain ⟨N,hN⟩ := eventually_atTop.mp hC
  obtain ⟨n,hn,hn'⟩ := violates_every_bound b C N
  have hb := hN n hn
  have hb' : ((prunedLevel b n).card:ℝ) ≤ C*claimedBase^n := by
    simpa only [Real.norm_eq_abs, abs_of_nonneg (show (0:ℝ)≤(prunedLevel b n).card by positivity),
      abs_of_pos (pow_pos claimedBase_properties.1 _)] using hb
  exact (not_le.mpr hn') hb'

theorem unpruned_not_bigO (b : Bool) :
    ¬ Asymptotics.IsBigO atTop (fun n => ((level b n).card:ℝ))
      (fun n => claimedBase^n) := by
  intro h
  obtain ⟨C,hC⟩ := h.bound
  obtain ⟨N,hN⟩ := eventually_atTop.mp hC
  obtain ⟨n,hn,hn'⟩ := violates_every_bound b C N
  have hb := hN n hn
  have hl : ((prunedLevel b n).card:ℝ) ≤ ((level b n).card:ℝ) := by
    exact_mod_cast Finset.card_le_card (Finset.filter_subset (fun x => x%3≠0) (level b n))
  have hh : C*claimedBase^n < ((level b n).card:ℝ) := hn'.trans_le hl
  have hb' : ((level b n).card:ℝ) ≤ C*claimedBase^n := by
    simpa only [Real.norm_eq_abs, abs_of_nonneg (show (0:ℝ)≤(level b n).card by positivity),
      abs_of_pos (pow_pos claimedBase_properties.1 _)] using hb
  exact (not_le.mpr hh) hb'

theorem both_normalizations_disprove_claim :
    (¬ Asymptotics.IsBigO atTop (fun n => ((level false n).card:ℝ))
      (fun n => claimedBase^n)) ∧
    (¬ Asymptotics.IsBigO atTop (fun n => ((level true n).card:ℝ))
      (fun n => claimedBase^n)) := ⟨unpruned_not_bigO false,unpruned_not_bigO true⟩

end TLMC1294
