import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

noncomputable section
open scoped BigOperators
namespace Conjecture8240

/-- `false` is cooperation and `true` is defection. The second player's
payoff is obtained by interchanging the two arguments. -/
def stage : Bool → Bool → ℝ
  | false, false => 2
  | true, false => 3
  | false, true => 0
  | true, true => 1

/-- Permanent punishment is triggered by any observed defection. -/
def state (initial : Bool) (actions : ℕ → Bool) : ℕ → Bool
  | 0 => initial
  | n + 1 => state initial actions n || actions n

def payoff (δ : ℝ) (initial : Bool) (actions : ℕ → Bool) : ℝ :=
  ∑' n : ℕ, δ ^ n * stage (actions n) (state initial actions n)

def prescribed (initial : Bool) : ℕ → Bool := fun _ => initial

/-- Both players use the same grim strategy. Every finite history reduces
to one of the two public states. Quantification over all action streams
includes every pure history-dependent unilateral deviation against it. -/
def GrimSPE (δ : ℝ) : Prop :=
  ∀ initial actions, payoff δ initial actions ≤ payoff δ initial (prescribed initial)

def value : Bool → ℝ | false => 4 | true => 2

theorem value_nonneg (b : Bool) : 0 ≤ value b := by cases b <;> norm_num [value]
theorem stage_nonneg (a b : Bool) : 0 ≤ stage a b := by
  cases a <;> cases b <;> norm_num [stage]

theorem bellman (b a : Bool) : stage a b + (1 / 2 : ℝ) * value (b || a) ≤ value b := by
  cases b <;> cases a <;> norm_num [stage, value]

/-- A finite-horizon bound retains the nonnegative terminal continuation
value; it therefore controls arbitrary, repeated deviations. -/
theorem finite_bound (b : Bool) (a : ℕ → Bool) (N : ℕ) :
    (∑ n ∈ Finset.range N, (1 / 2 : ℝ)^n * stage (a n) (state b a n)) +
      (1 / 2 : ℝ)^N * value (state b a N) ≤ value b := by
  induction N with
  | zero => simp [state]
  | succ N ih =>
    rw [Finset.sum_range_succ, pow_succ]
    have h := mul_le_mul_of_nonneg_left (bellman (state b a N) (a N))
      (pow_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2) N)
    simp only [state] at *
    nlinarith

theorem deviation_bound (b : Bool) (a : ℕ → Bool) : payoff (1 / 2) b a ≤ value b := by
  apply Real.tsum_le_of_sum_range_le
  · intro n
    exact mul_nonneg (pow_nonneg (by norm_num) n) (stage_nonneg _ _)
  · intro N
    have h := finite_bound b a N
    have hterminal := mul_nonneg (pow_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2) N)
      (value_nonneg (state b a N))
    linarith

theorem prescribed_state (b : Bool) (n : ℕ) : state b (prescribed b) n = b := by
  induction n with
  | zero => rfl
  | succ n ih => simp [state, ih, prescribed]

theorem prescribed_payoff (b : Bool) : payoff (1 / 2) b (prescribed b) = value b := by
  unfold payoff
  simp only [prescribed_state, prescribed]
  cases b
  · have h := (hasSum_geometric_two.mul_right (2 : ℝ)).tsum_eq
    norm_num at h ⊢
    simpa [stage, value] using h
  · simpa [stage, value] using hasSum_geometric_two.tsum_eq

theorem half_grim_spe : GrimSPE (1 / 2) := by
  intro b a
  rw [prescribed_payoff]
  exact deviation_bound b a

abbrev History := List (Bool × Bool)
abbrev Profile := Bool → History → Bool

/-- Histories are stored in reverse chronological order. `side=false`
is the first player, and `side=true` the second. -/
def outcome (side own other : Bool) : Bool × Bool :=
  if side then (other, own) else (own, other)

def trajectory (σ : Profile) (side : Bool) (h : History) (a : ℕ → Bool) : ℕ → History
  | 0 => h
  | n + 1 => let hn := trajectory σ side h a n
    outcome side (a n) (σ (!side) hn) :: hn

def historyPayoff (δ : ℝ) (σ : Profile) (side : Bool) (h : History) (a : ℕ → Bool) : ℝ :=
  ∑' n : ℕ, δ^n * stage (a n) (σ (!side) (trajectory σ side h a n))

theorem stage_le_three (a b : Bool) : stage a b ≤ 3 := by
  cases a <;> cases b <;> norm_num [stage]

/-- The payoff is a convergent discounted series for every strategy
profile and every unilateral stream throughout the discount domain. -/
theorem history_payoff_summable (δ : ℝ) (hδ : 0 ≤ δ) (hδ1 : δ < 1)
    (σ : Profile) (side : Bool) (h : History) (a : ℕ → Bool) :
    Summable (fun n : ℕ => δ^n * stage (a n) (σ (!side) (trajectory σ side h a n))) := by
  apply Summable.of_nonneg_of_le
    (fun n => mul_nonneg (pow_nonneg hδ n) (stage_nonneg _ _))
    (fun n => mul_le_mul_of_nonneg_left (stage_le_three _ _) (pow_nonneg hδ n))
    ((summable_geometric_of_lt_one hδ hδ1).mul_right (3 : ℝ))

def Compliant (σ : Profile) (side : Bool) (h : History) (a : ℕ → Bool) : Prop :=
  ∀ n, a n = σ side (trajectory σ side h a n)

/-- At every finite history and for both players, following the profile
is at least as good as every unilateral infinite action stream. -/
def SPE (δ : ℝ) (σ : Profile) : Prop :=
  ∀ side h, ∃ a, Compliant σ side h a ∧
    ∀ deviation, historyPayoff δ σ side h deviation ≤ historyPayoff δ σ side h a

def Cooperates (σ : Profile) : Prop :=
  ∀ side, Compliant σ side [] (fun _ => false)

def sustainable : Set ℝ :=
  {δ | 0 < δ ∧ δ < 1 ∧ ∃ σ : Profile, SPE δ σ ∧ Cooperates σ}
def critical : ℝ := sInf sustainable

def punished (h : History) : Bool := h.any (fun p => p.1 || p.2)
def grim : Profile := fun _ h => punished h

theorem trajectory_state (side : Bool) (h : History) (a : ℕ → Bool) (n : ℕ) :
    punished (trajectory grim side h a n) = state (punished h) a n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [trajectory, punished, List.any_cons, grim]
    change (((outcome side (a n) (punished (trajectory grim side h a n))).1 ||
      (outcome side (a n) (punished (trajectory grim side h a n))).2) ||
      punished (trajectory grim side h a n)) = state (punished h) a (n+1)
    rw [ih]
    simp only [state]
    cases side <;> cases a n <;> cases state (punished h) a n <;> rfl

theorem grim_payoff (δ : ℝ) (side : Bool) (h : History) (a : ℕ → Bool) :
    historyPayoff δ grim side h a = payoff δ (punished h) a := by
  unfold historyPayoff payoff
  apply tsum_congr
  intro n
  simp only [grim, trajectory_state]

theorem grim_compliant (side : Bool) (h : History) :
    Compliant grim side h (prescribed (punished h)) := by
  intro n
  simp only [grim, trajectory_state, prescribed_state, prescribed]

theorem grim_is_spe : SPE (1 / 2) grim := by
  intro side h
  refine ⟨prescribed (punished h), grim_compliant side h, ?_⟩
  intro a
  rw [grim_payoff, grim_payoff]
  exact half_grim_spe (punished h) a

theorem grim_cooperates : Cooperates grim := by
  intro side
  simpa [punished, prescribed] using grim_compliant side []

theorem half_sustainable : (1 / 2 : ℝ) ∈ sustainable :=
  ⟨by norm_num, by norm_num, grim, grim_is_spe, grim_cooperates⟩

/-- Even this particular fully verified cooperative equilibrium gives a
critical discount at most one half. No optimality assertion is needed. -/
theorem critical_le_half : critical ≤ 1 / 2 := by
  apply csInf_le
  · exact ⟨0, fun _ hx => le_of_lt hx.1⟩
  · exact half_sustainable

/-- Literal payoff-ratio assertion of the first conjunct, specialized
to this repeated prisoner's dilemma. `critical` ranges over all pure
history-dependent cooperative SPE, not just grim-trigger profiles. -/
def ClaimedRatio : Prop := critical = stage true false / stage false false

theorem conjecture8240_false : ¬ ClaimedRatio := by
  intro h
  have hc := critical_le_half
  unfold ClaimedRatio stage at h
  rw [h] at hc
  norm_num at hc

#print axioms half_grim_spe
#print axioms history_payoff_summable
#print axioms grim_is_spe
#print axioms critical_le_half
#print axioms conjecture8240_false
end Conjecture8240
