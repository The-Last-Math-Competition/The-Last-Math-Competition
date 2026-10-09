import Mathlib.Dynamics.PeriodicPts.Lemmas
import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.Algebra.GCDMonoid.Nat
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FinCases

open Function
open scoped BigOperators

namespace Conjecture1237

abbrev Vertex := Fin 3
abbrev Configuration := Vertex → ℕ

/-- The three directed unit arcs are v -> v+1, with addition modulo 3. -/
def arcs : Finset (Vertex × Vertex) := Finset.univ.filter fun e => e.2 = e.1 + 1

def arcLength (_ : Vertex × Vertex) : ℕ := 1

theorem arc_count : arcs.card = 3 := by decide

theorem one_outgoing_arc (v : Vertex) :
    (arcs.filter fun e => e.1 = v).card = 1 := by
  fin_cases v <;> decide

theorem one_incoming_arc (v : Vertex) :
    (arcs.filter fun e => e.2 = v).card = 1 := by
  fin_cases v <;> decide

theorem directed_cycle_strongly_connected (v w : Vertex) :
    ∃ k : Fin 3, (fun x : Vertex => x + 1)^[k.val] v = w := by
  fin_cases v <;> fin_cases w <;> decide

def outdegree (v : Vertex) : ℕ := (arcs.filter fun e => e.1 = v).card

def Legal (c : Configuration) (v : Vertex) : Prop := outdegree v ≤ c v

instance (c : Configuration) (v : Vertex) : Decidable (Legal c v) := inferInstanceAs
  (Decidable (outdegree v ≤ c v))

/-- Parallel chip firing: subtract each legal vertex's outdegree and send one
    chip along each of its outgoing arcs. -/
def step (c : Configuration) : Configuration := fun v =>
  c v - (if Legal c v then outdegree v else 0) +
    ∑ e ∈ arcs.filter (fun e => e.2 = v), if Legal c e.1 then 1 else 0

/-- The usual single-vertex firing, evaluated only at legal vertices below. -/
def fire (c : Configuration) (u : Vertex) : Configuration := fun v =>
  c v - (if v = u then outdegree u else 0) +
    (arcs.filter fun e => e.1 = u ∧ e.2 = v).card

def chipAt (w : Vertex) : Configuration := fun v => if v = w then 1 else 0

theorem unique_legal_vertex (w v : Vertex) : Legal (chipAt w) v ↔ v = w := by
  fin_cases w <;> fin_cases v <;> decide

theorem one_chip_transition (w : Vertex) : step (chipAt w) = chipAt (w + 1) := by
  fin_cases w <;> ext v <;> fin_cases v <;> decide

theorem parallel_equals_unique_legal_firing (w : Vertex) :
    step (chipAt w) = fire (chipAt w) w := by
  fin_cases w <;> ext v <;> fin_cases v <;> decide

theorem first_three_states :
    step (chipAt 0) = chipAt 1 ∧
    step (chipAt 1) = chipAt 2 ∧
    step (chipAt 2) = chipAt 0 := by decide

theorem return_after_three : IsPeriodicPt step 3 (chipAt 0) := by decide

theorem not_fixed : ¬ IsFixedPt step (chipAt 0) := by decide

theorem actual_period : minimalPeriod step (chipAt 0) = 3 := by
  haveI : Fact (Nat.Prime 3) := ⟨by decide⟩
  exact minimalPeriod_eq_prime return_after_three not_fixed

theorem arc_lengths_lcm : arcs.lcm arcLength = 1 := by decide

theorem conjectured_period_formula_false :
    minimalPeriod step (chipAt 0) ≠ arcs.lcm arcLength := by
  rw [actual_period, arc_lengths_lcm]
  decide

end Conjecture1237

#print axioms Conjecture1237.directed_cycle_strongly_connected
#print axioms Conjecture1237.unique_legal_vertex
#print axioms Conjecture1237.one_chip_transition
#print axioms Conjecture1237.parallel_equals_unique_legal_firing
#print axioms Conjecture1237.actual_period
#print axioms Conjecture1237.conjectured_period_formula_false
