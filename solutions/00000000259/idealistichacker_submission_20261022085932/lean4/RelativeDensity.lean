import PrimePell
import ProductBounds
import Mathlib.Analysis.SpecificLimits.Basic

open Filter
open scoped Topology

namespace PellDensity259

def Eligible (p : Nat) : Prop := p.Prime ∧ p % 4 = 1

def Solvable (p : Nat) : Prop := ∃ x y : Int, x^2 - (p : Int) * y^2 = -1

theorem every_eligible_solvable (p : Nat) (hp : Eligible p) : Solvable p :=
  PrimePell259.negative_pell_of_prime_one_mod_four p hp.1 hp.2

noncomputable section

def eligiblePrimesBelow (N : Nat) : Finset Nat := by
  classical
  exact (Finset.range N).filter (fun p => Eligible p)

def successfulPrimesBelow (N : Nat) : Finset Nat := by
  classical
  exact (Finset.range N).filter (fun p => Eligible p ∧ Solvable p)

theorem successful_eq_eligible (N : Nat) : successfulPrimesBelow N = eligiblePrimesBelow N := by
  classical
  ext p
  simp only [successfulPrimesBelow, eligiblePrimesBelow, Finset.mem_filter]
  exact ⟨fun h => ⟨h.1, h.2.1⟩,
    fun h => ⟨h.1, h.2, every_eligible_solvable p h.2⟩⟩

theorem eligible_count_pos (N : Nat) (hN : 6 ≤ N) : 0 < (eligiblePrimesBelow N).card := by
  apply Finset.card_pos.mpr
  refine ⟨5, ?_⟩
  simp only [eligiblePrimesBelow, Finset.mem_filter, Finset.mem_range]
  exact ⟨by omega, by norm_num [Eligible]⟩

def relativeDensity (N : Nat) : Real :=
  ((successfulPrimesBelow N).card : Real) / (eligiblePrimesBelow N).card

theorem relativeDensity_one (N : Nat) (hN : 6 ≤ N) : relativeDensity N = 1 := by
  unfold relativeDensity
  rw [successful_eq_eligible]
  apply div_self
  exact_mod_cast (Nat.ne_of_gt (eligible_count_pos N hN))

theorem relativeDensity_tendsto : Tendsto relativeDensity atTop (nhds (1 : Real)) := by
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_ge_atTop 6] with N hN
  exact (relativeDensity_one N hN).symm

theorem not_claimed_relative_density :
    ¬ Tendsto relativeDensity atTop (nhds PellConstant259.claimedConstant) := by
  intro h
  exact PellConstant259.claimedConstant_not_one
    (tendsto_nhds_unique h relativeDensity_tendsto)

theorem pell_109_certificate : (8890182 : Int)^2 - 109 * 851525^2 = -1 := by
  norm_num

end
end PellDensity259
