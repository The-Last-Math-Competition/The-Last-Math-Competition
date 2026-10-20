/-
Disproof of Conjecture 00000002160:
"The independence number of the Higman–Sims graph equals the Hoffman bound, and the kernel
of the bound is the Delsarte semilattice."
-/
import Conjecture2160.HigmanSims
import Conjecture2160.Spectral

namespace Conjecture2160

open SimpleGraph

/-- The least adjacency eigenvalue of the Higman–Sims graph is `-8`. -/
theorem higmanSims_minAdjEigenvalue : minAdjEigenvalue higmanSims = -8 :=
  srg_minAdjEigenvalue higmanSims higmanSims_isSRG

/-- Hoffman's ratio bound for the (22-regular) Higman–Sims graph is `100·8/(22+8) = 80/3`. -/
theorem higmanSims_hoffmanBound : hoffmanBound higmanSims 22 = 80 / 3 :=
  srg_hoffmanBound higmanSims higmanSims_isSRG

/-- The neighbourhood of `∞` (the 22 points) is an independent set, so `α(HS) ≥ 22`. -/
theorem higmanSims_indepNum_ge : 22 ≤ higmanSims.indepNum := by
  have hs : higmanSims.IsIndepSet
      ((Finset.univ.filter (fun v : Fin 100 => 1 ≤ (v : ℕ) ∧ (v : ℕ) ≤ 22) : Finset (Fin 100)) :
        Set (Fin 100)) := by
    intro a ha b hb hab hadj
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at ha hb
    change hsAdjNat a b = true at hadj
    unfold hsAdjNat at hadj
    split_ifs at hadj <;> simp at hadj <;> omega
  have := hs.card_le_indepNum
  simpa [show (Finset.univ.filter (fun v : Fin 100 => 1 ≤ (v : ℕ) ∧ (v : ℕ) ≤ 22)).card = 22
    from by decide] using this

/-- **Conjecture 00000002160 is false.**  The Higman–Sims graph is 22-regular, and its
independence number is *not* equal to Hoffman's ratio bound `n·(-λ_min)/(k-λ_min)`: the bound
equals `80/3`, which is not an integer. -/
theorem conjecture_2160_false :
    higmanSims.IsRegularOfDegree 22 ∧ (higmanSims.indepNum : ℝ) ≠ hoffmanBound higmanSims 22 :=
  ⟨higmanSims_isSRG.regular, srg_indepNum_ne_hoffmanBound higmanSims higmanSims_isSRG⟩

end Conjecture2160
