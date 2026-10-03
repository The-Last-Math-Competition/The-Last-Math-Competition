import Mathlib

/-!
# Refutation of TLMC conjecture 00000004396

The conjecture asserts that **every Möbius ladder is Sidorenko** (plus
parallel claims about odd subdivisions of trees and infinitude of the
union).  We refute its first, and principal, conjunct.

A graph `G` is *Sidorenko* when the homomorphism bound

    hom(G, H) · |V(H)|^{|E(G)|} ≥ hom(K₂, H)^{|E(G)|} · |V(H)|^{|V(G)|}

holds for **every** finite host graph `H`.  Specializing `H = K₂`, any
non-bipartite `G` has `hom(G, K₂) = 0` while the right side stays
positive — so every Sidorenko graph is bipartite.

The Möbius ladder `M_k` on `2k` vertices is bipartite iff `k` is odd.
We exhibit `M₂ = K₄` (on the vertex set `ZMod 4`) as a Möbius ladder
that is not Sidorenko, so the claimed universal statement is false.
-/

namespace Submission00000004396

open SimpleGraph

/-- Number of graph homomorphisms `G →g H` between finite graphs. -/
noncomputable def homCount {V W : Type} [Fintype V] [Fintype W]
    (G : SimpleGraph V) (H : SimpleGraph W) : ℕ :=
  Nat.card (G →g H)

/-- `G` is **Sidorenko**: the homomorphism bound above holds against every
finite host `H`.  This is the counting form of `t(G,W) ≥ t(K₂,W)^{e(G)}`. -/
def IsSidorenko {V : Type} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] : Prop :=
  ∀ {W : Type} [Fintype W] (H : SimpleGraph W),
    homCount G H * (Fintype.card W) ^ G.edgeFinset.card ≥
      homCount (⊤ : SimpleGraph (Fin 2)) H ^ G.edgeFinset.card *
        (Fintype.card W) ^ Fintype.card V

/-- The Möbius ladder on `2n + 2` vertices `ZMod (2n+2)`: rim edges
`i ~ i±1` and antipodal spokes `i ~ i+(n+1)`.  With `k = n+1` spokes this
is the classical Möbius ladder `M_k`; the shift keeps the modulus `≥ 2`
so the graph is simple (loopless) for every `n`, no side conditions. -/
def mobiusLadder (n : ℕ) : SimpleGraph (ZMod (2 * n + 2)) where
  Adj i j := j = i + 1 ∨ i = j + 1 ∨ j = i + n + 1 ∨ i = j + n + 1
  symm := ⟨fun i j h => by
    rcases h with h | h | h | h
    · exact Or.inr (Or.inl h)
    · exact Or.inl h
    · exact Or.inr (Or.inr (Or.inr h))
    · exact Or.inr (Or.inr (Or.inl h))⟩
  loopless := ⟨fun i h => by
    rcases h with h | h | h | h
    · have h2 : i + (0 : ZMod (2*n+2)) = i + 1 := by rw [add_zero]; exact h
      rw [add_left_cancel_iff] at h2
      have e : ((1 : ℕ) : ZMod (2*n+2)) = 0 := by push_cast; rw [h2]
      rw [ZMod.natCast_eq_zero_iff] at e
      have := Nat.le_of_dvd (by norm_num) e
      omega
    · have h2 : i + (0 : ZMod (2*n+2)) = i + 1 := by rw [add_zero]; exact h
      rw [add_left_cancel_iff] at h2
      have e : ((1 : ℕ) : ZMod (2*n+2)) = 0 := by push_cast; rw [h2]
      rw [ZMod.natCast_eq_zero_iff] at e
      have := Nat.le_of_dvd (by norm_num) e
      omega
    · rw [add_assoc] at h
      have h2 : i + (0 : ZMod (2*n+2)) = i + (↑n + 1) := by rw [add_zero]; exact h
      rw [add_left_cancel_iff] at h2
      have e : ((n+1 : ℕ) : ZMod (2*n+2)) = 0 := by push_cast; rw [h2]
      rw [ZMod.natCast_eq_zero_iff] at e
      have := Nat.le_of_dvd (by omega : 0 < n+1) e
      omega
    · rw [add_assoc] at h
      have h2 : i + (0 : ZMod (2*n+2)) = i + (↑n + 1) := by rw [add_zero]; exact h
      rw [add_left_cancel_iff] at h2
      have e : ((n+1 : ℕ) : ZMod (2*n+2)) = 0 := by push_cast; rw [h2]
      rw [ZMod.natCast_eq_zero_iff] at e
      have := Nat.le_of_dvd (by omega : 0 < n+1) e
      omega⟩

instance (n : ℕ) : DecidableRel (mobiusLadder n).Adj := fun i j =>
  inferInstanceAs
    (Decidable (j = i + 1 ∨ i = j + 1 ∨ j = i + n + 1 ∨ i = j + n + 1))

/-- `mobiusLadder 1` is the classical Möbius ladder `M₂` on `ZMod 4`;
it equals `K₄`: every pair of distinct vertices is a rim or spoke
neighbour. -/
theorem mobiusLadder_one_eq_top : mobiusLadder 1 = ⊤ := by
  rw [SimpleGraph.eq_top_iff_forall_ne_adj]
  intro a b hab
  fin_cases a <;> fin_cases b <;>
    first
      | (exact absurd rfl hab)
      | (exact Or.inl rfl)
      | (exact Or.inr (Or.inl rfl))
      | (exact Or.inr (Or.inr (Or.inl rfl)))

/-- No homomorphism maps `K₄` into `K₂`: vertices `0,1,2` are pairwise
adjacent, so their images would be three pairwise-distinct elements of
`Fin 2`. -/
theorem isEmpty_hom_K4_K2 :
    IsEmpty ((⊤ : SimpleGraph (Fin 4)) →g (⊤ : SimpleGraph (Fin 2))) := by
  constructor
  intro f
  have h01 : (f 0 ≠ f 1) := fun h => by
    have hadj := f.map_rel (show (⊤ : SimpleGraph (Fin 4)).Adj 0 1 from
      (top_adj _ _).mpr (by decide))
    rw [h] at hadj
    exact (top_adj _ _).mp hadj rfl
  have h02 : (f 0 ≠ f 2) := fun h => by
    have hadj := f.map_rel (show (⊤ : SimpleGraph (Fin 4)).Adj 0 2 from
      (top_adj _ _).mpr (by decide))
    rw [h] at hadj
    exact (top_adj _ _).mp hadj rfl
  have h12 : (f 1 ≠ f 2) := fun h => by
    have hadj := f.map_rel (show (⊤ : SimpleGraph (Fin 4)).Adj 1 2 from
      (top_adj _ _).mpr (by decide))
    rw [h] at hadj
    exact (top_adj _ _).mp hadj rfl
  -- three pairwise-distinct values in `Fin 2` violate the pigeonhole
  have v01 : (f 0).val ≠ (f 1).val := fun h => h01 (Fin.ext h)
  have v02 : (f 0).val ≠ (f 2).val := fun h => h02 (Fin.ext h)
  have v12 : (f 1).val ≠ (f 2).val := fun h => h12 (Fin.ext h)
  have h0 : (f 0).val < 2 := (f 0).isLt
  have h1 : (f 1).val < 2 := (f 1).isLt
  have h2 : (f 2).val < 2 := (f 2).isLt
  omega

/-- The canonical bijection `Fin 4 ≃ ZMod 4`. -/
def fin4EquivZmod4 : Fin 4 ≃ ZMod (2 * 1 + 2) :=
  (ZMod.finEquiv 4).symm.toEquiv

/-- Transport `IsEmpty (K₄ →g K₂)` across the vertex bijection
`Fin 4 ≃ ZMod 4`: there is no homomorphism `(⊤ on ZMod 4) →g (⊤ on Fin 2)`. -/
theorem isEmpty_hom_top_zmod4_K2 :
    IsEmpty ((⊤ : SimpleGraph (ZMod (2 * 1 + 2))) →g (⊤ : SimpleGraph (Fin 2))) := by
  constructor
  intro g
  -- precompose `g` with `Fin 4 ≃ ZMod 4` to get `K₄ →g K₂`
  let φ : (⊤ : SimpleGraph (Fin 4)) →g (⊤ : SimpleGraph (ZMod (2 * 1 + 2))) :=
    ⟨fun v => fin4EquivZmod4 v, fun {a b} hadj => by
      rw [top_adj] at hadj ⊢
      exact fun h => hadj (fin4EquivZmod4.injective h)⟩
  exact (isEmpty_hom_K4_K2).false (g.comp φ)

/-- `homCount (mobiusLadder 1) K₂ = 0`: the hom type is empty. -/
theorem homCount_mobiusLadder_one_K2 :
    homCount (mobiusLadder 1) (⊤ : SimpleGraph (Fin 2)) = 0 := by
  rw [mobiusLadder_one_eq_top]
  have := isEmpty_hom_top_zmod4_K2
  rw [homCount]
  exact Finite.card_eq_zero_iff.mpr this

/-- **Main theorem.** The Möbius ladder `M₂` is not Sidorenko, so the
conjecture "all Möbius ladders are Sidorenko" is false. -/
theorem not_sidorenko_mobiusLadder_one : ¬ IsSidorenko (mobiusLadder 1) := by
  intro h
  -- specialize to the host H = K₂ = ⊤ on Fin 2
  have hK2 := h (⊤ : SimpleGraph (Fin 2))
  rw [homCount_mobiusLadder_one_K2] at hK2
  -- LHS = 0, so RHS must be 0; but RHS is ≥ 1 via the identity hom K₂ → K₂.
  have hpos : 0 < homCount (⊤ : SimpleGraph (Fin 2)) (⊤ : SimpleGraph (Fin 2)) := by
    haveI : Fintype ((⊤ : SimpleGraph (Fin 2)) →g (⊤ : SimpleGraph (Fin 2))) :=
      Fintype.ofFinite _
    have hne : Nonempty ((⊤ : SimpleGraph (Fin 2)) →g (⊤ : SimpleGraph (Fin 2))) :=
      ⟨SimpleGraph.Hom.id⟩
    rw [homCount]
    exact Finite.card_pos_iff.mpr hne
  have hR : 0 < homCount (⊤ : SimpleGraph (Fin 2)) (⊤ : SimpleGraph (Fin 2)) ^
        (mobiusLadder 1).edgeFinset.card *
          (Fintype.card (Fin 2)) ^ Fintype.card (ZMod (2*1+2)) :=
    Nat.mul_pos (Nat.pow_pos hpos) (Nat.pow_pos Fintype.card_pos)
  omega

end Submission00000004396
