import Conjecture00000004770.PartitionsAndAnnulus

namespace Conjecture00000004770

/-!
# Scope Boundary: Induced Sublattices of Disc Noncrossing Partitions

While NO pair of *canonical* annular and boundary noncrossing partition families
forms non-isomorphic lattices with matching Möbius spectra, we prove here that the
obstruction is genuinely topological/canonical rather than an abstract poset-theoretic
identity: if one allows arbitrary finite subfamilies inside `NC(n)`, then:
1. Inside `NC(4)`, two explicit 5-element induced subposet lattices (`nc4SubStem5` and
   `nc4SubPentagon5`) are non-isomorphic lattices with the exact same lower-interval
   Möbius spectrum `{1: 2, -1: 2, 0: 1}`.
2. Inside `NC(8)` (realized via contiguous interval partitions), two explicit 10-element
   self-dual graded sublattices (`poset10A` and `poset10B`) are non-isomorphic lattices
   whose lower-interval, upper-interval, AND full two-variable Möbius spectra all coincide
   simultaneously (`bot = top = {1: 1, -1: 1, 0: 8}`, `full = {1: 12, -1: 11, 0: 30}`).
-/

/-- Decidable check of `IsDiscNC` via `finAll`. -/
def isDiscNCBool {N : Nat} (π : SetPartition N) : Bool :=
  finAll N (fun a => finAll N (fun b => finAll N (fun c => finAll N (fun d =>
    !(decide (a.1 < b.1 ∧ b.1 < c.1 ∧ c.1 < d.1) && π.rel a c && π.rel b d) || π.rel a b))))

theorem isDiscNC_of_bool {N : Nat} {π : SetPartition N} (h : isDiscNCBool π = true) :
    IsDiscNC π := by
  intro a b c d hab hbc hcd hac hbd
  have h1 := finAll_eq_true.mp h a
  have h2 := finAll_eq_true.mp h1 b
  have h3 := finAll_eq_true.mp h2 c
  have h4 := finAll_eq_true.mp h3 d
  have hlt : decide (a.1 < b.1 ∧ b.1 < c.1 ∧ c.1 < d.1) = true :=
    decide_eq_true ⟨hab, hbc, hcd⟩
  dsimp only [id] at hac hbd ⊢
  rw [hlt, hac, hbd] at h4
  simpa using h4

/-! ## 1. Minimal 5-Element Induced Sublattices in `NC(4)` Sharing `lowerMobiusMult` -/

def nc4Stem5Family : Fin 5 → SetPartition 4
  | ⟨0, _⟩ => mkColorPartition (fun v => v.1)
  | ⟨1, _⟩ => mkColorPartition (fun v => if v.1 = 2 ∨ v.1 = 3 then 2 else v.1)
  | ⟨2, _⟩ => mkColorPartition (fun v => if v.1 = 1 ∨ v.1 = 2 then 1 else v.1)
  | ⟨3, _⟩ => mkColorPartition (fun v => if v.1 = 0 then 0 else 1)
  | ⟨_ + 4, _⟩ => topPartition 4

def nc4Pentagon5Family : Fin 5 → SetPartition 4
  | ⟨0, _⟩ => mkColorPartition (fun v => v.1)
  | ⟨1, _⟩ => mkColorPartition (fun v => if v.1 = 2 ∨ v.1 = 3 then 2 else v.1)
  | ⟨2, _⟩ => mkColorPartition (fun v => if v.1 = 1 ∨ v.1 = 2 then 1 else v.1)
  | ⟨3, _⟩ => mkColorPartition (fun v => if v.1 = 0 ∨ v.1 = 1 then 0 else 2)
  | ⟨_ + 4, _⟩ => topPartition 4

def nc4SubStem5 : FinPoset 5 where
  le i j := refinesBool (nc4Stem5Family i) (nc4Stem5Family j)
  le_refl := finForall_decide (by decide)
  le_antisymm := finForall2_decide (by decide)
  le_trans := finForall3_decide (by decide)

def nc4SubPentagon5 : FinPoset 5 where
  le i j := refinesBool (nc4Pentagon5Family i) (nc4Pentagon5Family j)
  le_refl := finForall_decide (by decide)
  le_antisymm := finForall2_decide (by decide)
  le_trans := finForall3_decide (by decide)

theorem nc4Stem5_all_discNC : ∀ i : Fin 5, IsDiscNC (nc4Stem5Family i) := by
  intro i
  exact isDiscNC_of_bool (finAll_eq_true.mp (by decide : finAll 5 (fun k => isDiscNCBool (nc4Stem5Family k)) = true) i)

theorem nc4Pentagon5_all_discNC : ∀ i : Fin 5, IsDiscNC (nc4Pentagon5Family i) := by
  intro i
  exact isDiscNC_of_bool (finAll_eq_true.mp (by decide : finAll 5 (fun k => isDiscNCBool (nc4Pentagon5Family k)) = true) i)

theorem nc4Sub5_lower_mobius_separation :
    nc4SubStem5.IsLattice ∧
    nc4SubPentagon5.IsLattice ∧
    (∀ v : Int, lowerMobiusMult nc4SubStem5 ⟨0, by omega⟩ v =
                lowerMobiusMult nc4SubPentagon5 ⟨0, by omega⟩ v) ∧
    ¬ IsPosetIsomorphic nc4SubStem5 nc4SubPentagon5 := by
  refine ⟨(FinPoset.isLatticeBool_iff nc4SubStem5).mp (by decide),
          (FinPoset.isLatticeBool_iff nc4SubPentagon5).mp (by decide),
          ?_, ?_⟩
  · intro v
    by_cases hv1 : v = 1
    · subst hv1; decide
    · by_cases hvm1 : v = -1
      · subst hvm1; decide
      · by_cases hv0 : v = 0
        · subst hv0; decide
        · have hS_range : ∀ x : Fin 5,
              mobius nc4SubStem5 ⟨0, by omega⟩ x = 1 ∨
              mobius nc4SubStem5 ⟨0, by omega⟩ x = -1 ∨
              mobius nc4SubStem5 ⟨0, by omega⟩ x = 0 :=
            finForall_decide (by decide)
          have hP_range : ∀ x : Fin 5,
              mobius nc4SubPentagon5 ⟨0, by omega⟩ x = 1 ∨
              mobius nc4SubPentagon5 ⟨0, by omega⟩ x = -1 ∨
              mobius nc4SubPentagon5 ⟨0, by omega⟩ x = 0 :=
            finForall_decide (by decide)
          have hS : lowerMobiusMult nc4SubStem5 ⟨0, by omega⟩ v = 0 := by
            unfold lowerMobiusMult
            have hf : (fun x : Fin 5 => decide (mobius nc4SubStem5 ⟨0, by omega⟩ x = v)) =
                (fun _ => false) := by
              funext x
              have hne : mobius nc4SubStem5 ⟨0, by omega⟩ x ≠ v := by
                rcases hS_range x with h | h | h <;> omega
              exact decide_eq_false hne
            rw [hf]; rfl
          have hP : lowerMobiusMult nc4SubPentagon5 ⟨0, by omega⟩ v = 0 := by
            unfold lowerMobiusMult
            have hf : (fun x : Fin 5 => decide (mobius nc4SubPentagon5 ⟨0, by omega⟩ x = v)) =
                (fun _ => false) := by
              funext x
              have hne : mobius nc4SubPentagon5 ⟨0, by omega⟩ x ≠ v := by
                rcases hP_range x with h | h | h <;> omega
              exact decide_eq_false hne
            rw [hf]; rfl
          rw [hS, hP]
  · rintro ⟨e⟩
    have htS : nc4SubStem5.IsTop ⟨4, by omega⟩ := finForall_decide (by decide)
    have htP : nc4SubPentagon5.IsTop ⟨4, by omega⟩ := finForall_decide (by decide)
    have heq := e.upperMobiusMult_eq htS htP 0
    have hcalc : upperMobiusMult nc4SubStem5 ⟨4, by omega⟩ 0 ≠
                 upperMobiusMult nc4SubPentagon5 ⟨4, by omega⟩ 0 := by decide
    exact hcalc heq

/-! ## 2. Self-Dual Graded 10-Element Sublattices of `NC(8)` Sharing ALL Möbius Spectra -/

def intervalMaskPartition (mask : Nat) : SetPartition 8 where
  rel i j :=
    let lo := min i.1 j.1
    let hi := max i.1 j.1
    finAll 7 (fun g => !(decide (lo ≤ g.1 ∧ g.1 < hi)) || decide (mask.testBit g.1 = true))
  rel_refl i := by
    simp only [Nat.min_self, Nat.max_self]
    rw [finAll_eq_true]
    intro g
    have hnot : ¬ (i.1 ≤ g.1 ∧ g.1 < i.1) := by omega
    simp [hnot]
  rel_symm i j h := by
    have hmin : min j.1 i.1 = min i.1 j.1 := Nat.min_comm j.1 i.1
    have hmax : max j.1 i.1 = max i.1 j.1 := Nat.max_comm j.1 i.1
    dsimp only at h ⊢
    rw [hmin, hmax]
    exact h
  rel_trans i j k h1 h2 := by
    dsimp only at h1 h2 ⊢
    rw [finAll_eq_true] at h1 h2 ⊢
    intro g
    by_cases hg : min i.1 k.1 ≤ g.1 ∧ g.1 < max i.1 k.1
    · simp [hg]
      have hsplit : (min i.1 j.1 ≤ g.1 ∧ g.1 < max i.1 j.1) ∨
                    (min j.1 k.1 ≤ g.1 ∧ g.1 < max j.1 k.1) := by omega
      rcases hsplit with hs1 | hs2
      · have h1g := h1 g; simp [hs1] at h1g; exact h1g
      · have h2g := h2 g; simp [hs2] at h2g; exact h2g
    · simp [hg]

theorem intervalMaskPartition_isDiscNC (mask : Nat) :
    IsDiscNC (intervalMaskPartition mask) := by
  intro a b c _ hab hbc _ hac _
  dsimp only [id, intervalMaskPartition] at hac ⊢
  rw [finAll_eq_true] at hac ⊢
  intro g
  by_cases hg : min a.1 b.1 ≤ g.1 ∧ g.1 < max a.1 b.1
  · simp [hg]
    have hg_ac : min a.1 c.1 ≤ g.1 ∧ g.1 < max a.1 c.1 := by omega
    have hac_g := hac g
    simp [hg_ac] at hac_g
    exact hac_g
  · simp [hg]

def mask10A : Fin 10 → Nat
  | ⟨0, _⟩ => 0
  | ⟨1, _⟩ => 1
  | ⟨2, _⟩ => 3
  | ⟨3, _⟩ => 7
  | ⟨4, _⟩ => 11
  | ⟨5, _⟩ => 15
  | ⟨6, _⟩ => 31
  | ⟨7, _⟩ => 47
  | ⟨8, _⟩ => 63
  | ⟨_ + 9, _⟩ => 127

def mask10B : Fin 10 → Nat
  | ⟨0, _⟩ => 0
  | ⟨1, _⟩ => 1
  | ⟨2, _⟩ => 3
  | ⟨3, _⟩ => 5
  | ⟨4, _⟩ => 7
  | ⟨5, _⟩ => 15
  | ⟨6, _⟩ => 31
  | ⟨7, _⟩ => 47
  | ⟨8, _⟩ => 63
  | ⟨_ + 9, _⟩ => 127

def poset10A : FinPoset 10 where
  le i j := decide (mask10A i &&& mask10A j = mask10A i)
  le_refl := finForall_decide (by decide)
  le_antisymm := finForall2_decide (by decide)
  le_trans := finForall3_decide (by decide)

def poset10B : FinPoset 10 where
  le i j := decide (mask10B i &&& mask10B j = mask10B i)
  le_refl := finForall_decide (by decide)
  le_antisymm := finForall2_decide (by decide)
  le_trans := finForall3_decide (by decide)

/-- Isomorphism between `poset10A` / `poset10B` and the induced partition refinement order
on `{intervalMaskPartition (mask10A i)}` / `{intervalMaskPartition (mask10B i)}` in `NC(8)`. -/
theorem poset10A_eq_partition_refines (i j : Fin 10) :
    refinesBool (intervalMaskPartition (mask10A i)) (intervalMaskPartition (mask10A j)) =
    poset10A.le i j := by
  revert i j
  exact finForall2_decide (by decide)

theorem poset10B_eq_partition_refines (i j : Fin 10) :
    refinesBool (intervalMaskPartition (mask10B i)) (intervalMaskPartition (mask10B j)) =
    poset10B.le i j := by
  revert i j
  exact finForall2_decide (by decide)

def downSetCard {n : Nat} (P : FinPoset n) (x : Fin n) : Nat :=
  finCount n (fun y => P.le y x)

theorem PosetIso.map_downSetCard {n m : Nat} {P : FinPoset n} {Q : FinPoset m}
    (e : PosetIso P Q) (x : Fin n) :
    downSetCard Q (e.toFun x) = downSetCard P x := by
  unfold downSetCard
  symm
  apply finCount_bij e.toFun e.invFun e.left_inv e.right_inv
  intro y
  rw [e.map_le y x]

/-- **Main Scope-Boundary Theorem:** `poset10A` and `poset10B` (both realized as interval
partitions in `NC(8)`) are self-dual graded lattices whose lower, upper, AND full two-variable
Möbius spectra are all identical, yet they are non-isomorphic lattices! -/
theorem poset10AB_all_mobius_spectra_equal_non_iso :
    poset10A.IsLattice ∧
    poset10B.IsLattice ∧
    (∀ v : Int, lowerMobiusMult poset10A ⟨0, by omega⟩ v =
                lowerMobiusMult poset10B ⟨0, by omega⟩ v) ∧
    (∀ v : Int, upperMobiusMult poset10A ⟨9, by omega⟩ v =
                upperMobiusMult poset10B ⟨9, by omega⟩ v) ∧
    (∀ v : Int, fullMobiusCount poset10A v = fullMobiusCount poset10B v) ∧
    ¬ IsPosetIsomorphic poset10A poset10B := by
  have hArange : ∀ x y : Fin 10,
      mobius poset10A x y = 1 ∨ mobius poset10A x y = -1 ∨ mobius poset10A x y = 0 :=
    finForall2_decide (by decide)
  have hBrange : ∀ x y : Fin 10,
      mobius poset10B x y = 1 ∨ mobius poset10B x y = -1 ∨ mobius poset10B x y = 0 :=
    finForall2_decide (by decide)
  refine ⟨(FinPoset.isLatticeBool_iff poset10A).mp (by decide),
          (FinPoset.isLatticeBool_iff poset10B).mp (by decide),
          ?_, ?_, ?_, ?_⟩
  · intro v
    by_cases hv1 : v = 1
    · subst hv1; decide
    · by_cases hvm1 : v = -1
      · subst hvm1; decide
      · by_cases hv0 : v = 0
        · subst hv0; decide
        · have hA : lowerMobiusMult poset10A ⟨0, by omega⟩ v = 0 := by
            unfold lowerMobiusMult
            have hf : (fun x : Fin 10 => decide (mobius poset10A ⟨0, by omega⟩ x = v)) = (fun _ => false) := by
              funext x
              have hne : mobius poset10A ⟨0, by omega⟩ x ≠ v := by
                rcases hArange ⟨0, by omega⟩ x with h | h | h <;> omega
              exact decide_eq_false hne
            rw [hf]; rfl
          have hB : lowerMobiusMult poset10B ⟨0, by omega⟩ v = 0 := by
            unfold lowerMobiusMult
            have hf : (fun x : Fin 10 => decide (mobius poset10B ⟨0, by omega⟩ x = v)) = (fun _ => false) := by
              funext x
              have hne : mobius poset10B ⟨0, by omega⟩ x ≠ v := by
                rcases hBrange ⟨0, by omega⟩ x with h | h | h <;> omega
              exact decide_eq_false hne
            rw [hf]; rfl
          rw [hA, hB]
  · intro v
    by_cases hv1 : v = 1
    · subst hv1; decide
    · by_cases hvm1 : v = -1
      · subst hvm1; decide
      · by_cases hv0 : v = 0
        · subst hv0; decide
        · have hA : upperMobiusMult poset10A ⟨9, by omega⟩ v = 0 := by
            unfold upperMobiusMult
            have hf : (fun x : Fin 10 => decide (mobius poset10A x ⟨9, by omega⟩ = v)) = (fun _ => false) := by
              funext x
              have hne : mobius poset10A x ⟨9, by omega⟩ ≠ v := by
                rcases hArange x ⟨9, by omega⟩ with h | h | h <;> omega
              exact decide_eq_false hne
            rw [hf]; rfl
          have hB : upperMobiusMult poset10B ⟨9, by omega⟩ v = 0 := by
            unfold upperMobiusMult
            have hf : (fun x : Fin 10 => decide (mobius poset10B x ⟨9, by omega⟩ = v)) = (fun _ => false) := by
              funext x
              have hne : mobius poset10B x ⟨9, by omega⟩ ≠ v := by
                rcases hBrange x ⟨9, by omega⟩ with h | h | h <;> omega
              exact decide_eq_false hne
            rw [hf]; rfl
          rw [hA, hB]
  · intro v
    by_cases hv1 : v = 1
    · subst hv1; decide
    · by_cases hvm1 : v = -1
      · subst hvm1; decide
      · by_cases hv0 : v = 0
        · subst hv0; decide
        · have hA : fullMobiusCount poset10A v = 0 := by
            unfold fullMobiusCount
            rw [finSum_congr (g := fun _ => 0)]
            · exact finSum_zero 10
            · intro x
              rw [finSum_congr (g := fun _ => 0)]
              · exact finSum_zero 10
              · intro y
                have hne : mobius poset10A x y ≠ v := by
                  rcases hArange x y with h | h | h <;> omega
                simp [hne]
          have hB : fullMobiusCount poset10B v = 0 := by
            unfold fullMobiusCount
            rw [finSum_congr (g := fun _ => 0)]
            · exact finSum_zero 10
            · intro x
              rw [finSum_congr (g := fun _ => 0)]
              · exact finSum_zero 10
              · intro y
                have hne : mobius poset10B x y ≠ v := by
                  rcases hBrange x y with h | h | h <;> omega
                simp [hne]
          rw [hA, hB]
  · rintro ⟨e⟩
    have hcount : finCount 10 (fun x => decide (downSetCard poset10A x = 3)) =
                  finCount 10 (fun y => decide (downSetCard poset10B y = 3)) := by
      apply finCount_bij e.toFun e.invFun e.left_inv e.right_inv
      intro x
      rw [e.map_downSetCard x]
    have hneq : finCount 10 (fun x => decide (downSetCard poset10A x = 3)) ≠
                finCount 10 (fun y => decide (downSetCard poset10B y = 3)) := by decide
    exact hneq hcount

end Conjecture00000004770
