import Mathlib.Order.Antisymmetrization
import Mathlib.Order.Zorn
import Mathlib.Data.Sum.Order
import Mathlib.Data.ENat.Lattice
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Data.Rat.Encodable
import Mathlib.Logic.Denumerable
import Mathlib.Data.Nat.Prime.Infinite
import Mathlib.SetTheory.Cardinal.Continuum
import Mathlib.Analysis.Real.Cardinality
import Mathlib.Tactic.Push

/-! The full classical height-type lattice, not logical first-order types. -/
namespace TLMC4277
open Set Function

abbrev Prime := {p : ℕ // p.Prime}
abbrev HVal := WithTop ℕ
structure Characteristic where
  val : Prime → HVal
instance : CoeFun Characteristic (fun _ => Prime → HVal) := ⟨Characteristic.val⟩

/-- Finite-coordinate comparison, with infinite coordinates never decreased. -/
def Below (a b : Characteristic) : Prop :=
  (∀ p, a p = ⊤ → b p = ⊤) ∧ {p | ¬ a p ≤ b p}.Finite

theorem below_refl (a : Characteristic) : Below a a := by
  exact ⟨fun _ h => h, by simp⟩

theorem below_trans {a b c : Characteristic} (hab : Below a b) (hbc : Below b c) :
    Below a c := by
  refine ⟨fun p hp => hbc.1 p (hab.1 p hp), (hab.2.union hbc.2).subset ?_⟩
  intro p hp
  by_contra h
  simp only [mem_union, mem_ofPred_eq, not_or, not_not] at h
  exact hp (le_trans h.1 h.2)

instance characteristicPreorder : Preorder Characteristic where
  le := Below
  le_refl := below_refl
  le_trans := fun _ _ _ => below_trans

/-- Exactly the traditional equivalence: finitely many changes, all at finite coordinates. -/
def HeightEquivalent (a b : Characteristic) : Prop :=
  {p | a p ≠ b p}.Finite ∧ ∀ p, a p = ⊤ ↔ b p = ⊤

theorem equivalent_iff (a b : Characteristic) :
    AntisymmRel (· ≤ ·) a b ↔ HeightEquivalent a b := by
  constructor
  · rintro ⟨hab, hba⟩
    refine ⟨(hab.2.union hba.2).subset ?_, fun p => ⟨hab.1 p, hba.1 p⟩⟩
    intro p hp
    by_contra h
    simp only [mem_union, mem_ofPred_eq, not_or, not_not] at h
    exact hp (le_antisymm h.1 h.2)
  · rintro ⟨hf, ht⟩
    constructor
    · refine ⟨fun p => (ht p).mp, hf.subset ?_⟩
      intro p hp he
      exact hp (le_of_eq he)
    · refine ⟨fun p => (ht p).mpr, hf.subset ?_⟩
      intro p hp he
      exact hp (le_of_eq he.symm)

abbrev HeightType := Antisymmetrization Characteristic (· ≤ ·)
def typeOf (a : Characteristic) : HeightType := toAntisymmetrization (· ≤ ·) a

theorem typeOf_eq_iff (a b : Characteristic) :
    typeOf a = typeOf b ↔ HeightEquivalent a b := by
  exact Quotient.eq.trans (equivalent_iff a b)

theorem pointwise_below {a b : Characteristic} (h : ∀ p, a p ≤ b p) : a ≤ b := by
  refine ⟨fun p hp => top_unique (hp ▸ h p), ?_⟩
  have : {p | ¬a p ≤ b p} = ∅ := by ext p; simp [h p]
  rw [this]; exact finite_empty

def pointInf (a b : Characteristic) : Characteristic := ⟨fun p => a p ⊓ b p⟩
def pointSup (a b : Characteristic) : Characteristic := ⟨fun p => a p ⊔ b p⟩

theorem pointInf_le_left (a b : Characteristic) : pointInf a b ≤ a :=
  pointwise_below (fun _ => inf_le_left)
theorem pointInf_le_right (a b : Characteristic) : pointInf a b ≤ b :=
  pointwise_below (fun _ => inf_le_right)
theorem left_le_pointSup (a b : Characteristic) : a ≤ pointSup a b :=
  pointwise_below (fun _ => le_sup_left)
theorem right_le_pointSup (a b : Characteristic) : b ≤ pointSup a b :=
  pointwise_below (fun _ => le_sup_right)

theorem below_pointInf {a b c : Characteristic} (ha : c ≤ a) (hb : c ≤ b) :
    c ≤ pointInf a b := by
  refine ⟨fun p hp => by simp [pointInf, ha.1 p hp, hb.1 p hp],
    (ha.2.union hb.2).subset ?_⟩
  intro p hp
  by_contra h
  simp only [mem_union, mem_ofPred_eq, not_or, not_not] at h
  exact hp (le_inf h.1 h.2)

theorem pointSup_below {a b c : Characteristic} (ha : a ≤ c) (hb : b ≤ c) :
    pointSup a b ≤ c := by
  refine ⟨?_, (ha.2.union hb.2).subset ?_⟩
  · intro p hp
    have h : a p = ⊤ ∨ b p = ⊤ := by simpa [pointSup] using hp
    exact h.elim (ha.1 p) (hb.1 p)
  · intro p hp
    by_contra h
    simp only [mem_union, mem_ofPred_eq, not_or, not_not] at h
    exact hp (sup_le h.1 h.2)

/-- Quotient order equals the standard order by pointwise-comparable equivalent representatives. -/
theorem standard_order (a b : Characteristic) : typeOf a ≤ typeOf b ↔
    ∃ a' b', HeightEquivalent a a' ∧ HeightEquivalent b b' ∧ ∀ p, a' p ≤ b' p := by
  constructor
  · intro hab
    have h : a ≤ b := hab
    refine ⟨pointInf a b, b, (equivalent_iff _ _).mp ?_,
      (equivalent_iff _ _).mp ⟨le_rfl, le_rfl⟩, fun p => inf_le_right⟩
    exact ⟨below_pointInf le_rfl h, pointInf_le_left _ _⟩
  · rintro ⟨a', b', ha, hb, h⟩
    have ha' := (equivalent_iff _ _).mpr ha
    have hb' := (equivalent_iff _ _).mpr hb
    show a ≤ b
    exact le_trans ha'.1 (le_trans (pointwise_below h) hb'.2)

noncomputable def infType (a b : HeightType) : HeightType :=
  typeOf (pointInf (ofAntisymmetrization (· ≤ ·) a) (ofAntisymmetrization (· ≤ ·) b))
noncomputable def supType (a b : HeightType) : HeightType :=
  typeOf (pointSup (ofAntisymmetrization (· ≤ ·) a) (ofAntisymmetrization (· ≤ ·) b))

theorem rep_type (a : HeightType) : typeOf (ofAntisymmetrization (· ≤ ·) a) = a :=
  toAntisymmetrization_ofAntisymmetrization _ a

noncomputable instance heightTypeLattice : Lattice HeightType where
  inf := infType
  sup := supType
  inf_le_left a b := by
    have h : typeOf (pointInf (ofAntisymmetrization (· ≤ ·) a)
        (ofAntisymmetrization (· ≤ ·) b)) ≤ typeOf (ofAntisymmetrization (· ≤ ·) a) :=
      pointInf_le_left _ _
    exact h.trans_eq (rep_type a)
  inf_le_right a b := by
    have h : typeOf (pointInf (ofAntisymmetrization (· ≤ ·) a)
        (ofAntisymmetrization (· ≤ ·) b)) ≤ typeOf (ofAntisymmetrization (· ≤ ·) b) :=
      pointInf_le_right _ _
    exact h.trans_eq (rep_type b)
  le_inf a b c hab hac := by
    have h : typeOf (ofAntisymmetrization (· ≤ ·) a) ≤
        typeOf (pointInf (ofAntisymmetrization (· ≤ ·) b)
          (ofAntisymmetrization (· ≤ ·) c)) :=
      below_pointInf (ofAntisymmetrization_le_ofAntisymmetrization_iff.mpr hab)
        (ofAntisymmetrization_le_ofAntisymmetrization_iff.mpr hac)
    exact (rep_type a).symm.le.trans h
  le_sup_left a b := by
    have h : typeOf (ofAntisymmetrization (· ≤ ·) a) ≤
        typeOf (pointSup (ofAntisymmetrization (· ≤ ·) a)
          (ofAntisymmetrization (· ≤ ·) b)) := left_le_pointSup _ _
    exact (rep_type a).symm.le.trans h
  le_sup_right a b := by
    have h : typeOf (ofAntisymmetrization (· ≤ ·) b) ≤
        typeOf (pointSup (ofAntisymmetrization (· ≤ ·) a)
          (ofAntisymmetrization (· ≤ ·) b)) := right_le_pointSup _ _
    exact (rep_type b).symm.le.trans h
  sup_le a b c hac hbc := by
    have h : typeOf (pointSup (ofAntisymmetrization (· ≤ ·) a)
        (ofAntisymmetrization (· ≤ ·) b)) ≤ typeOf (ofAntisymmetrization (· ≤ ·) c) :=
      pointSup_below (ofAntisymmetrization_le_ofAntisymmetrization_iff.mpr hac)
        (ofAntisymmetrization_le_ofAntisymmetrization_iff.mpr hbc)
    exact h.trans_eq (rep_type c)

theorem quotient_inf (a b : Characteristic) :
    typeOf a ⊓ typeOf b = typeOf (pointInf a b) := by
  apply le_antisymm
  · have h : ∀ c : HeightType, c ≤ typeOf a → c ≤ typeOf b →
        c ≤ typeOf (pointInf a b) := by
      intro c
      induction c using Antisymmetrization.induction_on with
      | h c => exact fun ha hb => below_pointInf ha hb
    exact h _ inf_le_left inf_le_right
  · exact le_inf (pointInf_le_left a b) (pointInf_le_right a b)

theorem quotient_sup (a b : Characteristic) :
    typeOf a ⊔ typeOf b = typeOf (pointSup a b) := by
  apply le_antisymm
  · exact sup_le (left_le_pointSup a b) (right_le_pointSup a b)
  · have h : ∀ c : HeightType, typeOf a ≤ c → typeOf b ≤ c →
        typeOf (pointSup a b) ≤ c := by
      intro c
      induction c using Antisymmetrization.induction_on with
      | h c => exact fun ha hb => pointSup_below ha hb
    exact h _ le_sup_left le_sup_right

instance primeInfinite : Infinite Prime := by
  apply Set.infinite_coe_iff.mpr
  intro h
  exact Nat.not_bddAbove_setOfPred_prime h.bddAbove
noncomputable def primeRat : Prime ≃ ℚ := Classical.choice inferInstance

/-- Real cuts in rationally indexed prime positions, retaining every infinity coordinate. -/
noncomputable def cut (x : ℝ) : Characteristic :=
  ⟨fun p => if (primeRat p : ℝ) < x then ⊤ else 0⟩
noncomputable def cutType (x : ℝ) : HeightType := typeOf (cut x)

theorem cut_mono : Monotone cutType := by
  intro x y h
  apply pointwise_below
  intro p
  dsimp [cut]
  split_ifs with hx hy hy
  · exact le_rfl
  · exact False.elim (hy (lt_of_lt_of_le hx h))
  · exact bot_le
  · exact le_rfl

theorem cut_ne_of_lt {x y : ℝ} (hlt : x < y) : cutType x ≠ cutType y := by
  intro h
  obtain ⟨q, hxq, hqy⟩ := exists_rat_btwn hlt
  let p := primeRat.symm q
  have hpq : primeRat p = q := primeRat.apply_symm_apply q
  have ht := ((typeOf_eq_iff _ _).mp h).2 p
  have hx : cut x p = 0 := by simp [cut, hpq, not_lt.mpr hxq.le]
  have hy : cut y p = ⊤ := by simp [cut, hpq, hqy]
  have hbad := ht.mpr hy
  rw [hx] at hbad
  exact WithTop.zero_ne_top hbad

theorem cut_injective : Injective cutType := by
  intro x y h
  exact le_antisymm (le_of_not_gt fun hlt => cut_ne_of_lt hlt h.symm)
    (le_of_not_gt fun hlt => cut_ne_of_lt hlt h)

def cutChain : Set HeightType := Set.range cutType

theorem cutChain_isChain : IsChain (· ≤ ·) cutChain := by
  rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩ _
  exact (le_total x y).imp (fun h => cut_mono h) (fun h => cut_mono h)

theorem cutChain_uncountable : ¬ cutChain.Countable := by
  intro h
  let : Countable cutChain := h.to_subtype
  have : Countable ℝ := Function.Injective.countable
    (f := fun x : ℝ => (⟨cutType x, Set.mem_range_self x⟩ : cutChain))
    (fun _ _ h => cut_injective (congrArg Subtype.val h))
  exact not_countable (α := ℝ) this

/-- The actual ordered sum omega + omega-star appearing in the conjecture. -/
abbrev PrintedOrder := ℕ ⊕ₗ OrderDual ℕ

theorem maximal_chain_counterexample : ∃ M : Set HeightType,
    IsMaxChain (· ≤ ·) M ∧ ¬M.Countable ∧ ¬Nonempty (M ≃o PrintedOrder) := by
  obtain ⟨M, hM, hsub⟩ := cutChain_isChain.exists_maxChain
  have hunc : ¬M.Countable := fun hc => cutChain_uncountable (hc.mono hsub)
  refine ⟨M, hM, hunc, ?_⟩
  rintro ⟨e⟩
  let : Countable PrintedOrder := inferInstanceAs (Countable (ℕ ⊕ ℕ))
  have : Countable M := Function.Injective.countable e.injective
  exact hunc (Set.to_countable M)

theorem not_every_maximal_chain_has_printed_order :
    ¬∀ M : Set HeightType, IsMaxChain (· ≤ ·) M → Nonempty (M ≃o PrintedOrder) := by
  intro h
  obtain ⟨M, hM, _, hnot⟩ := maximal_chain_counterexample
  exact hnot (h M hM)

end TLMC4277
