import FieldTables

namespace Steiner1029

structure TableElem {q : Nat} (t : RawFieldTable q) where
  val : Fin q
deriving DecidableEq

theorem tableElem_ext {q : Nat} {t : RawFieldTable q} {a b : TableElem t}
    (h : a.val = b.val) : a = b := by
  cases a
  cases b
  cases h
  rfl

def tableElemEquiv {q : Nat} (t : RawFieldTable q) : TableElem t ≃ Fin q where
  toFun := TableElem.val
  invFun := TableElem.mk
  left_inv a := by cases a; rfl
  right_inv _ := rfl

instance tableElemFintype {q : Nat} (t : RawFieldTable q) : Fintype (TableElem t) :=
  Fintype.ofEquiv (Fin q) (tableElemEquiv t).symm

theorem tableElem_card {q : Nat} (t : RawFieldTable q) :
    Fintype.card (TableElem t) = q := by
  rw [Fintype.card_congr (tableElemEquiv t), Fintype.card_fin]

instance tableElemZero {q : Nat} (t : RawFieldTable q) : Zero (TableElem t) :=
  ⟨⟨t.zero⟩⟩

instance tableElemOne {q : Nat} (t : RawFieldTable q) : One (TableElem t) :=
  ⟨⟨t.one⟩⟩

instance tableElemAdd {q : Nat} (t : RawFieldTable q) : Add (TableElem t) :=
  ⟨fun a b => ⟨t.add a.val b.val⟩⟩

instance tableElemMul {q : Nat} (t : RawFieldTable q) : Mul (TableElem t) :=
  ⟨fun a b => ⟨t.mul a.val b.val⟩⟩

def tableNeg {q : Nat} (t : RawFieldTable q) (h : TableValid t) (a : Fin q) : Fin q :=
  Fin.find (fun b => t.add b a = t.zero) (h.2.2.2.1 a)

def tableInv {q : Nat} (t : RawFieldTable q) (h : TableValid t) (a : Fin q) : Fin q :=
  if ha : a = t.zero then t.zero
  else Fin.find (fun b => t.mul a b = t.one) (h.2.2.2.2.2.2.2.2 a ha)

theorem tableNeg_spec {q : Nat} (t : RawFieldTable q) (h : TableValid t) (a : Fin q) :
    t.add (tableNeg t h a) a = t.zero :=
  Fin.find_spec (h.2.2.2.1 a)

theorem tableInv_spec {q : Nat} (t : RawFieldTable q) (h : TableValid t)
    (a : Fin q) (ha : a ≠ t.zero) : t.mul a (tableInv t h a) = t.one := by
  unfold tableInv
  rw [dif_neg ha]
  exact Fin.find_spec (h.2.2.2.2.2.2.2.2 a ha)

theorem tableInv_zero {q : Nat} (t : RawFieldTable q) (h : TableValid t) :
    tableInv t h t.zero = t.zero := by
  simp [tableInv]

-- All computational operations use finite searches; h is erased proof data.
abbrev fieldOfTable {q : Nat} (t : RawFieldTable q) (h : TableValid t) : Field (TableElem t) := by
  letI : Neg (TableElem t) := ⟨fun a => ⟨tableNeg t h a.val⟩⟩
  letI : Inv (TableElem t) := ⟨fun a => ⟨tableInv t h a.val⟩⟩
  apply Field.ofMinimalAxioms (TableElem t)
  · intro a b c
    apply tableElem_ext
    exact h.2.1 a.val b.val c.val
  · intro a
    apply tableElem_ext
    exact h.2.2.1 a.val
  · intro a
    apply tableElem_ext
    exact tableNeg_spec t h a.val
  · intro a b c
    apply tableElem_ext
    exact h.2.2.2.2.1 a.val b.val c.val
  · intro a b
    apply tableElem_ext
    exact h.2.2.2.2.2.1 a.val b.val
  · intro a
    apply tableElem_ext
    exact h.2.2.2.2.2.2.1 a.val
  · intro a ha
    apply tableElem_ext
    apply tableInv_spec t h a.val
    intro hz
    apply ha
    exact tableElem_ext hz
  · apply tableElem_ext
    exact tableInv_zero t h
  · intro a b c
    apply tableElem_ext
    exact h.2.2.2.2.2.2.2.1 a.val b.val c.val
  · refine ⟨⟨t.zero⟩, ⟨t.one⟩, ?_⟩
    intro heq
    exact h.1 (congrArg TableElem.val heq)

theorem fieldOfTable_zero_val {q : Nat} (t : RawFieldTable q) (h : TableValid t) :
    letI := fieldOfTable t h
    (0 : TableElem t).val = t.zero := rfl

theorem fieldOfTable_one_val {q : Nat} (t : RawFieldTable q) (h : TableValid t) :
    letI := fieldOfTable t h
    (1 : TableElem t).val = t.one := rfl

theorem fieldOfTable_add_val {q : Nat} (t : RawFieldTable q) (h : TableValid t)
    (a b : TableElem t) :
    letI := fieldOfTable t h
    (a + b).val = t.add a.val b.val := rfl

theorem fieldOfTable_mul_val {q : Nat} (t : RawFieldTable q) (h : TableValid t)
    (a b : TableElem t) :
    letI := fieldOfTable t h
    (a * b).val = t.mul a.val b.val := rfl

def chosenFieldTable (q : Nat) : Option {t : RawFieldTable q // TableValid t} :=
  match hs : firstFieldTable q with
  | none => none
  | some t => some ⟨t, firstFieldTable_valid hs⟩

theorem chosenFieldTable_exists_of_model (K : Type*) [Field K] [Fintype K]
    (q : Nat) (h : Fintype.card K = q) :
    ∃ t, chosenFieldTable q = some t := by
  obtain ⟨t, ht⟩ := firstFieldTable_exists_of_model K q h
  unfold chosenFieldTable
  split
  · next hn =>
      rw [hn] at ht
      contradiction
  · exact ⟨_, rfl⟩

theorem chosenFieldTable_raw {q : Nat} {t : {t : RawFieldTable q // TableValid t}}
    (h : chosenFieldTable q = some t) : firstFieldTable q = some t.val := by
  unfold chosenFieldTable at h
  split at h
  · contradiction
  · next ht =>
      have heq := Option.some.inj h
      rw [← heq]
      exact ht

end Steiner1029

#check Steiner1029.tableElem_ext
#print axioms Steiner1029.tableElem_ext
#check Steiner1029.tableElem_card
#print axioms Steiner1029.tableElem_card
#check Steiner1029.tableNeg_spec
#print axioms Steiner1029.tableNeg_spec
#check Steiner1029.tableInv_spec
#print axioms Steiner1029.tableInv_spec
#check Steiner1029.tableInv_zero
#print axioms Steiner1029.tableInv_zero
#check Steiner1029.fieldOfTable_zero_val
#print axioms Steiner1029.fieldOfTable_zero_val
#check Steiner1029.fieldOfTable_one_val
#print axioms Steiner1029.fieldOfTable_one_val
#check Steiner1029.fieldOfTable_add_val
#print axioms Steiner1029.fieldOfTable_add_val
#check Steiner1029.fieldOfTable_mul_val
#print axioms Steiner1029.fieldOfTable_mul_val
#check Steiner1029.chosenFieldTable_exists_of_model
#print axioms Steiner1029.chosenFieldTable_exists_of_model
#check Steiner1029.chosenFieldTable_raw
#print axioms Steiner1029.chosenFieldTable_raw
#print axioms Steiner1029.tableElemEquiv
#print axioms Steiner1029.tableElemFintype
#print axioms Steiner1029.tableNeg
#print axioms Steiner1029.tableInv
#print axioms Steiner1029.fieldOfTable
#print axioms Steiner1029.chosenFieldTable
