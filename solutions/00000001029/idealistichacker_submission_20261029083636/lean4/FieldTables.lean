import Mathlib.Algebra.Field.MinimalAxioms
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Tactic

namespace Steiner1029

universe u

def allFunctions {A : Type u} (alphabet : List A) : (m : Nat) -> List (Fin m -> A)
  | 0 => [Fin.elim0]
  | m + 1 => alphabet.flatMap fun a =>
      (allFunctions alphabet m).map (fun f => Fin.cons a f)

theorem mem_allFunctions {A : Type u} (alphabet : List A)
    (h : forall a, List.Mem a alphabet) (m : Nat) (f : Fin m -> A) :
    List.Mem f (allFunctions alphabet m) := by
  induction m with
  | zero =>
      have hf : f = Fin.elim0 := by funext i; exact Fin.elim0 i
      rw [hf]
      exact List.Mem.head _
  | succ m ih =>
      apply List.mem_flatMap.mpr
      refine Exists.intro (f 0) (And.intro (h _) ?_)
      apply List.mem_map.mpr
      refine Exists.intro (fun i => f i.succ) (And.intro (ih _) ?_)
      funext i
      exact Fin.cases rfl (fun _ => rfl) i

structure RawFieldTable (q : Nat) where
  zero : Fin q
  one : Fin q
  add : Fin q -> Fin q -> Fin q
  mul : Fin q -> Fin q -> Fin q

def binaryTables (q : Nat) : List (Fin q -> Fin q -> Fin q) :=
  allFunctions (allFunctions (List.finRange q) q) q

theorem mem_binaryTables (q : Nat) (f : Fin q -> Fin q -> Fin q) :
    List.Mem f (binaryTables q) := by
  apply mem_allFunctions
  intro a
  apply mem_allFunctions
  intro x
  exact List.mem_finRange x

def fieldTables (q : Nat) : List (RawFieldTable q) :=
  (List.finRange q).flatMap fun z =>
    (List.finRange q).flatMap fun o =>
      (binaryTables q).flatMap fun a =>
        (binaryTables q).map fun m => RawFieldTable.mk z o a m

theorem mem_fieldTables (q : Nat) (t : RawFieldTable q) : List.Mem t (fieldTables q) := by
  apply List.mem_flatMap.mpr
  refine Exists.intro t.zero (And.intro (by simp) ?_)
  apply List.mem_flatMap.mpr
  refine Exists.intro t.one (And.intro (by simp) ?_)
  apply List.mem_flatMap.mpr
  refine Exists.intro t.add (And.intro (mem_binaryTables _ _) ?_)
  apply List.mem_map.mpr
  refine Exists.intro t.mul (And.intro (mem_binaryTables _ _) ?_)
  cases t
  rfl

def TableValid {q : Nat} (t : RawFieldTable q) : Prop :=
  And (Not (t.zero = t.one))
  (And (forall a b c, t.add (t.add a b) c = t.add a (t.add b c))
  (And (forall a, t.add t.zero a = a)
  (And (forall a, Exists fun b => t.add b a = t.zero)
  (And (forall a b c, t.mul (t.mul a b) c = t.mul a (t.mul b c))
  (And (forall a b, t.mul a b = t.mul b a)
  (And (forall a, t.mul t.one a = a)
  (And (forall a b c, t.mul a (t.add b c) = t.add (t.mul a b) (t.mul a c))
       (forall a, Not (a = t.zero) -> Exists fun b => t.mul a b = t.one))))))))

instance tableValidDecidable {q : Nat} (t : RawFieldTable q) : Decidable (TableValid t) := by
  unfold TableValid
  infer_instance

def firstFieldTable (q : Nat) : Option (RawFieldTable q) :=
  (fieldTables q).find? (fun t => decide (TableValid t))

theorem firstFieldTable_valid {q : Nat} {t : RawFieldTable q}
    (h : firstFieldTable q = some t) : TableValid t := by
  have ht := List.find?_some h
  exact of_decide_eq_true ht

def tableOfEquiv {K : Type u} [Field K] {q : Nat} (e : K ≃ Fin q) : RawFieldTable q where
  zero := e 0
  one := e 1
  add a b := e (e.symm a + e.symm b)
  mul a b := e (e.symm a * e.symm b)

theorem tableOfEquiv_valid {K : Type u} [Field K] {q : Nat} (e : K ≃ Fin q) :
    TableValid (tableOfEquiv e) := by
  refine And.intro ?_ (And.intro ?_ (And.intro ?_ (And.intro ?_
    (And.intro ?_ (And.intro ?_ (And.intro ?_ (And.intro ?_ ?_)))))))
  · intro h
    exact zero_ne_one (e.injective h)
  · intro a b c
    simpa [tableOfEquiv] using congrArg e (add_assoc (e.symm a) (e.symm b) (e.symm c))
  · intro a
    simp [tableOfEquiv]
  · intro a
    refine Exists.intro (e (-e.symm a)) ?_
    simp [tableOfEquiv]
  · intro a b c
    simpa [tableOfEquiv] using congrArg e (mul_assoc (e.symm a) (e.symm b) (e.symm c))
  · intro a b
    simpa [tableOfEquiv] using congrArg e (mul_comm (e.symm a) (e.symm b))
  · intro a
    simp [tableOfEquiv]
  · intro a b c
    simpa [tableOfEquiv] using congrArg e (mul_add (e.symm a) (e.symm b) (e.symm c))
  · intro a ha
    have hne : Not (e.symm a = 0) := by
      intro h
      apply ha
      change a = e 0
      rw [← h]
      exact (e.apply_symm_apply a).symm
    refine Exists.intro (e ((e.symm a)⁻¹)) ?_
    simpa [tableOfEquiv] using congrArg e (mul_inv_cancel₀ hne)

theorem firstFieldTable_exists_of_model (K : Type u) [Field K] [Fintype K]
    (q : Nat) (h : Fintype.card K = q) :
    Exists fun t => firstFieldTable q = some t := by
  classical
  let e : K ≃ Fin q := Fintype.equivFinOfCardEq h
  have ht : TableValid (tableOfEquiv e) := tableOfEquiv_valid e
  have hs : (firstFieldTable q).isSome := by
    apply List.find?_isSome.mpr
    refine Exists.intro (tableOfEquiv e) (And.intro (mem_fieldTables _ _) ?_)
    simpa using ht
  cases heq : firstFieldTable q with
  | none => simp [heq] at hs
  | some t => exact Exists.intro t rfl

end Steiner1029

#check Steiner1029.mem_allFunctions
#print axioms Steiner1029.mem_allFunctions
#check Steiner1029.mem_binaryTables
#print axioms Steiner1029.mem_binaryTables
#check Steiner1029.mem_fieldTables
#print axioms Steiner1029.mem_fieldTables
#check Steiner1029.firstFieldTable_valid
#print axioms Steiner1029.firstFieldTable_valid
#check Steiner1029.tableOfEquiv_valid
#print axioms Steiner1029.tableOfEquiv_valid
#check Steiner1029.firstFieldTable_exists_of_model
#print axioms Steiner1029.firstFieldTable_exists_of_model
#print axioms Steiner1029.allFunctions
#print axioms Steiner1029.binaryTables
#print axioms Steiner1029.fieldTables
#print axioms Steiner1029.tableValidDecidable
#print axioms Steiner1029.firstFieldTable
