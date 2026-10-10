import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Tactic

namespace FaceColoringParity

def edge : SimpleGraph (Fin 2) := ⊤
def star : SimpleGraph (Fin 4) where
  Adj u v := (u=0 ∧ v≠0) ∨ (v=0 ∧ u≠0)
  symm _ _ h := Or.symm h
  loopless v := by simp
instance : DecidableRel edge.Adj := by unfold edge; infer_instance
instance : DecidableRel star.Adj := fun u v => by unfold star; infer_instance

/-- Respecting-edge fixed-point-free involutions are exactly actual perfect matchings. -/
def matching {n : ℕ} (g : SimpleGraph (Fin n)) (p : Equiv.Perm (Fin n)) : Prop :=
  ∀ v, p (p v) = v ∧ p v ≠ v ∧ g.Adj v (p v)
instance {n : ℕ} (g : SimpleGraph (Fin n)) [DecidableRel g.Adj] : DecidablePred (matching g) :=
  fun p => by unfold matching; infer_instance

def matchingCount {n : ℕ} (g : SimpleGraph (Fin n)) [DecidableRel g.Adj] : ℕ :=
  (Finset.univ.filter (matching g)).card

theorem edge_matching_one : matchingCount edge = 1 := by decide
theorem star_matching_zero : matchingCount star = 0 := by decide

def Dart {n : ℕ} (g : SimpleGraph (Fin n)) :=
  {p : Fin n × Fin n // g.Adj p.1 p.2}
instance {n : ℕ} (g : SimpleGraph (Fin n)) [DecidableRel g.Adj] : Fintype (Dart g) := by
  unfold Dart
  infer_instance

instance {n : ℕ} (g : SimpleGraph (Fin n)) : DecidableEq (Dart g) := by
  unfold Dart
  infer_instance

def pairs2 : Fin 2 → Fin 2 × Fin 2 := ![(0,1),(1,0)]
def pairs6 : Fin 6 → Fin 4 × Fin 4 := ![(0,1),(1,0),(0,2),(2,0),(0,3),(3,0)]

def dart2 (i : Fin 2) : Dart edge := ⟨pairs2 i, by fin_cases i <;> decide⟩
def dart6 (i : Fin 6) : Dart star := ⟨pairs6 i, by fin_cases i <;> decide⟩

theorem dart2_bijective : Function.Bijective dart2 := by
  unfold Function.Bijective Function.Injective Function.Surjective
  decide
theorem dart6_bijective : Function.Bijective dart6 := by
  unfold Function.Bijective Function.Injective Function.Surjective
  decide

noncomputable def enumerate2 : Fin 2 ≃ Dart edge := Equiv.ofBijective dart2 dart2_bijective
noncomputable def enumerate6 : Fin 6 ≃ Dart star := Equiv.ofBijective dart6 dart6_bijective

def rev2 : Fin 2 → Fin 2 := ![1,0]
def rev6 : Fin 6 → Fin 6 := ![1,0,3,2,5,4]
def next2 : Fin 2 → Fin 2 := ![1,0]
def next6 : Fin 6 → Fin 6 := ![1,2,3,4,5,0]
def rot2 (i : Fin 2) : Fin 2 := next2 (rev2 i)
def rot6 (i : Fin 6) : Fin 6 := next6 (rev6 i)

/-- The reversal maps are the actual dart reversal, not arbitrary permutations. -/
theorem reversal2 : ∀ i, pairs2 (rev2 i) = (pairs2 i).swap := by decide
theorem reversal6 : ∀ i, pairs6 (rev6 i) = (pairs6 i).swap := by decide

/-- Actual local rotations keep the source vertex; all rotations here are bijective. -/
theorem rotation2 : (∀ i, (pairs2 (rot2 i)).1 = (pairs2 i).1) ∧ Function.Bijective rot2 := by decide
theorem rotation6 : (∀ i, (pairs6 (rot6 i)).1 = (pairs6 i).1) ∧ Function.Bijective rot6 := by decide

theorem face_rule2 : ∀ i, rot2 (rev2 i) = next2 i := by decide
theorem face_rule6 : ∀ i, rot6 (rev6 i) = next6 i := by decide

/-- Face successor on the actual dart set via its checked enumeration. -/
noncomputable def actualFace2 (d : Dart edge) : Dart edge := enumerate2 (next2 (enumerate2.symm d))
noncomputable def actualFace6 (d : Dart star) : Dart star := enumerate6 (next6 (enumerate6.symm d))

theorem face_bridge2 (i : Fin 2) : actualFace2 (enumerate2 i) = enumerate2 (next2 i) := by
  simp [actualFace2]
theorem face_bridge6 (i : Fin 6) : actualFace6 (enumerate6 i) = enumerate6 (next6 i) := by
  simp [actualFace6]

/-- Face classes are true orbits of the face successor. -/
def relation2 (i j : Fin 2) : Prop := ∃ k : Fin 2, next2^[k.val] i = j
def relation6 (i j : Fin 6) : Prop := ∃ k : Fin 6, next6^[k.val] i = j

theorem all_related2 : ∀ i j, relation2 i j := by
  unfold relation2
  decide
theorem all_related6 : ∀ i j, relation6 i j := by
  unfold relation6
  decide

def faceSetoid2 : Setoid (Fin 2) where
  r := relation2
  iseqv := ⟨fun i => all_related2 i i, fun _ => all_related2 _ _, fun _ _ => all_related2 _ _⟩
def faceSetoid6 : Setoid (Fin 6) where
  r := relation6
  iseqv := ⟨fun i => all_related6 i i, fun _ => all_related6 _ _, fun _ _ => all_related6 _ _⟩
abbrev Face2 := Quotient faceSetoid2
abbrev Face6 := Quotient faceSetoid6

instance : Subsingleton Face2 := ⟨by
  intro x y
  induction x using Quotient.inductionOn with | h i =>
    induction y using Quotient.inductionOn with | h j => exact Quotient.sound (all_related2 i j)⟩
instance : Subsingleton Face6 := ⟨by
  intro x y
  induction x using Quotient.inductionOn with | h i =>
    induction y using Quotient.inductionOn with | h j => exact Quotient.sound (all_related6 i j)⟩
noncomputable instance : Fintype Face2 := Fintype.ofSubsingleton ⟦(0 : Fin 2)⟧
noncomputable instance : Fintype Face6 := Fintype.ofSubsingleton ⟦(0 : Fin 6)⟧

instance : Unique Face2 where
  default := ⟦(0 : Fin 2)⟧
  uniq _ := Subsingleton.elim _ _
instance : Unique Face6 where
  default := ⟦(0 : Fin 6)⟧
  uniq _ := Subsingleton.elim _ _

/-- The actual face-coloring counts agree for every palette size. -/
theorem coloring_counts_equal (q : ℕ) :
    Fintype.card (Face2 → Fin q) = Fintype.card (Face6 → Fin q) := by
  simp [Fintype.card_fun, Fintype.card_ofSubsingleton]

/-- A direct bijection also identifies colorings, and hence their relabeling classes. -/
noncomputable def coloringEquiv (q : ℕ) : (Face2 → Fin q) ≃ (Face6 → Fin q) :=
  Equiv.piCongrLeft (fun _ => Fin q) (Equiv.ofUnique Face2 Face6)

theorem parity_different : matchingCount edge % 2 ≠ matchingCount star % 2 := by
  rw [edge_matching_one, star_matching_zero]
  norm_num

#print axioms edge_matching_one
#print axioms star_matching_zero
#print axioms dart2_bijective
#print axioms dart6_bijective
#print axioms reversal6
#print axioms rotation6
#print axioms all_related2
#print axioms all_related6
#print axioms coloring_counts_equal
#print axioms parity_different
end FaceColoringParity
