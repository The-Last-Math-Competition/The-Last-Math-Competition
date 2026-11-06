import Mathlib.AlgebraicTopology.SimplicialComplex.Basic
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Order.Preorder.Chain
import Mathlib.Tactic

namespace ChainSubdivision7126

variable (P : Type*) [PartialOrder P]

def FiniteChain (s : Finset P) : Prop :=
  ∀ a ∈ s, ∀ b ∈ s, a ≤ b ∨ b ≤ a

noncomputable section

open scoped Classical

def orderComplex : AbstractSimplicialComplex P where
  faces := {s | s.Nonempty ∧ FiniteChain P s}
  isRelLowerSet_faces := by
    intro s hs
    refine ⟨hs.1, ?_⟩
    intro t hts ht
    exact ⟨ht, fun a ha b hb => hs.2 a (hts ha) b (hts hb)⟩
  singleton_mem a := by
    refine ⟨Finset.singleton_nonempty a, ?_⟩
    intro x hx y hy
    simp only [Finset.mem_singleton] at hx hy
    subst x
    subst y
    exact Or.inl le_rfl

theorem mem_orderComplex (s : Finset P) :
    s ∈ orderComplex P ↔ s.Nonempty ∧ FiniteChain P s := Iff.rfl

def comparableGraph : SimpleGraph P where
  Adj a b := a ≠ b ∧ (a ≤ b ∨ b ≤ a)
  symm := ⟨by
    intro a b h
    exact ⟨h.1.symm,h.2.symm⟩⟩
  loopless := ⟨by intro a h; exact h.1 rfl⟩

theorem chain_iff_clique (s : Finset P) :
    FiniteChain P s ↔ (comparableGraph P).IsClique (s : Set P) := by
  constructor
  · intro h a ha b hb hne
    exact ⟨hne,h a ha b hb⟩
  · intro h a ha b hb
    by_cases hab : a=b
    · subst b
      exact Or.inl le_rfl
    · exact (h ha hb hab).2

theorem orderComplex_face_iff_clique (s : Finset P) :
    s ∈ orderComplex P ↔ s.Nonempty ∧ (comparableGraph P).IsClique (s : Set P) := by
  rw [mem_orderComplex,chain_iff_clique]

theorem pair_face_iff_adj (a b : P) (hne : a ≠ b) :
    ({a,b} : Finset P) ∈ orderComplex P ↔ (comparableGraph P).Adj a b := by
  rw [mem_orderComplex]
  simp only [FiniteChain, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨h,hc⟩
    exact ⟨hne,hc a (Or.inl rfl) b (Or.inr rfl)⟩
  · intro h
    refine ⟨by simp, ?_⟩
    intro x hx y hy
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
    · exact Or.inl le_rfl
    · exact h.2
    · exact h.2.symm
    · exact Or.inl le_rfl

def IsFlag (K : AbstractSimplicialComplex P) : Prop :=
  ∀ s : Finset P, s.Nonempty →
    (∀ a ∈ s, ∀ b ∈ s, a ≠ b → ({a,b} : Finset P) ∈ K) → s ∈ K

theorem orderComplex_isFlag : IsFlag P (orderComplex P) := by
  intro s hs hpairs
  apply (mem_orderComplex P s).mpr
  refine ⟨hs, ?_⟩
  intro a ha b hb
  by_cases hne : a=b
  · subst b
    exact Or.inl le_rfl
  · exact ((pair_face_iff_adj P a b hne).mp (hpairs a ha b hb hne)).2

theorem chain_iff_standard_isChain (s : Finset P) :
    FiniteChain P s ↔ IsChain (· ≤ ·) (s : Set P) := by
  constructor
  · intro h a ha b hb hne
    exact h a ha b hb
  · intro h a ha b hb
    by_cases hne : a=b
    · subst b
      exact Or.inl le_rfl
    · exact h ha hb hne

variable [Fintype P]

def facesOfSize (k : Nat) : Finset (Finset P) := by
  classical
  exact Finset.univ.filter (fun s => s ∈ orderComplex P ∧ s.card=k)

def chainsOfSize (k : Nat) : Finset (Finset P) := by
  classical
  exact Finset.univ.filter (fun s => s.Nonempty ∧ IsChain (· ≤ ·) (s : Set P) ∧ s.card=k)

theorem facesOfSize_eq_chains (k : Nat) : facesOfSize P k = chainsOfSize P k := by
  classical
  ext s
  simp [facesOfSize, chainsOfSize, mem_orderComplex, chain_iff_standard_isChain, and_assoc]

theorem face_count_eq_chain_count (k : Nat) :
    (facesOfSize P k).card = (chainsOfSize P k).card := by
  rw [facesOfSize_eq_chains]

def fVector (d : Nat) : Nat := (facesOfSize P (d+1)).card

theorem fVector_eq_chain_count (d : Nat) :
    fVector P d = (chainsOfSize P (d+1)).card := face_count_eq_chain_count P (d+1)

variable {P}

def chainFaceEquiv (k : Nat) :
    {s : Finset P // s ∈ facesOfSize P k} ≃ {s : Finset P // s ∈ chainsOfSize P k} where
  toFun s := ⟨s.val, by rw [← facesOfSize_eq_chains]; exact s.property⟩
  invFun s := ⟨s.val, by rw [facesOfSize_eq_chains]; exact s.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

variable (A : Type*)

def FacePoset (family : Finset (Finset A)) := ↥(family.filter Finset.Nonempty)

instance facePosetOrder (family : Finset (Finset A)) : PartialOrder (FacePoset A family) :=
  inferInstanceAs (PartialOrder ↥(family.filter Finset.Nonempty))

instance facePosetFinite (family : Finset (Finset A)) : Fintype (FacePoset A family) :=
  inferInstanceAs (Fintype ↥(family.filter Finset.Nonempty))

def faceFamilySubdivision (family : Finset (Finset A)) : AbstractSimplicialComplex (FacePoset A family) :=
  orderComplex (FacePoset A family)

theorem faceFamily_isFlag (family : Finset (Finset A)) :
    IsFlag (FacePoset A family) (faceFamilySubdivision A family) :=
  orderComplex_isFlag (FacePoset A family)

theorem faceFamily_fVector (family : Finset (Finset A)) (d : Nat) :
    fVector (FacePoset A family) d = (chainsOfSize (FacePoset A family) (d+1)).card :=
  fVector_eq_chain_count (FacePoset A family) d

def SetFacePoset (family : Finset (Set A)) := ↥(family.filter Set.Nonempty)

instance setFacePosetOrder (family : Finset (Set A)) : PartialOrder (SetFacePoset A family) :=
  inferInstanceAs (PartialOrder ↥(family.filter Set.Nonempty))

instance setFacePosetFinite (family : Finset (Set A)) : Fintype (SetFacePoset A family) :=
  inferInstanceAs (Fintype ↥(family.filter Set.Nonempty))

def setFaceSubdivision (family : Finset (Set A)) : AbstractSimplicialComplex (SetFacePoset A family) :=
  orderComplex (SetFacePoset A family)

def properFaceFamily (family : Finset (Set A)) (whole : Set A) : Finset (Set A) :=
  family.filter (fun F => F ≠ whole)

theorem setFaceSubdivision_isFlag (family : Finset (Set A)) :
    IsFlag (SetFacePoset A family) (setFaceSubdivision A family) :=
  orderComplex_isFlag (SetFacePoset A family)

theorem setFaceSubdivision_fVector (family : Finset (Set A)) (d : Nat) :
    fVector (SetFacePoset A family) d = (chainsOfSize (SetFacePoset A family) (d+1)).card :=
  fVector_eq_chain_count (SetFacePoset A family) d

theorem boundarySubdivision_isFlag (family : Finset (Set A)) (whole : Set A) :
    IsFlag (SetFacePoset A (properFaceFamily A family whole))
      (setFaceSubdivision A (properFaceFamily A family whole)) :=
  setFaceSubdivision_isFlag A (properFaceFamily A family whole)

theorem boundarySubdivision_fVector (family : Finset (Set A)) (whole : Set A) (d : Nat) :
    fVector (SetFacePoset A (properFaceFamily A family whole)) d =
      (chainsOfSize (SetFacePoset A (properFaceFamily A family whole)) (d+1)).card :=
  setFaceSubdivision_fVector A (properFaceFamily A family whole) d

theorem empty_face_excluded (family : Finset (Set A)) (F : SetFacePoset A family) :
    F.val.Nonempty := (Finset.mem_filter.mp F.property).2

theorem whole_excluded_from_boundary (family : Finset (Set A)) (whole : Set A)
    (F : SetFacePoset A (properFaceFamily A family whole)) : F.val ≠ whole := by
  exact (Finset.mem_filter.mp (Finset.mem_filter.mp F.property).1).2

variable {Q : Type*} [PartialOrder Q]

omit [Fintype P] in
theorem image_chain_iff (e : P ≃o Q) (s : Finset P) :
    FiniteChain Q (s.image e) ↔ FiniteChain P s := by
  constructor
  · intro h a ha b hb
    have hc := h (e a) (Finset.mem_image.mpr ⟨a,ha,rfl⟩) (e b) (Finset.mem_image.mpr ⟨b,hb,rfl⟩)
    exact hc.imp (fun h => e.le_iff_le.mp h) (fun h => e.le_iff_le.mp h)
  · intro h a ha b hb
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hb
    exact (h x hx y hy).imp (fun h => e.monotone h) (fun h => e.monotone h)

omit [Fintype P] in
theorem image_face_iff (e : P ≃o Q) (s : Finset P) :
    s.image e ∈ orderComplex Q ↔ s ∈ orderComplex P := by
  rw [mem_orderComplex,mem_orderComplex,image_chain_iff]
  simp only [Finset.image_nonempty]

def faceTransport [Fintype Q] (e : P ≃o Q) (k : Nat) :
    {s : Finset P // s ∈ facesOfSize P k} ≃ {s : Finset Q // s ∈ facesOfSize Q k} where
  toFun s := ⟨s.val.image e, by
    have h := Finset.mem_filter.mp s.property
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(image_face_iff e s.val).mpr h.2.1,
      (Finset.card_image_of_injective _ e.injective).trans h.2.2⟩⟩
  invFun s := ⟨s.val.image e.symm, by
    have h := Finset.mem_filter.mp s.property
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(image_face_iff e.symm s.val).mpr h.2.1,
      (Finset.card_image_of_injective _ e.symm.injective).trans h.2.2⟩⟩
  left_inv s := by
    apply Subtype.ext
    simp [Finset.image_image, Function.comp_def]
  right_inv s := by
    apply Subtype.ext
    simp [Finset.image_image, Function.comp_def]

theorem face_count_orderIso_invariant [Fintype Q] (e : P ≃o Q) (k : Nat) :
    (facesOfSize P k).card = (facesOfSize Q k).card := by
  simpa using Fintype.card_congr (faceTransport e k)

theorem fVector_orderIso_invariant [Fintype Q] (e : P ≃o Q) (d : Nat) :
    fVector P d = fVector Q d := face_count_orderIso_invariant e (d+1)

end
end ChainSubdivision7126
