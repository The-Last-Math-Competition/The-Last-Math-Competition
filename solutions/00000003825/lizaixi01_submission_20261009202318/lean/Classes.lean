import Family

namespace FixedAlphabetA1

def iterate {V : Type} (op : V → Option V) : ℕ → V → Option V
  | 0,x => some x
  | n+1,x => (op x).bind (iterate op n)

theorem normal_f_strings {V : Type} (A : A1Crystal V) (n : ℕ) (x : V) :
    iterate A.f n x ≠ none ↔ n ≤ A.phi x := by
  induction n generalizing x with
  | zero => simp [iterate]
  | succ n ih =>
    cases hx : A.f x with
    | none =>
      have hp := (A.f_none x).mp hx
      simp [iterate,hx,hp]
    | some y =>
      have hp := A.f_phi x y hx
      simp only [iterate,hx,Option.bind_some]
      rw [ih]
      omega

theorem normal_e_strings {V : Type} (A : A1Crystal V) (n : ℕ) (x : V) :
    iterate A.e n x ≠ none ↔ n ≤ A.eps x := by
  induction n generalizing x with
  | zero => simp [iterate]
  | succ n ih =>
    cases hx : A.e x with
    | none =>
      have hp := (A.e_none x).mp hx
      simp [iterate,hx,hp]
    | some y =>
      have hp := A.e_eps hx
      simp only [iterate,hx,Option.bind_some]
      rw [ih]
      omega

/-- Actual finite undirected edge paths; no connectivity assumption is built into the family. -/
inductive Walk {V : Type} (A : A1Crystal V) : V → V → Prop
  | refl (x) : Walk A x x
  | snoc {x y z} : Walk A x y → (A.f y = some z ∨ A.f z = some y) → Walk A x z

theorem Walk.trans {V : Type} {A : A1Crystal V} {x y z : V}
    (h1 : Walk A x y) (h2 : Walk A y z) : Walk A x z := by
  induction h2 with
  | refl => exact h1
  | snoc h edge ih => exact .snoc ih edge

theorem Walk.symm {V : Type} {A : A1Crystal V} {x y : V} (h : Walk A x y) : Walk A y x := by
  induction h with
  | refl => exact .refl _
  | @snoc y z h edge ih =>
    exact (Walk.snoc (Walk.refl z) edge.symm).trans ih

def Connected {V : Type} (A : A1Crystal V) : Prop := ∀ x y, Walk A x y

theorem from_highest (k i : ℕ) (hi : i<k+1) : Walk (family k) 0 ⟨i,hi⟩ := by
  induction i with
  | zero => exact .refl 0
  | succ i ih =>
    have hi' : i<k+1 := by omega
    apply Walk.snoc (ih hi')
    left
    exact (SupplementScout.lower_eq_some_iff k ⟨i,hi'⟩ ⟨i+1,hi⟩).mpr rfl

theorem family_connected (k : ℕ) : Connected (family k) := by
  intro x y
  exact (from_highest k x.val x.isLt).symm.trans (from_highest k y.val y.isLt)

theorem family_full_strings (k : ℕ) (i : Fin (k+1)) (n : ℕ) :
    (iterate (family k).e n i ≠ none ↔ n≤i.val) ∧
    (iterate (family k).f n i ≠ none ↔ n≤k-i.val) :=
  ⟨normal_e_strings (family k) n i,normal_f_strings (family k) n i⟩

theorem highest_weight_dimension (k : ℕ) :
    (family k).wt 0 = (k : ℤ) ∧ (family k).eps 0=0 ∧ (family k).phi 0=k ∧
    Fintype.card (Fin (k+1))=k+1 := by
  simp [family,SupplementScout.wt,SupplementScout.epsilon,SupplementScout.phi]

/-- Isomorphisms preserve the actual operators and crystal data, not only size. -/
structure CrystalIso {V W : Type} (A : A1Crystal V) (B : A1Crystal W) where
  equiv : V ≃ W
  map_e : ∀ x, B.e (equiv x) = (A.e x).map equiv
  map_f : ∀ x, B.f (equiv x) = (A.f x).map equiv
  map_wt : ∀ x, B.wt (equiv x)=A.wt x
  map_eps : ∀ x, B.eps (equiv x)=A.eps x
  map_phi : ∀ x, B.phi (equiv x)=A.phi x

namespace CrystalIso
def refl {V : Type} (A : A1Crystal V) : CrystalIso A A where
  equiv := Equiv.refl _
  map_e x := by simp
  map_f x := by simp
  map_wt x := rfl
  map_eps x := rfl
  map_phi x := rfl

def symm {V W : Type} {A : A1Crystal V} {B : A1Crystal W} (h : CrystalIso A B) : CrystalIso B A where
  equiv := h.equiv.symm
  map_e y := by
    have hs := congrArg (Option.map h.equiv.symm) (h.map_e (h.equiv.symm y))
    simpa [Option.map_map,Function.comp_def] using hs.symm
  map_f y := by
    have hs := congrArg (Option.map h.equiv.symm) (h.map_f (h.equiv.symm y))
    simpa [Option.map_map,Function.comp_def] using hs.symm
  map_wt y := by simpa using (h.map_wt (h.equiv.symm y)).symm
  map_eps y := by simpa using (h.map_eps (h.equiv.symm y)).symm
  map_phi y := by simpa using (h.map_phi (h.equiv.symm y)).symm

def trans {V W U : Type} {A : A1Crystal V} {B : A1Crystal W} {C : A1Crystal U}
    (h : CrystalIso A B) (g : CrystalIso B C) : CrystalIso A C where
  equiv := h.equiv.trans g.equiv
  map_e x := by
    change C.e (g.equiv (h.equiv x)) = (A.e x).map (h.equiv.trans g.equiv)
    rw [g.map_e,h.map_e]
    rw [Option.map_map]
    rfl
  map_f x := by
    change C.f (g.equiv (h.equiv x)) = (A.f x).map (h.equiv.trans g.equiv)
    rw [g.map_f,h.map_f]
    rw [Option.map_map]
    rfl
  map_wt x := (g.map_wt (h.equiv x)).trans (h.map_wt x)
  map_eps x := (g.map_eps (h.equiv x)).trans (h.map_eps x)
  map_phi x := (g.map_phi (h.equiv x)).trans (h.map_phi x)
end CrystalIso

/-- Genuine finite nonempty connected crystals embedded as subcrystals in the fixed monoid. -/
structure IrreducibleWordCrystal where
  size : ℕ
  base : Fin size
  crystal : A1Crystal (Fin size)
  connected : Connected crystal
  embed : Fin size → List Bool
  injective : Function.Injective embed
  e_bridge : ∀ x, monoidCrystal.e (embed x)=(crystal.e x).map embed
  f_bridge : ∀ x, monoidCrystal.f (embed x)=(crystal.f x).map embed
  wt_bridge : ∀ x, monoidCrystal.wt (embed x)=crystal.wt x
  eps_bridge : ∀ x, monoidCrystal.eps (embed x)=crystal.eps x
  phi_bridge : ∀ x, monoidCrystal.phi (embed x)=crystal.phi x

def familyObject (k : ℕ) : IrreducibleWordCrystal where
  size := k+1
  base := 0
  crystal := family k
  connected := family_connected k
  embed := embedding k
  injective := embedding_injective k
  e_bridge := embedding_e k
  f_bridge := embedding_f k
  wt_bridge x := (embedding_stats k x).2.2
  eps_bridge x := (embedding_stats k x).1
  phi_bridge x := (embedding_stats k x).2.1

instance isoSetoid : Setoid IrreducibleWordCrystal where
  r A B := Nonempty (CrystalIso A.crystal B.crystal)
  iseqv := {
    refl := fun A => ⟨CrystalIso.refl A.crystal⟩
    symm := fun ⟨h⟩ => ⟨h.symm⟩
    trans := fun ⟨h⟩ ⟨g⟩ => ⟨h.trans g⟩
  }

abbrev IrreducibleWordCrystalClass := Quotient isoSetoid
def familyClass (k : ℕ) : IrreducibleWordCrystalClass := Quotient.mk' (familyObject k)

theorem familyClass_injective : Function.Injective familyClass := by
  intro k l h
  rcases Quotient.exact h with ⟨iso⟩
  exact SupplementScout.card_distinguishes k l iso.equiv

theorem infinite_irreducible_classes : Infinite IrreducibleWordCrystalClass :=
  Infinite.of_injective familyClass familyClass_injective

theorem fixed_alphabet_finiteness_false : ¬ Finite IrreducibleWordCrystalClass := by
  letI := infinite_irreducible_classes
  exact Infinite.not_finite

end FixedAlphabetA1
