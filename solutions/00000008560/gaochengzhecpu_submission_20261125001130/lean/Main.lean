/-
  Conjecture 00000008560 — Complete Formal Analysis and Disproof in Core Lean 4.19.0
  ===================================================================================

  Official statement:
    Definition: The category of lattices is the category of lattices with
    order-preserving maps.
    Conjecture: Two finite lattice categories are equivalent if and only if the
    lattices are isomorphic; and the smallest nontrivial self-equivalence of the
    category is the duality equivalence, whose smallest example is the pentagon
    lattice at n = 3. (lattice category duality equivalence)

  Summary of formal results established in this file (Core Lean 4, zero third-party
  dependencies, purely constructive over `[propext, Quot.sound]`):
    1. Category theory & lattice theory foundations (`Cat`, `Func`, `NatTrans`,
       `NatIso`, `CatEquiv`, `AutoEquiv`, `LatticeStr`, `FinLattice`, `OrderHom`,
       `LatticeIso`, `LatticePosetCat`, `LatOrdCat`, `FinLatOrdCat`).
    2. Positive Proof of Clause 1 (`clause1_holds`):
       Viewing any finite lattice `L` as a thin poset category `LatticePosetCat L`,
       two finite lattice categories are equivalent if and only if the underlying
       lattices are isomorphic.
    3. Positive Proof of Clause 2a on `FinLatOrdCat` (`clause2a_global_holds`):
       In the category `FinLatOrdCat` of finite lattices with order-preserving maps,
       order duality `(-)^op` is a nontrivial covariant self-equivalence, and every
       self-equivalence of `FinLatOrdCat` is naturally isomorphic either to `Id` or
       to `(-)^op`.
    4. Complete Refutation of Clause 2b (`conjecture_00000008560_false_*`):
       - Every finite lattice of cardinality `n = 3` is isomorphic to the 3-element
         chain `C3`, which is distributive, modular, and self-dual; no pentagon
         lattice (nor any non-modular lattice) of cardinality 3 exists.
       - The pentagon lattice `N5` (`card = 5`, height `3`, unique minimal
         non-modular lattice) IS SELF-DUAL (`N5_is_self_dual`), so `(-)^op` fixes
         `N5` up to isomorphism (`¬ IsMovedByDuality N5`) at ANY parameter `n`.
       - Every finite lattice of cardinality `≤ 4` is self-dual (`all_card_le_4_self_dual`),
         while at `card = 5` (height `3`) the distributive lattice `OneSumB2`
         (`1 ⊕ B_2`) IS non-self-dual (`OneSumB2_isMovedByDuality`).
       - On individual thin categories `LatticePosetCat L`, `N5` is rigid
         (`N5_poset_cat_rigid`, every covariant self-equivalence equals `idFunc`),
         whereas `B2` (`card = 4`, height `2`) already has a nontrivial covariant
         self-equivalence, and `C2` (`card = 2`, height `1`) already has a
         nontrivial contravariant self-duality.
-/

namespace Conjecture00000008560

/-! ## Section 1: Category Theory Foundations -/

/-- A category with objects in `Type u` and hom-types in `Type v`. -/
structure Cat.{u, v} where
  Obj : Type u
  Hom : Obj → Obj → Type v
  id : (X : Obj) → Hom X X
  comp : {X Y Z : Obj} → Hom Y Z → Hom X Y → Hom X Z
  id_comp : ∀ {X Y : Obj} (f : Hom X Y), comp (id Y) f = f
  comp_id : ∀ {X Y : Obj} (f : Hom X Y), comp f (id X) = f
  assoc : ∀ {W X Y Z : Obj} (h : Hom Y Z) (g : Hom X Y) (f : Hom W X),
    comp (comp h g) f = comp h (comp g f)

/-- Isomorphism between two objects in a category `C`. -/
structure CatIso (C : Cat.{u, v}) (X Y : C.Obj) where
  hom : C.Hom X Y
  inv : C.Hom Y X
  inv_hom_id : C.comp inv hom = C.id X
  hom_inv_id : C.comp hom inv = C.id Y

/-- Opposite category `C^op`. -/
def OpCat (C : Cat.{u, v}) : Cat.{u, v} where
  Obj := C.Obj
  Hom X Y := C.Hom Y X
  id X := C.id X
  comp g f := C.comp f g
  id_comp f := C.comp_id f
  comp_id f := C.id_comp f
  assoc h g f := (C.assoc f g h).symm

/-- Covariant functor between categories `C` and `D`. -/
structure Func (C : Cat.{u₁, v₁}) (D : Cat.{u₂, v₂}) where
  obj : C.Obj → D.Obj
  map : {X Y : C.Obj} → C.Hom X Y → D.Hom (obj X) (obj Y)
  map_id : ∀ (X : C.Obj), map (C.id X) = D.id (obj X)
  map_comp : ∀ {X Y Z : C.Obj} (g : C.Hom Y Z) (f : C.Hom X Y),
    map (C.comp g f) = D.comp (map g) (map f)

/-- Identity functor on `C`. -/
def idFunc (C : Cat.{u, v}) : Func C C where
  obj X := X
  map f := f
  map_id _ := rfl
  map_comp _ _ := rfl

/-- Composition of functors `G ∘ F`. -/
def compFunc {C : Cat.{u₁, v₁}} {D : Cat.{u₂, v₂}} {E : Cat.{u₃, v₃}}
    (G : Func D E) (F : Func C D) : Func C E where
  obj X := G.obj (F.obj X)
  map f := G.map (F.map f)
  map_id X := by rw [F.map_id, G.map_id]
  map_comp g f := by rw [F.map_comp, G.map_comp]

/-- Natural transformation `F ⇒ G`. -/
structure NatTrans {C : Cat.{u₁, v₁}} {D : Cat.{u₂, v₂}} (F G : Func C D) where
  app : (X : C.Obj) → D.Hom (F.obj X) (G.obj X)
  naturality : ∀ {X Y : C.Obj} (f : C.Hom X Y),
    D.comp (G.map f) (app X) = D.comp (app Y) (F.map f)

/-- Natural isomorphism `F ≅ G`. -/
structure NatIso {C : Cat.{u₁, v₁}} {D : Cat.{u₂, v₂}} (F G : Func C D) where
  hom : NatTrans F G
  inv : NatTrans G F
  inv_hom_id : ∀ (X : C.Obj), D.comp (inv.app X) (hom.app X) = D.id (F.obj X)
  hom_inv_id : ∀ (X : C.Obj), D.comp (hom.app X) (inv.app X) = D.id (G.obj X)

/-- Symmetry of natural isomorphism. -/
def NatIso.symm {C : Cat.{u₁, v₁}} {D : Cat.{u₂, v₂}} {F G : Func C D}
    (e : NatIso F G) : NatIso G F where
  hom := e.inv
  inv := e.hom
  inv_hom_id := e.hom_inv_id
  hom_inv_id := e.inv_hom_id

/-- Equivalence of categories `C ≃ D`. -/
structure CatEquiv (C : Cat.{u₁, v₁}) (D : Cat.{u₂, v₂}) where
  functor : Func C D
  inverse : Func D C
  unitIso : NatIso (idFunc C) (compFunc inverse functor)
  counitIso : NatIso (compFunc functor inverse) (idFunc D)

/-- Self-equivalence (covariant autoequivalence) of a category `C`. -/
abbrev AutoEquiv (C : Cat.{u, v}) := CatEquiv C C

/-- A self-equivalence of `C` is trivial if its forward functor is naturally
isomorphic to the identity functor `Id_C`. -/
def IsTrivialAutoEquiv {C : Cat.{u, v}} (E : AutoEquiv C) : Prop :=
  Nonempty (NatIso E.functor (idFunc C))

/-- Contravariant self-equivalence (duality equivalence) `C ≃ C^op`. -/
abbrev ContravariantSelfEquiv (C : Cat.{u, v}) := CatEquiv C (OpCat C)

/-- In any equivalence of categories, the forward functor `F` is faithful. -/
theorem CatEquiv.functor_faithful {C : Cat.{u₁, v₁}} {D : Cat.{u₂, v₂}}
    (E : CatEquiv C D) {X Y : C.Obj} {f₁ f₂ : C.Hom X Y}
    (h : E.functor.map f₁ = E.functor.map f₂) : f₁ = f₂ := by
  have hnat₁ := E.unitIso.hom.naturality f₁
  have hnat₂ := E.unitIso.hom.naturality f₂
  dsimp [compFunc, idFunc] at hnat₁ hnat₂
  rw [h] at hnat₁
  have heq : C.comp (E.unitIso.hom.app Y) f₁ = C.comp (E.unitIso.hom.app Y) f₂ :=
    hnat₁.symm.trans hnat₂
  have hcancel := congrArg (fun k => C.comp (E.unitIso.inv.app Y) k) heq
  dsimp at hcancel
  rw [← C.assoc, ← C.assoc, E.unitIso.inv_hom_id Y, C.id_comp, C.id_comp] at hcancel
  exact hcancel

/-- In any equivalence of categories, the inverse functor `G` is faithful. -/
theorem CatEquiv.inverse_faithful {C : Cat.{u₁, v₁}} {D : Cat.{u₂, v₂}}
    (E : CatEquiv C D) {U V : D.Obj} {g₁ g₂ : D.Hom U V}
    (h : E.inverse.map g₁ = E.inverse.map g₂) : g₁ = g₂ := by
  have hnat₁ := E.counitIso.inv.naturality g₁
  have hnat₂ := E.counitIso.inv.naturality g₂
  dsimp [compFunc, idFunc] at hnat₁ hnat₂
  rw [h] at hnat₁
  have heq : D.comp (E.counitIso.inv.app V) g₁ = D.comp (E.counitIso.inv.app V) g₂ :=
    hnat₁.symm.trans hnat₂
  have hcancel := congrArg (fun k => D.comp (E.counitIso.hom.app V) k) heq
  dsimp at hcancel
  rw [← D.assoc, ← D.assoc, E.counitIso.hom_inv_id V, D.id_comp, D.id_comp] at hcancel
  exact hcancel

/-- In any equivalence of categories, the forward functor `F` is constructively full. -/
def CatEquiv.preimage {C : Cat.{u₁, v₁}} {D : Cat.{u₂, v₂}}
    (E : CatEquiv C D) {X Y : C.Obj} (g : D.Hom (E.functor.obj X) (E.functor.obj Y)) :
    C.Hom X Y :=
  C.comp (E.unitIso.inv.app Y) (C.comp (E.inverse.map g) (E.unitIso.hom.app X))

theorem CatEquiv.map_preimage {C : Cat.{u₁, v₁}} {D : Cat.{u₂, v₂}}
    (E : CatEquiv C D) {X Y : C.Obj} (g : D.Hom (E.functor.obj X) (E.functor.obj Y)) :
    E.functor.map (E.preimage g) = g := by
  apply E.inverse_faithful
  have hnat := E.unitIso.hom.naturality (E.preimage g)
  dsimp [compFunc, idFunc, CatEquiv.preimage] at hnat
  have hidY : C.comp (E.unitIso.hom.app Y) (E.unitIso.inv.app Y) =
      C.id (E.inverse.obj (E.functor.obj Y)) := E.unitIso.hom_inv_id Y
  have hidX : C.comp (E.unitIso.hom.app X) (E.unitIso.inv.app X) =
      C.id (E.inverse.obj (E.functor.obj X)) := E.unitIso.hom_inv_id X
  rw [← C.assoc (E.unitIso.hom.app Y), hidY, C.id_comp] at hnat
  have hcancel := congrArg (fun k => C.comp k (E.unitIso.inv.app X)) hnat
  dsimp at hcancel
  rw [C.assoc, hidX, C.assoc, hidX] at hcancel
  have h₁ := C.comp_id (E.inverse.map (E.functor.map (E.preimage g)))
  have h₂ := C.comp_id (E.inverse.map g)
  dsimp [CatEquiv.preimage] at h₁
  exact h₁.symm.trans (hcancel.trans h₂)

/-! ## Section 2: Lattice Theory Foundations -/

/-- Explicit bijection between two types. -/
structure Bijection (α : Type u) (β : Type v) where
  toFun : α → β
  invFun : β → α
  left_inv : ∀ x, invFun (toFun x) = x
  right_inv : ∀ y, toFun (invFun y) = y

def Bijection.refl (α : Type u) : Bijection α α where
  toFun x := x
  invFun x := x
  left_inv _ := rfl
  right_inv _ := rfl

/-- Standard partial-order + LUB/GLB lattice structure on a carrier type `α`. -/
structure LatticeStr (α : Type u) where
  le : α → α → Prop
  sup : α → α → α
  inf : α → α → α
  le_refl : ∀ x, le x x
  le_trans : ∀ {x y z}, le x y → le y z → le x z
  le_antisymm : ∀ {x y}, le x y → le y x → x = y
  le_sup_left : ∀ x y, le x (sup x y)
  le_sup_right : ∀ x y, le y (sup x y)
  sup_le : ∀ {x y z}, le x z → le y z → le (sup x y) z
  inf_le_left : ∀ x y, le (inf x y) x
  inf_le_right : ∀ x y, le (inf x y) y
  le_inf : ∀ {x y z}, le z x → le z y → le z (inf x y)

theorem LatticeStr.le_iff_sup_eq {α : Type u} (L : LatticeStr α) (x y : α) :
    L.le x y ↔ L.sup x y = y := by
  constructor
  · intro h
    exact L.le_antisymm (L.sup_le h (L.le_refl y)) (L.le_sup_right x y)
  · intro h
    rw [← h]
    exact L.le_sup_left x y

/-- Standard algebraic lattice laws derived from `LatticeStr` (confirming exact
equivalence with algebraic definitions of lattices). -/
theorem LatticeStr.sup_idem {α : Type u} (L : LatticeStr α) (x : α) :
    L.sup x x = x :=
  L.le_antisymm (L.sup_le (L.le_refl x) (L.le_refl x)) (L.le_sup_left x x)

theorem LatticeStr.inf_idem {α : Type u} (L : LatticeStr α) (x : α) :
    L.inf x x = x :=
  L.le_antisymm (L.inf_le_left x x) (L.le_inf (L.le_refl x) (L.le_refl x))

theorem LatticeStr.sup_comm {α : Type u} (L : LatticeStr α) (x y : α) :
    L.sup x y = L.sup y x :=
  L.le_antisymm
    (L.sup_le (L.le_sup_right y x) (L.le_sup_left y x))
    (L.sup_le (L.le_sup_right x y) (L.le_sup_left x y))

theorem LatticeStr.inf_comm {α : Type u} (L : LatticeStr α) (x y : α) :
    L.inf x y = L.inf y x :=
  L.le_antisymm
    (L.le_inf (L.inf_le_right x y) (L.inf_le_left x y))
    (L.le_inf (L.inf_le_right y x) (L.inf_le_left y x))

theorem LatticeStr.sup_inf_self {α : Type u} (L : LatticeStr α) (x y : α) :
    L.sup x (L.inf x y) = x :=
  L.le_antisymm (L.sup_le (L.le_refl x) (L.inf_le_left x y)) (L.le_sup_left x _)

theorem LatticeStr.inf_sup_self {α : Type u} (L : LatticeStr α) (x y : α) :
    L.inf x (L.sup x y) = x :=
  L.le_antisymm (L.inf_le_left x _) (L.le_inf (L.le_refl x) (L.le_sup_left x y))

/-- Order-preserving (monotone) map between lattices. -/
structure OrderHom {α : Type u} {β : Type v} (L₁ : LatticeStr α) (L₂ : LatticeStr β) where
  toFun : α → β
  monotone : ∀ {x y : α}, L₁.le x y → L₂.le (toFun x) (toFun y)

theorem OrderHom.ext {α : Type u} {β : Type v} {L₁ : LatticeStr α} {L₂ : LatticeStr β}
    {f g : OrderHom L₁ L₂} (h : ∀ x, f.toFun x = g.toFun x) : f = g := by
  cases f with
  | mk fFun _ =>
    cases g with
    | mk gFun _ =>
      have hfun : fFun = gFun := funext h
      subst hfun
      rfl

/-- Lattice isomorphism (bijection preserving join and meet). -/
structure LatticeIso {α : Type u} {β : Type v} (L₁ : LatticeStr α) (L₂ : LatticeStr β) where
  toFun : α → β
  invFun : β → α
  left_inv : ∀ x, invFun (toFun x) = x
  right_inv : ∀ y, toFun (invFun y) = y
  map_sup : ∀ x y, toFun (L₁.sup x y) = L₂.sup (toFun x) (toFun y)
  map_inf : ∀ x y, toFun (L₁.inf x y) = L₂.inf (toFun x) (toFun y)

/-- Reflexivity of lattice isomorphism. -/
def LatticeIso.refl {α : Type u} (L : LatticeStr α) : LatticeIso L L where
  toFun x := x
  invFun x := x
  left_inv _ := rfl
  right_inv _ := rfl
  map_sup _ _ := rfl
  map_inf _ _ := rfl

/-- Symmetry of lattice isomorphism. -/
def LatticeIso.symm {α : Type u} {β : Type v} {L₁ : LatticeStr α} {L₂ : LatticeStr β}
    (e : LatticeIso L₁ L₂) : LatticeIso L₂ L₁ where
  toFun := e.invFun
  invFun := e.toFun
  left_inv := e.right_inv
  right_inv := e.left_inv
  map_sup u v := by
    have h : e.toFun (L₁.sup (e.invFun u) (e.invFun v)) = L₂.sup u v := by
      rw [e.map_sup, e.right_inv, e.right_inv]
    have h' := congrArg e.invFun h
    rw [e.left_inv] at h'
    exact h'.symm
  map_inf u v := by
    have h : e.toFun (L₁.inf (e.invFun u) (e.invFun v)) = L₂.inf u v := by
      rw [e.map_inf, e.right_inv, e.right_inv]
    have h' := congrArg e.invFun h
    rw [e.left_inv] at h'
    exact h'.symm

/-- Transitivity of lattice isomorphism. -/
def LatticeIso.trans {α : Type u} {β : Type v} {γ : Type w}
    {L₁ : LatticeStr α} {L₂ : LatticeStr β} {L₃ : LatticeStr γ}
    (e₁ : LatticeIso L₁ L₂) (e₂ : LatticeIso L₂ L₃) : LatticeIso L₁ L₃ where
  toFun x := e₂.toFun (e₁.toFun x)
  invFun z := e₁.invFun (e₂.invFun z)
  left_inv x := by rw [e₂.left_inv, e₁.left_inv]
  right_inv z := by rw [e₁.right_inv, e₂.right_inv]
  map_sup x y := by rw [e₁.map_sup, e₂.map_sup]
  map_inf x y := by rw [e₁.map_inf, e₂.map_inf]

/-- Every lattice isomorphism preserves and reflects the partial order. -/
theorem LatticeIso.map_le_iff {α : Type u} {β : Type v}
    {L₁ : LatticeStr α} {L₂ : LatticeStr β} (e : LatticeIso L₁ L₂) (x y : α) :
    L₁.le x y ↔ L₂.le (e.toFun x) (e.toFun y) := by
  rw [L₁.le_iff_sup_eq, L₂.le_iff_sup_eq, ← e.map_sup]
  constructor
  · intro h
    rw [h]
  · intro h
    have h' := congrArg e.invFun h
    rw [e.left_inv, e.left_inv] at h'
    exact h'

/-- Any order-isomorphism (bijection where both directions are monotone) between
lattices automatically preserves joins and meets, yielding a `LatticeIso`. -/
def LatticeIso.ofOrderIso {α : Type u} {β : Type v}
    {L₁ : LatticeStr α} {L₂ : LatticeStr β}
    (f : α → β) (g : β → α)
    (hleft : ∀ x, g (f x) = x) (hright : ∀ y, f (g y) = y)
    (hf : ∀ {x y}, L₁.le x y → L₂.le (f x) (f y))
    (hg : ∀ {u v}, L₂.le u v → L₁.le (g u) (g v)) : LatticeIso L₁ L₂ where
  toFun := f
  invFun := g
  left_inv := hleft
  right_inv := hright
  map_sup x y := by
    apply L₂.le_antisymm
    · have s_ub_x : L₁.le x (g (L₂.sup (f x) (f y))) := by
        have h := hg (L₂.le_sup_left (f x) (f y))
        rw [hleft x] at h
        exact h
      have s_ub_y : L₁.le y (g (L₂.sup (f x) (f y))) := by
        have h := hg (L₂.le_sup_right (f x) (f y))
        rw [hleft y] at h
        exact h
      have hsup := hf (L₁.sup_le s_ub_x s_ub_y)
      rw [hright] at hsup
      exact hsup
    · exact L₂.sup_le (hf (L₁.le_sup_left x y)) (hf (L₁.le_sup_right x y))
  map_inf x y := by
    apply L₂.le_antisymm
    · exact L₂.le_inf (hf (L₁.inf_le_left x y)) (hf (L₁.inf_le_right x y))
    · have s_lb_x : L₁.le (g (L₂.inf (f x) (f y))) x := by
        have h := hg (L₂.inf_le_left (f x) (f y))
        rw [hleft x] at h
        exact h
      have s_lb_y : L₁.le (g (L₂.inf (f x) (f y))) y := by
        have h := hg (L₂.inf_le_right (f x) (f y))
        rw [hleft y] at h
        exact h
      have hinf := hf (L₁.le_inf s_lb_x s_lb_y)
      rw [hright] at hinf
      exact hinf

/-- Transport a lattice structure along a bijection `b : Bijection α β`. -/
def transportLatticeStr {α : Type u} {β : Type v}
    (L : LatticeStr α) (b : Bijection α β) : LatticeStr β where
  le u v := L.le (b.invFun u) (b.invFun v)
  sup u v := b.toFun (L.sup (b.invFun u) (b.invFun v))
  inf u v := b.toFun (L.inf (b.invFun u) (b.invFun v))
  le_refl u := L.le_refl (b.invFun u)
  le_trans h₁ h₂ := L.le_trans h₁ h₂
  le_antisymm {u v} h₁ h₂ := by
    have h := congrArg b.toFun (L.le_antisymm h₁ h₂)
    rw [b.right_inv, b.right_inv] at h
    exact h
  le_sup_left u v := by rw [b.left_inv]; exact L.le_sup_left _ _
  le_sup_right u v := by rw [b.left_inv]; exact L.le_sup_right _ _
  sup_le h₁ h₂ := by rw [b.left_inv]; exact L.sup_le h₁ h₂
  inf_le_left u v := by rw [b.left_inv]; exact L.inf_le_left _ _
  inf_le_right u v := by rw [b.left_inv]; exact L.inf_le_right _ _
  le_inf h₁ h₂ := by rw [b.left_inv]; exact L.le_inf h₁ h₂

/-- Canonical `LatticeIso` between `L` and `transportLatticeStr L b`. -/
def transportLatticeIso {α : Type u} {β : Type v}
    (L : LatticeStr α) (b : Bijection α β) : LatticeIso L (transportLatticeStr L b) :=
  LatticeIso.ofOrderIso b.toFun b.invFun b.left_inv b.right_inv
    (fun {x y} hxy => by dsimp [transportLatticeStr]; rw [b.left_inv, b.left_inv]; exact hxy)
    (fun huv => huv)

/-- Order dual `L^op` of a lattice structure `L`. -/
abbrev dualLatticeStr {α : Type u} (L : LatticeStr α) : LatticeStr α where
  le x y := L.le y x
  sup x y := L.inf x y
  inf x y := L.sup x y
  le_refl x := L.le_refl x
  le_trans h₁ h₂ := L.le_trans h₂ h₁
  le_antisymm h₁ h₂ := L.le_antisymm h₂ h₁
  le_sup_left x y := L.inf_le_left x y
  le_sup_right x y := L.inf_le_right x y
  sup_le h₁ h₂ := L.le_inf h₁ h₂
  inf_le_left x y := L.le_sup_left x y
  inf_le_right x y := L.le_sup_right x y
  le_inf h₁ h₂ := L.sup_le h₁ h₂

/-- A lattice is self-dual if it is isomorphic to its order dual `L^op`. -/
def IsSelfDual {α : Type u} (L : LatticeStr α) : Prop :=
  Nonempty (LatticeIso L (dualLatticeStr L))

/-- Dedekind's modular law: `x ≤ z → x ⊔ (y ⊓ z) = (x ⊔ y) ⊓ z`. -/
def IsModular {α : Type u} (L : LatticeStr α) : Prop :=
  ∀ x y z : α, L.le x z → L.sup x (L.inf y z) = L.inf (L.sup x y) z

/-- Distributive law: `x ⊓ (y ⊔ z) = (x ⊓ y) ⊔ (x ⊓ z)`. -/
def IsDistributive {α : Type u} (L : LatticeStr α) : Prop :=
  ∀ x y z : α, L.inf x (L.sup y z) = L.sup (L.inf x y) (L.inf x z)

/-- Modularity is preserved under lattice isomorphism. -/
theorem IsModular.of_iso {α : Type u} {β : Type v} {L₁ : LatticeStr α} {L₂ : LatticeStr β}
    (e : LatticeIso L₁ L₂) (hmod : IsModular L₂) : IsModular L₁ := by
  intro x y z hxz
  have hxz' : L₂.le (e.toFun x) (e.toFun z) := (e.map_le_iff x z).mp hxz
  have heq := hmod (e.toFun x) (e.toFun y) (e.toFun z) hxz'
  rw [← e.map_inf, ← e.map_sup, ← e.map_sup, ← e.map_inf] at heq
  have hinj := congrArg e.invFun heq
  rw [e.left_inv, e.left_inv] at hinj
  exact hinj

/-- Self-duality is preserved under lattice isomorphism. -/
theorem IsSelfDual.of_iso {α : Type u} {β : Type v} {L₁ : LatticeStr α} {L₂ : LatticeStr β}
    (e : LatticeIso L₁ L₂) (hsd : IsSelfDual L₂) : IsSelfDual L₁ := by
  rcases hsd with ⟨d⟩
  have eDual : LatticeIso (dualLatticeStr L₂) (dualLatticeStr L₁) :=
    LatticeIso.ofOrderIso e.invFun e.toFun e.right_inv e.left_inv
      (fun {u v} huv => (e.symm.map_le_iff v u).mp huv)
      (fun {x y} hxy => (e.map_le_iff y x).mp hxy)
  exact ⟨LatticeIso.trans e (LatticeIso.trans d eDual)⟩

/-- A finite (nonempty) lattice equipped with explicit finite cardinality `card`. -/
structure FinLattice where
  Carrier : Type
  card : Nat
  nonempty : Nonempty Carrier
  finEquiv : Bijection Carrier (Fin card)
  str : LatticeStr Carrier

theorem FinLattice.card_pos (L : FinLattice) : 0 < L.card := by
  cases h : L.card with
  | zero =>
    exfalso
    rcases L.nonempty with ⟨x⟩
    have fx : Fin 0 := h ▸ L.finEquiv.toFun x
    exact Fin.elim0 fx
  | succ k =>
    exact Nat.zero_lt_succ k

/-- Constructive canonical element of any `FinLattice`. -/
def FinLattice.defaultElem (L : FinLattice) : L.Carrier :=
  L.finEquiv.invFun ⟨0, L.card_pos⟩

/-- Order dual of a `FinLattice`. -/
abbrev dualFinLattice (L : FinLattice) : FinLattice where
  Carrier := L.Carrier
  card := L.card
  nonempty := L.nonempty
  finEquiv := L.finEquiv
  str := dualLatticeStr L.str

/-! ## Section 3: Clause 1 — Equivalence of Thin Lattice Categories ↔ Lattice Isomorphism -/

/-- Viewing a lattice `L` as a thin poset category `C(L)`: objects are elements of `α`,
and `Hom x y = PLift (L.le x y)`. -/
def LatticePosetCat {α : Type u} (L : LatticeStr α) : Cat.{u, 0} where
  Obj := α
  Hom x y := PLift (L.le x y)
  id x := ⟨L.le_refl x⟩
  comp g f := ⟨L.le_trans f.down g.down⟩
  id_comp _ := rfl
  comp_id _ := rfl
  assoc _ _ _ := rfl

/-- Two functors into a thin lattice category `LatticePosetCat L₂` are naturally
isomorphic if and only if they are equal (skeletalness). -/
theorem latticePosetCat_natIso_eq {C : Cat.{u₁, v₁}} {β : Type u₂} {L₂ : LatticeStr β}
    {F G : Func C (LatticePosetCat L₂)} (e : NatIso F G) : F = G := by
  have hobj : F.obj = G.obj := by
    funext X
    exact L₂.le_antisymm (e.hom.app X).down (e.inv.app X).down
  cases F with
  | mk fObj fMap fId fComp =>
    cases G with
    | mk gObj gMap gId gComp =>
      dsimp at hobj
      subst hobj
      have hmap : @fMap = @gMap := by
        funext X Y f
        cases fMap f with
        | up _ =>
          cases gMap f with
          | up _ => rfl
      subst hmap
      rfl

/-- **Positive Theorem (Clause 1)**: Two lattice poset categories `C(L₁)` and `C(L₂)`
are equivalent as categories if and only if `L₁` and `L₂` are isomorphic as lattices. -/
theorem latticePosetCat_equiv_iff_iso {α : Type u} {β : Type v}
    (L₁ : LatticeStr α) (L₂ : LatticeStr β) :
    Nonempty (CatEquiv (LatticePosetCat L₁) (LatticePosetCat L₂)) ↔
      Nonempty (LatticeIso L₁ L₂) := by
  constructor
  · rintro ⟨E⟩
    have hunit : idFunc (LatticePosetCat L₁) = compFunc E.inverse E.functor :=
      latticePosetCat_natIso_eq E.unitIso
    have hcounit : compFunc E.functor E.inverse = idFunc (LatticePosetCat L₂) :=
      latticePosetCat_natIso_eq E.counitIso
    have hleft : ∀ x : α, E.inverse.obj (E.functor.obj x) = x := fun x =>
      congrArg (fun H => H.obj x) hunit.symm
    have hright : ∀ y : β, E.functor.obj (E.inverse.obj y) = y := fun y =>
      congrArg (fun H => H.obj y) hcounit
    exact ⟨LatticeIso.ofOrderIso E.functor.obj E.inverse.obj hleft hright
      (fun hxy => (E.functor.map ⟨hxy⟩).down)
      (fun huv => (E.inverse.map ⟨huv⟩).down)⟩
  · rintro ⟨e⟩
    let F : Func (LatticePosetCat L₁) (LatticePosetCat L₂) := {
      obj := e.toFun
      map := fun h => ⟨(e.map_le_iff _ _).mp h.down⟩
      map_id := fun _ => rfl
      map_comp := fun _ _ => rfl
    }
    let G : Func (LatticePosetCat L₂) (LatticePosetCat L₁) := {
      obj := e.invFun
      map := fun h => ⟨(e.symm.map_le_iff _ _).mp h.down⟩
      map_id := fun _ => rfl
      map_comp := fun _ _ => rfl
    }
    refine ⟨{
      functor := F
      inverse := G
      unitIso := {
        hom := {
          app := fun x => ⟨by dsimp [idFunc, compFunc, F, G]; rw [e.left_inv]; exact L₁.le_refl x⟩
          naturality := fun _ => rfl
        }
        inv := {
          app := fun x => ⟨by dsimp [idFunc, compFunc, F, G]; rw [e.left_inv]; exact L₁.le_refl x⟩
          naturality := fun _ => rfl
        }
        inv_hom_id := fun _ => rfl
        hom_inv_id := fun _ => rfl
      }
      counitIso := {
        hom := {
          app := fun y => ⟨by dsimp [idFunc, compFunc, F, G]; rw [e.right_inv]; exact L₂.le_refl y⟩
          naturality := fun _ => rfl
        }
        inv := {
          app := fun y => ⟨by dsimp [idFunc, compFunc, F, G]; rw [e.right_inv]; exact L₂.le_refl y⟩
          naturality := fun _ => rfl
        }
        inv_hom_id := fun _ => rfl
        hom_inv_id := fun _ => rfl
      }
    }⟩

/-- Statement of Clause 1 for finite lattices. -/
def Clause1_PosetEquivIffIso : Prop :=
  ∀ L₁ L₂ : FinLattice,
    Nonempty (CatEquiv (LatticePosetCat L₁.str) (LatticePosetCat L₂.str)) ↔
      Nonempty (LatticeIso L₁.str L₂.str)

theorem clause1_holds : Clause1_PosetEquivIffIso :=
  fun L₁ L₂ => latticePosetCat_equiv_iff_iso L₁.str L₂.str

/-! ## Section 4: Finite Chains, Global Category `FinLatOrdCat`, and Autoequivalence Classification -/

/-- Standard linear chain lattice structure on `Fin n`. -/
abbrev finChainStr (n : Nat) : LatticeStr (Fin n) where
  le x y := x.val ≤ y.val
  sup x y := if x.val ≤ y.val then y else x
  inf x y := if x.val ≤ y.val then x else y
  le_refl x := Nat.le_refl x.val
  le_trans h₁ h₂ := Nat.le_trans h₁ h₂
  le_antisymm h₁ h₂ := Fin.ext (Nat.le_antisymm h₁ h₂)
  le_sup_left x _ := by
    split
    · assumption
    · exact Nat.le_refl x.val
  le_sup_right _ y := by
    split
    · exact Nat.le_refl y.val
    · rename_i h
      exact Nat.le_of_not_le h
  sup_le _ _ := by
    split <;> assumption
  inf_le_left x _ := by
    split
    · exact Nat.le_refl x.val
    · rename_i h
      exact Nat.le_of_not_le h
  inf_le_right _ y := by
    split
    · assumption
    · exact Nat.le_refl y.val
  le_inf _ _ := by
    split <;> assumption

/-- The `n`-element chain `C_n` as a `FinLattice` for `n > 0`. -/
abbrev finChain (n : Nat) (hn : 0 < n) : FinLattice where
  Carrier := Fin n
  card := n
  nonempty := ⟨⟨0, hn⟩⟩
  finEquiv := Bijection.refl (Fin n)
  str := finChainStr n

/-- Chains `C1`, `C2`, `C3`. -/
abbrev C1 : FinLattice := finChain 1 (by decide)
abbrev C2 : FinLattice := finChain 2 (by decide)
abbrev C3 : FinLattice := finChain 3 (by decide)

/-- Bundled (nonempty) small lattice, for the unrestricted global category `LatOrdCat`. -/
structure SmallLattice where
  Carrier : Type
  nonempty : Nonempty Carrier
  str : LatticeStr Carrier

abbrev dualSmallLattice (L : SmallLattice) : SmallLattice where
  Carrier := L.Carrier
  nonempty := L.nonempty
  str := dualLatticeStr L.str

/-- `LatOrdCat`: the unrestricted global category of small lattices with
order-preserving maps, matching the opening definition verbatim. -/
def LatOrdCat : Cat.{1, 0} where
  Obj := SmallLattice
  Hom L₁ L₂ := OrderHom L₁.str L₂.str
  id _ := { toFun := fun x => x, monotone := fun h => h }
  comp g f := {
    toFun := fun x => g.toFun (f.toFun x)
    monotone := fun h => g.monotone (f.monotone h)
  }
  id_comp _ := rfl
  comp_id _ := rfl
  assoc _ _ _ := rfl

/-- Covariant order-duality functor `(-)^op` on `LatOrdCat`. -/
abbrev globalDualityFunctor : Func LatOrdCat LatOrdCat where
  obj L := dualSmallLattice L
  map f := { toFun := f.toFun, monotone := fun h => f.monotone h }
  map_id _ := rfl
  map_comp _ _ := rfl

/-- Involutive covariant order-duality autoequivalence on `LatOrdCat`. -/
abbrev globalDualityAutoEquiv : AutoEquiv LatOrdCat where
  functor := globalDualityFunctor
  inverse := globalDualityFunctor
  unitIso := {
    hom := { app := fun _ => { toFun := fun x => x, monotone := fun h => h }, naturality := fun _ => rfl }
    inv := { app := fun _ => { toFun := fun x => x, monotone := fun h => h }, naturality := fun _ => rfl }
    inv_hom_id := fun _ => rfl
    hom_inv_id := fun _ => rfl
  }
  counitIso := {
    hom := { app := fun _ => { toFun := fun x => x, monotone := fun h => h }, naturality := fun _ => rfl }
    inv := { app := fun _ => { toFun := fun x => x, monotone := fun h => h }, naturality := fun _ => rfl }
    inv_hom_id := fun _ => rfl
    hom_inv_id := fun _ => rfl
  }

/-- Nontriviality of `globalDualityAutoEquiv` on `LatOrdCat`. -/
theorem globalDualityAutoEquiv_nontrivial : ¬ IsTrivialAutoEquiv globalDualityAutoEquiv := by
  rintro ⟨iso⟩
  let sC1 : SmallLattice := { Carrier := Fin 1, nonempty := ⟨0⟩, str := finChainStr 1 }
  let sC2 : SmallLattice := { Carrier := Fin 2, nonempty := ⟨0⟩, str := finChainStr 2 }
  let s : Fin 2 → Fin 2 := (iso.hom.app sC2).toFun
  let c₀ : LatOrdCat.Hom sC1 sC2 := { toFun := fun _ => 0, monotone := fun _ => Nat.le_refl 0 }
  let c₁ : LatOrdCat.Hom sC1 sC2 := { toFun := fun _ => 1, monotone := fun _ => Nat.le_refl 1 }
  have hnat₀ : (0 : Fin 2) = s 0 := congrArg (fun k => k.toFun (0 : Fin 1)) (iso.hom.naturality c₀)
  have hnat₁ : (1 : Fin 2) = s 1 := congrArg (fun k => k.toFun (0 : Fin 1)) (iso.hom.naturality c₁)
  have hmono : (s 1).val ≤ (s 0).val := (iso.hom.app sC2).monotone (by decide : (0 : Nat) ≤ 1)
  rw [← hnat₀, ← hnat₁] at hmono
  exact Nat.not_succ_le_zero 0 hmono

/-- `FinLatOrdCat`: the category of finite lattices with order-preserving maps,
matching the conjecture's opening definition directly. -/
def FinLatOrdCat : Cat.{1, 0} where
  Obj := FinLattice
  Hom L₁ L₂ := OrderHom L₁.str L₂.str
  id _ := { toFun := fun x => x, monotone := fun h => h }
  comp g f := {
    toFun := fun x => g.toFun (f.toFun x)
    monotone := fun h => g.monotone (f.monotone h)
  }
  id_comp _ := rfl
  comp_id _ := rfl
  assoc _ _ _ := rfl

/-- Isomorphisms in `FinLatOrdCat` coincide with lattice isomorphisms. -/
theorem finLatOrdIso_iff_latticeIso (L₁ L₂ : FinLattice) :
    Nonempty (CatIso FinLatOrdCat L₁ L₂) ↔ Nonempty (LatticeIso L₁.str L₂.str) := by
  constructor
  · rintro ⟨iso⟩
    have hleft : ∀ x, iso.inv.toFun (iso.hom.toFun x) = x := fun x =>
      congrArg (fun k => k.toFun x) iso.inv_hom_id
    have hright : ∀ y, iso.hom.toFun (iso.inv.toFun y) = y := fun y =>
      congrArg (fun k => k.toFun y) iso.hom_inv_id
    exact ⟨LatticeIso.ofOrderIso iso.hom.toFun iso.inv.toFun hleft hright
      iso.hom.monotone iso.inv.monotone⟩
  · rintro ⟨e⟩
    refine ⟨{
      hom := { toFun := e.toFun, monotone := fun h => (e.map_le_iff _ _).mp h }
      inv := { toFun := e.invFun, monotone := fun h => (e.symm.map_le_iff _ _).mp h }
      inv_hom_id := OrderHom.ext e.left_inv
      hom_inv_id := OrderHom.ext e.right_inv
    }⟩

/-- Covariant order-duality functor `(-)^op` on `FinLatOrdCat`. -/
def dualityFunctor : Func FinLatOrdCat FinLatOrdCat where
  obj L := dualFinLattice L
  map f := { toFun := f.toFun, monotone := fun h => f.monotone h }
  map_id _ := rfl
  map_comp _ _ := rfl

/-- Covariant order-duality autoequivalence `(-)^op` on `FinLatOrdCat`. -/
def dualityAutoEquiv : AutoEquiv FinLatOrdCat where
  functor := dualityFunctor
  inverse := dualityFunctor
  unitIso := {
    hom := { app := fun _ => { toFun := fun x => x, monotone := fun h => h }, naturality := fun _ => rfl }
    inv := { app := fun _ => { toFun := fun x => x, monotone := fun h => h }, naturality := fun _ => rfl }
    inv_hom_id := fun _ => rfl
    hom_inv_id := fun _ => rfl
  }
  counitIso := {
    hom := { app := fun _ => { toFun := fun x => x, monotone := fun h => h }, naturality := fun _ => rfl }
    inv := { app := fun _ => { toFun := fun x => x, monotone := fun h => h }, naturality := fun _ => rfl }
    inv_hom_id := fun _ => rfl
    hom_inv_id := fun _ => rfl
  }

/-- Constant point morphism `pt L x : C1 ⟶ L` in `FinLatOrdCat`. -/
def ptHom (L : FinLattice) (x : L.Carrier) : FinLatOrdCat.Hom C1 L where
  toFun _ := x
  monotone _ := L.str.le_refl x

/-- Any two morphisms into `C1` are equal (`C1` is terminal in `FinLatOrdCat`). -/
theorem hom_to_C1_eq {L : FinLattice} (f g : FinLatOrdCat.Hom L C1) : f = g := by
  apply OrderHom.ext
  intro x
  have hf := (f.toFun x).isLt
  have hg := (g.toFun x).isLt
  exact Fin.ext (by omega)

/-- There is no natural transformation `dualityFunctor ⇒ idFunc FinLatOrdCat`
(already obstructed by naturality on the constant maps `C1 ⟶ C2`). -/
theorem no_natTrans_duality_to_id :
    ¬ Nonempty (NatTrans dualityFunctor (idFunc FinLatOrdCat)) := by
  rintro ⟨α⟩
  let s : Fin 2 → Fin 2 := (α.app C2).toFun
  let c₀ : FinLatOrdCat.Hom C1 C2 := ptHom C2 (0 : Fin 2)
  let c₁ : FinLatOrdCat.Hom C1 C2 := ptHom C2 (1 : Fin 2)
  have hnat₀ : (0 : Fin 2) = s (0 : Fin 2) :=
    congrArg (fun k => k.toFun (0 : Fin 1)) (α.naturality c₀)
  have hnat₁ : (1 : Fin 2) = s (1 : Fin 2) :=
    congrArg (fun k => k.toFun (0 : Fin 1)) (α.naturality c₁)
  have hmono : (s (1 : Fin 2)).val ≤ (s (0 : Fin 2)).val :=
    (α.app C2).monotone (by decide : (0 : Nat) ≤ 1)
  rw [← hnat₀, ← hnat₁] at hmono
  exact Nat.not_succ_le_zero 0 hmono

/-- The duality autoequivalence `(-)^op` on `FinLatOrdCat` is nontrivial. -/
theorem dualityAutoEquiv_nontrivial : ¬ IsTrivialAutoEquiv dualityAutoEquiv := by
  rintro ⟨iso⟩
  exact no_natTrans_duality_to_id ⟨iso.hom⟩

/-- Helper: for any autoequivalence `E` of `FinLatOrdCat`, `(E.functor.obj C1).Carrier`
has at most one element. -/
theorem autoEquiv_obj_C1_subsingleton (E : AutoEquiv FinLatOrdCat)
    (a b : (E.functor.obj C1).Carrier) : a = b := by
  let FC1 := E.functor.obj C1
  let ca : FinLatOrdCat.Hom FC1 FC1 := { toFun := fun _ => a, monotone := fun _ => FC1.str.le_refl a }
  let cb : FinLatOrdCat.Hom FC1 FC1 := { toFun := fun _ => b, monotone := fun _ => FC1.str.le_refl b }
  have hpre : E.preimage ca = E.preimage cb := hom_to_C1_eq _ _
  have hmap : ca = cb := by
    rw [← E.map_preimage ca, ← E.map_preimage cb, hpre]
  exact congrArg (fun k => k.toFun a) hmap

/-- **Classification Theorem for `AutoEquiv FinLatOrdCat`**: Every covariant
self-equivalence of `FinLatOrdCat` is naturally isomorphic either to the identity
functor `idFunc FinLatOrdCat` or to the duality functor `dualityFunctor`. -/
theorem finLatOrdCat_autoEquiv_classification (E : AutoEquiv FinLatOrdCat) :
    IsTrivialAutoEquiv E ∨ Nonempty (NatIso E.functor dualityFunctor) := by
  let F := E.functor
  let star : (F.obj C1).Carrier := (F.obj C1).defaultElem
  let φ : (L : FinLattice) → L.Carrier → (F.obj L).Carrier :=
    fun L x => (F.map (ptHom L x)).toFun star
  let constFC1 : (L : FinLattice) → (F.obj L).Carrier → FinLatOrdCat.Hom (F.obj C1) (F.obj L) :=
    fun L y => { toFun := fun _ => y, monotone := fun _ => (F.obj L).str.le_refl y }
  let ψ : (L : FinLattice) → (F.obj L).Carrier → L.Carrier :=
    fun L y => (E.preimage (constFC1 L y)).toFun (0 : Fin 1)
  have hleft : ∀ (L : FinLattice) (x : L.Carrier), ψ L (φ L x) = x := by
    intro L x
    have hc : constFC1 L (φ L x) = F.map (ptHom L x) := by
      apply OrderHom.ext
      intro w
      have hw : w = star := autoEquiv_obj_C1_subsingleton E w star
      dsimp [constFC1, φ]
      rw [hw]
    have hpre : E.preimage (constFC1 L (φ L x)) = ptHom L x := by
      apply E.functor_faithful
      rw [E.map_preimage, hc]
    exact congrArg (fun k => k.toFun (0 : Fin 1)) hpre
  have hright : ∀ (L : FinLattice) (y : (F.obj L).Carrier), φ L (ψ L y) = y := by
    intro L y
    have hpt : ptHom L (ψ L y) = E.preimage (constFC1 L y) := by
      apply OrderHom.ext
      intro z
      have hz : z = (0 : Fin 1) := Subsingleton.elim z (0 : Fin 1)
      dsimp [ptHom, ψ]
      rw [hz]
    have hmap : F.map (ptHom L (ψ L y)) = constFC1 L y := by
      rw [hpt, E.map_preimage]
    exact congrArg (fun k => k.toFun star) hmap
  have hnat : ∀ {L₁ L₂ : FinLattice} (f : FinLatOrdCat.Hom L₁ L₂) (x : L₁.Carrier),
      (F.map f).toFun (φ L₁ x) = φ L₂ (f.toFun x) := by
    intro L₁ L₂ f x
    have hcomp : FinLatOrdCat.comp f (ptHom L₁ x) = ptHom L₂ (f.toFun x) := rfl
    have hf : (F.map (FinLatOrdCat.comp f (ptHom L₁ x))).toFun star =
        (F.map (ptHom L₂ (f.toFun x))).toFun star :=
      congrArg (fun k => (F.map k).toFun star) hcomp
    rw [F.map_comp] at hf
    exact hf
  -- Analyze the image of the 2-element chain `C2`
  let f0 : Fin 2 := 0
  let f1 : Fin 2 := 1
  let u : (F.obj C2).Carrier := φ C2 f0
  let v : (F.obj C2).Carrier := φ C2 f1
  have huv_ne : u ≠ v := by
    intro heq
    have h01 : ψ C2 u = ψ C2 v := congrArg (ψ C2) heq
    rw [hleft C2 f0, hleft C2 f1] at h01
    exact absurd h01 (by decide)
  have hC2_dichot : ∀ w : (F.obj C2).Carrier, w = u ∨ w = v := by
    intro w
    have hw := hright C2 w
    have hfin : ψ C2 w = f0 ∨ ψ C2 w = f1 := by
      rcases ψ C2 w with ⟨val, isLt⟩
      cases val with
      | zero => exact Or.inl rfl
      | succ k =>
        cases k with
        | zero => exact Or.inr rfl
        | succ _ => omega
    rcases hfin with h0 | h1
    · exact Or.inl (by rw [← hw, h0])
    · exact Or.inr (by rw [← hw, h1])
  rcases hC2_dichot ((F.obj C2).str.sup u v) with hsup_u | hsup_v
  · -- Case 2 (`u ⊔ v = u`, so `v ≤ u` in `F.obj C2`): `F ≅ dualityFunctor`
    right
    have hvu : (F.obj C2).str.le v u := by
      have h := (F.obj C2).str.le_sup_right u v
      rw [hsup_u] at h
      exact h
    have not_uv : ¬ (F.obj C2).str.le u v := fun huv =>
      huv_ne ((F.obj C2).str.le_antisymm huv hvu)
    have hphi_anti : ∀ (L : FinLattice) {x y : L.Carrier},
        (dualFinLattice L).str.le x y → (F.obj L).str.le (φ L x) (φ L y) := by
      intro L x y hyx
      let h : FinLatOrdCat.Hom C2 L := {
        toFun := fun i => if i = f0 then y else x
        monotone := by
          intro i j hij
          rcases i with ⟨iv, ilt⟩
          rcases j with ⟨jv, jlt⟩
          by_cases hi0 : iv = 0 <;> by_cases hj0 : jv = 0
          · subst hi0; subst hj0; exact L.str.le_refl _
          · subst hi0
            have hjne : (⟨jv, jlt⟩ : Fin 2) ≠ f0 := fun he => hj0 (congrArg Fin.val he)
            simp [f0, hjne]
            exact hyx
          · exfalso
            subst hj0
            have hij' : iv ≤ 0 := hij
            omega
          · have hine : (⟨iv, ilt⟩ : Fin 2) ≠ f0 := fun he => hi0 (congrArg Fin.val he)
            have hjne : (⟨jv, jlt⟩ : Fin 2) ≠ f0 := fun he => hj0 (congrArg Fin.val he)
            simp [hine, hjne]
            exact L.str.le_refl _
      }
      have hu := hnat h f0
      have hv := hnat h f1
      have hmono := (F.map h).monotone hvu
      dsimp [u, v, h, f0, f1] at hu hv
      rw [hu, hv] at hmono
      exact hmono
    have hpsi_anti : ∀ (L : FinLattice) {a b : (F.obj L).Carrier},
        (F.obj L).str.le a b → (dualFinLattice L).str.le (ψ L a) (ψ L b) := by
      intro L a b hab
      let h' : FinLatOrdCat.Hom (F.obj C2) (F.obj L) := {
        toFun := fun w => if ψ C2 w = f0 then b else a
        monotone := by
          intro w₁ w₂ hw
          rcases hC2_dichot w₁ with rfl | rfl <;> rcases hC2_dichot w₂ with rfl | rfl
          · exact (F.obj L).str.le_refl _
          · exfalso; exact not_uv hw
          · have hu0 : ψ C2 u = f0 := hleft C2 f0
            have hv1 : ψ C2 v = f1 := hleft C2 f1
            simp [hu0, hv1, f0, f1]
            exact hab
          · exact (F.obj L).str.le_refl _
      }
      let h : FinLatOrdCat.Hom C2 L := E.preimage h'
      have h01 : L.str.le (h.toFun f0) (h.toFun f1) := h.monotone (by decide : (0 : Nat) ≤ 1)
      have hmap : F.map h = h' := E.map_preimage h'
      have eq0 : φ L (h.toFun f0) = b := by
        rw [← hnat h f0, hmap]
        have hu0 : ψ C2 u = f0 := hleft C2 f0
        change (if ψ C2 u = f0 then b else a) = b
        simp [hu0]
      have eq1 : φ L (h.toFun f1) = a := by
        rw [← hnat h f1, hmap]
        have hv1 : ψ C2 v = f1 := hleft C2 f1
        change (if ψ C2 v = f0 then b else a) = a
        simp [hv1, f0, f1]
      have hb : h.toFun f0 = ψ L b := by rw [← eq0, hleft]
      have ha : h.toFun f1 = ψ L a := by rw [← eq1, hleft]
      rw [hb, ha] at h01
      exact h01
    refine ⟨{
      hom := {
        app := fun L => { toFun := ψ L, monotone := fun h => hpsi_anti L h }
        naturality := fun {L₁ L₂} f => by
          apply OrderHom.ext
          intro y
          have h := hnat f (ψ L₁ y)
          rw [hright L₁ y] at h
          have h' := congrArg (ψ L₂) h
          rw [hleft L₂] at h'
          exact h'.symm
      }
      inv := {
        app := fun L => { toFun := φ L, monotone := fun h => hphi_anti L h }
        naturality := fun {L₁ L₂} f => OrderHom.ext (fun x => hnat f x)
      }
      inv_hom_id := fun L => OrderHom.ext (hright L)
      hom_inv_id := fun L => OrderHom.ext (hleft L)
    }⟩
  · -- Case 1 (`u ⊔ v = v`, so `u ≤ v` in `F.obj C2`): `F ≅ idFunc FinLatOrdCat`
    left
    have huv : (F.obj C2).str.le u v := by
      have h := (F.obj C2).str.le_sup_left u v
      rw [hsup_v] at h
      exact h
    have not_vu : ¬ (F.obj C2).str.le v u := fun hvu =>
      huv_ne ((F.obj C2).str.le_antisymm huv hvu)
    have hphi_mono : ∀ (L : FinLattice) {x y : L.Carrier},
        L.str.le x y → (F.obj L).str.le (φ L x) (φ L y) := by
      intro L x y hxy
      let h : FinLatOrdCat.Hom C2 L := {
        toFun := fun i => if i = f0 then x else y
        monotone := by
          intro i j hij
          rcases i with ⟨iv, ilt⟩
          rcases j with ⟨jv, jlt⟩
          by_cases hi0 : iv = 0 <;> by_cases hj0 : jv = 0
          · subst hi0; subst hj0; exact L.str.le_refl _
          · subst hi0
            have hjne : (⟨jv, jlt⟩ : Fin 2) ≠ f0 := fun he => hj0 (congrArg Fin.val he)
            simp [f0, hjne]
            exact hxy
          · exfalso
            subst hj0
            have hij' : iv ≤ 0 := hij
            omega
          · have hine : (⟨iv, ilt⟩ : Fin 2) ≠ f0 := fun he => hi0 (congrArg Fin.val he)
            have hjne : (⟨jv, jlt⟩ : Fin 2) ≠ f0 := fun he => hj0 (congrArg Fin.val he)
            simp [hine, hjne]
            exact L.str.le_refl _
      }
      have hu := hnat h f0
      have hv := hnat h f1
      have hmono := (F.map h).monotone huv
      dsimp [u, v, h, f0, f1] at hu hv
      rw [hu, hv] at hmono
      exact hmono
    have hpsi_mono : ∀ (L : FinLattice) {a b : (F.obj L).Carrier},
        (F.obj L).str.le a b → L.str.le (ψ L a) (ψ L b) := by
      intro L a b hab
      let h' : FinLatOrdCat.Hom (F.obj C2) (F.obj L) := {
        toFun := fun w => if ψ C2 w = f0 then a else b
        monotone := by
          intro w₁ w₂ hw
          rcases hC2_dichot w₁ with rfl | rfl <;> rcases hC2_dichot w₂ with rfl | rfl
          · exact (F.obj L).str.le_refl _
          · have hu0 : ψ C2 u = f0 := hleft C2 f0
            have hv1 : ψ C2 v = f1 := hleft C2 f1
            simp [hu0, hv1, f0, f1]
            exact hab
          · exfalso; exact not_vu hw
          · exact (F.obj L).str.le_refl _
      }
      let h : FinLatOrdCat.Hom C2 L := E.preimage h'
      have h01 : L.str.le (h.toFun f0) (h.toFun f1) := h.monotone (by decide : (0 : Nat) ≤ 1)
      have hmap : F.map h = h' := E.map_preimage h'
      have eq0 : φ L (h.toFun f0) = a := by
        rw [← hnat h f0, hmap]
        have hu0 : ψ C2 u = f0 := hleft C2 f0
        change (if ψ C2 u = f0 then a else b) = a
        simp [hu0]
      have eq1 : φ L (h.toFun f1) = b := by
        rw [← hnat h f1, hmap]
        have hv1 : ψ C2 v = f1 := hleft C2 f1
        change (if ψ C2 v = f0 then a else b) = b
        simp [hv1, f0, f1]
      have ha : h.toFun f0 = ψ L a := by rw [← eq0, hleft]
      have hb : h.toFun f1 = ψ L b := by rw [← eq1, hleft]
      rw [ha, hb] at h01
      exact h01
    refine ⟨{
      hom := {
        app := fun L => { toFun := ψ L, monotone := fun h => hpsi_mono L h }
        naturality := fun {L₁ L₂} f => by
          apply OrderHom.ext
          intro y
          have h := hnat f (ψ L₁ y)
          rw [hright L₁ y] at h
          have h' := congrArg (ψ L₂) h
          rw [hleft L₂] at h'
          exact h'.symm
      }
      inv := {
        app := fun L => { toFun := φ L, monotone := fun h => hphi_mono L h }
        naturality := fun {L₁ L₂} f => OrderHom.ext (fun x => hnat f x)
      }
      inv_hom_id := fun L => OrderHom.ext (hright L)
      hom_inv_id := fun L => OrderHom.ext (hleft L)
    }⟩

/-- Statement of Clause 2a on `FinLatOrdCat`: `dualityAutoEquiv` is nontrivial and
every nontrivial self-equivalence of `FinLatOrdCat` is naturally isomorphic to it. -/
def Clause2a_DualityUniqueNontrivialAutoEquiv : Prop :=
  ¬ IsTrivialAutoEquiv dualityAutoEquiv ∧
    ∀ E : AutoEquiv FinLatOrdCat,
      ¬ IsTrivialAutoEquiv E → Nonempty (NatIso E.functor dualityFunctor)

theorem clause2a_global_holds : Clause2a_DualityUniqueNontrivialAutoEquiv :=
  ⟨dualityAutoEquiv_nontrivial, fun E hE =>
    match finLatOrdCat_autoEquiv_classification E with
    | Or.inl htriv => absurd htriv hE
    | Or.inr hdual => hdual⟩

/-! ## Section 5: Concrete Finite Lattices (`B2`, `N5`, `OneSumB2`) and Size `≤ 4` Classification -/

/-- Elements of the 4-element diamond (Boolean square) lattice `B2`. -/
inductive B2Elem where
  | bot | a | b | top
  deriving DecidableEq

def b2LeBool : B2Elem → B2Elem → Bool
  | .bot, _ => true
  | _, .top => true
  | .a, .a => true
  | .b, .b => true
  | _, _ => false

def b2Sup : B2Elem → B2Elem → B2Elem
  | .bot, y => y
  | x, .bot => x
  | .top, _ => .top
  | _, .top => .top
  | .a, .a => .a
  | .b, .b => .b
  | _, _ => .top

def b2Inf : B2Elem → B2Elem → B2Elem
  | .top, y => y
  | x, .top => x
  | .bot, _ => .bot
  | _, .bot => .bot
  | .a, .a => .a
  | .b, .b => .b
  | _, _ => .bot

abbrev b2Str : LatticeStr B2Elem where
  le x y := b2LeBool x y = true
  sup := b2Sup
  inf := b2Inf
  le_refl x := by cases x <;> decide
  le_trans {x y z} := by cases x <;> cases y <;> cases z <;> decide
  le_antisymm {x y} := by cases x <;> cases y <;> decide
  le_sup_left x y := by cases x <;> cases y <;> decide
  le_sup_right x y := by cases x <;> cases y <;> decide
  sup_le {x y z} := by cases x <;> cases y <;> cases z <;> decide
  inf_le_left x y := by cases x <;> cases y <;> decide
  inf_le_right x y := by cases x <;> cases y <;> decide
  le_inf {x y z} := by cases x <;> cases y <;> cases z <;> decide

abbrev B2 : FinLattice where
  Carrier := B2Elem
  card := 4
  nonempty := ⟨.bot⟩
  finEquiv := {
    toFun := fun | .bot => ⟨0, by decide⟩ | .a => ⟨1, by decide⟩
                 | .b => ⟨2, by decide⟩ | .top => ⟨3, by decide⟩
    invFun := fun
      | ⟨0, _⟩ => .bot
      | ⟨1, _⟩ => .a
      | ⟨2, _⟩ => .b
      | ⟨_ + 3, _⟩ => .top
    left_inv := fun x => by cases x <;> rfl
    right_inv := fun ⟨k, hk⟩ => by
      cases k with
      | zero => rfl
      | succ k₁ =>
        cases k₁ with
        | zero => rfl
        | succ k₂ =>
          cases k₂ with
          | zero => rfl
          | succ k₃ =>
            have hk3 : k₃ = 0 := by omega
            subst hk3
            rfl
  }
  str := b2Str

/-- Elements of the 5-element pentagon lattice `N5` (`bot < a < b < top`, `bot < c < top`). -/
inductive N5Elem where
  | bot | a | b | c | top
  deriving DecidableEq

def n5LeBool : N5Elem → N5Elem → Bool
  | .bot, _ => true
  | _, .top => true
  | .a, .a => true
  | .a, .b => true
  | .b, .b => true
  | .c, .c => true
  | _, _ => false

def n5Sup : N5Elem → N5Elem → N5Elem
  | .bot, y => y
  | x, .bot => x
  | .top, _ => .top
  | _, .top => .top
  | .a, .a => .a
  | .a, .b => .b
  | .b, .a => .b
  | .b, .b => .b
  | .c, .c => .c
  | _, _ => .top

def n5Inf : N5Elem → N5Elem → N5Elem
  | .top, y => y
  | x, .top => x
  | .bot, _ => .bot
  | _, .bot => .bot
  | .a, .a => .a
  | .a, .b => .a
  | .b, .a => .a
  | .b, .b => .b
  | .c, .c => .c
  | _, _ => .bot

abbrev n5Str : LatticeStr N5Elem where
  le x y := n5LeBool x y = true
  sup := n5Sup
  inf := n5Inf
  le_refl x := by cases x <;> decide
  le_trans {x y z} := by cases x <;> cases y <;> cases z <;> decide
  le_antisymm {x y} := by cases x <;> cases y <;> decide
  le_sup_left x y := by cases x <;> cases y <;> decide
  le_sup_right x y := by cases x <;> cases y <;> decide
  sup_le {x y z} := by cases x <;> cases y <;> cases z <;> decide
  inf_le_left x y := by cases x <;> cases y <;> decide
  inf_le_right x y := by cases x <;> cases y <;> decide
  le_inf {x y z} := by cases x <;> cases y <;> cases z <;> decide

/-- The pentagon lattice `N5` as a `FinLattice` (`card = 5`, height `3`). -/
abbrev N5 : FinLattice where
  Carrier := N5Elem
  card := 5
  nonempty := ⟨.bot⟩
  finEquiv := {
    toFun := fun | .bot => ⟨0, by decide⟩ | .a => ⟨1, by decide⟩ | .b => ⟨2, by decide⟩
                 | .c => ⟨3, by decide⟩ | .top => ⟨4, by decide⟩
    invFun := fun
      | ⟨0, _⟩ => .bot
      | ⟨1, _⟩ => .a
      | ⟨2, _⟩ => .b
      | ⟨3, _⟩ => .c
      | ⟨_ + 4, _⟩ => .top
    left_inv := fun x => by cases x <;> rfl
    right_inv := fun ⟨k, hk⟩ => by
      cases k with
      | zero => rfl
      | succ k₁ =>
        cases k₁ with
        | zero => rfl
        | succ k₂ =>
          cases k₂ with
          | zero => rfl
          | succ k₃ =>
            cases k₃ with
            | zero => rfl
            | succ k₄ =>
              have hk4 : k₄ = 0 := by omega
              subst hk4
              rfl
  }
  str := n5Str

/-- A lattice is a pentagon lattice if it is isomorphic to `N5`. -/
def IsPentagonLattice {α : Type u} (L : LatticeStr α) : Prop :=
  Nonempty (LatticeIso L N5.str)

/-- `N5` is non-modular (`a ≤ b`, yet `a ⊔ (c ⊓ b) = a ≠ b = (a ⊔ c) ⊓ b`). -/
theorem N5_not_modular : ¬ IsModular N5.str := by
  intro hmod
  have hab : N5.str.le .a .b := rfl
  have heq := hmod .a .c .b hab
  exact absurd heq (by decide)

/-- **Crucial Counterexample Fact 1**: The pentagon lattice `N5` IS SELF-DUAL!
Reversing the order swaps `bot ↔ top`, `a ↔ b`, and fixes `c`. -/
def n5DualMap : N5Elem → N5Elem
  | .bot => .top
  | .a => .b
  | .b => .a
  | .c => .c
  | .top => .bot

def n5SelfDualIso : LatticeIso N5.str (dualLatticeStr N5.str) :=
  LatticeIso.ofOrderIso n5DualMap n5DualMap
    (fun x => by cases x <;> rfl)
    (fun y => by cases y <;> rfl)
    (fun {x y} => by cases x <;> cases y <;> decide)
    (fun {u v} => by cases u <;> cases v <;> decide)

theorem N5_is_self_dual : IsSelfDual N5.str := ⟨n5SelfDualIso⟩

/-- Every pentagon lattice is self-dual (`L ≅ N5 → L ≅ L^op`). -/
theorem pentagon_always_self_dual {α : Type u} {L : LatticeStr α}
    (hp : IsPentagonLattice L) : IsSelfDual L := by
  rcases hp with ⟨e⟩
  exact IsSelfDual.of_iso e N5_is_self_dual

/-- **Crucial Counterexample Fact 2**: Viewed as a thin poset category `C(N5)`,
the pentagon lattice is rigid — every covariant self-equivalence equals `idFunc`. -/
theorem N5_poset_cat_rigid (E : AutoEquiv (LatticePosetCat N5.str)) :
    E.functor = idFunc (LatticePosetCat N5.str) := by
  have hunit : idFunc (LatticePosetCat N5.str) = compFunc E.inverse E.functor :=
    latticePosetCat_natIso_eq E.unitIso
  have hcounit : compFunc E.functor E.inverse = idFunc (LatticePosetCat N5.str) :=
    latticePosetCat_natIso_eq E.counitIso
  let f := E.functor.obj
  let g := E.inverse.obj
  have hleft : ∀ x : N5Elem, g (f x) = x := fun x =>
    congrArg (fun H => H.obj x) hunit.symm
  have hright : ∀ y : N5Elem, f (g y) = y := fun y =>
    congrArg (fun H => H.obj y) hcounit
  have hf_mono : ∀ {x y : N5Elem}, N5.str.le x y → N5.str.le (f x) (f y) :=
    fun hxy => (E.functor.map ⟨hxy⟩).down
  have hinj : ∀ {x y : N5Elem}, f x = f y → x = y := by
    intro x y h
    rw [← hleft x, ← hleft y, h]
  have hf_bot : f .bot = .bot := by
    have hle : N5.str.le (f .bot) .bot := by
      have hgb : N5.str.le .bot (g .bot) := by cases g .bot <;> decide
      have hm := hf_mono hgb
      rw [hright .bot] at hm
      exact hm
    exact N5.str.le_antisymm hle (by cases f .bot <;> decide)
  have hf_top : f .top = .top := by
    have hge : N5.str.le .top (f .top) := by
      have hgt : N5.str.le (g .top) .top := by cases g .top <;> decide
      have hm := hf_mono hgt
      rw [hright .top] at hm
      exact hm
    exact N5.str.le_antisymm (by cases f .top <;> decide) hge
  have hab_le : N5.str.le (f .a) (f .b) := hf_mono (by decide : N5.str.le .a .b)
  have hab_ne : f .a ≠ f .b := fun h => absurd (hinj h) (by decide)
  have ha_nb : f .a ≠ .bot := fun h => absurd (hinj (h.trans hf_bot.symm)) (by decide)
  have ha_nt : f .a ≠ .top := fun h => absurd (hinj (h.trans hf_top.symm)) (by decide)
  have hb_nb : f .b ≠ .bot := fun h => absurd (hinj (h.trans hf_bot.symm)) (by decide)
  have hb_nt : f .b ≠ .top := fun h => absurd (hinj (h.trans hf_top.symm)) (by decide)
  have hfab : f .a = .a ∧ f .b = .b := by
    cases hfa : f .a <;> cases hfb : f .b <;>
      rw [hfa] at ha_nb ha_nt hab_le hab_ne <;>
      rw [hfb] at hb_nb hb_nt hab_le hab_ne
    all_goals first | exact ⟨rfl, rfl⟩ | contradiction
  have hfc : f .c = .c := by
    have hc_nb : f .c ≠ .bot := fun h => absurd (hinj (h.trans hf_bot.symm)) (by decide)
    have hc_nt : f .c ≠ .top := fun h => absurd (hinj (h.trans hf_top.symm)) (by decide)
    have hc_na : f .c ≠ .a := fun h => absurd (hinj (h.trans hfab.1.symm)) (by decide)
    have hc_nb' : f .c ≠ .b := fun h => absurd (hinj (h.trans hfab.2.symm)) (by decide)
    cases h : f .c <;> rw [h] at hc_nb hc_nt hc_na hc_nb'
    all_goals first | rfl | contradiction
  have hobj : E.functor.obj = (idFunc (LatticePosetCat N5.str)).obj := by
    funext x
    cases x
    · exact hf_bot
    · exact hfab.1
    · exact hfab.2
    · exact hfc
    · exact hf_top
  cases hF : E.functor with
  | mk fObj fMap fId fComp =>
    rw [hF] at hobj
    dsimp [idFunc] at hobj
    subst hobj
    have hmap : @fMap = @(idFunc (LatticePosetCat N5.str)).map := by
      funext X Y k
      cases fMap k with
      | up _ =>
        cases k with
        | up _ => rfl
    subst hmap
    rfl

/-- Elements of the 5-element distributive lattice `OneSumB2` (`1 ⊕ B_2`:
`bot < u < x, y < top`, `x ∥ y`). -/
inductive OneSumB2Elem where
  | bot | u | x | y | top
  deriving DecidableEq

def oneSumB2LeBool : OneSumB2Elem → OneSumB2Elem → Bool
  | .bot, _ => true
  | _, .top => true
  | .u, .u => true
  | .u, .x => true
  | .u, .y => true
  | .x, .x => true
  | .y, .y => true
  | _, _ => false

def oneSumB2Sup : OneSumB2Elem → OneSumB2Elem → OneSumB2Elem
  | .bot, b => b
  | a, .bot => a
  | .top, _ => .top
  | _, .top => .top
  | .u, b => b
  | a, .u => a
  | .x, .x => .x
  | .y, .y => .y
  | _, _ => .top

def oneSumB2Inf : OneSumB2Elem → OneSumB2Elem → OneSumB2Elem
  | .top, b => b
  | a, .top => a
  | .bot, _ => .bot
  | _, .bot => .bot
  | .x, .x => .x
  | .y, .y => .y
  | _, _ => .u

abbrev oneSumB2Str : LatticeStr OneSumB2Elem where
  le a b := oneSumB2LeBool a b = true
  sup := oneSumB2Sup
  inf := oneSumB2Inf
  le_refl a := by cases a <;> decide
  le_trans {a b c} := by cases a <;> cases b <;> cases c <;> decide
  le_antisymm {a b} := by cases a <;> cases b <;> decide
  le_sup_left a b := by cases a <;> cases b <;> decide
  le_sup_right a b := by cases a <;> cases b <;> decide
  sup_le {a b c} := by cases a <;> cases b <;> cases c <;> decide
  inf_le_left a b := by cases a <;> cases b <;> decide
  inf_le_right a b := by cases a <;> cases b <;> decide
  le_inf {a b c} := by cases a <;> cases b <;> cases c <;> decide

/-- `OneSumB2` (`1 ⊕ B_2`) as a `FinLattice` (`card = 5`, height `3`). -/
abbrev OneSumB2 : FinLattice where
  Carrier := OneSumB2Elem
  card := 5
  nonempty := ⟨.bot⟩
  finEquiv := {
    toFun := fun | .bot => ⟨0, by decide⟩ | .u => ⟨1, by decide⟩ | .x => ⟨2, by decide⟩
                 | .y => ⟨3, by decide⟩ | .top => ⟨4, by decide⟩
    invFun := fun
      | ⟨0, _⟩ => .bot
      | ⟨1, _⟩ => .u
      | ⟨2, _⟩ => .x
      | ⟨3, _⟩ => .y
      | ⟨_ + 4, _⟩ => .top
    left_inv := fun a => by cases a <;> rfl
    right_inv := fun ⟨k, hk⟩ => by
      cases k with
      | zero => rfl
      | succ k₁ =>
        cases k₁ with
        | zero => rfl
        | succ k₂ =>
          cases k₂ with
          | zero => rfl
          | succ k₃ =>
            cases k₃ with
            | zero => rfl
            | succ k₄ =>
              have hk4 : k₄ = 0 := by omega
              subst hk4
              rfl
  }
  str := oneSumB2Str

theorem OneSumB2_distributive : IsDistributive OneSumB2.str := by
  intro a b c
  cases a <;> cases b <;> cases c <;> decide

theorem OneSumB2_modular : IsModular OneSumB2.str := by
  intro a b c
  cases a <;> cases b <;> cases c <;> decide

theorem OneSumB2_not_pentagon : ¬ IsPentagonLattice OneSumB2.str := by
  rintro ⟨e⟩
  exact N5_not_modular (IsModular.of_iso e.symm OneSumB2_modular)

/-- **True Minimal Non-Self-Dual Witness**: `OneSumB2` (`1 ⊕ B_2`, `card = 5`,
height `3`) is NOT self-dual (`u` is above only `bot` and below all non-`bot`
elements, whereas `top` has two distinct coatoms `x, y` with `x ⊔ y = top`). -/
theorem OneSumB2_not_self_dual : ¬ IsSelfDual OneSumB2.str := by
  rintro ⟨e⟩
  have hanti : ∀ a b : OneSumB2Elem, OneSumB2.str.le a b ↔ OneSumB2.str.le (e.toFun b) (e.toFun a) :=
    fun a b => e.map_le_iff a b
  have hf_bot : e.toFun .bot = .top := by
    have htop : OneSumB2.str.le .top (e.toFun .bot) := by
      have hb : OneSumB2.str.le .bot (e.invFun .top) := by cases e.invFun .top <;> decide
      have hm := (hanti .bot (e.invFun .top)).mp hb
      rw [e.right_inv .top] at hm
      exact hm
    exact OneSumB2.str.le_antisymm (by cases e.toFun .bot <;> decide) htop
  have hfu_ne_top : e.toFun .u ≠ .top := by
    intro h
    have heq : e.invFun (e.toFun .u) = e.invFun (e.toFun .bot) := by rw [h, hf_bot]
    rw [e.left_inv, e.left_inv] at heq
    exact absurd heq (by decide)
  have hgx_ne_bot : e.invFun .x ≠ .bot := by
    intro h
    have heq : e.toFun (e.invFun .x) = e.toFun .bot := congrArg e.toFun h
    rw [e.right_inv, hf_bot] at heq
    exact absurd heq (by decide)
  have hgy_ne_bot : e.invFun .y ≠ .bot := by
    intro h
    have heq : e.toFun (e.invFun .y) = e.toFun .bot := congrArg e.toFun h
    rw [e.right_inv, hf_bot] at heq
    exact absurd heq (by decide)
  have hu_le_gx : OneSumB2.str.le .u (e.invFun .x) := by
    cases h : e.invFun .x <;> first | decide | exact absurd h hgx_ne_bot
  have hu_le_gy : OneSumB2.str.le .u (e.invFun .y) := by
    cases h : e.invFun .y <;> first | decide | exact absurd h hgy_ne_bot
  have hx_le_fu : OneSumB2.str.le .x (e.toFun .u) := by
    have hm := (hanti .u (e.invFun .x)).mp hu_le_gx
    rw [e.right_inv .x] at hm
    exact hm
  have hy_le_fu : OneSumB2.str.le .y (e.toFun .u) := by
    have hm := (hanti .u (e.invFun .y)).mp hu_le_gy
    rw [e.right_inv .y] at hm
    exact hm
  have htop_le_fu : OneSumB2.str.le .top (e.toFun .u) :=
    OneSumB2.str.sup_le hx_le_fu hy_le_fu
  have hfu_eq_top : e.toFun .u = .top :=
    OneSumB2.str.le_antisymm (by cases e.toFun .u <;> decide) htop_le_fu
  exact hfu_ne_top hfu_eq_top

/-! ### Universal Classification of Finite Lattices of Cardinality `≤ 4` -/

/-- On `Fin 3`, pick the unique element distinct from `b` and `t` when `b ≠ t`. -/
def midOf3 (b t : Fin 3) : Fin 3 :=
  if (⟨0, by decide⟩ : Fin 3) ≠ b ∧ (⟨0, by decide⟩ : Fin 3) ≠ t then ⟨0, by decide⟩
  else if (⟨1, by decide⟩ : Fin 3) ≠ b ∧ (⟨1, by decide⟩ : Fin 3) ≠ t then ⟨1, by decide⟩
  else ⟨2, by decide⟩

theorem midOf3_spec :
    ∀ b t : Fin 3, b ≠ t →
      midOf3 b t ≠ b ∧ midOf3 b t ≠ t ∧
        ∀ x : Fin 3, x = b ∨ x = midOf3 b t ∨ x = t := by
  decide

/-- Every lattice structure on `Fin 3` is isomorphic to the 3-element chain `C3.str`. -/
def fin3LatticeIsoC3 (L : LatticeStr (Fin 3)) : LatticeIso C3.str L := by
  let e0 : Fin 3 := ⟨0, by decide⟩
  let e1 : Fin 3 := ⟨1, by decide⟩
  let e2 : Fin 3 := ⟨2, by decide⟩
  let b : Fin 3 := L.inf (L.inf e0 e1) e2
  let t : Fin 3 := L.sup (L.sup e0 e1) e2
  have hb_le : ∀ x : Fin 3, L.le b x := by
    intro x
    have h01 : L.le b (L.inf e0 e1) := L.inf_le_left _ _
    have h2 : L.le b e2 := L.inf_le_right _ _
    have h0 : L.le b e0 := L.le_trans h01 (L.inf_le_left _ _)
    have h1 : L.le b e1 := L.le_trans h01 (L.inf_le_right _ _)
    rcases x with ⟨k, hk⟩
    cases k with
    | zero => exact h0
    | succ k₁ =>
      cases k₁ with
      | zero => exact h1
      | succ k₂ =>
        have hk2 : k₂ = 0 := by omega
        subst hk2
        exact h2
  have hle_t : ∀ x : Fin 3, L.le x t := by
    intro x
    have h01 : L.le (L.sup e0 e1) t := L.le_sup_left _ _
    have h2 : L.le e2 t := L.le_sup_right _ _
    have h0 : L.le e0 t := L.le_trans (L.le_sup_left _ _) h01
    have h1 : L.le e1 t := L.le_trans (L.le_sup_right _ _) h01
    rcases x with ⟨k, hk⟩
    cases k with
    | zero => exact h0
    | succ k₁ =>
      cases k₁ with
      | zero => exact h1
      | succ k₂ =>
        have hk2 : k₂ = 0 := by omega
        subst hk2
        exact h2
  have hbt : b ≠ t := by
    intro heq
    have h0b : e0 = b := L.le_antisymm (heq ▸ hle_t e0) (hb_le e0)
    have h1b : e1 = b := L.le_antisymm (heq ▸ hle_t e1) (hb_le e1)
    exact absurd (h0b.trans h1b.symm) (by decide)
  let m : Fin 3 := midOf3 b t
  have hm := midOf3_spec b t hbt
  let f : Fin 3 → Fin 3 := fun
    | ⟨0, _⟩ => b
    | ⟨1, _⟩ => m
    | ⟨_ + 2, _⟩ => t
  let g : Fin 3 → Fin 3 := fun x =>
    if x = b then (0 : Fin 3)
    else if x = m then (1 : Fin 3)
    else (2 : Fin 3)
  have hmb : m ≠ b := hm.1
  have gb : g b = (0 : Fin 3) := by dsimp [g]; simp
  have gm : g m = (1 : Fin 3) := by dsimp [g]; simp [hmb]
  have gt_eq : g t = (2 : Fin 3) := by
    dsimp [g]
    have htb : t ≠ b := hbt.symm
    have htm : t ≠ m := hm.2.1.symm
    simp [htb, htm]
  refine LatticeIso.ofOrderIso f g ?_ ?_ ?_ ?_
  · intro i
    rcases i with ⟨k, hk⟩
    cases k with
    | zero => exact gb
    | succ k₁ =>
      cases k₁ with
      | zero => exact gm
      | succ k₂ =>
        have hk2 : k₂ = 0 := by omega
        subst hk2
        exact gt_eq
  · intro x
    rcases hm.2.2 x with rfl | rfl | rfl
    · rw [gb]
    · rw [gm]
    · rw [gt_eq]
  · intro i j hij
    rcases i with ⟨iv, ilt⟩
    rcases j with ⟨jv, jlt⟩
    cases iv with
    | zero => exact hb_le _
    | succ iv₁ =>
      cases iv₁ with
      | zero =>
        cases jv with
        | zero =>
          exfalso
          have hij' : 1 ≤ 0 := hij
          omega
        | succ jv₁ =>
          cases jv₁ with
          | zero => exact L.le_refl m
          | succ jv₂ =>
            have hj2 : jv₂ = 0 := by omega
            subst hj2
            exact hle_t m
      | succ iv₂ =>
        have hi2 : iv₂ = 0 := by omega
        subst hi2
        have hjv : 2 ≤ jv := hij
        have hj2 : jv = 2 := by omega
        subst hj2
        exact L.le_refl t
  · intro u v huv
    rcases hm.2.2 u with rfl | rfl | rfl <;> rcases hm.2.2 v with rfl | rfl | rfl
    · exact Nat.le_refl _
    · rw [gb, gm]; exact (by decide : (0 : Nat) ≤ 1)
    · rw [gb, gt_eq]; exact (by decide : (0 : Nat) ≤ 2)
    · exfalso; exact hm.1 (L.le_antisymm huv (hb_le m))
    · exact Nat.le_refl _
    · rw [gm, gt_eq]; exact (by decide : (1 : Nat) ≤ 2)
    · exfalso; exact hbt (L.le_antisymm (hb_le t) huv)
    · exfalso; exact hm.2.1 (L.le_antisymm (hle_t m) huv)
    · exact Nat.le_refl _

/-- **Universal Theorem at `n = 3`**: Every 3-element `FinLattice` is isomorphic
to `C3`, hence is modular, self-dual, and NOT a pentagon lattice. -/
theorem card_three_iso_C3 (L : FinLattice) (hcard : L.card = 3) :
    Nonempty (LatticeIso L.str C3.str) := by
  cases L with
  | mk Carrier card ne eqv str =>
    dsimp at hcard
    subst hcard
    have eFin := transportLatticeIso str eqv
    have eC3 := (fin3LatticeIsoC3 (transportLatticeStr str eqv)).symm
    exact ⟨LatticeIso.trans eFin eC3⟩

theorem C3_modular : IsModular C3.str := by
  unfold IsModular
  decide

def c3SelfDualIso : LatticeIso C3.str (dualLatticeStr C3.str) :=
  LatticeIso.ofOrderIso
    (fun i => ⟨2 - i.val, by omega⟩)
    (fun i => ⟨2 - i.val, by omega⟩)
    (fun i => Fin.ext (by have := i.isLt; dsimp; omega))
    (fun i => Fin.ext (by have := i.isLt; dsimp; omega))
    (fun {x y} hxy => by have := x.isLt; have := y.isLt; change 2 - y.val ≤ 2 - x.val; omega)
    (fun {u v} huv => by have := u.isLt; have := v.isLt; change 2 - u.val ≤ 2 - v.val; omega)

theorem C3_is_self_dual : IsSelfDual C3.str := ⟨c3SelfDualIso⟩

theorem no_pentagon_at_card_3 (L : FinLattice) (hcard : L.card = 3) :
    ¬ IsPentagonLattice L.str ∧ IsModular L.str ∧ IsSelfDual L.str := by
  rcases card_three_iso_C3 L hcard with ⟨e⟩
  have hmod : IsModular L.str := IsModular.of_iso e C3_modular
  have hsd : IsSelfDual L.str := IsSelfDual.of_iso e C3_is_self_dual
  have hnp : ¬ IsPentagonLattice L.str := by
    rintro ⟨ep⟩
    exact N5_not_modular (IsModular.of_iso ep.symm hmod)
  exact ⟨hnp, hmod, hsd⟩

/-- Uniform involution on `Fin 4` swapping `b ↔ t` and swapping the remaining two
elements — reverses order on EVERY 4-element bounded poset (`C4` and `B2` alike!). -/
def firstOther4 (b t : Fin 4) : Fin 4 :=
  if (⟨0, by decide⟩ : Fin 4) ≠ b ∧ (⟨0, by decide⟩ : Fin 4) ≠ t then ⟨0, by decide⟩
  else if (⟨1, by decide⟩ : Fin 4) ≠ b ∧ (⟨1, by decide⟩ : Fin 4) ≠ t then ⟨1, by decide⟩
  else ⟨2, by decide⟩

def secondOther4 (b t : Fin 4) : Fin 4 :=
  let p := firstOther4 b t
  if (⟨0, by decide⟩ : Fin 4) ≠ b ∧ (⟨0, by decide⟩ : Fin 4) ≠ t ∧ (⟨0, by decide⟩ : Fin 4) ≠ p then ⟨0, by decide⟩
  else if (⟨1, by decide⟩ : Fin 4) ≠ b ∧ (⟨1, by decide⟩ : Fin 4) ≠ t ∧ (⟨1, by decide⟩ : Fin 4) ≠ p then ⟨1, by decide⟩
  else if (⟨2, by decide⟩ : Fin 4) ≠ b ∧ (⟨2, by decide⟩ : Fin 4) ≠ t ∧ (⟨2, by decide⟩ : Fin 4) ≠ p then ⟨2, by decide⟩
  else ⟨3, by decide⟩

def dualPerm4 (b t x : Fin 4) : Fin 4 :=
  if x = b then t
  else if x = t then b
  else if x = firstOther4 b t then secondOther4 b t
  else firstOther4 b t

theorem dualPerm4_invol :
    ∀ b t x : Fin 4, b ≠ t → dualPerm4 b t (dualPerm4 b t x) = x := by
  decide

theorem dualPerm4_bot :
    ∀ b t : Fin 4, b ≠ t → dualPerm4 b t b = t := by
  decide

theorem dualPerm4_top :
    ∀ b t : Fin 4, b ≠ t → dualPerm4 b t t = b := by
  decide

theorem dualPerm4_cases :
    ∀ b t x y : Fin 4, b ≠ t →
      x = y ∨ x = b ∨ y = t ∨ y = b ∨ x = t ∨
        (dualPerm4 b t y = x ∧ dualPerm4 b t x = y) := by
  decide

/-- Every lattice structure on `Fin 4` is self-dual. -/
theorem fin4Lattice_selfDual (L : LatticeStr (Fin 4)) : IsSelfDual L := by
  let e0 : Fin 4 := ⟨0, by decide⟩
  let e1 : Fin 4 := ⟨1, by decide⟩
  let e2 : Fin 4 := ⟨2, by decide⟩
  let e3 : Fin 4 := ⟨3, by decide⟩
  let b : Fin 4 := L.inf (L.inf (L.inf e0 e1) e2) e3
  let t : Fin 4 := L.sup (L.sup (L.sup e0 e1) e2) e3
  have hb_le : ∀ x : Fin 4, L.le b x := by
    intro x
    have h012 : L.le b (L.inf (L.inf e0 e1) e2) := L.inf_le_left _ _
    have h3 : L.le b e3 := L.inf_le_right _ _
    have h01 : L.le b (L.inf e0 e1) := L.le_trans h012 (L.inf_le_left _ _)
    have h2 : L.le b e2 := L.le_trans h012 (L.inf_le_right _ _)
    have h0 : L.le b e0 := L.le_trans h01 (L.inf_le_left _ _)
    have h1 : L.le b e1 := L.le_trans h01 (L.inf_le_right _ _)
    rcases x with ⟨k, hk⟩
    cases k with
    | zero => exact h0
    | succ k₁ =>
      cases k₁ with
      | zero => exact h1
      | succ k₂ =>
        cases k₂ with
        | zero => exact h2
        | succ k₃ =>
          have hk3 : k₃ = 0 := by omega
          subst hk3
          exact h3
  have hle_t : ∀ x : Fin 4, L.le x t := by
    intro x
    have h012 : L.le (L.sup (L.sup e0 e1) e2) t := L.le_sup_left _ _
    have h3 : L.le e3 t := L.le_sup_right _ _
    have h01 : L.le (L.sup e0 e1) t := L.le_trans (L.le_sup_left _ _) h012
    have h2 : L.le e2 t := L.le_trans (L.le_sup_right _ _) h012
    have h0 : L.le e0 t := L.le_trans (L.le_sup_left _ _) h01
    have h1 : L.le e1 t := L.le_trans (L.le_sup_right _ _) h01
    rcases x with ⟨k, hk⟩
    cases k with
    | zero => exact h0
    | succ k₁ =>
      cases k₁ with
      | zero => exact h1
      | succ k₂ =>
        cases k₂ with
        | zero => exact h2
        | succ k₃ =>
          have hk3 : k₃ = 0 := by omega
          subst hk3
          exact h3
  have hbt : b ≠ t := by
    intro heq
    have h0b : e0 = b := L.le_antisymm (heq ▸ hle_t e0) (hb_le e0)
    have h1b : e1 = b := L.le_antisymm (heq ▸ hle_t e1) (hb_le e1)
    exact absurd (h0b.trans h1b.symm) (by decide)
  have hanti : ∀ {x y : Fin 4}, L.le x y → L.le (dualPerm4 b t y) (dualPerm4 b t x) := by
    intro x y hxy
    rcases dualPerm4_cases b t x y hbt with rfl | rfl | rfl | rfl | rfl | ⟨hyx, hxy'⟩
    · exact L.le_refl _
    · rw [dualPerm4_bot b t hbt]; exact hle_t _
    · rw [dualPerm4_top b t hbt]; exact hb_le _
    · have hxb : x = b := L.le_antisymm hxy (hb_le x)
      subst hxb; exact L.le_refl _
    · have hyt : y = t := L.le_antisymm (hle_t y) hxy
      subst hyt; exact L.le_refl _
    · rw [hyx, hxy']; exact hxy
  exact ⟨LatticeIso.ofOrderIso (dualPerm4 b t) (dualPerm4 b t)
    (fun x => dualPerm4_invol b t x hbt)
    (fun y => dualPerm4_invol b t y hbt)
    (fun hxy => hanti hxy)
    (fun huv => hanti huv)⟩

/-- Every lattice structure on `Fin 1` is self-dual. -/
theorem fin1Lattice_selfDual (L : LatticeStr (Fin 1)) : IsSelfDual L := by
  refine ⟨LatticeIso.ofOrderIso (fun x => x) (fun x => x) (fun _ => rfl) (fun _ => rfl) ?_ ?_⟩
  · intro x y _
    have hxy : y = x := Subsingleton.elim y x
    rw [hxy]
    exact L.le_refl x
  · intro u v _
    have huv : u = v := Subsingleton.elim u v
    rw [huv]
    exact L.le_refl v

/-- Every lattice structure on `Fin 2` is self-dual via the transposition `0 ↔ 1`. -/
abbrev swapFin2 : Fin 2 → Fin 2 := fun i => ⟨1 - i.val, by omega⟩

theorem swapFin2_cases :
    ∀ x y : Fin 2, x = y ∨ (swapFin2 y = x ∧ swapFin2 x = y) := by
  decide

theorem fin2Lattice_selfDual (L : LatticeStr (Fin 2)) : IsSelfDual L := by
  have hanti : ∀ {x y : Fin 2}, L.le x y → L.le (swapFin2 y) (swapFin2 x) := by
    intro x y hxy
    rcases swapFin2_cases x y with rfl | ⟨hyx, hxy'⟩
    · exact L.le_refl _
    · rw [hyx, hxy']; exact hxy
  exact ⟨LatticeIso.ofOrderIso swapFin2 swapFin2
    (fun i => Fin.ext (by have := i.isLt; dsimp [swapFin2]; omega))
    (fun i => Fin.ext (by have := i.isLt; dsimp [swapFin2]; omega))
    (fun hxy => hanti hxy)
    (fun huv => hanti huv)⟩

/-- **Universal Minimality Theorem**: Every finite lattice of cardinality `≤ 4`
is self-dual (`L ≅ L^op`). -/
theorem all_card_le_4_self_dual (L : FinLattice) (hcard : L.card ≤ 4) :
    IsSelfDual L.str := by
  have hpos := L.card_pos
  cases L with
  | mk Carrier card ne eqv str =>
    dsimp at hcard hpos
    have eFin := transportLatticeIso str eqv
    let LFin := transportLatticeStr str eqv
    have hFinSD : IsSelfDual LFin := by
      have hc : card = 1 ∨ card = 2 ∨ card = 3 ∨ card = 4 := by omega
      rcases hc with rfl | rfl | rfl | rfl
      · exact fin1Lattice_selfDual LFin
      · exact fin2Lattice_selfDual LFin
      · exact IsSelfDual.of_iso (fin3LatticeIsoC3 LFin).symm C3_is_self_dual
      · exact fin4Lattice_selfDual LFin
    exact IsSelfDual.of_iso eFin hFinSD

/-! ### Individual Thin-Category Smaller Examples (`B2` at `card = 4`, `C2` at `card = 2`) -/

/-- Swap `a ↔ b` on `B2`, giving a nontrivial covariant autoequivalence of `C(B2)`. -/
def b2Swap : B2Elem → B2Elem
  | .bot => .bot
  | .a => .b
  | .b => .a
  | .top => .top

def b2SwapPosetEquiv : AutoEquiv (LatticePosetCat B2.str) where
  functor := {
    obj := b2Swap
    map := fun {x y} h => ⟨by have hd := h.down; cases x <;> cases y <;> revert hd <;> decide⟩
    map_id := fun _ => rfl
    map_comp := fun _ _ => rfl
  }
  inverse := {
    obj := b2Swap
    map := fun {x y} h => ⟨by have hd := h.down; cases x <;> cases y <;> revert hd <;> decide⟩
    map_id := fun _ => rfl
    map_comp := fun _ _ => rfl
  }
  unitIso := {
    hom := {
      app := fun x => ⟨by cases x <;> decide⟩
      naturality := fun _ => rfl
    }
    inv := {
      app := fun x => ⟨by cases x <;> decide⟩
      naturality := fun _ => rfl
    }
    inv_hom_id := fun _ => rfl
    hom_inv_id := fun _ => rfl
  }
  counitIso := {
    hom := {
      app := fun x => ⟨by cases x <;> decide⟩
      naturality := fun _ => rfl
    }
    inv := {
      app := fun x => ⟨by cases x <;> decide⟩
      naturality := fun _ => rfl
    }
    inv_hom_id := fun _ => rfl
    hom_inv_id := fun _ => rfl
  }

theorem B2_has_nontrivial_poset_autoEquiv : ¬ IsTrivialAutoEquiv b2SwapPosetEquiv := by
  rintro ⟨iso⟩
  have heq := latticePosetCat_natIso_eq iso
  have ha : B2Elem.b = B2Elem.a := congrArg (fun F => F.obj B2Elem.a) heq
  exact absurd ha (by decide)

/-- Contravariant self-duality `C(C2) ≃ C(C2)^op` swapping `0 ↔ 1` (`card = 2`). -/
def c2ContravariantEquiv : ContravariantSelfEquiv (LatticePosetCat C2.str) where
  functor := {
    obj := swapFin2
    map := fun {x y} h => ⟨by
      have hd : x.val ≤ y.val := h.down
      have := x.isLt; have := y.isLt
      change 1 - y.val ≤ 1 - x.val
      omega⟩
    map_id := fun _ => rfl
    map_comp := fun _ _ => rfl
  }
  inverse := {
    obj := swapFin2
    map := fun {x y} h => ⟨by
      have hd : y.val ≤ x.val := h.down
      have := x.isLt; have := y.isLt
      change 1 - x.val ≤ 1 - y.val
      omega⟩
    map_id := fun _ => rfl
    map_comp := fun _ _ => rfl
  }
  unitIso := {
    hom := {
      app := fun x => ⟨by have := x.isLt; change x.val ≤ 1 - (1 - x.val); omega⟩
      naturality := fun _ => rfl
    }
    inv := {
      app := fun x => ⟨by have := x.isLt; change 1 - (1 - x.val) ≤ x.val; omega⟩
      naturality := fun _ => rfl
    }
    inv_hom_id := fun _ => rfl
    hom_inv_id := fun _ => rfl
  }
  counitIso := {
    hom := {
      app := fun x => ⟨by have := x.isLt; change x.val ≤ 1 - (1 - x.val); omega⟩
      naturality := fun _ => rfl
    }
    inv := {
      app := fun x => ⟨by have := x.isLt; change 1 - (1 - x.val) ≤ x.val; omega⟩
      naturality := fun _ => rfl
    }
    inv_hom_id := fun _ => rfl
    hom_inv_id := fun _ => rfl
  }

theorem C2_contravariant_nontrivial :
    c2ContravariantEquiv.functor.obj ≠ (fun x => x) := by
  intro h
  have h0 : (1 : Fin 2) = (0 : Fin 2) := congrArg (fun f => f (0 : Fin 2)) h
  exact absurd h0 (by decide)

/-! ## Section 6: Formalization and Refutation of Conjecture 00000008560 -/

/-- A finite lattice `L` is moved up to isomorphism by the global duality
equivalence `(-)^op` on `FinLatOrdCat` iff `dualityFunctor.obj L` is not
isomorphic to `L` in `FinLatOrdCat`. -/
def IsMovedByDuality (L : FinLattice) : Prop :=
  ¬ Nonempty (CatIso FinLatOrdCat (dualityFunctor.obj L) L)

theorem isMovedByDuality_iff_not_selfDual (L : FinLattice) :
    IsMovedByDuality L ↔ ¬ IsSelfDual L.str := by
  unfold IsMovedByDuality IsSelfDual
  constructor
  · intro h ⟨e⟩
    apply h
    exact (finLatOrdIso_iff_latticeIso (dualityFunctor.obj L) L).mpr ⟨e.symm⟩
  · intro h ⟨iso⟩
    apply h
    rcases (finLatOrdIso_iff_latticeIso (dualityFunctor.obj L) L).mp ⟨iso⟩ with ⟨e⟩
    exact ⟨e.symm⟩

/-- `N5` is NOT moved up to isomorphism by duality (`N5^op ≅ N5`). -/
theorem N5_not_movedByDuality : ¬ IsMovedByDuality N5 := by
  rw [isMovedByDuality_iff_not_selfDual]
  exact fun h => h N5_is_self_dual

/-- `OneSumB2` (`1 ⊕ B_2`, `card = 5`) IS moved up to isomorphism by duality,
confirming non-vacuity of `IsMovedByDuality`. -/
theorem OneSumB2_isMovedByDuality : IsMovedByDuality OneSumB2 := by
  rw [isMovedByDuality_iff_not_selfDual]
  exact OneSumB2_not_self_dual

/-- No finite lattice of cardinality `≤ 4` is moved by duality; the exact minimum
cardinality of a lattice moved by duality is `5` (witnessed by `OneSumB2`, NOT `N5`). -/
theorem min_card_movedByDuality :
    (∀ L : FinLattice, L.card ≤ 4 → ¬ IsMovedByDuality L) ∧
      (OneSumB2.card = 5 ∧ IsMovedByDuality OneSumB2 ∧ ¬ IsPentagonLattice OneSumB2.str) := by
  refine ⟨?_, ⟨rfl, OneSumB2_isMovedByDuality, OneSumB2_not_pentagon⟩⟩
  intro L hle hm
  exact (isMovedByDuality_iff_not_selfDual L).mp hm (all_card_le_4_self_dual L hle)

/-- **Reading 1 of Conjecture 00000008560 (Global Category, Cardinality `n = 3`)**:
Clause 1 (`C(L₁) ≃ C(L₂) ↔ L₁ ≅ L₂`) ∧ Clause 2a (`(-)^op` is the smallest/unique
nontrivial self-equivalence of `FinLatOrdCat`) ∧ Clause 2b (there exists a pentagon
lattice at `n = 3` moved by duality, minimal in cardinality). -/
def Conjecture00000008560_GlobalCardReading : Prop :=
  Clause1_PosetEquivIffIso ∧
    Clause2a_DualityUniqueNontrivialAutoEquiv ∧
    (∃ L : FinLattice, L.card = 3 ∧ IsPentagonLattice L.str ∧ IsMovedByDuality L) ∧
    (∀ L : FinLattice, IsMovedByDuality L → 3 ≤ L.card)

theorem conjecture_00000008560_false_global_card :
    ¬ Conjecture00000008560_GlobalCardReading := by
  rintro ⟨_, _, ⟨L, hcard, hpent, _⟩, _⟩
  exact (no_pentagon_at_card_3 L hcard).1 hpent

/-- **Reading 2 of Conjecture 00000008560 (Global Category, Any Parameterization `n` —
including height `n = 3` or `3` interior elements where `N5` lives)**:
Even dropping `L.card = 3` entirely, NO pentagon lattice is moved by duality! -/
def Conjecture00000008560_GlobalAnyParamReading : Prop :=
  Clause1_PosetEquivIffIso ∧
    Clause2a_DualityUniqueNontrivialAutoEquiv ∧
    (∃ L : FinLattice, IsPentagonLattice L.str ∧ IsMovedByDuality L)

theorem conjecture_00000008560_false_global_any_param :
    ¬ Conjecture00000008560_GlobalAnyParamReading := by
  rintro ⟨_, _, ⟨L, hpent, hmoved⟩⟩
  exact (isMovedByDuality_iff_not_selfDual L).mp hmoved (pentagon_always_self_dual hpent)

/-- **Reading 3 of Conjecture 00000008560 (Individual Poset Category `C(L)`, Covariant)**:
Asserts a pentagon lattice possesses a nontrivial covariant self-equivalence of `C(L)`.
Refuted because `C(N5)` is completely rigid (while `C(B2)` at `card = 4` already has one). -/
def Conjecture00000008560_PosetCovariantReading : Prop :=
  Clause1_PosetEquivIffIso ∧
    (∃ (L : FinLattice) (E : AutoEquiv (LatticePosetCat L.str)),
      IsPentagonLattice L.str ∧ ¬ IsTrivialAutoEquiv E)

theorem conjecture_00000008560_false_poset_covariant :
    ¬ Conjecture00000008560_PosetCovariantReading := by
  rintro ⟨_, ⟨L, E, ⟨eIso⟩, hNontriv⟩⟩
  have hunitL : idFunc (LatticePosetCat L.str) = compFunc E.inverse E.functor :=
    latticePosetCat_natIso_eq E.unitIso
  have hcounitL : compFunc E.functor E.inverse = idFunc (LatticePosetCat L.str) :=
    latticePosetCat_natIso_eq E.counitIso
  let isoE : LatticeIso L.str L.str :=
    LatticeIso.ofOrderIso E.functor.obj E.inverse.obj
      (fun x => congrArg (fun H => H.obj x) hunitL.symm)
      (fun y => congrArg (fun H => H.obj y) hcounitL)
      (fun hxy => (E.functor.map ⟨hxy⟩).down)
      (fun huv => (E.inverse.map ⟨huv⟩).down)
  let isoN5 : LatticeIso N5.str N5.str :=
    LatticeIso.trans eIso.symm (LatticeIso.trans isoE eIso)
  let EN5 : AutoEquiv (LatticePosetCat N5.str) := {
    functor := {
      obj := isoN5.toFun
      map := fun h => ⟨(isoN5.map_le_iff _ _).mp h.down⟩
      map_id := fun _ => rfl
      map_comp := fun _ _ => rfl
    }
    inverse := {
      obj := isoN5.invFun
      map := fun h => ⟨(isoN5.symm.map_le_iff _ _).mp h.down⟩
      map_id := fun _ => rfl
      map_comp := fun _ _ => rfl
    }
    unitIso := {
      hom := { app := fun x => ⟨by dsimp [idFunc, compFunc]; rw [isoN5.left_inv]; exact N5.str.le_refl x⟩, naturality := fun _ => rfl }
      inv := { app := fun x => ⟨by dsimp [idFunc, compFunc]; rw [isoN5.left_inv]; exact N5.str.le_refl x⟩, naturality := fun _ => rfl }
      inv_hom_id := fun _ => rfl
      hom_inv_id := fun _ => rfl
    }
    counitIso := {
      hom := { app := fun x => ⟨by dsimp [idFunc, compFunc]; rw [isoN5.right_inv]; exact N5.str.le_refl x⟩, naturality := fun _ => rfl }
      inv := { app := fun x => ⟨by dsimp [idFunc, compFunc]; rw [isoN5.right_inv]; exact N5.str.le_refl x⟩, naturality := fun _ => rfl }
      inv_hom_id := fun _ => rfl
      hom_inv_id := fun _ => rfl
    }
  }
  have hrig := N5_poset_cat_rigid EN5
  have hEx : ∀ x : L.Carrier, E.functor.obj x = x := by
    intro x
    have h1 : isoN5.toFun (eIso.toFun x) = eIso.toFun x :=
      congrArg (fun H => H.obj (eIso.toFun x)) hrig
    dsimp [isoN5, LatticeIso.trans, LatticeIso.symm, isoE, LatticeIso.ofOrderIso] at h1
    rw [eIso.left_inv x] at h1
    have h2 := congrArg eIso.invFun h1
    rw [eIso.left_inv, eIso.left_inv] at h2
    exact h2
  apply hNontriv
  refine ⟨{
    hom := { app := fun x => ⟨by dsimp [idFunc]; rw [hEx x]; exact L.str.le_refl x⟩, naturality := fun _ => rfl }
    inv := { app := fun x => ⟨by dsimp [idFunc]; rw [hEx x]; exact L.str.le_refl x⟩, naturality := fun _ => rfl }
    inv_hom_id := fun _ => rfl
    hom_inv_id := fun _ => rfl
  }⟩

/-- **Reading 4 of Conjecture 00000008560 (Individual Poset Category `C(L)`, Contravariant
Self-Duality)**: Asserts that `n = 3` (or `N5` of `card = 5`) is the smallest cardinality
of a finite lattice possessing a non-identity contravariant self-equivalence `C(L) ≃ C(L)^op`.
Refuted because `C2` (`card = 2`) already has one! -/
def Conjecture00000008560_PosetContravariantReading : Prop :=
  Clause1_PosetEquivIffIso ∧
    (∀ (L : FinLattice) (E : ContravariantSelfEquiv (LatticePosetCat L.str)),
      E.functor.obj ≠ (fun x => x) → 3 ≤ L.card)

theorem conjecture_00000008560_false_poset_contravariant :
    ¬ Conjecture00000008560_PosetContravariantReading := by
  rintro ⟨_, hmin⟩
  have hle : 3 ≤ C2.card := hmin C2 c2ContravariantEquiv C2_contravariant_nontrivial
  exact absurd hle (by decide)

/-- **Master Summary Theorem**: Clause 1 and Clause 2a (global `FinLatOrdCat`
autoequivalence classification) hold, whereas all four readings of Clause 2b
(and thus Conjecture 00000008560 as a whole) are FALSE. -/
theorem conjecture_00000008560_complete_resolution :
    Clause1_PosetEquivIffIso ∧
      Clause2a_DualityUniqueNontrivialAutoEquiv ∧
      ¬ Conjecture00000008560_GlobalCardReading ∧
      ¬ Conjecture00000008560_GlobalAnyParamReading ∧
      ¬ Conjecture00000008560_PosetCovariantReading ∧
      ¬ Conjecture00000008560_PosetContravariantReading :=
  ⟨clause1_holds,
   clause2a_global_holds,
   conjecture_00000008560_false_global_card,
   conjecture_00000008560_false_global_any_param,
   conjecture_00000008560_false_poset_covariant,
   conjecture_00000008560_false_poset_contravariant⟩

end Conjecture00000008560

#print axioms Conjecture00000008560.clause1_holds
#print axioms Conjecture00000008560.globalDualityAutoEquiv_nontrivial
#print axioms Conjecture00000008560.clause2a_global_holds
#print axioms Conjecture00000008560.no_pentagon_at_card_3
#print axioms Conjecture00000008560.N5_is_self_dual
#print axioms Conjecture00000008560.N5_poset_cat_rigid
#print axioms Conjecture00000008560.all_card_le_4_self_dual
#print axioms Conjecture00000008560.OneSumB2_isMovedByDuality
#print axioms Conjecture00000008560.min_card_movedByDuality
#print axioms Conjecture00000008560.conjecture_00000008560_complete_resolution
