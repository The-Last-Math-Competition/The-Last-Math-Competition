import Mathlib.CategoryTheory.Functor.Basic
import Mathlib.CategoryTheory.NatIso
import Mathlib.Algebra.Module.Equiv.Basic
import Mathlib.Algebra.Module.Pi

/-! Two genuine FI functors with identical positive-degree tails and distinct degree zero.
We bundle Z-modules explicitly because the cached Mathlib excludes ModuleCat. -/
namespace Conjecture5300
open CategoryTheory

structure FI where
  size : ℕ

@[reducible] instance : Category FI where
  Hom A B := Fin A.size ↪ Fin B.size
  id _ := Function.Embedding.refl _
  comp f g := f.trans g

structure ZMod where
  carrier : Type
  [group : AddCommGroup carrier]
  [module : Module ℤ carrier]

attribute [instance] ZMod.group ZMod.module

@[reducible] instance : Category ZMod where
  Hom A B := A.carrier →ₗ[ℤ] B.carrier
  id A := LinearMap.id
  comp f g := g.comp f

def applyHom {A B : ZMod} (f : A ⟶ B) (x : A.carrier) : B.carrier :=
  let g : A.carrier →ₗ[ℤ] B.carrier := f
  g x

abbrev zeroObj : ZMod := ⟨Empty → ℤ⟩
abbrev supportedObj (A : FI) : ZMod := ⟨(Fin A.size → Empty) → ℤ⟩

def supportedMap {A B : FI} (f : A ⟶ B) :
    (supportedObj A).carrier →ₗ[ℤ] (supportedObj B).carrier where
  toFun x p := x (p ∘ Function.Embedding.toFun f)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

abbrev supported : FI ⥤ ZMod where
  obj := supportedObj
  map f := supportedMap f
  map_id _ := by apply LinearMap.ext; intro x; funext p; rfl
  map_comp _ _ := by apply LinearMap.ext; intro x; funext p; rfl

abbrev zero : FI ⥤ ZMod where
  obj _ := zeroObj
  map _ := LinearMap.id
  map_id _ := rfl
  map_comp _ _ := rfl

theorem supported_subsingleton (n : ℕ) (hn : 1 ≤ n) :
    Subsingleton (supported.obj ⟨n⟩).carrier := by
  constructor
  intro x y
  funext p
  exact Empty.elim (p ⟨0, hn⟩)

def tailEquiv (n : ℕ) (hn : 1 ≤ n) :
    (supported.obj ⟨n⟩).carrier ≃ₗ[ℤ] (zero.obj ⟨n⟩).carrier := by
  letI := supported_subsingleton n hn
  exact
    { toFun := fun _ => 0
      invFun := fun _ => 0
      left_inv := fun _ => Subsingleton.elim _ _
      right_inv := fun _ => Subsingleton.elim _ _
      map_add' := fun _ _ => by simp
      map_smul' := fun _ _ => by simp }

theorem tail_naturality {A B : FI} (hA : 1 ≤ A.size) (hB : 1 ≤ B.size)
    (f : A ⟶ B) (x : (supported.obj A).carrier) :
    tailEquiv B.size hB (applyHom (supported.map f) x) =
      applyHom (zero.map f) (tailEquiv A.size hA x) := rfl

/-- The full subcategory of finite sets of positive size. -/
structure PositiveFI where
  size : ℕ
  positive : 1 ≤ size

instance : Category PositiveFI where
  Hom A B := Fin A.size ↪ Fin B.size
  id _ := Function.Embedding.refl _
  comp f g := f.trans g

def inclusion : PositiveFI ⥤ FI where
  obj A := ⟨A.size⟩
  map f := f

def positiveIso (A : PositiveFI) : supported.obj ⟨A.size⟩ ≅ zero.obj ⟨A.size⟩ where
  hom := (tailEquiv A.size A.positive).toLinearMap
  inv := (tailEquiv A.size A.positive).symm.toLinearMap
  hom_inv_id := by apply LinearMap.ext; intro x; exact (tailEquiv A.size A.positive).symm_apply_apply x
  inv_hom_id := by apply LinearMap.ext; intro x; exact (tailEquiv A.size A.positive).apply_symm_apply x

/-- Even the entire positive-degree functors are naturally isomorphic. -/
def tailIso : inclusion ⋙ supported ≅ inclusion ⋙ zero :=
  NatIso.ofComponents positiveIso (by
    intro A B f
    apply LinearMap.ext
    intro x
    exact (tail_naturality (A := ⟨A.size⟩) (B := ⟨B.size⟩) A.positive B.positive
      (show (⟨A.size⟩ : FI) ⟶ ⟨B.size⟩ from f) x).symm)

/-- The exceptional degree is an honest free rank-one abelian group. -/
def degreeZeroEquiv : (supported.obj ⟨0⟩).carrier ≃ₗ[ℤ] ℤ where
  toFun x := x (fun i => Fin.elim0 i)
  invFun z := fun _ => z
  left_inv x := by
    funext p
    have h : p = (fun i => Fin.elim0 i) := Subsingleton.elim _ _
    rw [h]
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- A generator in degree zero spans the only nonzero value. -/
theorem generated_in_degree_zero (n : ℕ) (x : (supported.obj ⟨n⟩).carrier) :
    ∃ z : ℤ, x = z • applyHom (supported.map
      (show (⟨0⟩ : FI) ⟶ ⟨n⟩ from
        ⟨(fun i => Fin.elim0 i), fun i => Fin.elim0 i⟩)) (fun _ => 1) := by
  cases n with
  | zero =>
    refine ⟨degreeZeroEquiv x, ?_⟩
    funext p
    change x p = x (fun i => Fin.elim0 i) * 1
    rw [mul_one]
    congr 1
    funext i
    exact Fin.elim0 i
  | succ n =>
    exact ⟨0, (supported_subsingleton (n + 1) (Nat.succ_le_succ (Nat.zero_le n))).elim _ _⟩

theorem not_iso : ¬ Nonempty (supported ≅ zero) := by
  rintro ⟨e⟩
  have h := congrArg (fun f => applyHom f (fun _ => (1 : ℤ)))
    (congrArg (fun t => t.app (⟨0⟩ : FI)) e.hom_inv_id)
  have hzero : applyHom (e.hom.app (⟨0⟩ : FI)) (fun _ => (1 : ℤ)) = 0 := Subsingleton.elim _ _
  have hone : (fun _ : Fin 0 → Empty => (1 : ℤ)) = 0 := by
    change applyHom (e.inv.app ⟨0⟩) (applyHom (e.hom.app ⟨0⟩) (fun _ => 1)) =
      (fun _ => 1) at h
    rw [hzero] at h
    have hz : applyHom (e.inv.app ⟨0⟩) 0 = 0 := map_zero
      (show zeroObj.carrier →ₗ[ℤ] (supported.obj ⟨0⟩).carrier from e.inv.app ⟨0⟩)
    exact h.symm.trans hz
  have := congrFun hone (fun i => Fin.elim0 i)
  exact Int.one_ne_zero this

def Claim : Prop :=
  ∃ V W : FI ⥤ ZMod,
    (∃ N : ℕ, ∀ n, N ≤ n → Nonempty ((V.obj ⟨n⟩).carrier ≃ₗ[ℤ]
      (W.obj ⟨n⟩).carrier)) ∧
      Nonempty (inclusion ⋙ V ≅ inclusion ⋙ W) ∧ ¬ Nonempty (V ≅ W)

theorem conjecture5300 : Claim :=
  ⟨supported, zero, ⟨1, fun n hn => ⟨tailEquiv n hn⟩⟩, ⟨tailIso⟩, not_iso⟩

#print axioms conjecture5300
#print axioms tail_naturality
#print axioms tailIso
#print axioms degreeZeroEquiv
#print axioms generated_in_degree_zero
end Conjecture5300




