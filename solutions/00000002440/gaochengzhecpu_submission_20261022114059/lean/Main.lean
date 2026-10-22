import Mathlib.Topology.Homotopy.HomotopyGroup
import Mathlib.Algebra.Category.Grp.Basic
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.Tactic

open CategoryTheory
open scoped Topology

noncomputable section
universe u v
namespace Conjecture2440

/- The carrier is an actual pointed topological space; no group or
   commutativity is supplied as part of this data. -/
structure BasedSpace where
  carrier : Type u
  topology : TopologicalSpace carrier
  point : carrier

attribute [instance] BasedSpace.topology

abbrev Pi3 (X : BasedSpace.{u}) := HomotopyGroup.Pi 3 X.carrier X.point
abbrev CubeLoop3 (X : BasedSpace.{u}) := GenLoop (Fin 3) X.carrier X.point

/- These are the actual coordinatewise concatenations of based maps
   I^3 -> X. Their interchange identity holds before taking homotopy classes. -/
theorem actual_cube_interchange (X : BasedSpace.{u}) (a b c d : CubeLoop3 X) :
    GenLoop.transAt (0 : Fin 3) (GenLoop.transAt 1 a b) (GenLoop.transAt 1 c d) =
      GenLoop.transAt (1 : Fin 3) (GenLoop.transAt 0 a c) (GenLoop.transAt 0 b d) :=
  GenLoop.transAt_distrib (by decide) a b c d

theorem actual_direction_zero_unital (X : BasedSpace.{u}) :
    EckmannHilton.IsUnital (HomotopyGroup.auxGroup (0 : Fin 3) (X := X.carrier)
      (x := X.point)).mul (1 : Pi3 X) :=
  HomotopyGroup.isUnital_auxGroup 0

theorem actual_direction_one_unital (X : BasedSpace.{u}) :
    EckmannHilton.IsUnital (HomotopyGroup.auxGroup (1 : Fin 3) (X := X.carrier)
      (x := X.point)).mul (1 : Pi3 X) :=
  HomotopyGroup.isUnital_auxGroup 1

/- Mathlib derives this CommGroup instance from the genuine cube-loop
   interchange law via Eckmann-Hilton; it is not a hypothesis. -/
theorem actual_pi3_comm (X : BasedSpace.{u}) (a b : Pi3 X) : a*b = b*a :=
  mul_comm a b

theorem actual_loops_commute_up_to_based_homotopy (X : BasedSpace.{u})
    (a b : CubeLoop3 X) :
    GenLoop.Homotopic (GenLoop.transAt (0 : Fin 3) a b)
      (GenLoop.transAt (0 : Fin 3) b a) := by
  have hab := HomotopyGroup.mul_spec (X := X.carrier) (x := X.point)
    (i := (0 : Fin 3)) (p := b) (q := a)
  have hba := HomotopyGroup.mul_spec (X := X.carrier) (x := X.point)
    (i := (0 : Fin 3)) (p := a) (q := b)
  have hc := actual_pi3_comm X (Quotient.mk' b) (Quotient.mk' a)
  exact Quotient.exact (hab.symm.trans (hc.trans hba))

def Nonabelian (G : Type*) [Group G] : Prop := ∃ a b : G, a*b ≠ b*a

theorem no_nonabelian_actual_pi3 (X : BasedSpace.{u}) : ¬ Nonabelian (Pi3 X) := by
  rintro ⟨a,b,hab⟩
  exact hab (actual_pi3_comm X a b)

/- A diagram of actual third homotopy groups. The maps are arbitrary group
   homomorphisms between the actual homotopy groups, so in particular this
   covers the homomorphisms induced by pointed continuous transition maps.
   There is no commutativity field. Cofiltered diagrams are special cases. -/
structure ThirdHomotopyDiagram (I : Type v) [Category I] where
  space : I → BasedSpace.{u}
  map : ∀ {i j : I}, (i ⟶ j) → Pi3 (space i) →* Pi3 (space j)
  map_id : ∀ i, map (𝟙 i) = MonoidHom.id (Pi3 (space i))
  map_comp : ∀ {i j k} (f : i ⟶ j) (g : j ⟶ k), map (f ≫ g) = (map g).comp (map f)

namespace ThirdHomotopyDiagram
variable {I : Type v} [Category I] (D : ThirdHomotopyDiagram.{u} I)

def groupDiagram : I ⥤ Grp.{u} where
  obj i := Grp.of (Pi3 (D.space i))
  map f := Grp.ofHom (D.map f)
  map_id i := by
    exact congrArg (fun h => Grp.ofHom h) (D.map_id i)
  map_comp f g := by
    exact congrArg (fun h => Grp.ofHom h) (D.map_comp f g)

/- The whole diagram factors through the category of commutative groups.
   This is a levelwise statement about the pro-system itself, not a claim
   inferred solely from commutativity of its inverse limit. -/
def abelianDiagram : I ⥤ CommGrp.{u} where
  obj i := CommGrp.of (Pi3 (D.space i))
  map f := CommGrp.ofHom (D.map f)
  map_id i := by
    exact congrArg (fun h => CommGrp.ofHom h) (D.map_id i)
  map_comp f g := by
    exact congrArg (fun h => CommGrp.ofHom h) (D.map_comp f g)

def abelian_factorization : D.abelianDiagram ⋙ forget₂ CommGrp Grp ≅ D.groupDiagram := by
  refine NatIso.ofComponents (fun i => ?_) ?_
  · refine { hom := Grp.ofHom ?_, inv := Grp.ofHom ?_, hom_inv_id := ?_, inv_hom_id := ?_ }
    · exact { toFun := fun x => x, map_one' := rfl, map_mul' := fun _ _ => rfl }
    · exact { toFun := fun x => x, map_one' := rfl, map_mul' := fun _ _ => rfl }
    · ext a; rfl
    · ext a; rfl
  · intro i j f
    ext a
    rfl

theorem every_actual_layer_comm (i : I) (a b : Pi3 (D.space i)) : a*b = b*a :=
  actual_pi3_comm (D.space i) a b

theorem no_nonabelian_layer : ¬ ∃ i : I, Nonabelian (Pi3 (D.space i)) := by
  rintro ⟨i,hi⟩
  exact no_nonabelian_actual_pi3 (D.space i) hi

end ThirdHomotopyDiagram

/- All quotient images of actual pi_3 are commutative. In particular every
   finite quotient used in profinite completion is commutative. -/
theorem every_quotient_image_comm (X : BasedSpace.{u}) {Q : Type*} [Group Q]
    (f : Pi3 X →* Q) (hf : Function.Surjective f) (a b : Q) : a*b = b*a := by
  obtain ⟨x,rfl⟩ := hf a
  obtain ⟨y,rfl⟩ := hf b
  calc
    f x * f y = f (x*y) := (f.map_mul x y).symm
    _ = f (y*x) := congrArg f (actual_pi3_comm X x y)
    _ = f y * f x := f.map_mul y x

theorem normal_quotient_comm (X : BasedSpace.{u}) (N : Subgroup (Pi3 X)) [N.Normal]
    (a b : Pi3 X ⧸ N) : a*b = b*a :=
  every_quotient_image_comm X (QuotientGroup.mk' N) (QuotientGroup.mk'_surjective N) a b

/- The actual inverse limit of a group diagram, realized as the subgroup
   of compatible tuples in its product. -/
def compatibleSubgroup {I : Type v} [Category I] (D : I ⥤ Grp.{u}) :
    Subgroup (∀ i, D.obj i) where
  carrier := {a | ∀ {i j} (f : i ⟶ j), (D.map f).hom (a i) = a j}
  one_mem' := by intro i j f; exact (D.map f).hom.map_one
  mul_mem' := by
    intro a b ha hb i j f
    change (D.map f).hom (a i * b i) = a j * b j
    rw [map_mul, ha f, hb f]
  inv_mem' := by
    intro a ha i j f
    change (D.map f).hom (a i)⁻¹ = (a j)⁻¹
    rw [map_inv, ha f]

theorem actual_pi3_inverse_limit_comm {I : Type v} [Category I]
    (D : ThirdHomotopyDiagram.{u} I) (a b : compatibleSubgroup D.groupDiagram) :
    a*b = b*a := by
  apply Subtype.ext
  funext i
  exact actual_pi3_comm (D.space i) (a.val i) (b.val i)

theorem quotient_inverse_limit_comm {I : Type v} [Category I]
    (X : I → BasedSpace.{u}) (Q : I ⥤ Grp.{u})
    (f : ∀ i, Pi3 (X i) →* Q.obj i) (hf : ∀ i, Function.Surjective (f i))
    (a b : compatibleSubgroup Q) : a*b = b*a := by
  apply Subtype.ext
  funext i
  exact every_quotient_image_comm (X i) (f i) (hf i) (a.val i) (b.val i)

#print axioms actual_cube_interchange
#print axioms actual_pi3_comm
#print axioms actual_loops_commute_up_to_based_homotopy
#print axioms ThirdHomotopyDiagram.abelian_factorization
#print axioms ThirdHomotopyDiagram.no_nonabelian_layer
#print axioms every_quotient_image_comm
#print axioms actual_pi3_inverse_limit_comm
#print axioms quotient_inverse_limit_comm

end Conjecture2440
