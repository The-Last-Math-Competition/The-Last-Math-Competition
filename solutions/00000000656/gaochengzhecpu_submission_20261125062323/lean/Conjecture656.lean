import Std

namespace Conjecture656

def sphereCellCount (degree : Nat) : Nat :=
  if degree = 0 ∨ degree = 2 then 1 else 0

abbrev Cochain (degree : Nat) := Fin (sphereCellCount degree) → Int

def zeroCochain (degree : Nat) : Cochain degree := fun _ => 0

/-- There are no consecutive nonempty cellular cochain groups for S². -/
def differential (degree : Nat) (_ : Cochain degree) : Cochain (degree + 1) :=
  zeroCochain (degree + 1)

theorem degree_one_cochain_is_zero (cochain : Cochain 1) : cochain = zeroCochain 1 := by
  funext i
  exact Fin.elim0 i

theorem degree_three_cochain_is_zero (cochain : Cochain 3) : cochain = zeroCochain 3 := by
  funext i
  exact Fin.elim0 i

abbrev TopCocycle := { a : Cochain 2 // differential 2 a = zeroCochain 3 }

def CoboundaryRelated (a b : TopCocycle) : Prop :=
  ∃ lower : Cochain 1, ∀ i, a.val i - b.val i = differential 1 lower i

theorem coboundary_related_iff_equal (a b : TopCocycle) :
    CoboundaryRelated a b ↔ a = b := by
  constructor
  · intro ⟨lower, cohomologous⟩
    apply Subtype.ext
    funext i
    have equal := cohomologous i
    change a.val i - b.val i = 0 at equal
    omega
  · intro same
    subst b
    exact ⟨zeroCochain 1, by intro i; simp [differential, zeroCochain]⟩

def topCocycleSetoid : Setoid TopCocycle where
  r := CoboundaryRelated
  iseqv := {
    refl := fun a => (coboundary_related_iff_equal a a).2 rfl
    symm := fun {a b} h =>
      (coboundary_related_iff_equal b a).2 ((coboundary_related_iff_equal a b).1 h).symm
    trans := fun {a b c} hab hbc =>
      (coboundary_related_iff_equal a c).2
        (((coboundary_related_iff_equal a b).1 hab).trans
          ((coboundary_related_iff_equal b c).1 hbc))
  }

/-- Degree-two cellular cohomology of the two-cell CW model of S². -/
def SphereH2 := Quotient topCocycleSetoid

private def topCell : Fin (sphereCellCount 2) := ⟨0, by decide⟩

def evaluate (cohomologyClass : SphereH2) : Int :=
  Quotient.lift (fun a : TopCocycle => a.val topCell)
    (fun a b h => congrArg (fun x : TopCocycle => x.val topCell)
      ((coboundary_related_iff_equal a b).1 h)) cohomologyClass

def classWithValue (value : Int) : SphereH2 :=
  Quotient.mk _ ⟨fun _ => value, rfl⟩

def addClasses (left right : SphereH2) : SphereH2 :=
  Quotient.liftOn₂ left right
    (fun a b : TopCocycle => Quotient.mk _ ⟨fun i => a.val i + b.val i, rfl⟩)
    (by
      intro a b a' b' sameA sameB
      have equalA := (coboundary_related_iff_equal a a').1 sameA
      have equalB := (coboundary_related_iff_equal b b').1 sameB
      rw [equalA, equalB])

theorem evaluation_on_class (value : Int) : evaluate (classWithValue value) = value := rfl

theorem evaluation_preserves_addition (left right : SphereH2) :
    evaluate (addClasses left right) = evaluate left + evaluate right := by
  refine Quotient.inductionOn₂ left right ?_
  intro a b
  rfl

theorem class_from_evaluation (cohomologyClass : SphereH2) :
    classWithValue (evaluate cohomologyClass) = cohomologyClass := by
  induction cohomologyClass using Quotient.inductionOn with
  | h cocycle =>
    apply Quotient.sound
    apply (coboundary_related_iff_equal _ _).2
    apply Subtype.ext
    funext i
    change cocycle.val topCell = cocycle.val i
    have unique : i = topCell := by
      apply Fin.ext
      have bound : i.val < 1 := i.isLt
      change i.val = 0
      omega
    rw [unique]

def Onto {A B : Type} (f : A → B) : Prop := ∀ b, ∃ a, f a = b

/-- The degree-one segment of the reduced Mayer–Vietoris sequence for the cap.
    The cap has trivial H₁ and its intersection has trivial reduced H₀. -/
theorem cap_inclusion_surjective {BallH1 CapH1 TotalH1 OverlapH0 : Type}
    (sumToTotal : BallH1 × CapH1 → TotalH1)
    (boundary : TotalH1 → OverlapH0)
    (capZero : CapH1) (overlapZero : OverlapH0)
    (capVanishing : ∀ c : CapH1, c = capZero)
    (overlapVanishing : ∀ c : OverlapH0, c = overlapZero)
    (exactAtTotal : ∀ c, boundary c = overlapZero →
      ∃ pair, sumToTotal pair = c) :
    Onto (fun b => sumToTotal (b, capZero)) := by
  intro c
  obtain ⟨⟨ball, cap⟩, mapsTo⟩ := exactAtTotal c (overlapVanishing (boundary c))
  exact ⟨ball, by simpa only [capVanishing cap] using mapsTo⟩

/-- The composition of the Hurewicz map, cap inclusion, Alexander duality and
    cellular evaluation carries the ball-complement group onto the integers. -/
theorem complement_maps_onto_integers {FundamentalGroup BallH1 TotalH1 : Type}
    (hurewicz : FundamentalGroup → BallH1) (ballInclusion : BallH1 → TotalH1)
    (duality : TotalH1 → SphereH2)
    (hurewiczOnto : Onto hurewicz) (ballInclusionOnto : Onto ballInclusion)
    (dualityOnto : Onto duality) :
    Onto (fun g => evaluate (duality (ballInclusion (hurewicz g)))) := by
  intro integer
  obtain ⟨total, toClass⟩ := dualityOnto (classWithValue integer)
  obtain ⟨ball, toTotal⟩ := ballInclusionOnto total
  obtain ⟨g, toBall⟩ := hurewiczOnto ball
  refine ⟨g, ?_⟩
  change evaluate (duality (ballInclusion (hurewicz g))) = integer
  rw [toBall, toTotal, toClass, evaluation_on_class]

theorem complement_has_distinct_elements
    {FundamentalGroup BallH1 CapH1 TotalH1 OverlapH0 : Type}
    (hurewicz : FundamentalGroup → BallH1)
    (sumToTotal : BallH1 × CapH1 → TotalH1)
    (boundary : TotalH1 → OverlapH0) (duality : TotalH1 → SphereH2)
    (capZero : CapH1) (overlapZero : OverlapH0)
    (capVanishing : ∀ c : CapH1, c = capZero)
    (overlapVanishing : ∀ c : OverlapH0, c = overlapZero)
    (exactAtTotal : ∀ c, boundary c = overlapZero →
      ∃ pair, sumToTotal pair = c)
    (hurewiczOnto : Onto hurewicz) (dualityOnto : Onto duality) :
    ∃ g₀ g₁ : FundamentalGroup, g₀ ≠ g₁ := by
  let winding : FundamentalGroup → Int :=
    fun g => evaluate (duality (sumToTotal (hurewicz g, capZero)))
  have onto : Onto winding :=
    complement_maps_onto_integers hurewicz (fun b => sumToTotal (b, capZero))
      duality hurewiczOnto
      (cap_inclusion_surjective sumToTotal boundary capZero overlapZero capVanishing
        overlapVanishing exactAtTotal) dualityOnto
  obtain ⟨g₀, zeroValue⟩ := onto 0
  obtain ⟨g₁, oneValue⟩ := onto 1
  refine ⟨g₀, g₁, ?_⟩
  intro equal
  exact Int.zero_ne_one (zeroValue.symm.trans ((congrArg winding equal).trans oneValue))

end Conjecture656

#print axioms Conjecture656.degree_one_cochain_is_zero
#print axioms Conjecture656.degree_three_cochain_is_zero
#print axioms Conjecture656.evaluation_on_class
#print axioms Conjecture656.evaluation_preserves_addition
#print axioms Conjecture656.class_from_evaluation
#print axioms Conjecture656.cap_inclusion_surjective
#print axioms Conjecture656.complement_has_distinct_elements
