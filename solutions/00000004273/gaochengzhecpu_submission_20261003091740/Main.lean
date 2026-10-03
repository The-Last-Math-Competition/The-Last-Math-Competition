import Std

/-! A finite reduced abelian 2-group with two successive nonzero Ulm invariants
both equal to one. Quotient dimensions are certified by explicit additive
coordinate isomorphisms with the one-dimensional vector space F_2. -/
namespace Conjecture04273

structure AbelianGroupData (A : Type) where
  zero : A
  add : A → A → A
  neg : A → A
  add_assoc : ∀ x y z, add (add x y) z = add x (add y z)
  zero_add : ∀ x, add zero x = x
  add_zero : ∀ x, add x zero = x
  neg_add : ∀ x, add (neg x) x = zero
  add_comm : ∀ x y, add x y = add y x

def double {A : Type} (D : AbelianGroupData A) (x : A) : A := D.add x x

def doubleIter {A : Type} (D : AbelianGroupData A) : Nat → A → A
  | 0 => id
  | n + 1 => fun x => double D (doubleIter D n x)

def IsTwoPrimary {A : Type} (D : AbelianGroupData A) : Prop :=
  ∀ x, ∃ n, doubleIter D n x = D.zero

def CountableCarrier (A : Type) : Prop :=
  ∃ code : A → Nat, ∀ x y, code x = code y → x = y

def pPowerImage {A : Type} (D : AbelianGroupData A) (n : Nat) (x : A) : Prop :=
  ∃ y, doubleIter D n y = x

-- U_n=(2^n G)[2]. The nth Ulm invariant is dim_F2(U_n/U_(n+1)).
def UlmSubgroup {A : Type} (D : AbelianGroupData A) (n : Nat) (x : A) : Prop :=
  pPowerImage D n x ∧ double D x = D.zero

def difference {A : Type} (D : AbelianGroupData A) (x y : A) : A := D.add x (D.neg y)

-- This is a coordinate model of the actual quotient U_n/U_(n+1), not an
-- assigned invariant. Fiber equivalence is exactly equality modulo U_(n+1),
-- and the coordinate respects the inherited group addition. The scalar
-- field F_2 has only 0 and 1, so an additive bijection is F_2-linear.
structure UlmQuotientIsF2 {A : Type} (D : AbelianGroupData A) (n : Nat) where
  coordinate : A → Fin 2
  representative : Fin 2 → A
  rep_in_upper : ∀ t, UlmSubgroup D n (representative t)
  coordinates_surject : ∀ t, coordinate (representative t) = t
  fibers_are_cosets : ∀ x y, UlmSubgroup D n x → UlmSubgroup D n y →
    (coordinate x = coordinate y ↔ UlmSubgroup D (n+1) (difference D x y))
  coordinates_add : ∀ x y, UlmSubgroup D n x → UlmSubgroup D n y →
    coordinate (D.add x y) = coordinate x + coordinate y
  coordinate_zero : coordinate D.zero = 0

def UlmInvariantIsOne {A : Type} (D : AbelianGroupData A) (n : Nat) : Prop :=
  Nonempty (UlmQuotientIsF2 D n)

-- The coordinate models yield actual bijections of quotient types. This
-- prevents replacing quotient dimensions with an unrelated numerical table.
structure Bijection (A B : Type) where
  forward : A → B
  backward : B → A
  left_inverse : ∀ a, backward (forward a) = a
  right_inverse : ∀ b, forward (backward b) = b

def ActualUlmQuotient {A : Type} (D : AbelianGroupData A) (n : Nat) :=
  Quot (fun (x y : {x // UlmSubgroup D n x}) =>
    UlmSubgroup D (n+1) (difference D x.val y.val))

def quotientBijection {A : Type} {D : AbelianGroupData A} {n : Nat}
    (q : UlmQuotientIsF2 D n) : Bijection (ActualUlmQuotient D n) (Fin 2) where
  forward := Quot.lift (fun x => q.coordinate x.val)
    (fun x y h => (q.fibers_are_cosets x.val y.val x.property y.property).mpr h)
  backward := fun t => Quot.mk _ ⟨q.representative t, q.rep_in_upper t⟩
  left_inverse := by
    intro a
    refine Quot.inductionOn a ?_
    intro x
    apply Quot.sound
    exact (q.fibers_are_cosets (q.representative (q.coordinate x.val)) x.val
      (q.rep_in_upper (q.coordinate x.val)) x.property).mp
      (q.coordinates_surject (q.coordinate x.val))
  right_inverse := q.coordinates_surject

def IsReducedAtTwo {A : Type} (D : AbelianGroupData A) : Prop :=
  ∀ H : A → Prop, (∀ x, H x → ∃ y, H y ∧ double D y = x) →
    ∀ x, H x → x = D.zero

abbrev G := Fin 2 × Fin 4

instance decidableForallG (P : G → Prop) [DecidablePred P] : Decidable (∀ x, P x) :=
  decidable_of_iff (∀ a : Fin 2, ∀ b : Fin 4, P (a,b))
    ⟨fun h x => h x.1 x.2, fun h a b => h (a,b)⟩

def elementsG : List G := [(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3)]

theorem elements_complete : ∀ x : G, x ∈ elementsG := by decide

instance decidableExistsG (P : G → Prop) [DecidablePred P] : Decidable (∃ x, P x) :=
  letI : Decidable (∃ x, x ∈ elementsG ∧ P x) := List.decidableBEx P elementsG
  decidable_of_iff (∃ x, x ∈ elementsG ∧ P x)
    ⟨fun ⟨x,_,h⟩ => ⟨x,h⟩, fun ⟨x,h⟩ => ⟨x,elements_complete x,h⟩⟩

def groupG : AbelianGroupData G where
  zero := (0, 0)
  add x y := (x.1 + y.1, x.2 + y.2)
  neg x := (0 - x.1, 0 - x.2)
  add_assoc := by decide
  zero_add := by decide
  add_zero := by decide
  neg_add := by decide
  add_comm := by decide

theorem double_twice_zero : ∀ x, doubleIter groupG 2 x = groupG.zero := by decide

theorem G_is_two_primary : IsTwoPrimary groupG := by
  intro x
  exact ⟨2, double_twice_zero x⟩

theorem G_is_reduced : IsReducedAtTwo groupG := by
  intro H hdiv x hx
  obtain ⟨y, hy, hxy⟩ := hdiv x hx
  obtain ⟨z, _, hyz⟩ := hdiv y hy
  rw [← hxy, ← hyz]
  exact double_twice_zero z

theorem G_is_countable : CountableCarrier G := by
  refine ⟨fun x => x.1.val * 4 + x.2.val, ?_⟩
  decide

theorem ulm0_description : ∀ x : G,
    UlmSubgroup groupG 0 x ↔ x.2 = 0 ∨ x.2 = 2 := by
  unfold UlmSubgroup pPowerImage
  decide

theorem ulm1_description : ∀ x : G,
    UlmSubgroup groupG 1 x ↔ x.1 = 0 ∧ (x.2 = 0 ∨ x.2 = 2) := by
  unfold UlmSubgroup pPowerImage
  decide

theorem ulm2_description : ∀ x : G,
    UlmSubgroup groupG 2 x ↔ x = groupG.zero := by
  unfold UlmSubgroup pPowerImage
  decide

def coordinate0 (x : G) : Fin 2 := x.1

def representative0 (t : Fin 2) : G := (t, 0)

def coordinate1 (x : G) : Fin 2 := if x.2 = 2 then 1 else 0

def representative1 (t : Fin 2) : G := if t = 0 then (0, 0) else (0, 2)

def quotient0 : UlmQuotientIsF2 groupG 0 where
  coordinate := coordinate0
  representative := representative0
  rep_in_upper := by unfold UlmSubgroup pPowerImage; decide
  coordinates_surject := by decide
  fibers_are_cosets := by unfold UlmSubgroup pPowerImage; decide
  coordinates_add := by unfold UlmSubgroup pPowerImage; decide
  coordinate_zero := by decide

def quotient1 : UlmQuotientIsF2 groupG 1 where
  coordinate := coordinate1
  representative := representative1
  rep_in_upper := by unfold UlmSubgroup pPowerImage; decide
  coordinates_surject := by decide
  fibers_are_cosets := by unfold UlmSubgroup pPowerImage; decide
  coordinates_add := by unfold UlmSubgroup pPowerImage; decide
  coordinate_zero := by decide

theorem ulm_invariant_zero_is_one : UlmInvariantIsOne groupG 0 := ⟨quotient0⟩
theorem ulm_invariant_one_is_one : UlmInvariantIsOne groupG 1 := ⟨quotient1⟩

-- Any strictly decreasing realizable sequence has unequal adjacent terms.
-- This assertion is therefore a necessary consequence of the conjecture,
-- already on the subclass of countable abelian 2-groups and indices 0,1.
def ClaimedNecessaryStrictDecrease : Prop :=
  ∀ (A : Type) (D : AbelianGroupData A), CountableCarrier A → IsTwoPrimary D → IsReducedAtTwo D →
    ¬ (UlmInvariantIsOne D 0 ∧ UlmInvariantIsOne D 1)

theorem conjecture04273_false : ¬ ClaimedNecessaryStrictDecrease := by
  intro h
  exact h G groupG G_is_countable G_is_two_primary G_is_reduced
    ⟨ulm_invariant_zero_is_one, ulm_invariant_one_is_one⟩

-- Also state the contradiction directly as equality versus strict decrease
-- of the ordinary dimension values certified by the two quotient models.
theorem two_nonzero_equal_invariants :
    UlmInvariantIsOne groupG 0 ∧ UlmInvariantIsOne groupG 1 ∧ ¬ (1 < (1 : Nat)) := by
  exact ⟨ulm_invariant_zero_is_one, ulm_invariant_one_is_one, by decide⟩

theorem full_conjecture_false (OtherAssertions : Prop) :
    ¬ (OtherAssertions ∧ ClaimedNecessaryStrictDecrease) := by
  intro h
  exact conjecture04273_false h.2

#print axioms quotientBijection
#print axioms G_is_reduced
#print axioms groupG
#print axioms quotient0
#print axioms quotient1
#print axioms conjecture04273_false
#print axioms full_conjecture_false
end Conjecture04273



