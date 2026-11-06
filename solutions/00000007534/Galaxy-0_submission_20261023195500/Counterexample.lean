import Std

namespace Counterexample7534

abbrev F2 := Bool
abbrev V := F2 × F2
abbrev C2 := Bool
instance (p : V → Prop) [DecidablePred p] : Decidable (∀ v : V, p v) :=
  if h : ∀ a b : Bool, p (a,b) then isTrue (fun ⟨a,b⟩ => h a b)
  else isFalse (fun h2 => h (fun a b => h2 (a,b)))
instance (p : V → Prop) [DecidablePred p] : Decidable (∃ v : V, p v) :=
  if h : ∃ a b : Bool, p (a,b) then isTrue (by rcases h with ⟨a,b,h⟩; exact ⟨(a,b),h⟩)
  else isFalse (by intro h2; rcases h2 with ⟨⟨a,b⟩,h2⟩; exact h ⟨a,b,h2⟩)
instance (p : Unit → Prop) [DecidablePred p] : Decidable (∀ v : Unit, p v) :=
  if h : p () then isTrue (fun ⟨⟩ => h) else isFalse (fun h2 => h (h2 ()))
instance (p : Unit → Prop) [DecidablePred p] : Decidable (∃ v : Unit, p v) :=
  if h : p () then isTrue ⟨(),h⟩ else isFalse (by intro h2; rcases h2 with ⟨⟨⟩,h2⟩; exact h h2)


def add (a b : F2) : F2 := xor a b
def mul (a b : F2) : F2 := a && b
def vzero : V := (false, false)
def vone : V := (true, false)
def vadd (v w : V) : V := (add v.1 w.1, add v.2 w.2)
def smul (a : F2) (v : V) : V := (mul a v.1, mul a v.2)
def swap (v : V) : V := (v.2, v.1)
def groupMul (g h : C2) : C2 := xor g h
def act (g : C2) (v : V) : V := if g then swap v else v

-- Coordinates are coefficients at the identity and the nontrivial group element.
def convolution (a b : V) : V :=
  (add (mul a.1 b.1) (mul a.2 b.2),
   add (mul a.1 b.2) (mul a.2 b.1))
def ringAct (a v : V) : V := vadd (smul a.1 v) (smul a.2 (swap v))
abbrev invariant (v : V) : Prop := ∀ g : C2, act g v = v

-- Finite checks here are kernel-reduced proofs over all inputs, not evaluations.
theorem f2_add_assoc : ∀ a b c : F2, add (add a b) c = add a (add b c) := by decide
theorem f2_add_comm : ∀ a b : F2, add a b = add b a := by decide
theorem f2_add_zero : ∀ a : F2, add a false = a := by decide
theorem f2_add_self : ∀ a : F2, add a a = false := by decide
theorem f2_mul_assoc : ∀ a b c : F2, mul (mul a b) c = mul a (mul b c) := by decide
theorem f2_mul_comm : ∀ a b : F2, mul a b = mul b a := by decide
theorem f2_mul_one : ∀ a : F2, mul a true = a := by decide
theorem f2_distrib : ∀ a b c : F2, mul a (add b c) = add (mul a b) (mul a c) := by decide
theorem f2_nonzero_inverse : ∀ a : F2, a ≠ false → mul a a = true := by decide
theorem group_assoc : ∀ g h k : C2, groupMul (groupMul g h) k = groupMul g (groupMul h k) := by decide
theorem group_unit : ∀ g : C2, groupMul false g = g := by decide
theorem group_inverse : ∀ g : C2, groupMul g g = false := by decide
theorem group_action : ∀ g h : C2, ∀ v : V, act (groupMul g h) v = act g (act h v) := by decide
theorem group_action_add : ∀ g : C2, ∀ v w : V, act g (vadd v w) = vadd (act g v) (act g w) := by decide
theorem group_action_scalar : ∀ g : C2, ∀ a : F2, ∀ v : V, act g (smul a v) = smul a (act g v) := by decide
theorem convolution_assoc : ∀ a b c : V, convolution (convolution a b) c = convolution a (convolution b c) := by decide
theorem convolution_comm : ∀ a b : V, convolution a b = convolution b a := by decide
theorem convolution_one : ∀ a : V, convolution vone a = a := by decide
theorem convolution_distrib : ∀ a b c : V, convolution a (vadd b c) = vadd (convolution a b) (convolution a c) := by decide
theorem regular_action : ∀ a v : V, ringAct a v = convolution a v := by decide
theorem ring_action_comp : ∀ a b v : V, ringAct (convolution a b) v = ringAct a (ringAct b v) := by decide
theorem basis_action : ∀ v : V, ringAct (false,true) v = swap v := by decide
theorem action_faithful : ∀ a b : V, (∀ v : V, ringAct a v = ringAct b v) → a = b := by decide
theorem invariants_diagonal : ∀ v : V, invariant v ↔ v.1 = v.2 := by decide
theorem fixed_nonzero : invariant (true,true) ∧ (true,true) ≠ vzero := by decide
theorem fixed_proper : ¬ invariant (true,false) := by decide
theorem all_idempotents : ∀ a : V, convolution a a = a ↔ a = vzero ∨ a = vone := by decide

abbrev ProjectsToInvariants (a : V) : Prop :=
  (∀ v : V, invariant (ringAct a v)) ∧ (∀ v : V, invariant v → ringAct a v = v)

theorem no_group_ring_retraction : ¬ ∃ a : V, ProjectsToInvariants a := by decide
theorem no_idempotent_projection : ¬ ∃ a : V, convolution a a = a ∧ ProjectsToInvariants a := by decide

-- Degree-zero cochains are functions on the vertex set, not formal labels.
def evaluate (v : V) (x : C2) : F2 := if x then v.2 else v.1
def fromFunction (f : C2 → F2) : V := (f false, f true)
theorem from_evaluate (v : V) : fromFunction (evaluate v) = v := rfl
theorem evaluate_from (f : C2 → F2) : evaluate (fromFunction f) = f := by
  funext x; cases x <;> rfl
theorem evaluate_action : ∀ g : C2, ∀ v : V, ∀ x : C2,
    evaluate (act g v) x = evaluate v (groupMul g x) := by decide

-- The degree-zero cochain complex of a discrete two-point simplicial complex:
-- C^{-1}=0, C^0=F2^2, C^1=0.  Both differentials are the unique zero maps.
abbrev Cminus := Unit
abbrev Cplus := Unit
def dminus (_ : Cminus) : V := vzero
def dplus (_ : V) : Cplus := ()
abbrev cycles (v : V) : Prop := dplus v = ()
abbrev boundary (v : V) : Prop := ∃ c : Cminus, dminus c = v

theorem complex_identity : ∀ c : Cminus, dplus (dminus c) = () := by decide
theorem all_cycles : ∀ v : V, cycles v := by decide
theorem boundaries_zero : ∀ v : V, boundary v ↔ v = vzero := by decide

abbrev homologous (v w : V) : Prop := boundary (vadd v w)
theorem homologous_iff : ∀ v w : V, homologous v w ↔ v = w := by decide
instance hSetoid : Setoid V where
  r := homologous
  iseqv := ⟨by intro v; exact (homologous_iff v v).mpr rfl,
    by intro v w h; exact (homologous_iff w v).mpr ((homologous_iff v w).mp h).symm,
    by intro v w z h k; exact (homologous_iff v z).mpr (((homologous_iff v w).mp h).trans ((homologous_iff w z).mp k))⟩
abbrev H0 := Quotient hSetoid
def classOf (v : V) : H0 := Quotient.mk _ v
def coordinates : H0 → V := Quotient.lift id (by intro v w h; exact (homologous_iff v w).mp h)
theorem coordinates_class (v : V) : coordinates (classOf v) = v := rfl
theorem class_coordinates (c : H0) : classOf (coordinates c) = c := by
  induction c using Quotient.inductionOn with
  | h v => rfl

def hAct (g : C2) (c : H0) : H0 := classOf (act g (coordinates c))
def hRingAct (a : V) (c : H0) : H0 := classOf (ringAct a (coordinates c))
def hInvariant (c : H0) : Prop := ∀ g : C2, hAct g c = c

theorem class_injective {v w : V} (h : classOf v = classOf w) : v = w := congrArg coordinates h
theorem h_invariant_iff (v : V) : hInvariant (classOf v) ↔ invariant v := by
  constructor
  · intro h g; exact class_injective (h g)
  · intro h g; exact congrArg classOf (h g)
theorem h_action_class (g : C2) (v : V) : hAct g (classOf v) = classOf (act g v) := rfl
theorem h_ring_action_class (a v : V) : hRingAct a (classOf v) = classOf (ringAct a v) := rfl

def HProjects (a : V) : Prop :=
  (∀ c : H0, hInvariant (hRingAct a c)) ∧
  (∀ c : H0, hInvariant c → hRingAct a c = c)

theorem cohomology_projection_implies_vector_projection (a : V) (h : HProjects a) : ProjectsToInvariants a := by
  constructor
  · intro v; exact (h_invariant_iff (ringAct a v)).mp (h.1 (classOf v))
  · intro v hv; exact class_injective (h.2 (classOf v) ((h_invariant_iff v).mpr hv))
theorem no_cohomology_group_ring_retraction : ¬ ∃ a : V, HProjects a := by
  rintro ⟨a,h⟩
  exact no_group_ring_retraction ⟨a, cohomology_projection_implies_vector_projection a h⟩
theorem no_cohomology_idempotent_projection : ¬ ∃ a : V, convolution a a = a ∧ HProjects a := by
  rintro ⟨a,_,h⟩
  exact no_cohomology_group_ring_retraction ⟨a,h⟩

-- Image equality alone, combined with idempotence, forces the retraction law.
abbrev ImageIsInvariants (a : V) : Prop :=
  ∀ w : V, invariant w ↔ ∃ v : V, ringAct a v = w
theorem no_idempotent_with_invariant_image :
    ¬ ∃ a : V, convolution a a = a ∧ ImageIsInvariants a := by decide

def HImageIsInvariants (a : V) : Prop :=
  ∀ c : H0, hInvariant c ↔ ∃ b : H0, hRingAct a b = c

theorem h_image_to_vector_image (a : V) (h : HImageIsInvariants a) : ImageIsInvariants a := by
  intro w
  constructor
  · intro hw
    obtain ⟨b,hb⟩ := (h (classOf w)).mp ((h_invariant_iff w).mpr hw)
    exact ⟨coordinates b, class_injective hb⟩
  · rintro ⟨v,hv⟩
    apply (h_invariant_iff w).mp
    apply (h (classOf w)).mpr
    exact ⟨classOf v, congrArg classOf hv⟩

theorem no_cohomology_idempotent_with_invariant_image :
    ¬ ∃ a : V, convolution a a = a ∧ HImageIsInvariants a := by
  rintro ⟨a,ha,hi⟩
  exact no_idempotent_with_invariant_image ⟨a,ha,h_image_to_vector_image a hi⟩

theorem norm_element_image : ImageIsInvariants (true,true) := by decide
theorem norm_element_square_zero : convolution (true,true) (true,true) = vzero := by decide
theorem norm_element_not_idempotent : convolution (true,true) (true,true) ≠ (true,true) := by decide
theorem cohomology_action_law (g h : C2) (c : H0) :
    hAct (groupMul g h) c = hAct g (hAct h c) := by
  exact congrArg classOf (group_action g h (coordinates c))
theorem cohomology_ring_action_law (a b : V) (c : H0) :
    hRingAct (convolution a b) c = hRingAct a (hRingAct b c) := by
  exact congrArg classOf (ring_action_comp a b (coordinates c))

-- A vector-space projection exists.  Its failure is specifically equivariance,
-- so the counterexample is not a denial of elementary linear algebra.
def ordinaryProjection (v : V) : V := (v.1,v.1)
theorem ordinary_is_projection :
    (∀ v : V, invariant (ordinaryProjection v)) ∧
    (∀ v : V, invariant v → ordinaryProjection v = v) ∧
    (∀ v w : V, ordinaryProjection (vadd v w) = vadd (ordinaryProjection v) (ordinaryProjection w)) ∧
    (∀ a : F2, ∀ v : V, ordinaryProjection (smul a v) = smul a (ordinaryProjection v)) := by decide
theorem ordinary_not_equivariant : ordinaryProjection (swap (true,false)) ≠ swap (ordinaryProjection (true,false)) := by decide

#print axioms no_cohomology_idempotent_with_invariant_image
#print axioms no_cohomology_idempotent_projection
#print axioms no_group_ring_retraction
end Counterexample7534
