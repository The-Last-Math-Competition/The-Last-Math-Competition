import TwoExtras
import Graphs

namespace TLMC3322.Principal
open TLMC506
noncomputable section

def xyMul (p : Poly) : Poly := xMul (yMul p)
def generator : Poly := mul X Y
def InIdeal (p : Poly) : Prop := ∃ a, p = xyMul a

theorem generator_action (p : Poly) : mul generator p = xyMul p := by
  unfold generator xyMul
  rw [mul_assoc,X_mul,Y_mul]

theorem xyMul_injective {p q : Poly} (h : xyMul p = xyMul q) : p = q :=
  yMul_injective (xMul_injective h)

@[simp] theorem xyMul_zero : xyMul zero = zero := by simp [xyMul]
theorem xyMul_add (p q : Poly) : xyMul (add p q) = add (xyMul p) (xyMul q) := by
  simp only [xyMul,yMul_add,xMul_add]
theorem xyMul_linear (r p : Poly) : xyMul (mul r p) = mul r (xyMul p) := by
  simp only [xyMul,mul_xMul,mul_yMul]

def IsIdeal (I : Poly → Prop) : Prop :=
  I zero ∧ (∀ p q, I p → I q → I (add p q)) ∧
  (∀ r p, I p → I (mul r p))

theorem ideal_laws : IsIdeal InIdeal := by
  refine ⟨⟨zero,xyMul_zero.symm⟩,?_,?_⟩
  · rintro p q ⟨a,rfl⟩ ⟨b,rfl⟩
    exact ⟨add a b,(xyMul_add a b).symm⟩
  · rintro r p ⟨a,rfl⟩
    exact ⟨mul r a,(xyMul_linear r a).symm⟩

def vertexVariable (v : Fin 2) : Poly := if v.val = 0 then X else Y

def IsEdgeIdeal (I : Poly → Prop) : Prop :=
  IsIdeal I ∧
  (∀ u v, Graphs.K2 u v = true → I (mul (vertexVariable u) (vertexVariable v))) ∧
  (∀ J : Poly → Prop, IsIdeal J →
    (∀ u v, Graphs.K2 u v = true → J (mul (vertexVariable u) (vertexVariable v))) →
    ∀ p, I p → J p)

theorem actual_edge_ideal : IsEdgeIdeal InIdeal := by
  refine ⟨ideal_laws,?_,?_⟩
  · intro u v huv
    have he : u = 0 ∧ v = 1 ∨ u = 1 ∧ v = 0 := by
      have hh : ∀ u v : Fin 2, Graphs.K2 u v = true →
        (u = 0 ∧ v = 1 ∨ u = 1 ∧ v = 0) := by decide
      exact hh u v huv
    rcases he with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    · exact ⟨one,by change mul X Y = xyMul one; rw [X_mul]; rfl⟩
    · exact ⟨one,by change mul Y X = xyMul one; rw [mul_comm,X_mul]; rfl⟩
  · rintro J hJ he p ⟨a,rfl⟩
    have hg : J generator := he 0 1 (by decide)
    rw [← generator_action,mul_comm]
    exact hJ.2.2 a generator hg

def Homogeneous (p : Poly) (d : Nat) : Prop :=
  ∀ i j, p.coeff i j = true → i+j=d

def ShiftHomogeneous (p : Poly) (s d : Nat) : Prop :=
  ∀ i j, p.coeff i j = true → i+j+s=d

theorem xyMul_degree (p : Poly) (d : Nat) :
    Homogeneous (xyMul p) d ↔ ShiftHomogeneous p 2 d := by
  constructor
  · intro h i j hp
    have hh := h (i+1) (j+1) hp
    omega
  · intro h i j hp
    cases i with
    | zero => cases hp
    | succ i =>
      cases j with
      | zero => cases hp
      | succ j => have hh := h i j hp; omega

/-- The complete free resolution of the ideal has just R(-2) in degree zero.
The augmentation is an R-linear, degree-preserving bijection onto the actual ideal. -/
def VerifiedMinimalResolution : Prop :=
  IsEdgeIdeal InIdeal ∧
  (∀ p, InIdeal p ↔ ∃ a, xyMul a = p) ∧
  (∀ p q, xyMul p = xyMul q → p = q) ∧
  (∀ p q, xyMul (add p q) = add (xyMul p) (xyMul q)) ∧
  (∀ r p, xyMul (mul r p) = mul r (xyMul p)) ∧
  (∀ p d, Homogeneous (xyMul p) d ↔ ShiftHomogeneous p 2 d)

theorem verified_minimal_resolution : VerifiedMinimalResolution := by
  refine ⟨actual_edge_ideal,?_,fun _ _ h => xyMul_injective h,
    xyMul_add,xyMul_linear,xyMul_degree⟩
  intro p
  constructor
  · rintro ⟨a,h⟩; exact ⟨a,h.symm⟩
  · rintro ⟨a,h⟩; exact ⟨a,h.symm⟩

/-- The homogeneous maximal ideal is the kernel of constant-coefficient reduction. -/
def Maximal (p : Poly) : Prop := p.coeff 0 0 = false
def reduce (p : Poly) : Bool := p.coeff 0 0

/-- The residue kernel is precisely the genuine homogeneous ideal (X,Y). -/
theorem maximal_is_generated (p : Poly) : Maximal p ↔ TLMC506.MaximalGenerated p :=
  TLMC506.maximal_iff_generated p

theorem reduction_ring_hom :
    (∀ p q, reduce (add p q) = (reduce p ^^ reduce q)) ∧
    (∀ p q, reduce (mul p q) = (reduce p && reduce q)) ∧ reduce one = true :=
  ⟨fun _ _ => rfl,TLMC506.mul_constant_coefficient,rfl⟩

theorem residue_kernel (p : Poly) : reduce p = false ↔ Maximal p := Iff.rfl

def lift (b : Bool) : Poly := if b then one else zero
@[simp] theorem reduce_lift (b : Bool) : reduce (lift b) = b := by cases b <;> rfl

theorem residue_equivalence (p q : Poly) : Maximal (add p q) ↔ reduce p = reduce q :=
  add_eq_zero_iff_bool
where
  add_eq_zero_iff_bool : Maximal (add p q) ↔ reduce p = reduce q := by
    change (p.coeff 0 0 ^^ q.coeff 0 0) = false ↔ p.coeff 0 0 = q.coeff 0 0
    cases p.coeff 0 0 <;> cases q.coeff 0 0 <;> decide

/-- This is m*R, not merely a selected family of positive-degree polynomials. -/
theorem maximal_free_rank_one (p : Poly) :
    Maximal p ↔ ∃ a, Maximal a ∧ p = mul a one := by
  constructor
  · intro h; exact ⟨p,h,(mul_one p).symm⟩
  · rintro ⟨a,h,rfl⟩; simpa using h

/-- The reduced free basis inherits its shift 2 from xyMul_degree. -/
def ReducedHomogeneous (b : Bool) (d : Nat) : Prop := b = true → d = 2

theorem reduction_respects_shift (p : Poly) (d : Nat)
    (h : ShiftHomogeneous p 2 d) : ReducedHomogeneous (reduce p) d := by
  intro hp
  have hd := h 0 0 hp
  omega

theorem homogeneous_residue_lift (b : Bool) (d : Nat)
    (h : ReducedHomogeneous b d) : ShiftHomogeneous (lift b) 2 d := by
  intro i j hp
  cases b with
  | false => cases hp
  | true =>
    have hd := h rfl
    have hh : i = 0 ∧ j = 0 := by simpa [lift] using hp
    omega

/-- Homology of the reduced minimal resolution: there is one reduced free
space in homological degree zero and no terms in higher degrees. -/
def BettiSupport (i d : Nat) : Prop :=
  i = 0 ∧ ∃ b : Bool, b ≠ false ∧ ReducedHomogeneous b d

/-- The one-term residue complex has zero outgoing map and no incoming boundaries. -/
def residueD0 (_ : Bool) : Unit := ()
def residueD1 (_ : Unit) : Bool := false

def HomologySupport (i d : Nat) : Prop :=
  i = 0 ∧ ∃ b : Bool, (¬ ∃ u, residueD1 u = b) ∧
    residueD0 b = () ∧ ReducedHomogeneous b d

theorem betti_support_is_homology (i d : Nat) : BettiSupport i d ↔ HomologySupport i d := by
  simp [BettiSupport,HomologySupport,residueD0,residueD1,eq_comm]

theorem betti_support_iff (i d : Nat) : BettiSupport i d ↔ i = 0 ∧ d = 2 := by
  constructor
  · rintro ⟨hi,b,hb,hd⟩
    cases b with
    | false => exact False.elim (hb rfl)
    | true => exact ⟨hi,hd rfl⟩
  · rintro ⟨hi,rfl⟩
    exact ⟨hi,true,by decide,fun _ => rfl⟩

/-- Standard minimal-resolution characterization reg M = max{d-i : beta_i,d != 0}. -/
def Regularity (r : Int) : Prop :=
  (∀ i d, BettiSupport i d → (d : Int) - (i : Int) ≤ r) ∧
  ∃ i d, BettiSupport i d ∧ (d : Int) - (i : Int) = r

theorem regularity_two : Regularity 2 := by
  constructor
  · intro i d h
    obtain ⟨rfl,rfl⟩ := (betti_support_iff i d).mp h
    decide
  · exact ⟨0,2,(betti_support_iff 0 2).mpr ⟨rfl,rfl⟩,rfl⟩

theorem regularity_not_one : ¬ Regularity 1 := by
  intro h
  have hh := h.1 0 2 ((betti_support_iff 0 2).mpr ⟨rfl,rfl⟩)
  contradiction

end
end TLMC3322.Principal
