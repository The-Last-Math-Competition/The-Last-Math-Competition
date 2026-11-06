import TriangleModule
import ThreeExtras

namespace TLMC3322.Triangle
open ThreePoly
noncomputable section

def Hom2 (v : Free2) (d : Nat) : Prop :=
  ShiftHomogeneous v.1 3 d ∧ ShiftHomogeneous v.2 3 d

def Hom3 (v : Free3) (d : Nat) : Prop :=
  ShiftHomogeneous v.1 2 d ∧ ShiftHomogeneous v.2.1 2 d ∧ ShiftHomogeneous v.2.2 2 d

theorem shift_add {a b : Poly} {s d : Nat}
    (ha : ShiftHomogeneous a s d) (hb : ShiftHomogeneous b s d) :
    ShiftHomogeneous (add a b) s d := by
  intro i j k h
  cases h1 : a.coeff i j k with
  | true => exact ha i j k h1
  | false =>
    have h2 : b.coeff i j k = true := by simpa [h1] using h
    exact hb i j k h2

theorem differential1_homogeneous (v : Free3) (d : Nat) (h : Hom3 v d) :
    Homogeneous (differential1 v) d := by
  have ha : ShiftHomogeneous (xMul (yMul v.1)) 0 d := by
    apply (xMul_shift_homogeneous_iff _ 0 d).mpr
    exact (yMul_shift_homogeneous_iff _ 1 d).mpr h.1
  have hb : ShiftHomogeneous (xMul (zMul v.2.1)) 0 d := by
    apply (xMul_shift_homogeneous_iff _ 0 d).mpr
    exact (zMul_shift_homogeneous_iff _ 1 d).mpr h.2.1
  have hc : ShiftHomogeneous (yMul (zMul v.2.2)) 0 d := by
    apply (yMul_shift_homogeneous_iff _ 0 d).mpr
    exact (zMul_shift_homogeneous_iff _ 1 d).mpr h.2.2
  exact shift_add (shift_add ha hb) hc

theorem differential2_homogeneous_iff (v : Free2) (d : Nat) :
    Hom3 (differential2 v) d ↔ Hom2 v d := by
  constructor
  · intro h
    exact ⟨(yMul_shift_homogeneous_iff _ 2 d).mp h.2.1,
      (xMul_shift_homogeneous_iff _ 2 d).mp h.2.2⟩
  · intro h
    exact ⟨(zMul_shift_homogeneous_iff _ 2 d).mpr (shift_add h.1 h.2),
      (yMul_shift_homogeneous_iff _ 2 d).mpr h.1,
      (xMul_shift_homogeneous_iff _ 2 d).mpr h.2⟩

def QuotientHomogeneous (q : QuotientModule) (d : Nat) : Prop :=
  ∃ p, Homogeneous p d ∧ project p = q

theorem projection_homogeneous (p : Poly) (d : Nat) (h : Homogeneous p d) :
    QuotientHomogeneous (project p) d := ⟨p,h,rfl⟩

abbrev Residue2 := Bool × Bool
abbrev Residue3 := Bool × Bool × Bool

def reduce0 (p : Poly) : Bool := p.coeff 0 0 0
def reduce2 (v : Free2) : Residue2 := (reduce0 v.1,reduce0 v.2)
def reduce3 (v : Free3) : Residue3 := (reduce0 v.1,reduce0 v.2.1,reduce0 v.2.2)
def lift2 (v : Residue2) : Free2 := (constant v.1,constant v.2)
def lift3 (v : Residue3) : Free3 := (constant v.1,constant v.2.1,constant v.2.2)

def residueZero2 : Residue2 := (false,false)
def residueZero3 : Residue3 := (false,false,false)

@[simp] theorem reduce2_lift (v : Residue2) : reduce2 (lift2 v) = v := by
  rcases v with ⟨a,b⟩; cases a <;> cases b <;> rfl
@[simp] theorem reduce3_lift (v : Residue3) : reduce3 (lift3 v) = v := by
  rcases v with ⟨a,b,c⟩; cases a <;> cases b <;> cases c <;> rfl

def MaximalFree2 (v : Free2) : Prop := Maximal v.1 ∧ Maximal v.2
def MaximalFree3 (v : Free3) : Prop := Maximal v.1 ∧ Maximal v.2.1 ∧ Maximal v.2.2

theorem residue_kernel2 (v : Free2) : reduce2 v = residueZero2 ↔ MaximalFree2 v := by
  simp only [reduce2,residueZero2,MaximalFree2,Maximal,reduce0,Prod.mk.injEq]

theorem residue_kernel3 (v : Free3) : reduce3 v = residueZero3 ↔ MaximalFree3 v := by
  simp only [reduce3,residueZero3,MaximalFree3,Maximal,reduce0,Prod.mk.injEq]

def f0 : Free2 := (one,zero)
def f1 : Free2 := (zero,one)

/-- These are exactly mF: sums of maximal-ideal coefficients times free basis vectors. -/
theorem maximal_free2_generated (v : Free2) : MaximalFree2 v ↔
    ∃ a b, Maximal a ∧ Maximal b ∧ v = add2 (mul2 a f0) (mul2 b f1) := by
  constructor
  · intro h
    exact ⟨v.1,v.2,h.1,h.2,by simp [add2,mul2,f0,f1]⟩
  · rintro ⟨a,b,ha,hb,rfl⟩
    simpa [add2,mul2,f0,f1,MaximalFree2] using And.intro ha hb

theorem maximal_free3_generated (v : Free3) : MaximalFree3 v ↔
    ∃ a b c, Maximal a ∧ Maximal b ∧ Maximal c ∧
      v = add3 (add3 (mul3 a e0) (mul3 b e1)) (mul3 c e2) := by
  constructor
  · intro h
    exact ⟨v.1,v.2.1,v.2.2,h.1,h.2.1,h.2.2,by simp [add3,mul3,e0,e1,e2]⟩
  · rintro ⟨a,b,c,ha,hb,hc,rfl⟩
    simpa [add3,mul3,e0,e1,e2,MaximalFree3] using And.intro ha (And.intro hb hc)

theorem differential1_minimal (v : Free3) : Maximal (differential1 v) := rfl

theorem differential2_minimal (v : Free2) : MaximalFree3 (differential2 v) :=
  ⟨rfl,rfl,rfl⟩

theorem reduced_differential1_zero (v : Free3) : reduce0 (differential1 v) = false := rfl

theorem reduced_differential2_zero (v : Free2) : reduce3 (differential2 v) = residueZero3 := rfl

/-- Residue degrees inherited from the actual shifted free summands. -/
def ReducedHomogeneous (b : Bool) (s d : Nat) : Prop := b = true → d = s
def ReducedHom2 (v : Residue2) (s d : Nat) : Prop :=
  ReducedHomogeneous v.1 s d ∧ ReducedHomogeneous v.2 s d
def ReducedHom3 (v : Residue3) (s d : Nat) : Prop :=
  ReducedHomogeneous v.1 s d ∧ ReducedHomogeneous v.2.1 s d ∧ ReducedHomogeneous v.2.2 s d

theorem reduce_respects_shift (p : Poly) (s d : Nat) (h : ShiftHomogeneous p s d) :
    ReducedHomogeneous (reduce0 p) s d := by
  intro hp
  have hh := h 0 0 0 hp
  omega

theorem constant_respects_shift (b : Bool) (s d : Nat) (h : ReducedHomogeneous b s d) :
    ShiftHomogeneous (constant b) s d := by
  intro i j k hp
  cases b with
  | false => cases hp
  | true =>
    have hh : i=0 ∧ j=0 ∧ k=0 := by simpa using hp
    have hd := h rfl
    omega

theorem reduce2_homogeneous (v : Free2) (d : Nat) (h : Hom2 v d) :
    ReducedHom2 (reduce2 v) 3 d :=
  ⟨reduce_respects_shift v.1 3 d h.1,reduce_respects_shift v.2 3 d h.2⟩

theorem reduce3_homogeneous (v : Free3) (d : Nat) (h : Hom3 v d) :
    ReducedHom3 (reduce3 v) 2 d :=
  ⟨reduce_respects_shift v.1 2 d h.1,
   reduce_respects_shift v.2.1 2 d h.2.1,reduce_respects_shift v.2.2 2 d h.2.2⟩

theorem lift2_homogeneous (v : Residue2) (d : Nat) (h : ReducedHom2 v 3 d) :
    Hom2 (lift2 v) d :=
  ⟨constant_respects_shift v.1 3 d h.1,constant_respects_shift v.2 3 d h.2⟩

theorem lift3_homogeneous (v : Residue3) (d : Nat) (h : ReducedHom3 v 2 d) :
    Hom3 (lift3 v) d :=
  ⟨constant_respects_shift v.1 2 d h.1,
   constant_respects_shift v.2.1 2 d h.2.1,constant_respects_shift v.2.2 2 d h.2.2⟩

/-- Full exact minimal graded free resolution of the ACTUAL quotient module:
0 -> R(-3)^2 -> R(-2)^3 -> R -> R/I -> 0. -/
def VerifiedMinimalResolution : Prop :=
  IsEdgeIdeal InIdeal ∧
  (∀ q, ∃ p, project p = q) ∧
  (∀ p, project p = project zero ↔ ∃ v, differential1 v = p) ∧
  (∀ v, differential1 v = zero ↔ ∃ u, differential2 u = v) ∧
  (∀ u v, differential2 u = differential2 v → u = v) ∧
  (∀ r v, differential1 (mul3 r v) = mul r (differential1 v)) ∧
  (∀ r v, differential2 (mul2 r v) = mul3 r (differential2 v)) ∧
  (∀ v d, Hom3 v d → Homogeneous (differential1 v) d) ∧
  (∀ v d, Hom3 (differential2 v) d ↔ Hom2 v d) ∧
  (∀ v, Maximal (differential1 v)) ∧
  (∀ v, MaximalFree3 (differential2 v))

theorem verified_minimal_resolution : VerifiedMinimalResolution := by
  refine ⟨actual_edge_ideal,projection_surjective,?_,kernel_exact,
    fun _ _ h => differential2_injective h,differential1_linear,differential2_linear,
    differential1_homogeneous,differential2_homogeneous_iff,
    differential1_minimal,differential2_minimal⟩
  intro p
  rw [projection_kernel]
  constructor
  · rintro ⟨v,h⟩; exact ⟨v,h.symm⟩
  · rintro ⟨v,h⟩; exact ⟨v,h.symm⟩

end
end TLMC3322.Triangle
