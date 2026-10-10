import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Data.Int.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FinCases

set_option maxRecDepth 4096
namespace Coordinate4846

@[ext] structure G where
  p : ℤ
  q : ℤ
  r : ℤ
  s : ℤ
  t : ℤ
  a : ℤ
  b : ℤ
  c : ℤ
  deriving DecidableEq

def product (u v : G) : G :=
  ⟨u.p+v.p, u.q+v.q, u.r+v.r, u.s+v.s+u.p*v.q,
   u.t+v.t+u.q*v.r, u.a+v.a, u.b+v.b,
   u.c+v.c+u.p*v.t+u.s*v.r+u.a*v.b⟩
def unit : G := ⟨0,0,0,0,0,0,0,0⟩
def inverse (u : G) : G :=
  ⟨-u.p,-u.q,-u.r,-u.s+u.p*u.q,-u.t+u.q*u.r,-u.a,-u.b,
   -u.c+u.p*u.t+u.s*u.r-u.p*u.q*u.r+u.a*u.b⟩

instance : Group G where
  mul := product
  one := unit
  inv := inverse
  mul_assoc := by
    intro u v w
    change product (product u v) w = product u (product v w)
    ext <;> simp [product] <;> ring
  one_mul := by
    intro u; change product unit u = u
    ext <;> simp [product,unit]
  mul_one := by
    intro u; change product u unit = u
    ext <;> simp [product,unit]
  inv_mul_cancel := by
    intro u; change product (inverse u) u = unit
    ext <;> simp [product,inverse,unit] <;> ring

theorem mul_def (u v : G) : u*v = product u v := rfl
theorem one_def : (1:G) = unit := rfl
theorem inv_def (u : G) : u⁻¹ = inverse u := rfl

def X (n : ℤ) : G := ⟨n,0,0,0,0,0,0,0⟩
def Y (n : ℤ) : G := ⟨0,n,0,0,0,0,0,0⟩
def Z (n : ℤ) : G := ⟨0,0,n,0,0,0,0,0⟩
def P (n : ℤ) : G := ⟨0,0,0,n,0,0,0,0⟩
def Q (n : ℤ) : G := ⟨0,0,0,0,n,0,0,0⟩
def A (n : ℤ) : G := ⟨0,0,0,0,0,n,0,0⟩
def B (n : ℤ) : G := ⟨0,0,0,0,0,0,n,0⟩
def C (n : ℤ) : G := ⟨0,0,0,0,0,0,0,n⟩
def comm (u v : G) : G := u*v*u⁻¹*v⁻¹

theorem comm_XY (x y : ℤ) : comm (X x) (Y y) = P (x*y) := by
  ext <;> simp [mul_def,one_def,inv_def,comm,product,inverse,X,Y,P] <;> ring
theorem comm_YZ (y z : ℤ) : comm (Y y) (Z z) = Q (y*z) := by
  ext <;> simp [mul_def,one_def,inv_def,comm,product,inverse,Y,Z,Q] <;> ring
theorem comm_PZ (p z : ℤ) : comm (P p) (Z z) = C (p*z) := by
  ext <;> simp [mul_def,one_def,inv_def,comm,product,inverse,P,Z,C] <;> ring
theorem comm_XQ (x q : ℤ) : comm (X x) (Q q) = C (x*q) := by
  ext <;> simp [mul_def,one_def,inv_def,comm,product,inverse,X,Q,C] <;> ring
theorem comm_AB (a b : ℤ) : comm (A a) (B b) = C (a*b) := by
  ext <;> simp [mul_def,one_def,inv_def,comm,product,inverse,A,B,C] <;> ring
theorem nested_comm (m : ℤ) : comm (comm (X m) (Y m)) (Z m) = C (m^3) := by
  rw [comm_XY,comm_PZ]; congr 1; ring
theorem C_central (u : G) (k : ℤ) : u*C k = C k*u := by
  ext <;> simp [mul_def,product,C] <;> ring
theorem C_injective : Function.Injective C := by
  intro x y h; exact congrArg G.c h
theorem normalForm (u : G) :
  X u.p * Y u.q * Z u.r * P (u.s-u.p*u.q) * Q (u.t-u.q*u.r) *
  A u.a * B u.b * C (u.c-u.p*u.t-u.a*u.b) = u := by
  ext <;> simp [mul_def,product,X,Y,Z,P,Q,A,B,C] <;> ring

def H : Subgroup G where
  carrier := {u | u.p=0 ∧ u.q=0 ∧ u.r=0 ∧ u.s=0 ∧ u.t=0}
  one_mem' := by simp [one_def,unit]
  mul_mem' := by
    intro u v hu hv
    rcases hu with ⟨hp,hq,hr,hs,ht⟩
    rcases hv with ⟨hP,hQ,hR,hS,hT⟩
    simp [mul_def,product,hp,hq,hr,hs,ht,hP,hQ,hR,hS,hT]
  inv_mem' := by
    intro u hu
    rcases hu with ⟨hp,hq,hr,hs,ht⟩
    simp [inv_def,inverse,hp,hq,hr,hs,ht]

@[simp] theorem mem_H (u : G) : u ∈ H ↔
  u.p=0 ∧ u.q=0 ∧ u.r=0 ∧ u.s=0 ∧ u.t=0 := Iff.rfl
theorem A_mem (n : ℤ) : A n ∈ H := by simp [A]
theorem B_mem (n : ℤ) : B n ∈ H := by simp [B]
theorem C_mem (n : ℤ) : C n ∈ H := by simp [C]
theorem H_normalForm (u : G) (hu : u ∈ H) :
  A u.a * B u.b * C (u.c-u.a*u.b) = u := by
  rcases hu with ⟨hp,hq,hr,hs,ht⟩
  ext <;> simp [mul_def,product,A,B,C,hp,hq,hr,hs,ht] <;> ring

@[ext] structure Heisenberg where
  a : ℤ
  b : ℤ
  c : ℤ
  deriving DecidableEq
def Heisenberg.product (u v : Heisenberg) : Heisenberg :=
  ⟨u.a+v.a,u.b+v.b,u.c+v.c+u.a*v.b⟩
def Heisenberg.inverse (u : Heisenberg) : Heisenberg :=
  ⟨-u.a,-u.b,-u.c+u.a*u.b⟩
instance : Group Heisenberg where
  mul := Heisenberg.product
  one := ⟨0,0,0⟩
  inv := Heisenberg.inverse
  mul_assoc := by
    intro u v w
    change Heisenberg.product (Heisenberg.product u v) w = Heisenberg.product u (Heisenberg.product v w)
    ext <;> simp [Heisenberg.product] <;> ring
  one_mul := by
    intro u; change Heisenberg.product ⟨0,0,0⟩ u = u
    ext <;> simp [Heisenberg.product]
  mul_one := by
    intro u; change Heisenberg.product u ⟨0,0,0⟩ = u
    ext <;> simp [Heisenberg.product]
  inv_mul_cancel := by
    intro u; change Heisenberg.product (Heisenberg.inverse u) u = ⟨0,0,0⟩
    ext <;> simp [Heisenberg.product,Heisenberg.inverse] <;> ring
def inclusion : Heisenberg →* G where
  toFun := fun u => ⟨0,0,0,0,0,u.a,u.b,u.c⟩
  map_one' := rfl
  map_mul' := by
    intro u v
    change (⟨0,0,0,0,0,u.a+v.a,u.b+v.b,u.c+v.c+u.a*v.b⟩ : G) =
      product ⟨0,0,0,0,0,u.a,u.b,u.c⟩ ⟨0,0,0,0,0,v.a,v.b,v.c⟩
    ext <;> simp [product]
@[simp] theorem inclusion_apply (u : Heisenberg) :
  inclusion u = ⟨0,0,0,0,0,u.a,u.b,u.c⟩ := rfl
theorem inclusion_injective : Function.Injective inclusion := by
  intro u v h
  have ha := congrArg G.a h
  have hb := congrArg G.b h
  have hc := congrArg G.c h
  exact Heisenberg.ext ha hb hc
theorem inclusion_range : inclusion.range = H := by
  ext u
  constructor
  · rintro ⟨v,rfl⟩; simp
  · intro hu
    rcases hu with ⟨hp,hq,hr,hs,ht⟩
    refine ⟨⟨u.a,u.b,u.c⟩, ?_⟩
    ext <;> simp [hp,hq,hr,hs,ht]

end Coordinate4846
