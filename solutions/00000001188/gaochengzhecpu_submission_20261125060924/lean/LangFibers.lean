import Std

namespace LangFibers

universe u v

/-- The group laws used in the torsor argument. -/
class GroupLaws (G : Type u) extends Mul G, OfNat G 1 where
  inverse : G → G
  assoc : ∀ a b c : G, (a*b)*c = a*(b*c)
  one_mul : ∀ a : G, 1*a = a
  mul_one : ∀ a : G, a*1 = a
  inverse_mul : ∀ a : G, inverse a*a = 1
  mul_inverse : ∀ a : G, a*inverse a = 1

local postfix:max "⁻¹" => GroupLaws.inverse

structure Bijection (A : Type u) (B : Type v) where
  forward : A → B
  backward : B → A
  leftInverse : ∀ a, backward (forward a) = a
  rightInverse : ∀ b, forward (backward b) = b

section Group

variable {G : Type u} [GroupLaws G]

def lang (F : G → G) (x : G) : G := x⁻¹ * F x

def FixedPoints (F : G → G) := {h : G // F h = h}
def Fiber (F : G → G) (z : G) := {x : G // lang F x = z}

theorem lang_eq_iff (F : G → G) (x z : G) : lang F x = z ↔ F x = x*z := by
  constructor
  · intro h
    have h' := congrArg (x * ·) h
    change x*(lang F x) = x*z at h'
    rw [lang, ← GroupLaws.assoc, GroupLaws.mul_inverse, GroupLaws.one_mul] at h'
    exact h'
  · intro h
    rw [lang, h, ← GroupLaws.assoc, GroupLaws.inverse_mul, GroupLaws.one_mul]

private theorem cancel_right {a b c : G} (h : a*c = b*c) : a = b := by
  have he := congrArg (· * c⁻¹) h
  simpa only [GroupLaws.assoc, GroupLaws.mul_inverse, GroupLaws.mul_one] using he

/-- Translation by a chosen base point identifies fixed points with the fiber. -/
def fiber_bijection (F : G → G) (map_mul : ∀ a b, F (a*b) = F a * F b)
    (z : G) (x : Fiber F z) : Bijection (FixedPoints F) (Fiber F z) where
  forward h := ⟨h.val*x.val, by
    apply (lang_eq_iff F _ z).mpr
    rw [map_mul, h.property, (lang_eq_iff F _ z).mp x.property, GroupLaws.assoc]⟩
  backward y := ⟨y.val*x.val⁻¹, by
    have hmul : (y.val*x.val⁻¹)*x.val = y.val := by
      rw [GroupLaws.assoc, GroupLaws.inverse_mul, GroupLaws.mul_one]
    apply cancel_right (c := F x.val)
    rw [← map_mul, hmul, (lang_eq_iff F _ z).mp x.property, ← GroupLaws.assoc, hmul]
    exact (lang_eq_iff F _ z).mp y.property⟩
  leftInverse h := by
    apply Subtype.ext
    change (h.val*x.val)*x.val⁻¹ = h.val
    rw [GroupLaws.assoc, GroupLaws.mul_inverse, GroupLaws.mul_one]
  rightInverse y := by
    apply Subtype.ext
    change (y.val*x.val⁻¹)*x.val = y.val
    rw [GroupLaws.assoc, GroupLaws.inverse_mul, GroupLaws.mul_one]

theorem nonempty_fibers_uniform (F : G → G) (map_mul : ∀ a b, F (a*b) = F a * F b)
    (a b : G) (x : Fiber F a) (y : Fiber F b) : Nonempty (Bijection (Fiber F a) (Fiber F b)) := by
  let p := fiber_bijection F map_mul a x
  let q := fiber_bijection F map_mul b y
  refine ⟨⟨(fun u => q.forward (p.backward u)), (fun v => p.forward (q.backward v)), ?_, ?_⟩⟩
  · intro u
    change p.forward (q.backward (q.forward (p.backward u))) = u
    rw [q.leftInverse, p.rightInverse]
  · intro v
    change q.forward (p.backward (p.forward (q.backward v))) = v
    rw [p.leftInverse, q.rightInverse]

def uniform_all_targets (F : G → G) : Prop :=
  ∀ a b, Nonempty (Bijection (Fiber F a) (Fiber F b))

end Group

/-- `false` is the identity in the split two-element group. -/
local instance : GroupLaws Bool where
  mul := Bool.xor
  ofNat := false
  inverse := id
  assoc a b c := by cases a <;> cases b <;> cases c <;> rfl
  one_mul a := by cases a <;> rfl
  mul_one a := by cases a <;> rfl
  inverse_mul a := by cases a <;> rfl
  mul_inverse a := by cases a <;> rfl

def mu2Point (a : Bool) : Nat := if a then 2 else 1

theorem mu2_points_over_f3 (r : Fin 3) : r.val*r.val % 3 = 1 ↔
    ∃ a : Bool, mu2Point a = r.val := by
  have h : r = 0 ∨ r = 1 ∨ r = 2 := by
    simp only [Fin.ext_iff]
    have := r.isLt
    omega
  rcases h with rfl | rfl | rfl <;> decide

theorem mu2_multiplication (a b : Bool) : mu2Point (a*b) = (mu2Point a * mu2Point b)%3 := by
  cases a <;> cases b <;> decide

def frobenius : Bool → Bool := id

theorem mu2_frobenius (a : Bool) : mu2Point (frobenius a) = (mu2Point a)^3%3 := by
  cases a <;> decide

def fiberPoints (target : Bool) : List Bool :=
  [false, true].filter fun x => lang frobenius x == target

theorem fiber_enumeration (target x : Bool) :
    x ∈ fiberPoints target ↔ lang frobenius x = target := by
  cases target <;> cases x <;> decide

theorem exact_fiber_counts : (fiberPoints false).length = 2 ∧ (fiberPoints true).length = 0 := by
  decide

theorem all_target_uniformity_false : ¬ uniform_all_targets frobenius := by
  intro hu
  obtain ⟨b⟩ := hu false true
  have y := b.forward ⟨false, by decide⟩
  have h := y.property
  have hmem := (fiber_enumeration true y.val).mpr h
  have hempty : fiberPoints true = [] := by decide
  rw [hempty] at hmem
  exact List.not_mem_nil hmem

theorem split_mu2_counterexample :
    (∀ a b : Bool, frobenius (a*b) = frobenius a * frobenius b) ∧
    (fiberPoints false).length = 2 ∧ (fiberPoints true).length = 0 ∧
    ¬ uniform_all_targets frobenius :=
  ⟨fun _ _ => rfl, exact_fiber_counts.1, exact_fiber_counts.2, all_target_uniformity_false⟩

#print axioms fiber_bijection
#print axioms nonempty_fibers_uniform
#print axioms exact_fiber_counts
#print axioms split_mu2_counterexample

end LangFibers
