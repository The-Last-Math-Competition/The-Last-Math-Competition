import Std
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace TLMC1043
abbrev F := Fin 11
/-- Zero-fixed reciprocal on the prime field F_11. -/
def inv (x : F) : F :=
  match x.val with
  | 0 => 0 | 1 => 1 | 2 => 6 | 3 => 4 | 4 => 3 | 5 => 9
  | 6 => 2 | 7 => 8 | 8 => 7 | 9 => 5 | _ => 10
/-- The chosen permutation is (7 8)(9 10). -/
def witness (x : F) : F :=
  if x = 7 then 8 else if x = 8 then 7 else if x = 9 then 10 else if x = 10 then 9 else x

theorem inv_power : ∀ x : F, inv x = x ^ 9 := by decide
theorem inv_involutive : ∀ x : F, inv (inv x) = x := by decide
theorem inv_nonzero : ∀ a : F, a ≠ 0 → inv a ≠ 0 := by decide
theorem inv_scale : ∀ a y : F, a ≠ 0 → inv (inv a * y) = a * inv y := by decide
theorem mul_distrib : ∀ a b c : F, a * (b + c) = a*b + a*c := by decide
theorem add_assoc : ∀ a b c : F, (a+b)+c = a+(b+c) := by decide
theorem mul_assoc : ∀ a b c : F, (a*b)*c = a*(b*c) := by decide
theorem affine_consistency : ∀ a b x : F,
    ((a*1+b)-(a*0+b))*x+(a*0+b) = a*x+b := by decide
theorem strip_layer : ∀ y b : F, inv ((inv y+b)-b) = y := by decide
theorem witness_involutive : ∀ x : F, witness (witness x) = x := by decide
theorem witness_bijective : (∀ x y, witness x = witness y → x = y) ∧
    (∀ y, ∃ x, witness x = y) := by
  constructor
  · intro x y h
    have q := congrArg witness h
    simpa only [witness_involutive] using q
  · intro y
    exact ⟨witness y, witness_involutive y⟩

/-- k counts inversions, and every affine slope is explicitly nonzero.
This inductive syntax is precisely an alternating affine/inversion expression. -/
inductive Represents : Nat → (F → F) → Prop where
  | affine (a b : F) (ha : a ≠ 0) : Represents 0 (fun x => a*x+b)
  | step {k : Nat} {f : F → F} (a b : F) (ha : a ≠ 0)
      (h : Represents k f) : Represents (k+1) (fun x => a * inv (f x) + b)

/-- The standard rank-at-most predicate; no numeric minimum is assumed. -/
def RankAtMost (n : Nat) (f : F → F) : Prop := ∃ k, k ≤ n ∧ Represents k f

/-- Outer layers are listed first. Zero translation coefficients are allowed. -/
def normal : List F → F → F → F → F
  | [], a, c, x => a*x+c
  | b::bs, a, c, x => inv (normal bs a c x)+b

/-- Scaling/translation closure, proved for arbitrary list length. -/
theorem normal_affine (bs : List F) (a c s t : F) (hs : s ≠ 0) :
    ∃ bs' a' c', bs'.length = bs.length ∧
      ∀ x, normal bs' a' c' x = s * normal bs a c x + t := by
  induction bs generalizing a c s t with
  | nil =>
    refine ⟨[], s*a, s*c+t, rfl, ?_⟩
    intro x
    simp only [normal]
    rw [mul_distrib, ← mul_assoc, add_assoc]
  | cons b bs ih =>
    obtain ⟨cs, a', c', hlen, heq⟩ := ih a c (inv s) 0 (inv_nonzero s hs)
    refine ⟨(s*b+t)::cs, a', c', ?_, ?_⟩
    · simp only [List.length_cons, hlen]
    · intro x
      simp only [normal, heq, Fin.add_zero]
      rw [inv_scale s _ hs, mul_distrib, add_assoc]

/-- Every arbitrary affine/inversion expression has a complete normalized form. -/
theorem complete_normal_form {k : Nat} {f : F → F} (h : Represents k f) :
    ∃ bs a c, bs.length = k ∧ ∀ x, normal bs a c x = f x := by
  induction h with
  | affine a b ha => exact ⟨[], a, b, rfl, fun _ => rfl⟩
  | @step k f a b ha h ih =>
    obtain ⟨bs, u, v, hlen, heq⟩ := ih
    obtain ⟨cs, u', v', hlen', heq'⟩ :=
      normal_affine bs u v (inv a) 0 (inv_nonzero a ha)
    refine ⟨b::cs, u', v', ?_, ?_⟩
    · simp only [List.length_cons, hlen', hlen]
    · intro x
      simp only [normal, heq', Fin.add_zero, heq]
      rw [inv_scale a _ ha]

/-- Strip outer layers, in their specified order. -/
def strip : List F → (F → F) → (F → F)
  | [], f => f
  | b::bs, f => strip bs (fun x => inv (f x-b))

theorem strip_normal (bs : List F) (a c : F) :
    strip bs (normal bs a c) = (fun x => a*x+c) := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
    simp only [strip, normal]
    have h : (fun x => inv ((inv (normal bs a c x)+b)-b)) = normal bs a c := by
      funext x
      exact strip_layer _ _
    rw [h]
    exact ih

def NotAffine (f : F → F) : Prop := ∃ x, f x ≠ (f 1-f 0)*x+f 0

theorem affine_not_NotAffine (a c : F) : ¬ NotAffine (fun x => a*x+c) := by
  intro ⟨x, hx⟩
  exact hx (affine_consistency a c x).symm

end TLMC1043
