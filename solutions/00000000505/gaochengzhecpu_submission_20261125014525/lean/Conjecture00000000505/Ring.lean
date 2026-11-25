namespace Conjecture00000000505

/-- Commutative ring with identity, axiomatized from first principles in Core Lean 4. -/
class CAlgRing (R : Type u) where
  zero : R
  one : R
  add : R → R → R
  mul : R → R → R
  neg : R → R
  add_assoc : ∀ a b c : R, add (add a b) c = add a (add b c)
  add_comm : ∀ a b : R, add a b = add b a
  zero_add : ∀ a : R, add zero a = a
  add_left_neg : ∀ a : R, add (neg a) a = zero
  mul_assoc : ∀ a b c : R, mul (mul a b) c = mul a (mul b c)
  mul_comm : ∀ a b : R, mul a b = mul b a
  one_mul : ∀ a : R, mul one a = a
  left_distrib : ∀ a b c : R, mul a (add b c) = add (mul a b) (mul a c)

instance [CAlgRing R] : OfNat R 0 := ⟨CAlgRing.zero⟩
instance [CAlgRing R] : OfNat R 1 := ⟨CAlgRing.one⟩
instance [CAlgRing R] : Add R := ⟨CAlgRing.add⟩
instance [CAlgRing R] : Mul R := ⟨CAlgRing.mul⟩
instance [CAlgRing R] : Neg R := ⟨CAlgRing.neg⟩
instance [CAlgRing R] : Sub R := ⟨fun a b => CAlgRing.add a (CAlgRing.neg b)⟩

section RingLemmas
variable {R : Type u} [CAlgRing R]

theorem r_add_assoc (a b c : R) : (a + b) + c = a + (b + c) := CAlgRing.add_assoc a b c
theorem r_add_comm (a b : R) : a + b = b + a := CAlgRing.add_comm a b
theorem r_zero_add (a : R) : (0 : R) + a = a := CAlgRing.zero_add a
theorem r_add_zero (a : R) : a + (0 : R) = a := by
  rw [r_add_comm, r_zero_add]
theorem r_add_left_neg (a : R) : (-a) + a = 0 := CAlgRing.add_left_neg a
theorem r_add_right_neg (a : R) : a + (-a) = 0 := by
  rw [r_add_comm, r_add_left_neg]
theorem r_sub_def (a b : R) : a - b = a + (-b) := rfl

theorem r_add_left_cancel {a b c : R} (h : a + b = a + c) : b = c := by
  have h1 : (-a) + (a + b) = (-a) + (a + c) := congrArg (fun x => (-a) + x) h
  rw [← r_add_assoc, ← r_add_assoc, r_add_left_neg, r_zero_add, r_zero_add] at h1
  exact h1

theorem r_add_right_cancel {a b c : R} (h : b + a = c + a) : b = c := by
  apply r_add_left_cancel (a := a)
  rw [r_add_comm a b, r_add_comm a c]
  exact h

theorem r_neg_zero : (-(0 : R)) = 0 := by
  apply r_add_right_cancel (a := (0 : R))
  rw [r_add_left_neg, r_zero_add]

theorem r_neg_neg (a : R) : -(-a) = a := by
  apply r_add_right_cancel (a := -a)
  rw [r_add_left_neg, r_add_right_neg]

theorem r_neg_add (a b : R) : -(a + b) = (-a) + (-b) := by
  apply r_add_right_cancel (a := a + b)
  rw [r_add_left_neg]
  symm
  calc
    ((-a) + (-b)) + (a + b)
      = (-a) + ((-b) + (b + a)) := by rw [r_add_comm a b, r_add_assoc]
    _ = (-a) + (((-b) + b) + a) := by rw [← r_add_assoc (-b) b a]
    _ = (-a) + ((0 : R) + a) := by rw [r_add_left_neg]
    _ = (-a) + a := by rw [r_zero_add]
    _ = 0 := r_add_left_neg a

theorem r_sub_self (a : R) : a - a = 0 := r_add_right_neg a

theorem r_eq_of_sub_eq_zero {a b : R} (h : a - b = 0) : a = b := by
  apply r_add_right_cancel (a := -b)
  rw [r_add_right_neg]
  exact h

theorem r_mul_assoc (a b c : R) : (a * b) * c = a * (b * c) := CAlgRing.mul_assoc a b c
theorem r_mul_comm (a b : R) : a * b = b * a := CAlgRing.mul_comm a b
theorem r_one_mul (a : R) : (1 : R) * a = a := CAlgRing.one_mul a
theorem r_mul_one (a : R) : a * (1 : R) = a := by rw [r_mul_comm, r_one_mul]
theorem r_left_distrib (a b c : R) : a * (b + c) = a * b + a * c := CAlgRing.left_distrib a b c
theorem r_right_distrib (a b c : R) : (a + b) * c = a * c + b * c := by
  rw [r_mul_comm, r_left_distrib, r_mul_comm c a, r_mul_comm c b]

theorem r_mul_zero (a : R) : a * (0 : R) = 0 := by
  apply r_add_left_cancel (a := a * (0 : R))
  rw [← r_left_distrib, r_add_zero, r_add_zero]

theorem r_zero_mul (a : R) : (0 : R) * a = 0 := by
  rw [r_mul_comm, r_mul_zero]

theorem r_mul_neg (a b : R) : a * (-b) = -(a * b) := by
  apply r_add_left_cancel (a := a * b)
  rw [← r_left_distrib, r_add_right_neg, r_mul_zero, r_add_right_neg]

theorem r_neg_mul (a b : R) : (-a) * b = -(a * b) := by
  rw [r_mul_comm, r_mul_neg, r_mul_comm]

theorem r_mul_sub (a b c : R) : a * (b - c) = a * b - a * c := by
  change a * (b + (-c)) = a * b + (-(a * c))
  rw [r_left_distrib, r_mul_neg]

theorem r_sub_mul (a b c : R) : (a - b) * c = a * c - b * c := by
  change (a + (-b)) * c = a * c + (-(b * c))
  rw [r_right_distrib, r_neg_mul]

/-- Natural-number power in a commutative ring. -/
def rpow (a : R) : Nat → R
  | 0 => 1
  | n + 1 => a * rpow a n

theorem rpow_zero (a : R) : rpow a 0 = 1 := rfl
theorem rpow_succ (a : R) (n : Nat) : rpow a (n + 1) = a * rpow a n := rfl
theorem rpow_one (a : R) : rpow a 1 = a := by
  change a * 1 = a
  exact r_mul_one a

theorem zero_rpow {m : Nat} (hm : 1 ≤ m) : rpow (0 : R) m = 0 := by
  cases m with
  | zero => omega
  | succ k =>
    change (0 : R) * rpow 0 k = 0
    exact r_zero_mul _

theorem mul_rpow (a b : R) : ∀ n : Nat, rpow (a * b) n = rpow a n * rpow b n
  | 0 => by
    change (1 : R) = 1 * 1
    rw [r_one_mul]
  | n + 1 => by
    change (a * b) * rpow (a * b) n = (a * rpow a n) * (b * rpow b n)
    rw [mul_rpow a b n]
    calc
      (a * b) * (rpow a n * rpow b n)
        = a * (b * (rpow a n * rpow b n)) := by rw [r_mul_assoc]
      _ = a * ((b * rpow a n) * rpow b n) := by rw [← r_mul_assoc b]
      _ = a * ((rpow a n * b) * rpow b n) := by rw [r_mul_comm b (rpow a n)]
      _ = a * (rpow a n * (b * rpow b n)) := by rw [r_mul_assoc (rpow a n)]
      _ = (a * rpow a n) * (b * rpow b n) := by rw [← r_mul_assoc a]

end RingLemmas

/-- Integral domain predicate (`1 ≠ 0` and no nonzero zero-divisors). -/
structure IsDomain (R : Type u) [CAlgRing R] : Prop where
  one_ne_zero : (1 : R) ≠ 0
  mul_eq_zero : ∀ {a b : R}, a * b = 0 → a = 0 ∨ b = 0

theorem IsDomain.rpow_ne_zero {R : Type u} [CAlgRing R] (hd : IsDomain R)
    {a : R} (ha : a ≠ 0) : ∀ m : Nat, rpow a m ≠ 0
  | 0 => hd.one_ne_zero
  | m + 1 => fun h => by
    cases hd.mul_eq_zero h with
    | inl h1 => exact ha h1
    | inr h2 => exact IsDomain.rpow_ne_zero hd ha m h2

theorem IsDomain.mul_left_cancel {R : Type u} [CAlgRing R] (hd : IsDomain R)
    {a b c : R} (ha : a ≠ 0) (h : a * b = a * c) : b = c := by
  have hsub : a * (b - c) = 0 := by
    rw [r_mul_sub, h, r_sub_self]
  cases hd.mul_eq_zero hsub with
  | inl h1 => exact False.elim (ha h1)
  | inr h2 => exact r_eq_of_sub_eq_zero h2

/-- Field structure extending `CAlgRing` with multiplicative inverses for nonzero elements. -/
class CAlgField (K : Type u) extends CAlgRing K where
  one_ne_zero : (1 : K) ≠ 0
  inv : K → K
  mul_inv_cancel : ∀ a : K, a ≠ 0 → mul a (inv a) = one

theorem CAlgField.isDomain (K : Type u) [CAlgField K] : IsDomain K where
  one_ne_zero := CAlgField.one_ne_zero
  mul_eq_zero := by
    intro a b hab
    by_cases ha : a = 0
    · exact Or.inl ha
    · right
      have hinv : a * CAlgField.inv a = 1 := CAlgField.mul_inv_cancel a ha
      calc
        b = (1 : K) * b := by rw [r_one_mul]
        _ = (CAlgField.inv a * a) * b := by rw [r_mul_comm (CAlgField.inv a) a, hinv]
        _ = CAlgField.inv a * (a * b) := by rw [r_mul_assoc]
        _ = CAlgField.inv a * 0 := by rw [hab]
        _ = 0 := r_mul_zero _

/-- An ideal of a commutative ring `R`. -/
structure Ideal (R : Type u) [CAlgRing R] where
  carrier : R → Prop
  zero_mem : carrier 0
  add_mem : ∀ {a b : R}, carrier a → carrier b → carrier (a + b)
  mul_mem_left : ∀ (r : R) {a : R}, carrier a → carrier (r * a)

instance [CAlgRing R] : Membership R (Ideal R) where
  mem I x := I.carrier x

section IdealLemmas
variable {R : Type u} [CAlgRing R]

theorem Ideal.neg_mem (I : Ideal R) {a : R} (ha : a ∈ I) : (-a) ∈ I := by
  have h : (-1 : R) * a ∈ I := I.mul_mem_left (-1) ha
  have heq : (-1 : R) * a = -a := by rw [r_neg_mul, r_one_mul]
  rw [← heq]
  exact h

theorem Ideal.sub_mem (I : Ideal R) {a b : R} (ha : a ∈ I) (hb : b ∈ I) : a - b ∈ I :=
  I.add_mem ha (I.neg_mem hb)

theorem Ideal.mul_mem_right (I : Ideal R) {a : R} (r : R) (ha : a ∈ I) : a * r ∈ I := by
  rw [r_mul_comm]
  exact I.mul_mem_left r ha

/-- Recursive linear-combination predicate for a finite list of generators. -/
def inSpan : List R → R → Prop
  | [], x => x = 0
  | f :: fs, x => ∃ r y : R, inSpan fs y ∧ x = r * f + y

theorem inSpan_zero : ∀ fs : List R, inSpan fs 0
  | [] => rfl
  | f :: fs => ⟨0, 0, inSpan_zero fs, by rw [r_zero_mul, r_add_zero]⟩

theorem inSpan_add : ∀ {fs : List R} {a b : R}, inSpan fs a → inSpan fs b → inSpan fs (a + b)
  | [], a, b, ha, hb => by
    change a = 0 at ha
    change b = 0 at hb
    change a + b = 0
    rw [ha, hb, r_add_zero]
  | f :: fs, _, _, ⟨r1, y1, hy1, ha⟩, ⟨r2, y2, hy2, hb⟩ => by
    refine ⟨r1 + r2, y1 + y2, inSpan_add hy1 hy2, ?_⟩
    rw [ha, hb, r_right_distrib]
    calc
      (r1 * f + y1) + (r2 * f + y2)
        = r1 * f + (y1 + (r2 * f + y2)) := by rw [r_add_assoc]
      _ = r1 * f + ((r2 * f + y2) + y1) := by rw [r_add_comm y1]
      _ = r1 * f + (r2 * f + (y2 + y1)) := by rw [r_add_assoc (r2 * f)]
      _ = (r1 * f + r2 * f) + (y1 + y2) := by rw [← r_add_assoc (r1 * f), r_add_comm y2 y1]

theorem inSpan_mul_left : ∀ {fs : List R} (c : R) {a : R}, inSpan fs a → inSpan fs (c * a)
  | [], c, a, ha => by
    change a = 0 at ha
    change c * a = 0
    rw [ha, r_mul_zero]
  | f :: fs, c, _, ⟨r, y, hy, ha⟩ => by
    refine ⟨c * r, c * y, inSpan_mul_left c hy, ?_⟩
    rw [ha, r_left_distrib, r_mul_assoc]

/-- The ideal `(f_1, ..., f_r)` generated by a finite list `fs` of ring elements. -/
def Ideal.span (fs : List R) : Ideal R where
  carrier := inSpan fs
  zero_mem := inSpan_zero fs
  add_mem := inSpan_add
  mul_mem_left := inSpan_mul_left

theorem Ideal.mem_span_head (f : R) (fs : List R) : f ∈ Ideal.span (f :: fs) :=
  ⟨1, 0, inSpan_zero fs, by rw [r_one_mul, r_add_zero]⟩

theorem Ideal.mem_span_tail (f : R) {fs : List R} {x : R} (hx : x ∈ Ideal.span fs) :
    x ∈ Ideal.span (f :: fs) :=
  ⟨0, x, hx, by rw [r_zero_mul, r_zero_add]⟩

theorem Ideal.mem_span_of_mem {fs : List R} {g : R} (hg : g ∈ fs) : g ∈ Ideal.span fs := by
  induction fs with
  | nil => cases hg
  | cons f tail ih =>
    cases hg with
    | head => exact Ideal.mem_span_head g tail
    | tail _ hmem => exact Ideal.mem_span_tail f (ih hmem)

theorem Ideal.span_le {fs : List R} {I : Ideal R} (h : ∀ f ∈ fs, f ∈ I) :
    ∀ {x : R}, x ∈ Ideal.span fs → x ∈ I := by
  induction fs with
  | nil =>
    intro x hx
    change x = 0 at hx
    rw [hx]
    exact I.zero_mem
  | cons f tail ih =>
    intro x ⟨r, y, hy, hx⟩
    rw [hx]
    have hf : f ∈ I := h f (List.Mem.head _)
    have hyI : y ∈ I := ih (fun g hg => h g (List.Mem.tail _ hg)) hy
    exact I.add_mem (I.mul_mem_left r hf) hyI

/-- Sum `I + J` of two ideals. -/
def Ideal.sum (I J : Ideal R) : Ideal R where
  carrier x := ∃ a b : R, a ∈ I ∧ b ∈ J ∧ x = a + b
  zero_mem := ⟨0, 0, I.zero_mem, J.zero_mem, by rw [r_add_zero]⟩
  add_mem := by
    intro x y ⟨a1, b1, ha1, hb1, hx⟩ ⟨a2, b2, ha2, hb2, hy⟩
    refine ⟨a1 + a2, b1 + b2, I.add_mem ha1 ha2, J.add_mem hb1 hb2, ?_⟩
    rw [hx, hy]
    calc
      (a1 + b1) + (a2 + b2)
        = a1 + (b1 + (a2 + b2)) := by rw [r_add_assoc]
      _ = a1 + ((a2 + b2) + b1) := by rw [r_add_comm b1]
      _ = a1 + (a2 + (b2 + b1)) := by rw [r_add_assoc a2]
      _ = (a1 + a2) + (b1 + b2) := by rw [← r_add_assoc a1, r_add_comm b2 b1]
  mul_mem_left := by
    intro r x ⟨a, b, ha, hb, hx⟩
    refine ⟨r * a, r * b, I.mul_mem_left r ha, J.mul_mem_left r hb, ?_⟩
    rw [hx, r_left_distrib]

/-- Radical predicate `x ∈ √I` (`∃ m ≥ 1, x^m ∈ I`). -/
def Ideal.inRadical (I : Ideal R) (x : R) : Prop :=
  ∃ m : Nat, 1 ≤ m ∧ rpow x m ∈ I

/-- Equality of radicals `√I = √J`. -/
def Ideal.SameRadical (I J : Ideal R) : Prop :=
  ∀ x : R, Ideal.inRadical I x ↔ Ideal.inRadical J x

/-- Arithmetical rank `ara(I) = r`: `r` is the minimum number of elements of `R`
whose generated ideal has the same radical as `I`. -/
def IsArithmeticalRank (R : Type u) [CAlgRing R] (I : Ideal R) (r : Nat) : Prop :=
  (∃ fs : List R, fs.length = r ∧ Ideal.SameRadical (Ideal.span fs) I) ∧
  (∀ s : Nat, s < r → ¬ ∃ gs : List R, gs.length = s ∧ Ideal.SameRadical (Ideal.span gs) I)

/-- Prime ideal predicate (`I ≠ R` and `a * b ∈ I → a ∈ I ∨ b ∈ I`). -/
def Ideal.IsPrime (I : Ideal R) : Prop :=
  (1 : R) ∉ I ∧ ∀ a b : R, a * b ∈ I → a ∈ I ∨ b ∈ I

/-- Strict inclusion `I ⊂ J` of ideals. -/
def Ideal.StrictSubset (I J : Ideal R) : Prop :=
  (∀ x : R, x ∈ I → x ∈ J) ∧ (∃ y : R, y ∈ J ∧ y ∉ I)

end IdealLemmas

end Conjecture00000000505
