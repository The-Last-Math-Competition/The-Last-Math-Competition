/-
  Conjecture 00000004759 — Foundational Algebra & Operator-Valued Free Probability
  Core Lean 4.19.0 (zero external dependencies).

  Defines:
  1. Unital associative rings (`AssocRing`) and commutative rings (`CommAssocRing`).
  2. Operator-valued probability spaces `(A, B, ι, E)` (`OpValProbSpace`).
  3. Subalgebras containing `ι(B)` and Voiculescu's all-order `B`-freeness (`IsBFree`).
  4. Universal low-depth expectations (`E(XY) = E(X)E(Y)`, `E(X b₁ Y b₂ X) = E(X (b₁ E(Y) b₂) X)`, etc.)
     and exact computability of all polynomials in `B⟨X, Y⟩` of degree at most 3 from the
     `B`-multilinear moment oracles of `X` and `Y`.
-/

namespace Conjecture00000004759

/-- Unital associative ring (not necessarily commutative) in Core Lean 4. -/
class AssocRing (R : Type u) extends Add R, Sub R, Neg R, Mul R where
  zero : R
  one : R
  add_assoc : ∀ a b c : R, (a + b) + c = a + (b + c)
  add_comm : ∀ a b : R, a + b = b + a
  zero_add : ∀ a : R, zero + a = a
  add_zero : ∀ a : R, a + zero = a
  add_left_neg : ∀ a : R, (-a) + a = zero
  sub_eq_add_neg : ∀ a b : R, a - b = a + (-b)
  mul_assoc : ∀ a b c : R, (a * b) * c = a * (b * c)
  one_mul : ∀ a : R, one * a = a
  mul_one : ∀ a : R, a * one = a
  left_distrib : ∀ a b c : R, a * (b + c) = a * b + a * c
  right_distrib : ∀ a b c : R, (a + b) * c = a * c + b * c

instance (priority := 100) [AssocRing R] : OfNat R 0 where
  ofNat := AssocRing.zero

instance (priority := 100) [AssocRing R] : OfNat R 1 where
  ofNat := AssocRing.one

/-- Commutative unital associative ring. -/
class CommAssocRing (R : Type u) extends AssocRing R where
  mul_comm : ∀ a b : R, a * b = b * a

section RingLemmas
variable {R : Type u} [AssocRing R]

theorem zero_add_ring (a : R) : (0 : R) + a = a := AssocRing.zero_add a
theorem add_zero_ring (a : R) : a + (0 : R) = a := AssocRing.add_zero a
theorem one_mul_ring (a : R) : (1 : R) * a = a := AssocRing.one_mul a
theorem mul_one_ring (a : R) : a * (1 : R) = a := AssocRing.mul_one a
theorem add_left_neg_ring (a : R) : (-a) + a = (0 : R) := AssocRing.add_left_neg a

theorem add_right_neg_ring (a : R) : a + (-a) = (0 : R) := by
  rw [AssocRing.add_comm, add_left_neg_ring]

theorem sub_self_ring (a : R) : a - a = (0 : R) := by
  rw [AssocRing.sub_eq_add_neg, add_right_neg_ring]

theorem add_sub_cancel_ring (a b : R) : (a - b) + b = a := by
  rw [AssocRing.sub_eq_add_neg, AssocRing.add_assoc, add_left_neg_ring, add_zero_ring]

theorem add_left_cancel_ring {a b c : R} (h : a + b = a + c) : b = c := by
  have h1 : (-a) + (a + b) = (-a) + (a + c) := congrArg (fun x => (-a) + x) h
  rw [← AssocRing.add_assoc, ← AssocRing.add_assoc, add_left_neg_ring,
      zero_add_ring, zero_add_ring] at h1
  exact h1

theorem mul_zero_ring (a : R) : a * (0 : R) = (0 : R) := by
  have h : a * (0 : R) + a * (0 : R) = a * (0 : R) + (0 : R) := by
    rw [← AssocRing.left_distrib, add_zero_ring, add_zero_ring]
  exact add_left_cancel_ring h

theorem zero_mul_ring (a : R) : (0 : R) * a = (0 : R) := by
  have h : (0 : R) * a + (0 : R) * a = (0 : R) * a + (0 : R) := by
    rw [← AssocRing.right_distrib, add_zero_ring, add_zero_ring]
  exact add_left_cancel_ring h

theorem neg_zero_ring : (-(0 : R)) = (0 : R) := by
  have h := add_left_neg_ring (0 : R)
  rw [add_zero_ring] at h
  exact h

theorem mul_neg_ring (a b : R) : a * (-b) = -(a * b) := by
  have h : a * b + a * (-b) = a * b + (-(a * b)) := by
    rw [← AssocRing.left_distrib, add_right_neg_ring, mul_zero_ring, add_right_neg_ring]
  exact add_left_cancel_ring h

theorem neg_mul_ring (a b : R) : (-a) * b = -(a * b) := by
  have h : a * b + (-a) * b = a * b + (-(a * b)) := by
    rw [← AssocRing.right_distrib, add_right_neg_ring, zero_mul_ring, add_right_neg_ring]
  exact add_left_cancel_ring h

theorem mul_sub_ring (a b c : R) : a * (b - c) = a * b - a * c := by
  rw [AssocRing.sub_eq_add_neg, AssocRing.left_distrib, mul_neg_ring, ← AssocRing.sub_eq_add_neg]

theorem sub_mul_ring (a b c : R) : (a - b) * c = a * c - b * c := by
  rw [AssocRing.sub_eq_add_neg, AssocRing.right_distrib, neg_mul_ring, ← AssocRing.sub_eq_add_neg]

/-- Right-nested power `a ^ n` in an `AssocRing`. -/
def ringPow (a : R) : Nat → R
  | 0 => 1
  | n + 1 => a * ringPow a n

/-- Product of a list of ring elements. -/
def listProd : List R → R
  | [] => 1
  | x :: xs => x * listProd xs

theorem listProd_append : ∀ (xs ys : List R), listProd (xs ++ ys) = listProd xs * listProd ys
  | [], ys => by simp [listProd, one_mul_ring]
  | x :: xs, ys => by
      simp [listProd, listProd_append xs ys, AssocRing.mul_assoc]

theorem listProd_zero_head (xs : List R) : listProd ((0 : R) :: xs) = 0 := by
  simp [listProd, zero_mul_ring]

theorem listProd_contains_zero : ∀ (as : List R), (0 : R) ∈ as → listProd as = 0
  | [], h => nomatch h
  | a :: as, h => by
      cases List.mem_cons.mp h with
      | inl ha => subst ha; exact listProd_zero_head as
      | inr has =>
          simp [listProd, listProd_contains_zero as has, mul_zero_ring]

end RingLemmas

/-- Standard `Int` instance of `CommAssocRing`. -/
instance : CommAssocRing Int where
  zero := 0
  one := 1
  add_assoc := Int.add_assoc
  add_comm := Int.add_comm
  zero_add := Int.zero_add
  add_zero := Int.add_zero
  add_left_neg := Int.add_left_neg
  sub_eq_add_neg := fun _ _ => Int.sub_eq_add_neg
  mul_assoc := Int.mul_assoc
  one_mul := Int.one_mul
  mul_one := Int.mul_one
  left_distrib := Int.mul_add
  right_distrib := Int.add_mul
  mul_comm := Int.mul_comm

/-- An operator-valued noncommutative probability space `(A, B, ι, E)` in the sense of
    Voiculescu (1995) and Speicher (1998): `ι : B → A` embeds the unital subalgebra `B`
    into `A`, and `E : A → B` is a `B`-bimodule conditional expectation with `E(ι(b)) = b`. -/
structure OpValProbSpace (A : Type u) (B : Type v) [AssocRing A] [AssocRing B] where
  iota : B → A
  iota_zero : iota 0 = 0
  iota_one : iota 1 = 1
  iota_add : ∀ b₁ b₂ : B, iota (b₁ + b₂) = iota b₁ + iota b₂
  iota_neg : ∀ b : B, iota (-b) = -(iota b)
  iota_mul : ∀ b₁ b₂ : B, iota (b₁ * b₂) = iota b₁ * iota b₂
  exp : A → B
  exp_zero : exp 0 = 0
  exp_add : ∀ x y : A, exp (x + y) = exp x + exp y
  exp_neg : ∀ x : A, exp (-x) = -(exp x)
  exp_iota : ∀ b : B, exp (iota b) = b
  exp_bimod : ∀ (b₁ b₂ : B) (x : A), exp (iota b₁ * x * iota b₂) = b₁ * exp x * b₂

section OpValLemmas
variable {A : Type u} {B : Type v} [AssocRing A] [AssocRing B]

theorem exp_sub (S : OpValProbSpace A B) (x y : A) : S.exp (x - y) = S.exp x - S.exp y := by
  rw [AssocRing.sub_eq_add_neg, S.exp_add, S.exp_neg, ← AssocRing.sub_eq_add_neg]

theorem iota_sub (S : OpValProbSpace A B) (b₁ b₂ : B) :
    S.iota (b₁ - b₂) = S.iota b₁ - S.iota b₂ := by
  rw [AssocRing.sub_eq_add_neg, S.iota_add, S.iota_neg, ← AssocRing.sub_eq_add_neg]

theorem exp_one (S : OpValProbSpace A B) : S.exp 1 = 1 := by
  rw [← S.iota_one, S.exp_iota]

theorem exp_left_bimod (S : OpValProbSpace A B) (b : B) (x : A) :
    S.exp (S.iota b * x) = b * S.exp x := by
  have h := S.exp_bimod b 1 x
  rw [S.iota_one, mul_one_ring, mul_one_ring] at h
  exact h

theorem exp_right_bimod (S : OpValProbSpace A B) (x : A) (b : B) :
    S.exp (x * S.iota b) = S.exp x * b := by
  have h := S.exp_bimod 1 b x
  rw [S.iota_one, one_mul_ring, one_mul_ring] at h
  exact h

theorem exp_centered (S : OpValProbSpace A B) (x : A) :
    S.exp (x - S.iota (S.exp x)) = 0 := by
  rw [exp_sub, S.exp_iota, sub_self_ring]

/-- A subalgebra predicate `P : A → Prop` containing `ι(B)`. -/
structure IsSubalgebra (S : OpValProbSpace A B) (P : A → Prop) : Prop where
  has_iota : ∀ b : B, P (S.iota b)
  has_add : ∀ {x y}, P x → P y → P (x + y)
  has_neg : ∀ {x}, P x → P (-x)
  has_mul : ∀ {x y}, P x → P y → P (x * y)

theorem IsSubalgebra.has_sub {S : OpValProbSpace A B} {P : A → Prop}
    (hP : IsSubalgebra S P) {x y : A} (hx : P x) (hy : P y) : P (x - y) := by
  rw [AssocRing.sub_eq_add_neg]
  exact hP.has_add hx (hP.has_neg hy)

/-- Alternating membership of `as` in `P₀` (`false`) and `P₁` (`true`). -/
inductive AltMem (P₀ P₁ : A → Prop) : Bool → List A → Prop
  | single_false {a : A} : P₀ a → AltMem P₀ P₁ false [a]
  | single_true {a : A} : P₁ a → AltMem P₀ P₁ true [a]
  | cons_false {a : A} {as : List A} : P₀ a → AltMem P₀ P₁ true as → AltMem P₀ P₁ false (a :: as)
  | cons_true {a : A} {as : List A} : P₁ a → AltMem P₀ P₁ false as → AltMem P₀ P₁ true (a :: as)

/-- Every element in `as` is centered (`E(a) = 0`). -/
def AllCentered (S : OpValProbSpace A B) (as : List A) : Prop :=
  ∀ a ∈ as, S.exp a = 0

/-- Voiculescu's all-order `B`-freeness of two `B`-subalgebras `P₀` and `P₁`. -/
structure IsBFree (S : OpValProbSpace A B) (P₀ P₁ : A → Prop) : Prop where
  sub₀ : IsSubalgebra S P₀
  sub₁ : IsSubalgebra S P₁
  vanish : ∀ (start : Bool) (as : List A),
    AltMem P₀ P₁ start as → AllCentered S as → S.exp (listProd as) = 0

/-- The embedded base algebra `ι(B)` itself as a `B`-subalgebra. -/
def IotaSubalg (S : OpValProbSpace A B) (a : A) : Prop := ∃ b : B, a = S.iota b

theorem iotaSubalg_isSubalgebra (S : OpValProbSpace A B) : IsSubalgebra S (IotaSubalg S) where
  has_iota b := ⟨b, rfl⟩
  has_add := by
    rintro x y ⟨b₁, rfl⟩ ⟨b₂, rfl⟩
    exact ⟨b₁ + b₂, (S.iota_add b₁ b₂).symm⟩
  has_neg := by
    rintro x ⟨b, rfl⟩
    exact ⟨-b, (S.iota_neg b).symm⟩
  has_mul := by
    rintro x y ⟨b₁, rfl⟩ ⟨b₂, rfl⟩
    exact ⟨b₁ * b₂, (S.iota_mul b₁ b₂).symm⟩

private theorem altMem_iota_contains_zero (S : OpValProbSpace A B) {P : A → Prop} :
    ∀ {start : Bool} {as : List A},
      AltMem P (IotaSubalg S) start as → AllCentered S as →
      (start = true → (0 : A) ∈ as) ∧ (start = false → as.length ≥ 2 → (0 : A) ∈ as)
  | false, [_], AltMem.single_false _, _ =>
      ⟨fun h => Bool.noConfusion h, fun _ hlen => by simp at hlen⟩
  | true, [_], AltMem.single_true ⟨b, rfl⟩, hc => by
      refine ⟨fun _ => ?_, fun h => Bool.noConfusion h⟩
      have hb : b = 0 := by
        have h0 := hc (S.iota b) (List.Mem.head [])
        rw [S.exp_iota] at h0; exact h0
      subst hb; rw [S.iota_zero]; exact List.Mem.head []
  | false, a :: as, AltMem.cons_false _ hrest, hc => by
      have hc' : AllCentered S as := fun x hx => hc x (List.Mem.tail a hx)
      have ih := (altMem_iota_contains_zero S hrest hc').1 rfl
      exact ⟨fun h => Bool.noConfusion h, fun _ _ => List.Mem.tail a ih⟩
  | true, _ :: as, AltMem.cons_true ⟨b, rfl⟩ _, hc => by
      refine ⟨fun _ => ?_, fun h => Bool.noConfusion h⟩
      have hb : b = 0 := by
        have h0 := hc (S.iota b) (List.Mem.head as)
        rw [S.exp_iota] at h0; exact h0
      subst hb; rw [S.iota_zero]; exact List.Mem.head as

/-- Every `B`-subalgebra `P` is `B`-free from the base subalgebra `ι(B)`. -/
theorem isBFree_iotaSubalg (S : OpValProbSpace A B) {P : A → Prop} (hP : IsSubalgebra S P) :
    IsBFree S P (IotaSubalg S) where
  sub₀ := hP
  sub₁ := iotaSubalg_isSubalgebra S
  vanish := by
    intro start as halt hc
    cases start with
    | true =>
        have h0 := (altMem_iota_contains_zero S halt hc).1 rfl
        rw [listProd_contains_zero as h0, S.exp_zero]
    | false =>
        cases halt with
        | single_false _ =>
            simp [listProd, mul_one_ring]
            exact hc _ (List.Mem.head [])
        | cons_false _ hrest =>
            have hc' : AllCentered S _ := fun x hx => hc x (List.Mem.tail _ hx)
            have h0 := (altMem_iota_contains_zero S hrest hc').1 rfl
            rw [listProd_contains_zero _ (List.Mem.tail _ h0), S.exp_zero]

/-! ### Universal Low-Depth Identities Under `B`-Freeness -/

theorem exp_XY_bfree (S : OpValProbSpace A B) {P₀ P₁ : A → Prop} (hF : IsBFree S P₀ P₁)
    {X Y : A} (hX : P₀ X) (hY : P₁ Y) (b : B) :
    S.exp (X * S.iota b * Y) = S.exp X * b * S.exp Y := by
  let X₀ := X - S.iota (S.exp X)
  let Y₀ := S.iota b * (Y - S.iota (S.exp Y))
  have hX₀_mem : P₀ X₀ := hF.sub₀.has_sub hX (hF.sub₀.has_iota _)
  have hY₀_mem : P₁ Y₀ := hF.sub₁.has_mul (hF.sub₁.has_iota b)
    (hF.sub₁.has_sub hY (hF.sub₁.has_iota _))
  have hX₀_c : S.exp X₀ = 0 := exp_centered S X
  have hY₀_c : S.exp Y₀ = 0 := by
    dsimp [Y₀]
    rw [exp_left_bimod, exp_centered, mul_zero_ring]
  have halt : AltMem P₀ P₁ false [X₀, Y₀] :=
    AltMem.cons_false hX₀_mem (AltMem.single_true hY₀_mem)
  have hc : AllCentered S [X₀, Y₀] := by
    intro u hu
    rcases List.mem_cons.mp hu with rfl | h2
    · exact hX₀_c
    · rcases List.mem_cons.mp h2 with rfl | h3
      · exact hY₀_c
      · nomatch h3
  have hv := hF.vanish false [X₀, Y₀] halt hc
  simp [listProd, mul_one_ring] at hv
  have hexp : X₀ * Y₀ = (X * S.iota b * Y - X * S.iota (b * S.exp Y))
      - (S.iota (S.exp X * b) * Y - S.iota (S.exp X * b * S.exp Y)) := by
    dsimp [X₀, Y₀]
    rw [sub_mul_ring,
        ← AssocRing.mul_assoc X (S.iota b) (Y - S.iota (S.exp Y)),
        mul_sub_ring (X * S.iota b),
        AssocRing.mul_assoc X (S.iota b) (S.iota (S.exp Y)),
        ← S.iota_mul b (S.exp Y),
        ← AssocRing.mul_assoc (S.iota (S.exp X)) (S.iota b) (Y - S.iota (S.exp Y)),
        ← S.iota_mul (S.exp X) b,
        mul_sub_ring (S.iota (S.exp X * b)),
        ← S.iota_mul (S.exp X * b) (S.exp Y)]
  rw [hexp, exp_sub, exp_sub, exp_sub, exp_right_bimod, exp_left_bimod, S.exp_iota,
      ← AssocRing.mul_assoc (S.exp X) b (S.exp Y), sub_self_ring,
      AssocRing.sub_eq_add_neg _ 0, neg_zero_ring, add_zero_ring] at hv
  have hfin : S.exp (X * S.iota b * Y) =
      (S.exp (X * S.iota b * Y) - S.exp X * b * S.exp Y) + S.exp X * b * S.exp Y := by
    rw [add_sub_cancel_ring]
  rw [hfin, hv, zero_add_ring]

theorem exp_YX_bfree (S : OpValProbSpace A B) {P₀ P₁ : A → Prop} (hF : IsBFree S P₀ P₁)
    {X Y : A} (hX : P₀ X) (hY : P₁ Y) (b : B) :
    S.exp (Y * S.iota b * X) = S.exp Y * b * S.exp X := by
  have hsym : IsBFree S P₁ P₀ := {
    sub₀ := hF.sub₁
    sub₁ := hF.sub₀
    vanish := by
      intro start as halt hc
      have swapAlt : ∀ {st : Bool} {xs : List A}, AltMem P₁ P₀ st xs → AltMem P₀ P₁ (!st) xs := by
        intro st xs h
        induction h with
        | single_false hp => exact AltMem.single_true hp
        | single_true hp => exact AltMem.single_false hp
        | cons_false hp _ ih => exact AltMem.cons_true hp ih
        | cons_true hp _ ih => exact AltMem.cons_false hp ih
      exact hF.vanish (!start) as (swapAlt halt) hc
  }
  exact exp_XY_bfree S hsym hY hX b

theorem exp_add_sq_bfree (S : OpValProbSpace A B) {P₀ P₁ : A → Prop} (hF : IsBFree S P₀ P₁)
    {X Y : A} (hX : P₀ X) (hY : P₁ Y) :
    S.exp ((X + Y) * (X + Y)) =
      ((S.exp (X * X) + S.exp X * S.exp Y) + S.exp Y * S.exp X) + S.exp (Y * Y) := by
  have hxy : S.exp (X * Y) = S.exp X * S.exp Y := by
    have h := exp_XY_bfree S hF hX hY 1
    rw [S.iota_one, mul_one_ring, mul_one_ring] at h; exact h
  have hyx : S.exp (Y * X) = S.exp Y * S.exp X := by
    have h := exp_YX_bfree S hF hX hY 1
    rw [S.iota_one, mul_one_ring, mul_one_ring] at h; exact h
  have hexp : (X + Y) * (X + Y) = ((X * X + X * Y) + Y * X) + Y * Y := by
    rw [AssocRing.left_distrib, AssocRing.right_distrib, AssocRing.right_distrib,
        AssocRing.add_assoc (X * X) (Y * X) (X * Y + Y * Y),
        ← AssocRing.add_assoc (Y * X) (X * Y) (Y * Y),
        AssocRing.add_comm (Y * X) (X * Y),
        ← AssocRing.add_assoc (X * X) (X * Y + Y * X) (Y * Y),
        ← AssocRing.add_assoc (X * X) (X * Y) (Y * X)]
  rw [hexp, S.exp_add, S.exp_add, S.exp_add, hxy, hyx]

/-- Fundamental degree-3 nested identity under `B`-freeness:
    `E(X · ι(b₁) · Y · ι(b₂) · X) = E(X · ι(b₁ · E(Y) · b₂) · X)`. -/
theorem exp_XYX_bfree (S : OpValProbSpace A B) {P₀ P₁ : A → Prop} (hF : IsBFree S P₀ P₁)
    {X Y : A} (hX : P₀ X) (hY : P₁ Y) (b₁ b₂ : B) :
    S.exp (X * S.iota b₁ * Y * S.iota b₂ * X) =
      S.exp (X * S.iota (b₁ * S.exp Y * b₂) * X) := by
  let X₀ := X - S.iota (S.exp X)
  let M₀ := S.iota b₁ * (Y - S.iota (S.exp Y)) * S.iota b₂
  have hX₀_mem : P₀ X₀ := hF.sub₀.has_sub hX (hF.sub₀.has_iota _)
  have hM₀_mem : P₁ M₀ :=
    hF.sub₁.has_mul
      (hF.sub₁.has_mul (hF.sub₁.has_iota b₁) (hF.sub₁.has_sub hY (hF.sub₁.has_iota _)))
      (hF.sub₁.has_iota b₂)
  have hX₀_c : S.exp X₀ = 0 := exp_centered S X
  have hM₀_c : S.exp M₀ = 0 := by
    dsimp [M₀]
    rw [S.exp_bimod, exp_centered, mul_zero_ring, zero_mul_ring]
  have halt3 : AltMem P₀ P₁ false [X₀, M₀, X₀] :=
    AltMem.cons_false hX₀_mem (AltMem.cons_true hM₀_mem (AltMem.single_false hX₀_mem))
  have hc3 : AllCentered S [X₀, M₀, X₀] := by
    intro u hu
    rcases List.mem_cons.mp hu with rfl | h2
    · exact hX₀_c
    · rcases List.mem_cons.mp h2 with rfl | h3
      · exact hM₀_c
      · rcases List.mem_cons.mp h3 with rfl | h4
        · exact hX₀_c
        · nomatch h4
  have hv3 := hF.vanish false [X₀, M₀, X₀] halt3 hc3
  simp [listProd, mul_one_ring, ← AssocRing.mul_assoc] at hv3
  have hv_left : S.exp (X₀ * M₀) = 0 := by
    have h := exp_XY_bfree S hF hX₀_mem hM₀_mem 1
    rw [S.iota_one, mul_one_ring, hX₀_c, zero_mul_ring, zero_mul_ring] at h
    exact h
  have hv_right : S.exp (M₀ * X₀) = 0 := by
    have h := exp_YX_bfree S hF hX₀_mem hM₀_mem 1
    rw [S.iota_one, mul_one_ring, hM₀_c, zero_mul_ring, zero_mul_ring] at h
    exact h
  have hX_split : X = X₀ + S.iota (S.exp X) := by
    dsimp [X₀]; rw [add_sub_cancel_ring]
  have hXMX : S.exp (X * M₀ * X) = 0 := by
    conv => lhs; rw [hX_split]
    rw [AssocRing.right_distrib, AssocRing.right_distrib,
        AssocRing.left_distrib, AssocRing.left_distrib,
        S.exp_add, S.exp_add, S.exp_add, hv3, zero_add_ring,
        exp_right_bimod, hv_left, zero_mul_ring, zero_add_ring,
        AssocRing.mul_assoc (S.iota (S.exp X)) M₀ X₀, exp_left_bimod, hv_right,
        mul_zero_ring, zero_add_ring,
        S.exp_bimod, hM₀_c, mul_zero_ring, zero_mul_ring]
  have hM₀_eq : X * M₀ * X =
      X * S.iota b₁ * Y * S.iota b₂ * X - X * S.iota (b₁ * S.exp Y * b₂) * X := by
    dsimp [M₀]
    rw [mul_sub_ring (S.iota b₁), sub_mul_ring _ _ (S.iota b₂),
        mul_sub_ring X, sub_mul_ring _ _ X,
        ← S.iota_mul b₁ (S.exp Y), ← S.iota_mul (b₁ * S.exp Y) b₂,
        ← AssocRing.mul_assoc X (S.iota b₁ * Y) (S.iota b₂),
        ← AssocRing.mul_assoc X (S.iota b₁) Y]
  rw [hM₀_eq, exp_sub] at hXMX
  have hfin : S.exp (X * S.iota b₁ * Y * S.iota b₂ * X) =
      (S.exp (X * S.iota b₁ * Y * S.iota b₂ * X) - S.exp (X * S.iota (b₁ * S.exp Y * b₂) * X))
      + S.exp (X * S.iota (b₁ * S.exp Y * b₂) * X) := by
    rw [add_sub_cancel_ring]
  rw [hfin, hXMX, zero_add_ring]

theorem exp_YXY_bfree (S : OpValProbSpace A B) {P₀ P₁ : A → Prop} (hF : IsBFree S P₀ P₁)
    {X Y : A} (hX : P₀ X) (hY : P₁ Y) (b₁ b₂ : B) :
    S.exp (Y * S.iota b₁ * X * S.iota b₂ * Y) =
      S.exp (Y * S.iota (b₁ * S.exp X * b₂) * Y) := by
  have hsym : IsBFree S P₁ P₀ := {
    sub₀ := hF.sub₁
    sub₁ := hF.sub₀
    vanish := by
      intro start as halt hc
      have swapAlt : ∀ {st : Bool} {xs : List A}, AltMem P₁ P₀ st xs → AltMem P₀ P₁ (!st) xs := by
        intro st xs h
        induction h with
        | single_false hp => exact AltMem.single_true hp
        | single_true hp => exact AltMem.single_false hp
        | cons_false hp _ ih => exact AltMem.cons_true hp ih
        | cons_true hp _ ih => exact AltMem.cons_false hp ih
      exact hF.vanish (!start) as (swapAlt halt) hc
  }
  exact exp_XYX_bfree S hsym hY hX b₁ b₂

theorem exp_XXY_bfree (S : OpValProbSpace A B) {P₀ P₁ : A → Prop} (hF : IsBFree S P₀ P₁)
    {X Y : A} (hX : P₀ X) (hY : P₁ Y) (b₁ b₂ : B) :
    S.exp (X * S.iota b₁ * X * S.iota b₂ * Y) =
      S.exp (X * S.iota b₁ * X) * b₂ * S.exp Y :=
  exp_XY_bfree S hF (hF.sub₀.has_mul (hF.sub₀.has_mul hX (hF.sub₀.has_iota b₁)) hX) hY b₂

theorem exp_YYX_bfree (S : OpValProbSpace A B) {P₀ P₁ : A → Prop} (hF : IsBFree S P₀ P₁)
    {X Y : A} (hX : P₀ X) (hY : P₁ Y) (b₁ b₂ : B) :
    S.exp (Y * S.iota b₁ * Y * S.iota b₂ * X) =
      S.exp (Y * S.iota b₁ * Y) * b₂ * S.exp X :=
  exp_YX_bfree S hF hX (hF.sub₁.has_mul (hF.sub₁.has_mul hY (hF.sub₁.has_iota b₁)) hY) b₂

theorem exp_XYY_bfree (S : OpValProbSpace A B) {P₀ P₁ : A → Prop} (hF : IsBFree S P₀ P₁)
    {X Y : A} (hX : P₀ X) (hY : P₁ Y) (b₁ b₂ : B) :
    S.exp (X * S.iota b₁ * Y * S.iota b₂ * Y) =
      S.exp X * b₁ * S.exp (Y * S.iota b₂ * Y) := by
  have h := exp_XY_bfree S hF hX
    (hF.sub₁.has_mul (hF.sub₁.has_mul hY (hF.sub₁.has_iota b₂)) hY) b₁
  rw [← AssocRing.mul_assoc (X * S.iota b₁) (Y * S.iota b₂) Y,
      ← AssocRing.mul_assoc (X * S.iota b₁) Y (S.iota b₂)] at h
  exact h

theorem exp_YXX_bfree (S : OpValProbSpace A B) {P₀ P₁ : A → Prop} (hF : IsBFree S P₀ P₁)
    {X Y : A} (hX : P₀ X) (hY : P₁ Y) (b₁ b₂ : B) :
    S.exp (Y * S.iota b₁ * X * S.iota b₂ * X) =
      S.exp Y * b₁ * S.exp (X * S.iota b₂ * X) := by
  have h := exp_YX_bfree S hF
    (hF.sub₀.has_mul (hF.sub₀.has_mul hX (hF.sub₀.has_iota b₂)) hX) hY b₁
  rw [← AssocRing.mul_assoc (Y * S.iota b₁) (X * S.iota b₂) X,
      ← AssocRing.mul_assoc (Y * S.iota b₁) X (S.iota b₂)] at h
  exact h

end OpValLemmas

end Conjecture00000004759
