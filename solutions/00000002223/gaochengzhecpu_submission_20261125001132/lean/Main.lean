/-
  Conjecture 00000002223 — Self-Contained Core Lean 4.19.0 Formalization
  =======================================================================
  Official Statement (SOURCE.md):
  - English: "Definition: Amalgamated duplication is the doubled-copy ring of a prime ideal.
    Conjecture: The diameter of its zero-divisor graph is at most three; and the spectral
    condition on ideals attaining three is given by prime chains of length two.
    (duplicated ring zero-divisor graph diameter three)"
  - Chinese: "定义：amalgamated duplication 指素理想的双副本环。猜想：其零因子图的直径不超过三；
    且达到三的理想谱条件由素链的长度二给出。（重复环零因子图直径三）"
-/

namespace Conjecture2223

universe u v

/-! ## Section 1. Commutative Rings with Identity (`1 ≠ 0`), Homomorphisms, and Ideals -/

class CommRing (R : Type u) where
  zero : R
  one : R
  add : R → R → R
  mul : R → R → R
  neg : R → R
  zero_ne_one : zero ≠ one
  add_assoc : ∀ a b c : R, add (add a b) c = add a (add b c)
  add_comm : ∀ a b : R, add a b = add b a
  zero_add : ∀ a : R, add zero a = a
  add_left_neg : ∀ a : R, add (neg a) a = zero
  mul_assoc : ∀ a b c : R, mul (mul a b) c = mul a (mul b c)
  mul_comm : ∀ a b : R, mul a b = mul b a
  one_mul : ∀ a : R, mul one a = a
  left_distrib : ∀ a b c : R, mul a (add b c) = add (mul a b) (mul a c)

instance instOfNatZeroOfCommRing (R : Type u) [CommRing R] : OfNat R 0 := ⟨CommRing.zero⟩
instance instOfNatOneOfCommRing (R : Type u) [CommRing R] : OfNat R 1 := ⟨CommRing.one⟩
instance instAddOfCommRing (R : Type u) [CommRing R] : Add R := ⟨CommRing.add⟩
instance instMulOfCommRing (R : Type u) [CommRing R] : Mul R := ⟨CommRing.mul⟩
instance instNegOfCommRing (R : Type u) [CommRing R] : Neg R := ⟨CommRing.neg⟩
instance instSubOfCommRing (R : Type u) [CommRing R] : Sub R := ⟨fun a b => a + (-b)⟩

section RingLemmas
variable {R : Type u} [CommRing R]

theorem ring_zero_ne_one : (0 : R) ≠ (1 : R) := CommRing.zero_ne_one
theorem ring_add_assoc (a b c : R) : (a + b) + c = a + (b + c) := CommRing.add_assoc a b c
theorem ring_add_comm (a b : R) : a + b = b + a := CommRing.add_comm a b
theorem ring_zero_add (a : R) : (0 : R) + a = a := CommRing.zero_add a
theorem ring_add_left_neg (a : R) : (-a) + a = 0 := CommRing.add_left_neg a
theorem ring_mul_assoc (a b c : R) : (a * b) * c = a * (b * c) := CommRing.mul_assoc a b c
theorem ring_mul_comm (a b : R) : a * b = b * a := CommRing.mul_comm a b
theorem ring_one_mul (a : R) : (1 : R) * a = a := CommRing.one_mul a
theorem ring_left_distrib (a b c : R) : a * (b + c) = a * b + a * c := CommRing.left_distrib a b c

theorem ring_add_zero (a : R) : a + 0 = a := by
  rw [ring_add_comm, ring_zero_add]

theorem ring_add_right_neg (a : R) : a + (-a) = 0 := by
  rw [ring_add_comm, ring_add_left_neg]

theorem ring_mul_one (a : R) : a * 1 = a := by
  rw [ring_mul_comm, ring_one_mul]

theorem ring_right_distrib (a b c : R) : (a + b) * c = a * c + b * c := by
  rw [ring_mul_comm, ring_left_distrib, ring_mul_comm c a, ring_mul_comm c b]

theorem ring_add_left_cancel {a b c : R} (h : a + b = a + c) : b = c := by
  have h1 : (-a) + (a + b) = (-a) + (a + c) := congrArg (fun x => (-a) + x) h
  rw [← ring_add_assoc, ← ring_add_assoc, ring_add_left_neg, ring_zero_add, ring_zero_add] at h1
  exact h1

theorem ring_add_right_cancel {a b c : R} (h : b + a = c + a) : b = c := by
  apply ring_add_left_cancel (a := a)
  rw [ring_add_comm a b, ring_add_comm a c]
  exact h

theorem ring_mul_zero (a : R) : a * 0 = 0 := by
  apply ring_add_left_cancel (a := a * 0)
  rw [← ring_left_distrib, ring_add_zero, ring_add_zero]

theorem ring_zero_mul (a : R) : (0 : R) * a = 0 := by
  rw [ring_mul_comm, ring_mul_zero]

theorem ring_neg_eq_of_add_eq_zero {a b : R} (h : a + b = 0) : -a = b := by
  apply ring_add_right_cancel (a := a)
  rw [ring_add_left_neg, ring_add_comm b a]
  exact h.symm

theorem ring_neg_zero : -(0 : R) = 0 :=
  ring_neg_eq_of_add_eq_zero (ring_add_zero 0)

theorem ring_neg_neg (a : R) : -(-a) = a :=
  ring_neg_eq_of_add_eq_zero (ring_add_left_neg a)

theorem ring_neg_add (a b : R) : -(a + b) = (-a) + (-b) := by
  apply ring_neg_eq_of_add_eq_zero
  calc
    (a + b) + ((-a) + (-b)) = a + (b + ((-a) + (-b))) := ring_add_assoc a b _
    _ = a + (b + ((-b) + (-a))) := by rw [ring_add_comm (-a) (-b)]
    _ = a + ((b + (-b)) + (-a)) := by rw [← ring_add_assoc b (-b) (-a)]
    _ = a + (0 + (-a)) := by rw [ring_add_right_neg]
    _ = a + (-a) := by rw [ring_zero_add]
    _ = 0 := ring_add_right_neg a

theorem ring_mul_neg (a b : R) : a * (-b) = -(a * b) := by
  symm
  apply ring_neg_eq_of_add_eq_zero
  rw [← ring_left_distrib, ring_add_right_neg, ring_mul_zero]

theorem ring_neg_mul (a b : R) : (-a) * b = -(a * b) := by
  rw [ring_mul_comm, ring_mul_neg, ring_mul_comm]

theorem ring_sub_def (a b : R) : a - b = a + (-b) := rfl

theorem ring_sub_self (a : R) : a - a = 0 := ring_add_right_neg a

theorem ring_sub_zero (a : R) : a - 0 = a := by
  change a + (-(0 : R)) = a
  rw [ring_neg_zero, ring_add_zero]

theorem ring_zero_sub (a : R) : (0 : R) - a = -a := by
  change (0 : R) + (-a) = -a
  exact ring_zero_add (-a)

theorem ring_sub_eq_zero {a b : R} : a - b = 0 ↔ a = b := by
  constructor
  · intro h
    have h1 : (a + (-b)) + b = 0 + b := congrArg (fun x => x + b) h
    rw [ring_add_assoc, ring_add_left_neg, ring_add_zero, ring_zero_add] at h1
    exact h1
  · intro h
    subst h
    exact ring_sub_self a

theorem ring_add_sub_cancel (a b : R) : (a + b) - a = b := by
  change (a + b) + (-a) = b
  rw [ring_add_comm a b, ring_add_assoc, ring_add_right_neg, ring_add_zero]

theorem ring_left_distrib_sub (a b c : R) : a * (b - c) = a * b - a * c := by
  change a * (b + (-c)) = a * b + (-(a * c))
  rw [ring_left_distrib, ring_mul_neg]

theorem ring_right_distrib_sub (a b c : R) : (a - b) * c = a * c - b * c := by
  change (a + (-b)) * c = a * c + (-(b * c))
  rw [ring_right_distrib, ring_neg_mul]

def ringPow (a : R) : Nat → R
  | 0 => 1
  | k + 1 => a * ringPow a k

theorem ringPow_zero (a : R) : ringPow a 0 = 1 := rfl
theorem ringPow_succ (a : R) (k : Nat) : ringPow a (k + 1) = a * ringPow a k := rfl

end RingLemmas

structure RingHom (R : Type u) (S : Type v) [CommRing R] [CommRing S] where
  toFun : R → S
  map_zero : toFun 0 = 0
  map_one : toFun 1 = 1
  map_add : ∀ a b : R, toFun (a + b) = toFun a + toFun b
  map_mul : ∀ a b : R, toFun (a * b) = toFun a * toFun b

structure RingIso (R : Type u) (S : Type v) [CommRing R] [CommRing S] where
  toFun : R → S
  invFun : S → R
  left_inv : ∀ a : R, invFun (toFun a) = a
  right_inv : ∀ b : S, toFun (invFun b) = b
  map_add : ∀ a b : R, toFun (a + b) = toFun a + toFun b
  map_mul : ∀ a b : R, toFun (a * b) = toFun a * toFun b

theorem ringIso_toFun_inj {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    (e : RingIso R S) {a₁ a₂ : R} (h : e.toFun a₁ = e.toFun a₂) : a₁ = a₂ := by
  have h1 := congrArg e.invFun h
  rw [e.left_inv, e.left_inv] at h1
  exact h1

structure Ideal (R : Type u) [CommRing R] where
  mem : R → Prop
  zero_mem : mem 0
  add_mem : ∀ {a b : R}, mem a → mem b → mem (a + b)
  neg_mem : ∀ {a : R}, mem a → mem (-a)
  mul_mem_left : ∀ (r : R) {a : R}, mem a → mem (r * a)

section IdealLemmas
variable {R : Type u} [CommRing R]

theorem Ideal.ext {I J : Ideal R} (h : ∀ x : R, I.mem x ↔ J.mem x) : I = J := by
  cases I with
  | mk mI _ _ _ _ =>
    cases J with
    | mk mJ _ _ _ _ =>
      have hm : mI = mJ := funext (fun x => propext (h x))
      subst hm
      rfl

theorem Ideal.sub_mem (I : Ideal R) {a b : R} (ha : I.mem a) (hb : I.mem b) :
    I.mem (a - b) :=
  I.add_mem ha (I.neg_mem hb)

theorem Ideal.mul_mem_right (I : Ideal R) {a : R} (r : R) (ha : I.mem a) :
    I.mem (a * r) := by
  rw [ring_mul_comm]
  exact I.mul_mem_left r ha

def IdealSubset (I J : Ideal R) : Prop :=
  ∀ x : R, I.mem x → J.mem x

def IdealStrictSubset (I J : Ideal R) : Prop :=
  IdealSubset I J ∧ ∃ x : R, J.mem x ∧ ¬ I.mem x

theorem idealStrictSubset_iff_subset_and_ne (I J : Ideal R) :
    IdealStrictSubset I J ↔ (IdealSubset I J ∧ I ≠ J) := by
  constructor
  · rintro ⟨hsub, x, hxJ, hxI⟩
    refine ⟨hsub, fun heq => ?_⟩
    subst heq
    exact hxI hxJ
  · rintro ⟨hsub, hne⟩
    refine ⟨hsub, ?_⟩
    cases Classical.em (∃ x : R, J.mem x ∧ ¬ I.mem x) with
    | inl hex => exact hex
    | inr hno =>
      exfalso
      apply hne
      apply Ideal.ext
      intro x
      constructor
      · exact hsub x
      · intro hxJ
        cases Classical.em (I.mem x) with
        | inl hxI => exact hxI
        | inr hnxI => exact False.elim (hno ⟨x, hxJ, hnxI⟩)

def IsPrimeIdeal (R : Type u) [CommRing R] (P : Ideal R) : Prop :=
  ¬ P.mem 1 ∧ ∀ a b : R, P.mem (a * b) → P.mem a ∨ P.mem b

def IsIntegralDomain (R : Type u) [CommRing R] : Prop :=
  ∀ a b : R, a * b = 0 → a = 0 ∨ b = 0

def zeroIdeal (R : Type u) [CommRing R] : Ideal R where
  mem := fun x => x = 0
  zero_mem := rfl
  add_mem := by
    intro a b ha hb
    rw [ha, hb, ring_add_zero]
  neg_mem := by
    intro a ha
    rw [ha, ring_neg_zero]
  mul_mem_left := by
    intro r a ha
    rw [ha, ring_mul_zero]

theorem zeroIdeal_isPrime_iff_domain :
    IsPrimeIdeal R (zeroIdeal R) ↔ IsIntegralDomain R := by
  constructor
  · rintro ⟨_, hmul⟩ a b hab
    exact hmul a b hab
  · intro hdom
    refine ⟨fun h1 => ring_zero_ne_one h1.symm, ?_⟩
    intro a b hab
    exact hdom a b hab

theorem domain_ringPow_ne_zero (hdom : IsIntegralDomain R) {c : R} (hc : c ≠ 0) :
    ∀ k : Nat, ringPow c k ≠ 0
  | 0 => fun h => ring_zero_ne_one h.symm
  | k + 1 => by
    intro h
    cases hdom c (ringPow c k) h with
    | inl hc0 => exact hc hc0
    | inr hk0 => exact domain_ringPow_ne_zero hdom hc k hk0

theorem prime_not_mem_pow {P : Ideal R} (hP : IsPrimeIdeal R P) {c : R}
    (hc : ¬ P.mem c) : ∀ k : Nat, ¬ P.mem (ringPow c k)
  | 0 => hP.1
  | k + 1 => by
    intro hmem
    cases hP.2 c (ringPow c k) hmem with
    | inl hc' => exact hc hc'
    | inr hk => exact prime_not_mem_pow hP hc k hk

end IdealLemmas

/-! ## Section 2. Prime Chains and Spectral Height Conditions -/

inductive HasPrimeChainEndingAt (R : Type u) [CommRing R] : Ideal R → Nat → Prop where
  | zero {P : Ideal R} : IsPrimeIdeal R P → HasPrimeChainEndingAt R P 0
  | step {Q P : Ideal R} {k : Nat} :
      HasPrimeChainEndingAt R Q k → IsPrimeIdeal R P → IdealStrictSubset Q P →
      HasPrimeChainEndingAt R P (k + 1)

def HasPrimeChainOfLength (R : Type u) [CommRing R] (k : Nat) : Prop :=
  ∃ P : Ideal R, HasPrimeChainEndingAt R P k

def HasExactHeight (R : Type u) [CommRing R] (P : Ideal R) (k : Nat) : Prop :=
  HasPrimeChainEndingAt R P k ∧ ¬ HasPrimeChainEndingAt R P (k + 1)

theorem hasPrimeChainEndingAt_isPrime {R : Type u} [CommRing R] {P : Ideal R} {k : Nat}
    (h : HasPrimeChainEndingAt R P k) : IsPrimeIdeal R P := by
  cases h with
  | zero hP => exact hP
  | step _ hP _ => exact hP

theorem hasPrimeChainEndingAt_pred {R : Type u} [CommRing R] {P : Ideal R} {k : Nat}
    (h : HasPrimeChainEndingAt R P (k + 1)) : HasPrimeChainEndingAt R P k := by
  induction k generalizing P with
  | zero =>
    cases h with
    | step _ hP _ => exact HasPrimeChainEndingAt.zero hP
  | succ k ih =>
    cases h with
    | step hQ hP hQP => exact HasPrimeChainEndingAt.step (ih hQ) hP hQP

theorem hasPrimeChainEndingAt_mono {R : Type u} [CommRing R] {P : Ideal R} {m n : Nat}
    (hmn : m ≤ n) (hn : HasPrimeChainEndingAt R P n) : HasPrimeChainEndingAt R P m := by
  induction n generalizing P with
  | zero =>
    have hm0 : m = 0 := Nat.eq_zero_of_le_zero hmn
    subst hm0
    exact hn
  | succ n ih =>
    cases Nat.eq_or_lt_of_le hmn with
    | inl heq =>
      subst heq
      exact hn
    | inr hlt =>
      have hle : m ≤ n := Nat.le_of_lt_succ hlt
      exact ih hle (hasPrimeChainEndingAt_pred hn)

theorem hasPrimeChainOfLength_mono {R : Type u} [CommRing R] {m n : Nat}
    (hmn : m ≤ n) : HasPrimeChainOfLength R n → HasPrimeChainOfLength R m := by
  rintro ⟨P, hP⟩
  exact ⟨P, hasPrimeChainEndingAt_mono hmn hP⟩

theorem hasExactHeight_no_longer {R : Type u} [CommRing R] {P : Ideal R} {k m : Nat}
    (hexact : HasExactHeight R P k) (hkm : k < m) : ¬ HasPrimeChainEndingAt R P m := by
  intro hm
  exact hexact.2 (hasPrimeChainEndingAt_mono hkm hm)

theorem hasPrimeChainOfLength_two_iff (R : Type u) [CommRing R] :
    HasPrimeChainOfLength R 2 ↔
      ∃ Q₀ Q₁ Q₂ : Ideal R,
        IsPrimeIdeal R Q₀ ∧ IsPrimeIdeal R Q₁ ∧ IsPrimeIdeal R Q₂ ∧
        IdealStrictSubset Q₀ Q₁ ∧ IdealStrictSubset Q₁ Q₂ := by
  constructor
  · rintro ⟨Q₂, h₂⟩
    cases h₂ with
    | step h₁ hQ₂ h12 =>
      cases h₁ with
      | step h₀ hQ₁ h01 =>
        cases h₀ with
        | zero hQ₀ =>
          exact ⟨_, _, Q₂, hQ₀, hQ₁, hQ₂, h01, h12⟩
  · rintro ⟨Q₀, Q₁, Q₂, hQ₀, hQ₁, hQ₂, h01, h12⟩
    exact ⟨Q₂, HasPrimeChainEndingAt.step
      (HasPrimeChainEndingAt.step (HasPrimeChainEndingAt.zero hQ₀) hQ₁ h01) hQ₂ h12⟩

/-! ## Section 3. Amalgamated Duplication `R ⋈ P` (D'Anna–Fontana 2007) -/

def AmalgamatedDuplication (R : Type u) [CommRing R] (P : Ideal R) : Type u :=
  { x : R × R // P.mem (x.2 - x.1) }

section DuplicationStructure
variable {R : Type u} [CommRing R] (P : Ideal R)

theorem dup_ext {x y : AmalgamatedDuplication R P}
    (h1 : x.val.1 = y.val.1) (h2 : x.val.2 = y.val.2) : x = y :=
  Subtype.ext (Prod.ext h1 h2)

theorem mem_duplication_iff_add (r s : R) :
    P.mem (s - r) ↔ ∃ p : R, P.mem p ∧ s = r + p := by
  constructor
  · intro h
    refine ⟨s - r, h, ?_⟩
    calc
      s = (s - r) + r := by
        change s = (s + (-r)) + r
        rw [ring_add_assoc, ring_add_left_neg, ring_add_zero]
      _ = r + (s - r) := ring_add_comm (s - r) r
  · rintro ⟨p, hp, rfl⟩
    rw [ring_add_sub_cancel]
    exact hp

theorem dup_add_closed (x y : AmalgamatedDuplication R P) :
    P.mem ((x.val.2 + y.val.2) - (x.val.1 + y.val.1)) := by
  have h : (x.val.2 + y.val.2) - (x.val.1 + y.val.1) =
      (x.val.2 - x.val.1) + (y.val.2 - y.val.1) := by
    change (x.val.2 + y.val.2) + (-(x.val.1 + y.val.1)) =
      (x.val.2 + (-x.val.1)) + (y.val.2 + (-y.val.1))
    rw [ring_neg_add, ring_add_assoc x.val.2 y.val.2, ← ring_add_assoc y.val.2 (-x.val.1) (-y.val.1),
        ring_add_comm y.val.2 (-x.val.1), ring_add_assoc (-x.val.1) y.val.2 (-y.val.1),
        ← ring_add_assoc x.val.2 (-x.val.1)]
  rw [h]
  exact P.add_mem x.property y.property

theorem dup_neg_closed (x : AmalgamatedDuplication R P) :
    P.mem ((-x.val.2) - (-x.val.1)) := by
  have h : (-x.val.2) - (-x.val.1) = -(x.val.2 - x.val.1) := by
    change (-x.val.2) + (-(-x.val.1)) = -(x.val.2 + (-x.val.1))
    rw [ring_neg_add]
  rw [h]
  exact P.neg_mem x.property

theorem dup_mul_closed (x y : AmalgamatedDuplication R P) :
    P.mem ((x.val.2 * y.val.2) - (x.val.1 * y.val.1)) := by
  have h : x.val.2 * (y.val.2 - y.val.1) + y.val.1 * (x.val.2 - x.val.1) =
      (x.val.2 * y.val.2) - (x.val.1 * y.val.1) := by
    rw [ring_left_distrib_sub, ring_left_distrib_sub,
        ring_mul_comm y.val.1 x.val.2, ring_mul_comm y.val.1 x.val.1]
    calc
      (x.val.2 * y.val.2 - x.val.2 * y.val.1) + (x.val.2 * y.val.1 - x.val.1 * y.val.1)
        = (x.val.2 * y.val.2 + (-(x.val.2 * y.val.1))) +
            (x.val.2 * y.val.1 + (-(x.val.1 * y.val.1))) := rfl
      _ = x.val.2 * y.val.2 + ((-(x.val.2 * y.val.1)) +
            (x.val.2 * y.val.1 + (-(x.val.1 * y.val.1)))) := ring_add_assoc _ _ _
      _ = x.val.2 * y.val.2 + (((-(x.val.2 * y.val.1)) + x.val.2 * y.val.1) +
            (-(x.val.1 * y.val.1))) := by rw [← ring_add_assoc (-(x.val.2 * y.val.1))]
      _ = x.val.2 * y.val.2 + (0 + (-(x.val.1 * y.val.1))) := by rw [ring_add_left_neg]
      _ = (x.val.2 * y.val.2) - (x.val.1 * y.val.1) := by rw [ring_zero_add]; rfl
  rw [← h]
  exact P.add_mem (P.mul_mem_left x.val.2 y.property) (P.mul_mem_left y.val.1 x.property)

instance instCommRingAmalgamatedDuplication : CommRing (AmalgamatedDuplication R P) where
  zero := ⟨(0, 0), by rw [ring_sub_self]; exact P.zero_mem⟩
  one := ⟨(1, 1), by rw [ring_sub_self]; exact P.zero_mem⟩
  add := fun x y => ⟨(x.val.1 + y.val.1, x.val.2 + y.val.2), dup_add_closed P x y⟩
  mul := fun x y => ⟨(x.val.1 * y.val.1, x.val.2 * y.val.2), dup_mul_closed P x y⟩
  neg := fun x => ⟨(-x.val.1, -x.val.2), dup_neg_closed P x⟩
  zero_ne_one := by
    intro h
    have h1 : (0 : R) = 1 := congrArg (fun z => z.val.1) h
    exact ring_zero_ne_one h1
  add_assoc := fun a b c => dup_ext P (ring_add_assoc _ _ _) (ring_add_assoc _ _ _)
  add_comm := fun a b => dup_ext P (ring_add_comm _ _) (ring_add_comm _ _)
  zero_add := fun a => dup_ext P (ring_zero_add _) (ring_zero_add _)
  add_left_neg := fun a => dup_ext P (ring_add_left_neg _) (ring_add_left_neg _)
  mul_assoc := fun a b c => dup_ext P (ring_mul_assoc _ _ _) (ring_mul_assoc _ _ _)
  mul_comm := fun a b => dup_ext P (ring_mul_comm _ _) (ring_mul_comm _ _)
  one_mul := fun a => dup_ext P (ring_one_mul _) (ring_one_mul _)
  left_distrib := fun a b c => dup_ext P (ring_left_distrib _ _ _) (ring_left_distrib _ _ _)

@[simp] theorem dup_zero_fst : (0 : AmalgamatedDuplication R P).val.1 = 0 := rfl
@[simp] theorem dup_zero_snd : (0 : AmalgamatedDuplication R P).val.2 = 0 := rfl
@[simp] theorem dup_one_fst : (1 : AmalgamatedDuplication R P).val.1 = 1 := rfl
@[simp] theorem dup_one_snd : (1 : AmalgamatedDuplication R P).val.2 = 1 := rfl
@[simp] theorem dup_add_fst (x y : AmalgamatedDuplication R P) :
    (x + y).val.1 = x.val.1 + y.val.1 := rfl
@[simp] theorem dup_add_snd (x y : AmalgamatedDuplication R P) :
    (x + y).val.2 = x.val.2 + y.val.2 := rfl
@[simp] theorem dup_mul_fst (x y : AmalgamatedDuplication R P) :
    (x * y).val.1 = x.val.1 * y.val.1 := rfl
@[simp] theorem dup_mul_snd (x y : AmalgamatedDuplication R P) :
    (x * y).val.2 = x.val.2 * y.val.2 := rfl

def diagDup (r : R) : AmalgamatedDuplication R P :=
  ⟨(r, r), by rw [ring_sub_self]; exact P.zero_mem⟩

def pullbackIdeal1 (I : Ideal R) : Ideal (AmalgamatedDuplication R P) where
  mem := fun x => I.mem x.val.1
  zero_mem := I.zero_mem
  add_mem := fun ha hb => I.add_mem ha hb
  neg_mem := fun ha => I.neg_mem ha
  mul_mem_left := fun r _ ha => I.mul_mem_left r.val.1 ha

theorem pullbackIdeal1_isPrime {Q : Ideal R} (hQ : IsPrimeIdeal R Q) :
    IsPrimeIdeal (AmalgamatedDuplication R P) (pullbackIdeal1 P Q) := by
  refine ⟨hQ.1, ?_⟩
  intro a b hab
  exact hQ.2 a.val.1 b.val.1 hab

theorem pullbackIdeal1_strictMono {I J : Ideal R} (hIJ : IdealStrictSubset I J) :
    IdealStrictSubset (pullbackIdeal1 P I) (pullbackIdeal1 P J) := by
  rcases hIJ with ⟨hsub, x, hxJ, hxI⟩
  refine ⟨fun z hz => hsub z.val.1 hz, diagDup P x, hxJ, hxI⟩

theorem lift_primeChainEndingAt {Q : Ideal R} {k : Nat}
    (h : HasPrimeChainEndingAt R Q k) :
    HasPrimeChainEndingAt (AmalgamatedDuplication R P) (pullbackIdeal1 P Q) k := by
  induction h with
  | zero hQ =>
    exact HasPrimeChainEndingAt.zero (pullbackIdeal1_isPrime P hQ)
  | step _ hP' hstrict ih =>
    exact HasPrimeChainEndingAt.step ih
      (pullbackIdeal1_isPrime P hP') (pullbackIdeal1_strictMono P hstrict)

theorem lift_primeChainOfLength {k : Nat}
    (h : HasPrimeChainOfLength R k) :
    HasPrimeChainOfLength (AmalgamatedDuplication R P) k := by
  rcases h with ⟨Q, hQ⟩
  exact ⟨pullbackIdeal1 P Q, lift_primeChainEndingAt P hQ⟩

end DuplicationStructure

/-! ## Section 4. Zero-Divisor Graph `Γ(A)`, Diameter Uniqueness, and Clause 1 (`diam ≤ 3`) -/

def IsNonzeroZeroDivisor (A : Type u) [CommRing A] (x : A) : Prop :=
  x ≠ 0 ∧ ∃ y : A, y ≠ 0 ∧ x * y = 0

def ZeroDivisorVertex (A : Type u) [CommRing A] : Type u :=
  { x : A // IsNonzeroZeroDivisor A x }

def zdgAdj {A : Type u} [CommRing A] (u v : ZeroDivisorVertex A) : Prop :=
  u ≠ v ∧ u.val * v.val = 0

theorem zdgAdj_irrefl {A : Type u} [CommRing A] (u : ZeroDivisorVertex A) : ¬ zdgAdj u u :=
  fun h => h.1 rfl

theorem zdgAdj_symm {A : Type u} [CommRing A] {u v : ZeroDivisorVertex A}
    (h : zdgAdj u v) : zdgAdj v u := by
  refine ⟨fun heq => h.1 heq.symm, ?_⟩
  rw [ring_mul_comm]
  exact h.2

inductive HasWalkOfLength {A : Type u} [CommRing A] :
    ZeroDivisorVertex A → ZeroDivisorVertex A → Nat → Prop where
  | refl (u : ZeroDivisorVertex A) : HasWalkOfLength u u 0
  | step {u w v : ZeroDivisorVertex A} {n : Nat} :
      zdgAdj u w → HasWalkOfLength w v n → HasWalkOfLength u v (n + 1)

inductive ListNodup {α : Type u} : List α → Prop where
  | nil : ListNodup []
  | cons {x : α} {xs : List α} : (∀ y : α, y ∈ xs → x ≠ y) → ListNodup xs → ListNodup (x :: xs)

inductive IsChainAdj {A : Type u} [CommRing A] : List (ZeroDivisorVertex A) → Prop where
  | nil : IsChainAdj []
  | single (u : ZeroDivisorVertex A) : IsChainAdj [u]
  | cons {u w : ZeroDivisorVertex A} {rest : List (ZeroDivisorVertex A)} :
      zdgAdj u w → IsChainAdj (w :: rest) → IsChainAdj (u :: w :: rest)

def HasSimplePathOfLength {A : Type u} [CommRing A]
    (u v : ZeroDivisorVertex A) (k : Nat) : Prop :=
  ∃ vs : List (ZeroDivisorVertex A),
    ListNodup (u :: vs) ∧ IsChainAdj (u :: vs) ∧
    (u :: vs).getLast (List.cons_ne_nil u vs) = v ∧ vs.length = k

theorem simplePath_implies_walk {A : Type u} [CommRing A] :
    ∀ (u v : ZeroDivisorVertex A) (vs : List (ZeroDivisorVertex A)),
      IsChainAdj (u :: vs) →
      (u :: vs).getLast (List.cons_ne_nil u vs) = v →
      HasWalkOfLength u v vs.length
  | u, _, [], _, hlast => by
    have hu : u = _ := hlast
    subst hu
    exact HasWalkOfLength.refl u
  | u, v, w :: rest, hchain, hlast => by
    cases hchain with
    | cons hadj hrest =>
      have hlast' : (w :: rest).getLast (List.cons_ne_nil w rest) = v := hlast
      exact HasWalkOfLength.step hadj (simplePath_implies_walk w v rest hrest hlast')

theorem walk_implies_simplePath_le {A : Type u} [CommRing A]
    {u v : ZeroDivisorVertex A} {k : Nat} (hw : HasWalkOfLength u v k) :
    ∃ m : Nat, m ≤ k ∧ HasSimplePathOfLength u v m := by
  induction hw with
  | refl u =>
    exact ⟨0, Nat.le_refl 0, [], ListNodup.cons (fun _ hy => nomatch hy) ListNodup.nil,
      IsChainAdj.single u, rfl, rfl⟩
  | @step u w _ n hadj _ ih =>
    rcases ih with ⟨m, hmn, vs, hnodup, hchain, hlast, hlen⟩
    cases Classical.em (u ∈ (w :: vs)) with
    | inl hmem =>
      have hsplit : ∀ (x : ZeroDivisorVertex A) (xs : List (ZeroDivisorVertex A)),
          ListNodup (x :: xs) → IsChainAdj (x :: xs) → u ∈ (x :: xs) →
          ∃ ys : List (ZeroDivisorVertex A),
            ListNodup (u :: ys) ∧ IsChainAdj (u :: ys) ∧
            (u :: ys).getLast (List.cons_ne_nil u ys) =
              (x :: xs).getLast (List.cons_ne_nil x xs) ∧
            ys.length ≤ xs.length := by
        intro x xs
        induction xs generalizing x with
        | nil =>
          intro hnd hch hin
          have hux : u = x := by
            cases hin with
            | head => rfl
            | tail _ hm => nomatch hm
          subst hux
          exact ⟨[], hnd, hch, rfl, Nat.le_refl 0⟩
        | cons x2 rest ihxs =>
          intro hnd hch hin
          cases hnd with
          | cons hne hnd' =>
            cases hch with
            | cons hadj_x hch' =>
              cases hin with
              | head =>
                exact ⟨x2 :: rest, ListNodup.cons hne hnd',
                  IsChainAdj.cons hadj_x hch', rfl, Nat.le_refl _⟩
              | tail _ hin' =>
                rcases ihxs x2 hnd' hch' hin' with ⟨ys, hndy, hchy, hlasty, hleny⟩
                exact ⟨ys, hndy, hchy, hlasty, Nat.le_trans hleny (Nat.le_succ _)⟩
      rcases hsplit w vs hnodup hchain hmem with ⟨ys, hndy, hchy, hlasty, hleny⟩
      rw [hlast] at hlasty
      rw [hlen] at hleny
      exact ⟨ys.length, Nat.le_trans hleny (Nat.le_trans hmn (Nat.le_succ n)),
        ys, hndy, hchy, hlasty, rfl⟩
    | inr hnmem =>
      refine ⟨m + 1, Nat.succ_le_succ hmn, w :: vs, ?_, IsChainAdj.cons hadj hchain, hlast, ?_⟩
      · exact ListNodup.cons (fun y hy heq => hnmem (heq ▸ hy)) hnodup
      · simp [hlen]

def HasDistAtMost (A : Type u) [CommRing A] (u v : ZeroDivisorVertex A) (d : Nat) : Prop :=
  ∃ m : Nat, m ≤ d ∧ HasWalkOfLength u v m

theorem exists_walk_le_iff_exists_simplePath_le {A : Type u} [CommRing A]
    (u v : ZeroDivisorVertex A) (d : Nat) :
    HasDistAtMost A u v d ↔ ∃ m : Nat, m ≤ d ∧ HasSimplePathOfLength u v m := by
  constructor
  · rintro ⟨k, hkd, hw⟩
    rcases walk_implies_simplePath_le hw with ⟨m, hmk, hsp⟩
    exact ⟨m, Nat.le_trans hmk hkd, hsp⟩
  · rintro ⟨m, hmd, vs, _, hch, hlast, hlen⟩
    subst hlen
    exact ⟨vs.length, hmd, simplePath_implies_walk u v vs hch hlast⟩

def HasExactDist (A : Type u) [CommRing A] (u v : ZeroDivisorVertex A) (d : Nat) : Prop :=
  HasWalkOfLength u v d ∧ ∀ m : Nat, m < d → ¬ HasWalkOfLength u v m

def HasDiameterAtMost (A : Type u) [CommRing A] (d : Nat) : Prop :=
  ∀ u v : ZeroDivisorVertex A, HasDistAtMost A u v d

def HasGraphDiameter (A : Type u) [CommRing A] (d : Nat) : Prop :=
  Nonempty (ZeroDivisorVertex A) ∧
  HasDiameterAtMost A d ∧
  (∃ u v : ZeroDivisorVertex A, HasExactDist A u v d)

theorem hasGraphDiameter_unique {A : Type u} [CommRing A] {d₁ d₂ : Nat}
    (h1 : HasGraphDiameter A d₁) (h2 : HasGraphDiameter A d₂) : d₁ = d₂ := by
  rcases h1 with ⟨_, hmax1, u1, v1, _, hmin1⟩
  rcases h2 with ⟨_, hmax2, u2, v2, _, hmin2⟩
  rcases hmax2 u1 v1 with ⟨m1, hm1, hw1⟩
  have hle1 : d₁ ≤ d₂ := by
    cases Nat.lt_or_ge d₂ d₁ with
    | inl hlt => exact False.elim (hmin1 m1 (Nat.lt_of_le_of_lt hm1 hlt) hw1)
    | inr hge => exact hge
  rcases hmax1 u2 v2 with ⟨m2, hm2, hw2⟩
  have hle2 : d₂ ≤ d₁ := by
    cases Nat.lt_or_ge d₁ d₂ with
    | inl hlt => exact False.elim (hmin2 m2 (Nat.lt_of_le_of_lt hm2 hlt) hw2)
    | inr hge => exact hge
  exact Nat.le_antisymm hle1 hle2

/-- **Clause 1 (Anderson–Livingston 1999, Theorem 2.3):**
    In EVERY commutative ring `A`, every pair of vertices in `Γ(A)` has distance `≤ 3`. -/
theorem zeroDivisorGraph_diameter_at_most_three (A : Type u) [CommRing A] :
    HasDiameterAtMost A 3 := by
  intro x y
  cases Classical.em (x = y) with
  | inl heq =>
    subst heq
    exact ⟨0, by omega, HasWalkOfLength.refl x⟩
  | inr hxy_ne =>
    cases Classical.em (x.val * y.val = 0) with
    | inl hxy_mul =>
      exact ⟨1, by omega, HasWalkOfLength.step ⟨hxy_ne, hxy_mul⟩ (HasWalkOfLength.refl y)⟩
    | inr hxy_nz =>
      rcases x.property.2 with ⟨a, ha_nz, hxa⟩
      rcases y.property.2 with ⟨b, hb_nz, hyb⟩
      have ha_zd : IsNonzeroZeroDivisor A a :=
        ⟨ha_nz, x.val, x.property.1, by rw [ring_mul_comm]; exact hxa⟩
      have hb_zd : IsNonzeroZeroDivisor A b :=
        ⟨hb_nz, y.val, y.property.1, by rw [ring_mul_comm]; exact hyb⟩
      let va : ZeroDivisorVertex A := ⟨a, ha_zd⟩
      let vb : ZeroDivisorVertex A := ⟨b, hb_zd⟩
      have hva_ne_y : va ≠ y := by
        intro heq
        have hval : a = y.val := congrArg Subtype.val heq
        rw [hval] at hxa
        exact hxy_nz hxa
      have hvb_ne_x : x ≠ vb := by
        intro heq
        have hval : x.val = b := congrArg Subtype.val heq
        rw [← hval, ring_mul_comm] at hyb
        exact hxy_nz hyb
      cases Classical.em (a * b = 0) with
      | inr hab_nz =>
        have hxc : x.val * (a * b) = 0 := by
          rw [← ring_mul_assoc, hxa, ring_zero_mul]
        have hcy : (a * b) * y.val = 0 := by
          rw [ring_mul_assoc, ring_mul_comm b y.val, hyb, ring_mul_zero]
        have hc_zd : IsNonzeroZeroDivisor A (a * b) :=
          ⟨hab_nz, x.val, x.property.1, by rw [ring_mul_comm]; exact hxc⟩
        let vc : ZeroDivisorVertex A := ⟨a * b, hc_zd⟩
        have hx_ne_vc : x ≠ vc := by
          intro heq
          have hval : x.val = a * b := congrArg Subtype.val heq
          rw [← hval] at hcy
          exact hxy_nz hcy
        have hvc_ne_y : vc ≠ y := by
          intro heq
          have hval : a * b = y.val := congrArg Subtype.val heq
          rw [hval] at hxc
          exact hxy_nz hxc
        exact ⟨2, by omega,
          HasWalkOfLength.step ⟨hx_ne_vc, hxc⟩
            (HasWalkOfLength.step ⟨hvc_ne_y, hcy⟩ (HasWalkOfLength.refl y))⟩
      | inl hab_zero =>
        cases Classical.em (va = vb) with
        | inl hvab_eq =>
          have hval : a = b := congrArg Subtype.val hvab_eq
          have hx_ne_va : x ≠ va := by rw [hvab_eq]; exact hvb_ne_x
          have hay : a * y.val = 0 := by rw [hval, ring_mul_comm]; exact hyb
          exact ⟨2, by omega,
            HasWalkOfLength.step ⟨hx_ne_va, hxa⟩
              (HasWalkOfLength.step ⟨hva_ne_y, hay⟩ (HasWalkOfLength.refl y))⟩
        | inr hvab_ne =>
          cases Classical.em (x = va) with
          | inl hxva =>
            have hval : x.val = a := congrArg Subtype.val hxva
            have hxb : x.val * b = 0 := by rw [hval]; exact hab_zero
            have hvb_ne_y : vb ≠ y := by
              intro heq
              have hby : b = y.val := congrArg Subtype.val heq
              rw [hby] at hxb
              exact hxy_nz hxb
            have hby_zero : b * y.val = 0 := by rw [ring_mul_comm]; exact hyb
            exact ⟨2, by omega,
              HasWalkOfLength.step ⟨hvb_ne_x, hxb⟩
                (HasWalkOfLength.step ⟨hvb_ne_y, hby_zero⟩ (HasWalkOfLength.refl y))⟩
          | inr hx_ne_va =>
            cases Classical.em (vb = y) with
            | inl hvby =>
              have hval : b = y.val := congrArg Subtype.val hvby
              have hay : a * y.val = 0 := by rw [← hval]; exact hab_zero
              exact ⟨2, by omega,
                HasWalkOfLength.step ⟨hx_ne_va, hxa⟩
                  (HasWalkOfLength.step ⟨hva_ne_y, hay⟩ (HasWalkOfLength.refl y))⟩
            | inr hvb_ne_y =>
              have hby_zero : b * y.val = 0 := by rw [ring_mul_comm]; exact hyb
              exact ⟨3, by omega,
                HasWalkOfLength.step ⟨hx_ne_va, hxa⟩
                  (HasWalkOfLength.step ⟨hvab_ne, hab_zero⟩
                    (HasWalkOfLength.step ⟨hvb_ne_y, hby_zero⟩ (HasWalkOfLength.refl y)))⟩

theorem amalgamatedDuplication_diameter_at_most_three
    (R : Type u) [CommRing R] (P : Ideal R) :
    HasDiameterAtMost (AmalgamatedDuplication R P) 3 :=
  zeroDivisorGraph_diameter_at_most_three (AmalgamatedDuplication R P)

theorem walk_len_zero_iff {A : Type u} [CommRing A] {u v : ZeroDivisorVertex A} :
    HasWalkOfLength u v 0 ↔ u = v := by
  constructor
  · intro h
    cases h
    rfl
  · intro h
    subst h
    exact HasWalkOfLength.refl u

theorem walk_len_one_iff {A : Type u} [CommRing A] {u v : ZeroDivisorVertex A} :
    HasWalkOfLength u v 1 ↔ zdgAdj u v := by
  constructor
  · intro h
    cases h with
    | step hadj hrest =>
      cases hrest
      exact hadj
  · intro hadj
    exact HasWalkOfLength.step hadj (HasWalkOfLength.refl v)

theorem walk_len_two_iff {A : Type u} [CommRing A] {u v : ZeroDivisorVertex A} :
    HasWalkOfLength u v 2 ↔ ∃ w : ZeroDivisorVertex A, zdgAdj u w ∧ zdgAdj w v := by
  constructor
  · intro h
    cases h with
    | step hadj1 hrest =>
      cases hrest with
      | step hadj2 hrest0 =>
        cases hrest0
        exact ⟨_, hadj1, hadj2⟩
  · rintro ⟨w, h1, h2⟩
    exact HasWalkOfLength.step h1 (HasWalkOfLength.step h2 (HasWalkOfLength.refl v))

/-! ## Section 5. Boolean Rings Have Krull Dimension Zero (No Prime Chains of Length `≥ 1`) -/

def IsBooleanRing (R : Type u) [CommRing R] : Prop :=
  ∀ a : R, a * a = a

theorem boolean_prime_subset_eq {R : Type u} [CommRing R] (hB : IsBooleanRing R)
    {Q₀ Q₁ : Ideal R} (hQ₀ : IsPrimeIdeal R Q₀) (hQ₁ : IsPrimeIdeal R Q₁)
    (hsub : IdealSubset Q₀ Q₁) : Q₀ = Q₁ := by
  apply Ideal.ext
  intro a
  constructor
  · exact hsub a
  · intro ha₁
    cases Classical.em (Q₀.mem a) with
    | inl ha₀ => exact ha₀
    | inr hna₀ =>
      exfalso
      have hmul0 : a * (1 - a) = 0 := by
        rw [ring_left_distrib_sub, ring_mul_one, hB a, ring_sub_self]
      have hmem0 : Q₀.mem (a * (1 - a)) := by
        rw [hmul0]
        exact Q₀.zero_mem
      cases hQ₀.2 a (1 - a) hmem0 with
      | inl ha₀ => exact hna₀ ha₀
      | inr h1ma =>
        have h1ma₁ : Q₁.mem (1 - a) := hsub (1 - a) h1ma
        have hsum : (1 - a) + a = 1 := by
          change (1 + (-a)) + a = 1
          rw [ring_add_assoc, ring_add_left_neg, ring_add_zero]
        have h1mem : Q₁.mem 1 := by
          rw [← hsum]
          exact Q₁.add_mem h1ma₁ ha₁
        exact hQ₁.1 h1mem

theorem boolean_no_prime_chain_len_one {R : Type u} [CommRing R] (hB : IsBooleanRing R) :
    ¬ HasPrimeChainOfLength R 1 := by
  rintro ⟨P, hP⟩
  cases hP with
  | step hQ hPprime hstrict =>
    have hQprime : IsPrimeIdeal R _ := hasPrimeChainEndingAt_isPrime hQ
    have heq := boolean_prime_subset_eq hB hQprime hPprime hstrict.1
    exact ((idealStrictSubset_iff_subset_and_ne _ _).mp hstrict).2 heq

theorem boolean_no_prime_chain_ge_one {R : Type u} [CommRing R] (hB : IsBooleanRing R)
    {k : Nat} (hk : 1 ≤ k) : ¬ HasPrimeChainOfLength R k := by
  intro hchain
  exact boolean_no_prime_chain_len_one hB (hasPrimeChainOfLength_mono hk hchain)

theorem amalgamatedDuplication_isBoolean {R : Type u} [CommRing R]
    (hB : IsBooleanRing R) (P : Ideal R) :
    IsBooleanRing (AmalgamatedDuplication R P) := by
  intro x
  exact dup_ext P (hB x.val.1) (hB x.val.2)

/-! ## Section 6. Exact Finite Cardinality & Uniqueness -/

def HasCardinality (α : Type u) (n : Nat) : Prop :=
  ∃ elems : List α, ListNodup elems ∧ (∀ x : α, x ∈ elems) ∧ elems.length = n

theorem list_remove_length {α : Type u} :
    ∀ (xs : List α) (a : α), ListNodup xs → a ∈ xs →
      ∃ ys : List α, ListNodup ys ∧
        (∀ z : α, z ∈ ys ↔ (z ∈ xs ∧ z ≠ a)) ∧ xs.length = ys.length + 1
  | [], _, _, ha => nomatch ha
  | x :: rest, a, ListNodup.cons hne hnd, ha => by
    cases Classical.em (x = a) with
    | inl hxa =>
      subst hxa
      refine ⟨rest, hnd, ?_, rfl⟩
      intro z
      constructor
      · intro hz
        exact ⟨List.Mem.tail x hz, fun hzx => hne z hz hzx.symm⟩
      · rintro ⟨hz, hza⟩
        cases hz with
        | head => exact False.elim (hza rfl)
        | tail _ hzr => exact hzr
    | inr hxna =>
      have har : a ∈ rest := by
        cases ha with
        | head => exact False.elim (hxna rfl)
        | tail _ hm => exact hm
      rcases list_remove_length rest a hnd har with ⟨ys, hndy, hmemy, hleny⟩
      refine ⟨x :: ys, ListNodup.cons (fun z hz => hne z ((hmemy z).mp hz).1) hndy, ?_, ?_⟩
      · intro z
        constructor
        · intro hz
          cases hz with
          | head => exact ⟨List.Mem.head rest, hxna⟩
          | tail _ hzy =>
            rcases (hmemy z).mp hzy with ⟨hzr, hza⟩
            exact ⟨List.Mem.tail x hzr, hza⟩
        · rintro ⟨hz, hza⟩
          cases hz with
          | head => exact List.Mem.head ys
          | tail _ hzr => exact List.Mem.tail x ((hmemy z).mpr ⟨hzr, hza⟩)
      · simp [hleny]

theorem nodup_length_le_of_subset {α : Type u} :
    ∀ (xs ys : List α), ListNodup xs → ListNodup ys →
      (∀ z : α, z ∈ xs → z ∈ ys) → xs.length ≤ ys.length
  | [], _, _, _, _ => Nat.zero_le _
  | x :: rest, ys, ListNodup.cons hne hndx, hndy, hsub => by
    have hxy : x ∈ ys := hsub x (List.Mem.head rest)
    rcases list_remove_length ys x hndy hxy with ⟨ys', hndy', hmemy', hleny⟩
    have hsub' : ∀ z : α, z ∈ rest → z ∈ ys' := by
      intro z hz
      exact (hmemy' z).mpr ⟨hsub z (List.Mem.tail x hz), fun hzx => hne z hz hzx.symm⟩
    have hle := nodup_length_le_of_subset rest ys' hndx hndy' hsub'
    simp only [List.length_cons]
    omega

theorem hasCardinality_unique {α : Type u} {m n : Nat}
    (hm : HasCardinality α m) (hn : HasCardinality α n) : m = n := by
  rcases hm with ⟨xs, hndx, hallx, hlenx⟩
  rcases hn with ⟨ys, hndy, hally, hleny⟩
  have h1 := nodup_length_le_of_subset xs ys hndx hndy (fun z _ => hally z)
  have h2 := nodup_length_le_of_subset ys xs hndy hndx (fun z _ => hallx z)
  omega

theorem listNodup_map {α : Type u} {β : Type v} (f : α → β)
    (hinj : ∀ a₁ a₂ : α, f a₁ = f a₂ → a₁ = a₂) :
    ∀ (xs : List α), ListNodup xs → ListNodup (xs.map f)
  | [], _ => ListNodup.nil
  | x :: rest, ListNodup.cons hne hnd => by
    refine ListNodup.cons ?_ (listNodup_map f hinj rest hnd)
    intro y hy heq
    rcases List.mem_map.mp hy with ⟨x', hx', rfl⟩
    exact hne x' hx' (hinj x x' heq)

theorem ringIso_preserves_cardinality {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    {m n : Nat} (hm : HasCardinality R m) (hn : HasCardinality S n)
    (e : RingIso R S) : m = n := by
  rcases hm with ⟨xs, hndx, hallx, hlenx⟩
  have hmS : HasCardinality S m := by
    refine ⟨xs.map e.toFun, listNodup_map e.toFun (fun _ _ h => ringIso_toFun_inj e h) xs hndx, ?_, ?_⟩
    · intro b
      exact List.mem_map.mpr ⟨e.invFun b, hallx (e.invFun b), e.right_inv b⟩
    · simp [hlenx]
  exact hasCardinality_unique hmS hn

/-! ## Section 7. `𝔽₂` and Infinite Boolean Counterexample Family `R^(m) = 𝔽₂^(m+2)` -/

inductive F2 : Type where
  | zero : F2
  | one : F2
  deriving DecidableEq

def f2Add : F2 → F2 → F2
  | .zero, b => b
  | .one, .zero => .one
  | .one, .one => .zero

def f2Mul : F2 → F2 → F2
  | .one, .one => .one
  | _, _ => .zero

instance instCommRingF2 : CommRing F2 where
  zero := F2.zero
  one := F2.one
  add := f2Add
  mul := f2Mul
  neg := fun a => a
  zero_ne_one := by intro h; cases h
  add_assoc := by intro a b c; cases a <;> cases b <;> cases c <;> rfl
  add_comm := by intro a b; cases a <;> cases b <;> rfl
  zero_add := by intro a; cases a <;> rfl
  add_left_neg := by intro a; cases a <;> rfl
  mul_assoc := by intro a b c; cases a <;> cases b <;> cases c <;> rfl
  mul_comm := by intro a b; cases a <;> cases b <;> rfl
  one_mul := by intro a; cases a <;> rfl
  left_distrib := by intro a b c; cases a <;> cases b <;> cases c <;> rfl

@[simp] theorem f2_zero_eq : F2.zero = (0 : F2) := rfl
@[simp] theorem f2_one_eq : F2.one = (1 : F2) := rfl
@[simp] theorem f2_mul_zero_simp (a : F2) : a * (0 : F2) = 0 := by cases a <;> rfl
@[simp] theorem f2_zero_mul_simp (a : F2) : (0 : F2) * a = 0 := by cases a <;> rfl
@[simp] theorem f2_mul_one_simp (a : F2) : a * (1 : F2) = a := by cases a <;> rfl
@[simp] theorem f2_one_mul_simp (a : F2) : (1 : F2) * a = a := by cases a <;> rfl

theorem f2_isBoolean : IsBooleanRing F2 := by
  intro a
  cases a <;> rfl

theorem f2_isDomain : IsIntegralDomain F2 := by
  intro a b hab
  cases a <;> cases b
  · exact Or.inl rfl
  · exact Or.inl rfl
  · exact Or.inr rfl
  · cases hab

def BoolVec (n : Nat) : Type := Fin n → F2

instance instCommRingBoolVecSucc (k : Nat) : CommRing (BoolVec (k + 1)) where
  zero := fun _ => 0
  one := fun _ => 1
  add := fun f g i => f i + g i
  mul := fun f g i => f i * g i
  neg := fun f i => -f i
  zero_ne_one := by
    intro h
    have h0 : (0 : F2) = 1 := congrFun h ⟨0, Nat.zero_lt_succ k⟩
    exact ring_zero_ne_one h0
  add_assoc := fun f g h => funext (fun i => ring_add_assoc (f i) (g i) (h i))
  add_comm := fun f g => funext (fun i => ring_add_comm (f i) (g i))
  zero_add := fun f => funext (fun i => ring_zero_add (f i))
  add_left_neg := fun f => funext (fun i => ring_add_left_neg (f i))
  mul_assoc := fun f g h => funext (fun i => ring_mul_assoc (f i) (g i) (h i))
  mul_comm := fun f g => funext (fun i => ring_mul_comm (f i) (g i))
  one_mul := fun f => funext (fun i => ring_one_mul (f i))
  left_distrib := fun f g h => funext (fun i => ring_left_distrib (f i) (g i) (h i))

@[simp] theorem boolVec_zero_apply {k : Nat} (i : Fin (k + 1)) :
    (0 : BoolVec (k + 1)) i = 0 := rfl
@[simp] theorem boolVec_one_apply {k : Nat} (i : Fin (k + 1)) :
    (1 : BoolVec (k + 1)) i = 1 := rfl
@[simp] theorem boolVec_add_apply {k : Nat} (f g : BoolVec (k + 1)) (i : Fin (k + 1)) :
    (f + g) i = f i + g i := rfl
@[simp] theorem boolVec_mul_apply {k : Nat} (f g : BoolVec (k + 1)) (i : Fin (k + 1)) :
    (f * g) i = f i * g i := rfl

theorem boolVec_isBoolean (k : Nat) : IsBooleanRing (BoolVec (k + 1)) := by
  intro f
  exact funext (fun i => f2_isBoolean (f i))

def consBoolVec {n : Nat} (b : F2) (f : BoolVec n) : BoolVec (n + 1) :=
  fun i =>
    if _ : i.val = 0 then b
    else f ⟨i.val - 1, by omega⟩

theorem consBoolVec_inj {n : Nat} {b₁ b₂ : F2} {f₁ f₂ : BoolVec n}
    (h : consBoolVec b₁ f₁ = consBoolVec b₂ f₂) : b₁ = b₂ ∧ f₁ = f₂ := by
  have hb : b₁ = b₂ := by
    have h0 := congrFun h ⟨0, Nat.zero_lt_succ n⟩
    simpa [consBoolVec] using h0
  refine ⟨hb, funext (fun j => ?_)⟩
  have hj := congrFun h ⟨j.val + 1, Nat.succ_lt_succ j.isLt⟩
  have hne : j.val + 1 ≠ 0 := Nat.succ_ne_zero j.val
  simpa [consBoolVec, hne] using hj

def allBoolVecs : (n : Nat) → List (BoolVec n)
  | 0 => [fun i => nomatch i]
  | n + 1 =>
    (allBoolVecs n).map (consBoolVec F2.zero) ++
    (allBoolVecs n).map (consBoolVec F2.one)

theorem allBoolVecs_length : ∀ n : Nat, (allBoolVecs n).length = 2 ^ n
  | 0 => rfl
  | n + 1 => by
    simp [allBoolVecs, allBoolVecs_length n, Nat.pow_succ]
    omega

theorem nodup_append {α : Type u} :
    ∀ (xs ys : List α), ListNodup xs → ListNodup ys →
      (∀ a : α, a ∈ xs → a ∈ ys → False) → ListNodup (xs ++ ys)
  | [], ys, _, hndy, _ => hndy
  | x :: rest, ys, ListNodup.cons hne hndx, hndy, hdisj => by
    refine ListNodup.cons ?_ (nodup_append rest ys hndx hndy
      (fun a ha hay => hdisj a (List.Mem.tail x ha) hay))
    intro z hz hxz
    rw [← hxz] at hz
    cases List.mem_append.mp hz with
    | inl hzr => exact hne x hzr rfl
    | inr hzy => exact hdisj x (List.Mem.head rest) hzy

theorem allBoolVecs_nodup : ∀ n : Nat, ListNodup (allBoolVecs n)
  | 0 => ListNodup.cons (fun _ hy => nomatch hy) ListNodup.nil
  | n + 1 => by
    have ih := allBoolVecs_nodup n
    have h0 := listNodup_map (consBoolVec F2.zero)
      (fun _ _ h => (consBoolVec_inj h).2) (allBoolVecs n) ih
    have h1 := listNodup_map (consBoolVec F2.one)
      (fun _ _ h => (consBoolVec_inj h).2) (allBoolVecs n) ih
    refine nodup_append _ _ h0 h1 ?_
    intro g hg0 hg1
    rcases List.mem_map.mp hg0 with ⟨f0, _, hf0⟩
    rcases List.mem_map.mp hg1 with ⟨f1, _, hf1⟩
    rw [← hf0] at hf1
    have hb := (consBoolVec_inj hf1).1
    cases hb

theorem allBoolVecs_complete : ∀ (n : Nat) (g : BoolVec n), g ∈ allBoolVecs n
  | 0, g => by
    have heq : g = (fun i => nomatch i) := funext (fun i => nomatch i)
    rw [heq]
    exact List.Mem.head []
  | n + 1, g => by
    let tail : BoolVec n := fun j => g ⟨j.val + 1, Nat.succ_lt_succ j.isLt⟩
    have htail : tail ∈ allBoolVecs n := allBoolVecs_complete n tail
    have hg : g = consBoolVec (g ⟨0, Nat.zero_lt_succ n⟩) tail := by
      apply funext
      intro i
      cases hi : i.val with
      | zero =>
        have hi0 : i = ⟨0, Nat.zero_lt_succ n⟩ := Fin.ext hi
        rw [hi0]
        simp [consBoolVec]
      | succ j =>
        have hlt_j : j < n := by omega
        have hij : (⟨i.val - 1, by omega⟩ : Fin n) = ⟨j, hlt_j⟩ := by
          apply Fin.ext
          dsimp
          omega
        have hi' : i = ⟨j + 1, Nat.succ_lt_succ hlt_j⟩ := Fin.ext hi
        simp [consBoolVec, hi, tail, hij, hi']
    rw [hg]
    cases g ⟨0, Nat.zero_lt_succ n⟩ with
    | zero =>
      exact List.mem_append.mpr (Or.inl (List.mem_map.mpr ⟨tail, htail, rfl⟩))
    | one =>
      exact List.mem_append.mpr (Or.inr (List.mem_map.mpr ⟨tail, htail, rfl⟩))

theorem boolVec_hasCardinality (n : Nat) : HasCardinality (BoolVec n) (2 ^ n) :=
  ⟨allBoolVecs n, allBoolVecs_nodup n, allBoolVecs_complete n, allBoolVecs_length n⟩

def firstCoordZeroIdeal (k : Nat) : Ideal (BoolVec (k + 1)) where
  mem := fun f => f ⟨0, Nat.zero_lt_succ k⟩ = 0
  zero_mem := rfl
  add_mem := by
    intro a b ha hb
    change a ⟨0, _⟩ + b ⟨0, _⟩ = 0
    rw [ha, hb]
    rfl
  neg_mem := by
    intro a ha
    exact ha
  mul_mem_left := by
    intro r a ha
    change r ⟨0, _⟩ * a ⟨0, _⟩ = 0
    rw [ha, ring_mul_zero]

theorem firstCoordZeroIdeal_isPrime (k : Nat) :
    IsPrimeIdeal (BoolVec (k + 1)) (firstCoordZeroIdeal k) := by
  refine ⟨?_, ?_⟩
  · intro h
    exact ring_zero_ne_one h.symm
  · intro a b hab
    exact f2_isDomain (a ⟨0, Nat.zero_lt_succ k⟩) (b ⟨0, Nat.zero_lt_succ k⟩) hab

abbrev CounterexampleRingFamily (m : Nat) : Type := BoolVec (m + 2)
abbrev CounterexamplePrimeFamily (m : Nat) : Ideal (CounterexampleRingFamily m) :=
  firstCoordZeroIdeal (m + 1)
abbrev CounterexampleDupFamily (m : Nat) : Type :=
  AmalgamatedDuplication (CounterexampleRingFamily m) (CounterexamplePrimeFamily m)

theorem pow2_strict_mono {a b : Nat} (h : a < b) : 2 ^ a < 2 ^ b := by
  induction b with
  | zero => omega
  | succ b ih =>
    have hpos : 0 < 2 ^ b := by
      clear h ih
      induction b with
      | zero => omega
      | succ k ihk => simp [Nat.pow_succ]; omega
    cases Nat.eq_or_lt_of_le (Nat.le_of_lt_succ h) with
    | inl heq =>
      subst heq
      simp [Nat.pow_succ]
      omega
    | inr hlt =>
      have ih' := ih hlt
      simp [Nat.pow_succ]
      omega

theorem counterexampleRingFamily_pairwise_noniso {m₁ m₂ : Nat} (hne : m₁ ≠ m₂) :
    ¬ Nonempty (RingIso (CounterexampleRingFamily m₁) (CounterexampleRingFamily m₂)) := by
  rintro ⟨e⟩
  have hcard := ringIso_preserves_cardinality
    (boolVec_hasCardinality (m₁ + 2)) (boolVec_hasCardinality (m₂ + 2)) e
  cases Nat.lt_or_gt_of_ne hne with
  | inl hlt =>
    have hlt2 := pow2_strict_mono (Nat.add_lt_add_right hlt 2)
    omega
  | inr hgt =>
    have hgt2 := pow2_strict_mono (Nat.add_lt_add_right hgt 2)
    omega

/-- Isomorphism `(𝔽₂^(m+2)) ⋈ P^(m) ≅ 𝔽₂^(2m+3)` (note `2*m + 3 = (2*m + 2) + 1`),
    establishing exact cardinality `2^(2m+3)` and pairwise non-isomorphism of the
    duplicated rings as well. -/
def dupToBoolVecIso (m : Nat) :
    RingIso (CounterexampleDupFamily m) (BoolVec ((2 * m + 2) + 1)) where
  toFun := fun x i =>
    if hi : i.val < m + 2 then x.val.1 ⟨i.val, hi⟩
    else x.val.2 ⟨i.val - (m + 1), by omega⟩
  invFun := fun g =>
    ⟨(fun j => g ⟨j.val, by omega⟩,
      fun j =>
        if _ : j.val = 0 then g ⟨0, by omega⟩
        else g ⟨j.val + (m + 1), by omega⟩),
     by
       change g ⟨0, _⟩ - g ⟨0, _⟩ = 0
       exact ring_sub_self _⟩
  left_inv := by
    intro x
    apply dup_ext (CounterexamplePrimeFamily m)
    · apply funext
      intro j
      have hj : j.val < m + 2 := j.isLt
      simp [hj]
    · apply funext
      intro j
      cases hj0 : j.val with
      | zero =>
        have hj_eq : j = ⟨0, by omega⟩ := Fin.ext hj0
        rw [hj_eq]
        have hx : x.val.2 ⟨0, by omega⟩ - x.val.1 ⟨0, by omega⟩ = 0 := x.property
        have hx' := (ring_sub_eq_zero.mp hx).symm
        simpa using hx'
      | succ k =>
        have hne : j.val ≠ 0 := by omega
        have hnlt : ¬ (j.val + (m + 1) < m + 2) := by omega
        have hsub : (⟨j.val + (m + 1) - (m + 1), by omega⟩ : Fin (m + 2)) = j := by
          apply Fin.ext
          dsimp
          omega
        simp [hne, hnlt, hsub]
  right_inv := by
    intro g
    apply funext
    intro i
    by_cases hi : i.val < m + 2
    · simp [hi]
    · have hne0 : i.val - (m + 1) ≠ 0 := by omega
      have hidx : (⟨i.val - (m + 1) + (m + 1), by omega⟩ : Fin ((2 * m + 2) + 1)) = i := by
        apply Fin.ext
        dsimp
        omega
      simp [hi, hne0, hidx]
  map_add := by
    intro a b
    apply funext
    intro i
    change (if hi : i.val < m + 2 then (a + b).val.1 ⟨i.val, hi⟩ else (a + b).val.2 ⟨i.val - (m + 1), _⟩) =
      (if hi : i.val < m + 2 then a.val.1 ⟨i.val, hi⟩ else a.val.2 ⟨i.val - (m + 1), _⟩) +
      (if hi : i.val < m + 2 then b.val.1 ⟨i.val, hi⟩ else b.val.2 ⟨i.val - (m + 1), _⟩)
    by_cases hi : i.val < m + 2 <;> simp [hi]
  map_mul := by
    intro a b
    apply funext
    intro i
    change (if hi : i.val < m + 2 then (a * b).val.1 ⟨i.val, hi⟩ else (a * b).val.2 ⟨i.val - (m + 1), _⟩) =
      (if hi : i.val < m + 2 then a.val.1 ⟨i.val, hi⟩ else a.val.2 ⟨i.val - (m + 1), _⟩) *
      (if hi : i.val < m + 2 then b.val.1 ⟨i.val, hi⟩ else b.val.2 ⟨i.val - (m + 1), _⟩)
    by_cases hi : i.val < m + 2 <;> simp [hi]

theorem counterexampleDupFamily_pairwise_noniso {m₁ m₂ : Nat} (hne : m₁ ≠ m₂) :
    ¬ Nonempty (RingIso (CounterexampleDupFamily m₁) (CounterexampleDupFamily m₂)) := by
  rintro ⟨e⟩
  let e1 := dupToBoolVecIso m₁
  let e2 := dupToBoolVecIso m₂
  let comp : RingIso (BoolVec ((2 * m₁ + 2) + 1)) (BoolVec ((2 * m₂ + 2) + 1)) := {
    toFun := fun v => e2.toFun (e.toFun (e1.invFun v))
    invFun := fun w => e1.toFun (e.invFun (e2.invFun w))
    left_inv := fun v => by rw [e2.left_inv, e.left_inv, e1.right_inv]
    right_inv := fun w => by rw [e1.left_inv, e.right_inv, e2.right_inv]
    map_add := fun u v => by
      have hinv : ∀ x y, e1.invFun (x + y) = e1.invFun x + e1.invFun y := by
        intro x y
        apply ringIso_toFun_inj e1
        rw [e1.right_inv, e1.map_add, e1.right_inv, e1.right_inv]
      rw [hinv, e.map_add, e2.map_add]
    map_mul := fun u v => by
      have hinv : ∀ x y, e1.invFun (x * y) = e1.invFun x * e1.invFun y := by
        intro x y
        apply ringIso_toFun_inj e1
        rw [e1.right_inv, e1.map_mul, e1.right_inv, e1.right_inv]
      rw [hinv, e.map_mul, e2.map_mul]
  }
  have hcard := ringIso_preserves_cardinality
    (boolVec_hasCardinality ((2 * m₁ + 2) + 1))
    (boolVec_hasCardinality ((2 * m₂ + 2) + 1)) comp
  cases Nat.lt_or_gt_of_ne hne with
  | inl hlt =>
    have hlt2 := pow2_strict_mono (by omega : (2 * m₁ + 2) + 1 < (2 * m₂ + 2) + 1)
    omega
  | inr hgt =>
    have hgt2 := pow2_strict_mono (by omega : (2 * m₂ + 2) + 1 < (2 * m₁ + 2) + 1)
    omega

/-- Exact diameter `3` of `Γ(R^(m) ⋈ P^(m))` for every `m : Nat`! -/
theorem counterexampleDupFamily_hasDiameter_three (m : Nat) :
    HasGraphDiameter (CounterexampleDupFamily m) 3 := by
  let idx0 : Fin (m + 2) := ⟨0, by omega⟩
  let idx1 : Fin (m + 2) := ⟨1, by omega⟩
  let fx : BoolVec (m + 2) := fun i => if i.val = 0 then 0 else 1
  let fy : BoolVec (m + 2) := fun i => if i.val = 1 then 0 else 1
  let g1 : BoolVec (m + 2) := fun _ => 1
  let e0 : BoolVec (m + 2) := fun i => if i.val = 0 then 1 else 0
  let e1 : BoolVec (m + 2) := fun i => if i.val = 1 then 1 else 0
  let z0 : BoolVec (m + 2) := fun _ => 0

  let x : CounterexampleDupFamily m := ⟨(fx, fx), by change fx idx0 - fx idx0 = 0; exact ring_sub_self _⟩
  let y : CounterexampleDupFamily m := ⟨(fy, g1), by change g1 idx0 - fy idx0 = 0; rfl⟩
  let a : CounterexampleDupFamily m := ⟨(e0, e0), by change e0 idx0 - e0 idx0 = 0; exact ring_sub_self _⟩
  let b : CounterexampleDupFamily m := ⟨(e1, z0), by change z0 idx0 - e1 idx0 = 0; rfl⟩

  have hx_nz : x ≠ 0 := by
    intro h
    have h1 : fx idx1 = 0 := congrFun (congrArg (fun u => u.val.1) h) idx1
    simp [fx, idx1] at h1
  have hy_nz : y ≠ 0 := by
    intro h
    have h0 : fy idx0 = 0 := congrFun (congrArg (fun u => u.val.1) h) idx0
    simp [fy, idx0] at h0
  have ha_nz : a ≠ 0 := by
    intro h
    have h0 : e0 idx0 = 0 := congrFun (congrArg (fun u => u.val.1) h) idx0
    simp [e0, idx0] at h0
  have hb_nz : b ≠ 0 := by
    intro h
    have h1 : e1 idx1 = 0 := congrFun (congrArg (fun u => u.val.1) h) idx1
    simp [e1, idx1] at h1

  have hxa : x * a = 0 := by
    apply dup_ext (CounterexamplePrimeFamily m) <;> apply funext <;> intro i
    · change fx i * e0 i = 0
      by_cases hi : i.val = 0 <;> simp [fx, e0, hi]
    · change fx i * e0 i = 0
      by_cases hi : i.val = 0 <;> simp [fx, e0, hi]
  have hyb : y * b = 0 := by
    apply dup_ext (CounterexamplePrimeFamily m) <;> apply funext <;> intro i
    · change fy i * e1 i = 0
      by_cases hi : i.val = 1 <;> simp [fy, e1, hi]
    · change g1 i * z0 i = 0
      simp [g1, z0]
  have hab : a * b = 0 := by
    apply dup_ext (CounterexamplePrimeFamily m) <;> apply funext <;> intro i
    · change e0 i * e1 i = 0
      by_cases hi0 : i.val = 0
      · have hi1 : i.val ≠ 1 := by omega
        simp [e0, e1, hi0, hi1]
      · simp [e0, e1, hi0]
    · change e0 i * z0 i = 0
      simp [e0, z0]

  let vx : ZeroDivisorVertex (CounterexampleDupFamily m) := ⟨x, hx_nz, a, ha_nz, hxa⟩
  let vy : ZeroDivisorVertex (CounterexampleDupFamily m) := ⟨y, hy_nz, b, hb_nz, hyb⟩
  let va : ZeroDivisorVertex (CounterexampleDupFamily m) :=
    ⟨a, ha_nz, x, hx_nz, by rw [ring_mul_comm]; exact hxa⟩
  let vb : ZeroDivisorVertex (CounterexampleDupFamily m) :=
    ⟨b, hb_nz, y, hy_nz, by rw [ring_mul_comm]; exact hyb⟩

  have hvx_ne_va : vx ≠ va := by
    intro h
    have h0 : fx idx0 = e0 idx0 := congrFun (congrArg (fun u => u.val.val.1) h) idx0
    simp [fx, e0, idx0] at h0
  have hva_ne_vb : va ≠ vb := by
    intro h
    have h0 : e0 idx0 = e1 idx0 := congrFun (congrArg (fun u => u.val.val.1) h) idx0
    simp [e0, e1, idx0] at h0
  have hvb_ne_vy : vb ≠ vy := by
    intro h
    have h0 : e1 idx0 = fy idx0 := congrFun (congrArg (fun u => u.val.val.1) h) idx0
    simp [e1, fy, idx0] at h0
  have hby : b * y = 0 := by rw [ring_mul_comm]; exact hyb

  have hwalk3 : HasWalkOfLength vx vy 3 :=
    HasWalkOfLength.step ⟨hvx_ne_va, hxa⟩
      (HasWalkOfLength.step ⟨hva_ne_vb, hab⟩
        (HasWalkOfLength.step ⟨hvb_ne_vy, hby⟩ (HasWalkOfLength.refl vy)))

  refine ⟨⟨vx⟩, amalgamatedDuplication_diameter_at_most_three _ _, vx, vy, hwalk3, ?_⟩
  intro d hd hwd
  match d with
  | 0 =>
    have heq := walk_len_zero_iff.mp hwd
    have h0 : fx idx0 = fy idx0 := congrFun (congrArg (fun u => u.val.val.1) heq) idx0
    simp [fx, fy, idx0] at h0
  | 1 =>
    have hadj := walk_len_one_iff.mp hwd
    have hmul1 : fx idx1 * g1 idx1 = 0 := by
      have h2 := congrFun (congrArg (fun u => u.val.2) hadj.2) idx1
      simpa [vx, vy, x, y] using h2
    simp [fx, g1, idx1] at hmul1
  | 2 =>
    rcases walk_len_two_iff.mp hwd with ⟨w, hxw, hwy⟩
    apply w.property.1
    apply dup_ext (CounterexamplePrimeFamily m)
    · apply funext
      intro i
      by_cases hi0 : i.val = 0
      · have hi_eq : i = idx0 := Fin.ext hi0
        rw [hi_eq]
        have hw2_0 : w.val.val.2 idx0 * g1 idx0 = 0 :=
          congrFun (congrArg (fun u => u.val.2) hwy.2) idx0
        have hw2_zero : w.val.val.2 idx0 = 0 := by
          simpa [g1] using hw2_0
        have hmem : w.val.val.2 idx0 - w.val.val.1 idx0 = 0 := w.val.property
        have heq12 := ring_sub_eq_zero.mp hmem
        rw [hw2_zero] at heq12
        exact heq12.symm
      · have h1 : fx i * w.val.val.1 i = 0 :=
          congrFun (congrArg (fun u => u.val.1) hxw.2) i
        have hfx1 : fx i = 1 := by simp [fx, hi0]
        rw [hfx1] at h1
        simpa using h1
    · apply funext
      intro i
      have hw2 : w.val.val.2 i * g1 i = 0 :=
        congrFun (congrArg (fun u => u.val.2) hwy.2) i
      simpa [g1] using hw2
  | d + 3 => omega

theorem counterexampleFamily_no_primeChain_base (m : Nat) {k : Nat} (hk : 1 ≤ k) :
    ¬ HasPrimeChainOfLength (CounterexampleRingFamily m) k :=
  boolean_no_prime_chain_ge_one (boolVec_isBoolean (m + 1)) hk

theorem counterexampleFamily_no_primeChain_dup (m : Nat) {k : Nat} (hk : 1 ≤ k) :
    ¬ HasPrimeChainOfLength (CounterexampleDupFamily m) k :=
  boolean_no_prime_chain_ge_one
    (amalgamatedDuplication_isBoolean (boolVec_isBoolean (m + 1)) (CounterexamplePrimeFamily m)) hk

/-! ## Section 8. Integral Domain Duplication Theorem (`diam(Γ(D ⋈ P)) = 2 ≠ 3`) -/

section DomainDuplication
variable {D : Type u} [CommRing D]

theorem domain_nonzero_proper_ideal_two_distinct
    (hdom : IsIntegralDomain D) {P : Ideal D} (hnot1 : ¬ P.mem 1)
    {p : D} (hp_mem : P.mem p) (hp_nz : p ≠ 0) :
    ∃ p₁ p₂ : D, P.mem p₁ ∧ P.mem p₂ ∧ p₁ ≠ 0 ∧ p₂ ≠ 0 ∧ p₁ ≠ p₂ := by
  cases Classical.em (p + p = 0) with
  | inr h2p_nz =>
    refine ⟨p, p + p, hp_mem, P.add_mem hp_mem hp_mem, hp_nz, h2p_nz, ?_⟩
    intro heq
    have h0 : p + 0 = p + p := by rw [ring_add_zero]; exact heq
    exact hp_nz (ring_add_left_cancel h0).symm
  | inl _ =>
    cases Classical.em (∃ r : D, r ≠ 0 ∧ r ≠ 1) with
    | inl hex =>
      rcases hex with ⟨r, hr0, hr1⟩
      have hrp_nz : r * p ≠ 0 := by
        intro hz
        cases hdom r p hz with
        | inl h => exact hr0 h
        | inr h => exact hp_nz h
      refine ⟨p, r * p, hp_mem, P.mul_mem_left r hp_mem, hp_nz, hrp_nz, ?_⟩
      intro heq
      have hsub : (r - 1) * p = 0 := by
        rw [ring_right_distrib_sub, ring_one_mul, ← heq, ring_sub_self]
      cases hdom (r - 1) p hsub with
      | inl hr_eq => exact hr1 (ring_sub_eq_zero.mp hr_eq)
      | inr hp0 => exact hp_nz hp0
    | inr hno =>
      exfalso
      cases Classical.em (p = 1) with
      | inl hp1 =>
        rw [hp1] at hp_mem
        exact hnot1 hp_mem
      | inr hp1 =>
        exact hno ⟨p, hp_nz, hp1⟩

theorem domain_dup_zd_partition (hdom : IsIntegralDomain D) (P : Ideal D)
    (z : ZeroDivisorVertex (AmalgamatedDuplication D P)) :
    (z.val.val.1 = 0 ∧ z.val.val.2 ≠ 0 ∧ P.mem z.val.val.2) ∨
    (z.val.val.2 = 0 ∧ z.val.val.1 ≠ 0 ∧ P.mem z.val.val.1) := by
  rcases z.property with ⟨hz_nz, w, hw_nz, hzw⟩
  have h1 : z.val.val.1 * w.val.1 = 0 := congrArg Prod.fst (congrArg Subtype.val hzw)
  have h2 : z.val.val.2 * w.val.2 = 0 := congrArg Prod.snd (congrArg Subtype.val hzw)
  cases hdom z.val.val.1 w.val.1 h1 with
  | inl hz1 =>
    left
    have hz2_nz : z.val.val.2 ≠ 0 := by
      intro hz2
      exact hz_nz (dup_ext P hz1 hz2)
    have hmem : P.mem (z.val.val.2 - z.val.val.1) := z.val.property
    rw [hz1, ring_sub_zero] at hmem
    exact ⟨hz1, hz2_nz, hmem⟩
  | inr hw1 =>
    cases hdom z.val.val.2 w.val.2 h2 with
    | inl hz2 =>
      right
      have hz1_nz : z.val.val.1 ≠ 0 := by
        intro hz1
        exact hz_nz (dup_ext P hz1 hz2)
      have hmem : P.mem (z.val.val.2 - z.val.val.1) := z.val.property
      rw [hz2, ring_zero_sub] at hmem
      have hmem' : P.mem (-(-z.val.val.1)) := P.neg_mem hmem
      rw [ring_neg_neg] at hmem'
      exact ⟨hz2, hz1_nz, hmem'⟩
    | inr hw2 =>
      exact False.elim (hw_nz (dup_ext P hw1 hw2))

def leftDupZd (P : Ideal D) (p : D) (hp_mem : P.mem p) (hp_nz : p ≠ 0) :
    ZeroDivisorVertex (AmalgamatedDuplication D P) :=
  let u : AmalgamatedDuplication D P := ⟨(0, p), by rw [ring_sub_zero]; exact hp_mem⟩
  let v : AmalgamatedDuplication D P :=
    ⟨(p, 0), by rw [ring_zero_sub]; exact P.neg_mem hp_mem⟩
  have hu_nz : u ≠ 0 := fun h => hp_nz (congrArg (fun x => x.val.2) h)
  have hv_nz : v ≠ 0 := fun h => hp_nz (congrArg (fun x => x.val.1) h)
  have huv : u * v = 0 := dup_ext P (ring_zero_mul p) (ring_mul_zero p)
  ⟨u, hu_nz, v, hv_nz, huv⟩

def rightDupZd (P : Ideal D) (p : D) (hp_mem : P.mem p) (hp_nz : p ≠ 0) :
    ZeroDivisorVertex (AmalgamatedDuplication D P) :=
  let u : AmalgamatedDuplication D P :=
    ⟨(p, 0), by rw [ring_zero_sub]; exact P.neg_mem hp_mem⟩
  let v : AmalgamatedDuplication D P := ⟨(0, p), by rw [ring_sub_zero]; exact hp_mem⟩
  have hu_nz : u ≠ 0 := fun h => hp_nz (congrArg (fun x => x.val.1) h)
  have hv_nz : v ≠ 0 := fun h => hp_nz (congrArg (fun x => x.val.2) h)
  have huv : u * v = 0 := dup_ext P (ring_mul_zero p) (ring_zero_mul p)
  ⟨u, hu_nz, v, hv_nz, huv⟩

/-- **General Integral Domain Duplication Theorem:**
    For EVERY commutative integral domain `D` and EVERY nonzero prime ideal `P` of `D`,
    `Γ(D ⋈ P)` is complete bipartite of **exact diameter 2** (never `3`). -/
theorem domain_nonzero_prime_duplication_diam_two
    (hdom : IsIntegralDomain D) {P : Ideal D} (hP : IsPrimeIdeal D P)
    (hne0 : ∃ p : D, P.mem p ∧ p ≠ 0) :
    HasGraphDiameter (AmalgamatedDuplication D P) 2 := by
  rcases hne0 with ⟨p, hp_mem, hp_nz⟩
  rcases domain_nonzero_proper_ideal_two_distinct hdom hP.1 hp_mem hp_nz with
    ⟨p₁, p₂, hp₁_mem, hp₂_mem, hp₁_nz, hp₂_nz, hp12_ne⟩
  let u₁ := leftDupZd P p₁ hp₁_mem hp₁_nz
  let u₂ := leftDupZd P p₂ hp₂_mem hp₂_nz
  let v₁ := rightDupZd P p₁ hp₁_mem hp₁_nz

  have hdiam_le : HasDiameterAtMost (AmalgamatedDuplication D P) 2 := by
    intro x y
    cases Classical.em (x = y) with
    | inl heq =>
      subst heq
      exact ⟨0, by omega, HasWalkOfLength.refl x⟩
    | inr hxy_ne =>
      cases domain_dup_zd_partition hdom P x with
      | inl hxL =>
        rcases hxL with ⟨hx1, hx2_nz, _⟩
        cases domain_dup_zd_partition hdom P y with
        | inr hyR =>
          rcases hyR with ⟨hy2, _, _⟩
          have hmul : x.val * y.val = 0 :=
            dup_ext P (by simp [hx1, ring_zero_mul]) (by simp [hy2, ring_mul_zero])
          exact ⟨1, by omega, HasWalkOfLength.step ⟨hxy_ne, hmul⟩ (HasWalkOfLength.refl y)⟩
        | inl hyL =>
          rcases hyL with ⟨hy1, hy2_nz, _⟩
          have hx_ne_v1 : x ≠ v₁ := by
            intro heq
            have h := congrArg (fun w => w.val.val.2) heq
            exact hx2_nz h
          have hv1_ne_y : v₁ ≠ y := by
            intro heq
            have h := congrArg (fun w => w.val.val.2) heq
            exact hy2_nz h.symm
          have hxv1 : x.val * v₁.val = 0 :=
            dup_ext P (by simp [hx1, ring_zero_mul]) (by simp [v₁, rightDupZd, ring_mul_zero])
          have hv1y : v₁.val * y.val = 0 :=
            dup_ext P (by simp [hy1, ring_mul_zero]) (by simp [v₁, rightDupZd, ring_zero_mul])
          exact ⟨2, by omega,
            HasWalkOfLength.step ⟨hx_ne_v1, hxv1⟩
              (HasWalkOfLength.step ⟨hv1_ne_y, hv1y⟩ (HasWalkOfLength.refl y))⟩
      | inr hxR =>
        rcases hxR with ⟨hx2, hx1_nz, _⟩
        cases domain_dup_zd_partition hdom P y with
        | inl hyL =>
          rcases hyL with ⟨hy1, _, _⟩
          have hmul : x.val * y.val = 0 :=
            dup_ext P (by simp [hy1, ring_mul_zero]) (by simp [hx2, ring_zero_mul])
          exact ⟨1, by omega, HasWalkOfLength.step ⟨hxy_ne, hmul⟩ (HasWalkOfLength.refl y)⟩
        | inr hyR =>
          rcases hyR with ⟨hy2, hy1_nz, _⟩
          have hx_ne_u1 : x ≠ u₁ := by
            intro heq
            have h := congrArg (fun w => w.val.val.1) heq
            exact hx1_nz h
          have hu1_ne_y : u₁ ≠ y := by
            intro heq
            have h := congrArg (fun w => w.val.val.1) heq
            exact hy1_nz h.symm
          have hxu1 : x.val * u₁.val = 0 :=
            dup_ext P (by simp [u₁, leftDupZd, ring_mul_zero]) (by simp [hx2, ring_zero_mul])
          have hu1y : u₁.val * y.val = 0 :=
            dup_ext P (by simp [u₁, leftDupZd, ring_zero_mul]) (by simp [hy2, ring_mul_zero])
          exact ⟨2, by omega,
            HasWalkOfLength.step ⟨hx_ne_u1, hxu1⟩
              (HasWalkOfLength.step ⟨hu1_ne_y, hu1y⟩ (HasWalkOfLength.refl y))⟩

  have hu1_ne_v1 : u₁ ≠ v₁ := by
    intro heq
    have h := congrArg (fun w => w.val.val.1) heq
    exact hp₁_nz h.symm
  have hv1_ne_u2 : v₁ ≠ u₂ := by
    intro heq
    have h := congrArg (fun w => w.val.val.1) heq
    exact hp₁_nz h
  have hu1v1 : u₁.val * v₁.val = 0 :=
    dup_ext P (ring_zero_mul p₁) (ring_mul_zero p₁)
  have hv1u2 : v₁.val * u₂.val = 0 :=
    dup_ext P (ring_mul_zero p₁) (ring_zero_mul p₂)
  have hwalk2 : HasWalkOfLength u₁ u₂ 2 :=
    HasWalkOfLength.step ⟨hu1_ne_v1, hu1v1⟩
      (HasWalkOfLength.step ⟨hv1_ne_u2, hv1u2⟩ (HasWalkOfLength.refl u₂))

  refine ⟨⟨u₁⟩, hdiam_le, u₁, u₂, hwalk2, ?_⟩
  intro m hm hwm
  match m with
  | 0 =>
    have heq := walk_len_zero_iff.mp hwm
    have h := congrArg (fun w => w.val.val.2) heq
    exact hp12_ne h
  | 1 =>
    have hadj := walk_len_one_iff.mp hwm
    have hmul : p₁ * p₂ = 0 := congrArg (fun w => w.val.2) hadj.2
    cases hdom p₁ p₂ hmul with
    | inl h1 => exact hp₁_nz h1
    | inr h2 => exact hp₂_nz h2
  | m + 2 => omega

theorem domain_chain_ge_one_diam_two
    (hdom : IsIntegralDomain D) {P : Ideal D} {k : Nat} (hk : 1 ≤ k)
    (hchain : HasPrimeChainEndingAt D P k) :
    HasGraphDiameter (AmalgamatedDuplication D P) 2 := by
  have hchain1 : HasPrimeChainEndingAt D P 1 := hasPrimeChainEndingAt_mono hk hchain
  cases hchain1 with
  | @step Q _ _ _ hP hstrict =>
    rcases hstrict with ⟨_, p, hpP, hpQ⟩
    have hp_nz : p ≠ 0 := by
      intro hp0
      rw [hp0] at hpQ
      exact hpQ Q.zero_mem
    exact domain_nonzero_prime_duplication_diam_two hdom hP ⟨p, hpP, hp_nz⟩

end DomainDuplication

/-! ## Section 9. Generic Polynomial Ring `Poly R` and Exact Height-2 Witness `𝔽₂[x, y]` -/

section Polynomials

def sumRange {R : Type u} [CommRing R] : Nat → (Nat → R) → R
  | 0, _ => 0
  | n + 1, f => sumRange n f + f n

section SumLemmas
variable {R : Type u} [CommRing R]

theorem sumRange_congr {n : Nat} {f g : Nat → R} (h : ∀ i, i < n → f i = g i) :
    sumRange n f = sumRange n g := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp [sumRange]
    rw [ih (fun i hi => h i (Nat.lt_succ_of_lt hi)), h n (Nat.lt_succ_self n)]

theorem sumRange_zero_fn (n : Nat) : sumRange n (fun _ => (0 : R)) = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [sumRange, ih, ring_add_zero]

theorem sumRange_add (n : Nat) (f g : Nat → R) :
    sumRange n (fun i => f i + g i) = sumRange n f + sumRange n g := by
  induction n with
  | zero => symm; exact ring_add_zero 0
  | succ n ih =>
    simp [sumRange, ih]
    calc
      (sumRange n f + sumRange n g) + (f n + g n)
        = sumRange n f + (sumRange n g + (f n + g n)) := ring_add_assoc _ _ _
      _ = sumRange n f + ((sumRange n g + f n) + g n) := by rw [← ring_add_assoc (sumRange n g)]
      _ = sumRange n f + ((f n + sumRange n g) + g n) := by rw [ring_add_comm (sumRange n g) (f n)]
      _ = sumRange n f + (f n + (sumRange n g + g n)) := by rw [ring_add_assoc (f n)]
      _ = (sumRange n f + f n) + (sumRange n g + g n) := by rw [← ring_add_assoc]

theorem mul_sumRange (a : R) (n : Nat) (f : Nat → R) :
    a * sumRange n f = sumRange n (fun i => a * f i) := by
  induction n with
  | zero => exact ring_mul_zero a
  | succ n ih =>
    simp [sumRange, ring_left_distrib, ih]

theorem sumRange_mul (n : Nat) (f : Nat → R) (a : R) :
    sumRange n f * a = sumRange n (fun i => f i * a) := by
  induction n with
  | zero => exact ring_zero_mul a
  | succ n ih =>
    simp [sumRange, ring_right_distrib, ih]

theorem sumRange_succ_left (n : Nat) (f : Nat → R) :
    sumRange (n + 1) f = f 0 + sumRange n (fun i => f (i + 1)) := by
  induction n with
  | zero =>
    simp [sumRange, ring_zero_add, ring_add_zero]
  | succ n ih =>
    calc
      sumRange (n + 2) f = sumRange (n + 1) f + f (n + 1) := rfl
      _ = (f 0 + sumRange n (fun i => f (i + 1))) + f (n + 1) := by rw [ih]
      _ = f 0 + (sumRange n (fun i => f (i + 1)) + f (n + 1)) := ring_add_assoc _ _ _
      _ = f 0 + sumRange (n + 1) (fun i => f (i + 1)) := rfl

theorem sumRange_rev (n : Nat) (f : Nat → R) :
    sumRange (n + 1) f = sumRange (n + 1) (fun i => f (n - i)) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    calc
      sumRange (n + 2) f = sumRange (n + 1) f + f (n + 1) := rfl
      _ = sumRange (n + 1) (fun i => f (n - i)) + f (n + 1) := by rw [ih]
      _ = f (n + 1) + sumRange (n + 1) (fun i => f (n - i)) := ring_add_comm _ _
      _ = f (n + 1 - 0) + sumRange (n + 1) (fun i => f ((n + 1) - (i + 1))) := by
        have hcongr : sumRange (n + 1) (fun i => f (n - i)) =
            sumRange (n + 1) (fun i => f ((n + 1) - (i + 1))) :=
          sumRange_congr (fun i _ => by
            have heq : n - i = (n + 1) - (i + 1) := by omega
            rw [heq])
        rw [hcongr]
        rfl
      _ = sumRange (n + 2) (fun i => f (n + 1 - i)) := by
        symm
        exact sumRange_succ_left (n + 1) (fun i => f (n + 1 - i))

theorem sumRange_single (n d : Nat) (v : R) (hd : d < n) :
    sumRange n (fun i => if i = d then v else 0) = v := by
  induction n with
  | zero => omega
  | succ n ih =>
    change sumRange n (fun i => if i = d then v else 0) + (if n = d then v else 0) = v
    by_cases hnd : n = d
    · subst hnd
      have hz : sumRange n (fun i => if i = n then v else 0) =
          sumRange n (fun _ => (0 : R)) :=
        sumRange_congr (fun i hi => by
          have hne : i ≠ n := by omega
          simp [hne])
      rw [hz, sumRange_zero_fn, ring_zero_add]
      simp
    · have hlt : d < n := by omega
      simp [hnd, ih hlt, ring_add_zero]

theorem cauchy_assoc (g h : Nat → R) :
    ∀ (n : Nat) (f : Nat → R),
      sumRange (n + 1) (fun k => sumRange (k + 1) (fun i => f i * g (k - i)) * h (n - k)) =
      sumRange (n + 1) (fun i => f i * sumRange (n - i + 1) (fun j => g j * h (n - i - j)))
  | 0, f => by
    simp [sumRange, ring_zero_add, ring_mul_assoc]
  | n + 1, f => by
    let lhsFn : Nat → R := fun k =>
      sumRange (k + 1) (fun i => f i * g (k - i)) * h (n + 1 - k)
    have hsplit_lhs : sumRange (n + 2) lhsFn =
        lhsFn 0 + sumRange (n + 1) (fun m => lhsFn (m + 1)) :=
      sumRange_succ_left (n + 1) lhsFn
    have hlhs0 : lhsFn 0 = f 0 * (g 0 * h (n + 1)) := by
      simp [lhsFn, sumRange, ring_zero_add, ring_mul_assoc]
    have hlhs_step : sumRange (n + 1) (fun m => lhsFn (m + 1)) =
        sumRange (n + 1) (fun m => f 0 * (g (m + 1) * h (n - m))) +
        sumRange (n + 1) (fun m =>
          sumRange (m + 1) (fun i => f (i + 1) * g (m - i)) * h (n - m)) := by
      rw [← sumRange_add]
      apply sumRange_congr
      intro m _
      dsimp [lhsFn]
      rw [sumRange_succ_left (m + 1)]
      have hsub : n + 1 - (m + 1) = n - m := by omega
      rw [hsub, ring_right_distrib, ring_mul_assoc]
      have hinner : sumRange (m + 1) (fun i => f (i + 1) * g (m + 1 - (i + 1))) =
          sumRange (m + 1) (fun i => f (i + 1) * g (m - i)) :=
        sumRange_congr (fun i _ => by
          have he : m + 1 - (i + 1) = m - i := by omega
          rw [he])
      rw [hinner]
      rfl
    have h_f0_combine : f 0 * (g 0 * h (n + 1)) +
        sumRange (n + 1) (fun m => f 0 * (g (m + 1) * h (n - m))) =
        f 0 * sumRange (n + 2) (fun j => g j * h (n + 1 - j)) := by
      rw [← mul_sumRange, ← ring_left_distrib]
      congr 1
      symm
      rw [sumRange_succ_left (n + 1)]
      have hcongr : sumRange (n + 1) (fun i => g (i + 1) * h (n + 1 - (i + 1))) =
          sumRange (n + 1) (fun m => g (m + 1) * h (n - m)) :=
        sumRange_congr (fun m _ => by
          have he : n + 1 - (m + 1) = n - m := by omega
          rw [he])
      rw [hcongr]
      rfl
    have ih := cauchy_assoc g h n (fun i => f (i + 1))
    calc
      sumRange (n + 2) lhsFn
        = f 0 * (g 0 * h (n + 1)) +
          (sumRange (n + 1) (fun m => f 0 * (g (m + 1) * h (n - m))) +
           sumRange (n + 1) (fun m =>
             sumRange (m + 1) (fun i => f (i + 1) * g (m - i)) * h (n - m))) := by
          rw [hsplit_lhs, hlhs0, hlhs_step]
      _ = (f 0 * (g 0 * h (n + 1)) +
            sumRange (n + 1) (fun m => f 0 * (g (m + 1) * h (n - m)))) +
          sumRange (n + 1) (fun i =>
            f (i + 1) * sumRange (n - i + 1) (fun j => g j * h (n - i - j))) := by
          rw [← ring_add_assoc, ih]
      _ = f 0 * sumRange (n + 2) (fun j => g j * h (n + 1 - j)) +
          sumRange (n + 1) (fun i =>
            f (i + 1) * sumRange ((n + 1) - (i + 1) + 1)
              (fun j => g j * h ((n + 1) - (i + 1) - j))) := by
          rw [h_f0_combine]
          congr 1
          apply sumRange_congr
          intro i _
          have he : (n + 1) - (i + 1) = n - i := by omega
          rw [he]
      _ = sumRange (n + 2) (fun i =>
            f i * sumRange (n + 1 - i + 1) (fun j => g j * h (n + 1 - i - j))) := by
          symm
          exact sumRange_succ_left (n + 1) _

end SumLemmas

def IsFinSupp {R : Type u} [CommRing R] (f : Nat → R) : Prop :=
  ∃ N : Nat, ∀ k : Nat, N ≤ k → f k = 0

def Poly (R : Type u) [CommRing R] : Type u :=
  { f : Nat → R // IsFinSupp f }

section PolyStructure
variable {R : Type u} [CommRing R]

theorem Poly.ext {p q : Poly R} (h : ∀ n : Nat, p.val n = q.val n) : p = q :=
  Subtype.ext (funext h)

def polyZero : Poly R := ⟨fun _ => 0, 0, fun _ _ => rfl⟩

def polyC (c : R) : Poly R :=
  ⟨fun k => if k = 0 then c else 0, 1, fun k hk => by
    have hne : k ≠ 0 := by omega
    simp [hne]⟩

def polyAdd (p q : Poly R) : Poly R :=
  ⟨fun k => p.val k + q.val k, by
    rcases p.property with ⟨Np, hp⟩
    rcases q.property with ⟨Nq, hq⟩
    refine ⟨Np + Nq, fun k hk => ?_⟩
    dsimp
    rw [hp k (by omega), hq k (by omega), ring_add_zero]⟩

def polyNeg (p : Poly R) : Poly R :=
  ⟨fun k => -p.val k, by
    rcases p.property with ⟨Np, hp⟩
    refine ⟨Np, fun k hk => ?_⟩
    dsimp
    rw [hp k hk, ring_neg_zero]⟩

def polyMul (p q : Poly R) : Poly R :=
  ⟨fun n => sumRange (n + 1) (fun i => p.val i * q.val (n - i)), by
    rcases p.property with ⟨Np, hp⟩
    rcases q.property with ⟨Nq, hq⟩
    refine ⟨Np + Nq, fun n hn => ?_⟩
    dsimp
    have hz : sumRange (n + 1) (fun i => p.val i * q.val (n - i)) =
        sumRange (n + 1) (fun _ => (0 : R)) := by
      apply sumRange_congr
      intro i _
      by_cases hi : Np ≤ i
      · rw [hp i hi, ring_zero_mul]
      · have hqi : Nq ≤ n - i := by omega
        rw [hq (n - i) hqi, ring_mul_zero]
    rw [hz, sumRange_zero_fn]⟩

instance instCommRingPoly : CommRing (Poly R) where
  zero := polyZero
  one := polyC 1
  add := polyAdd
  mul := polyMul
  neg := polyNeg
  zero_ne_one := by
    intro h
    have h0 : (0 : R) = 1 := congrFun (congrArg Subtype.val h) 0
    exact ring_zero_ne_one h0
  add_assoc := fun a b c => Poly.ext (fun n => ring_add_assoc (a.val n) (b.val n) (c.val n))
  add_comm := fun a b => Poly.ext (fun n => ring_add_comm (a.val n) (b.val n))
  zero_add := fun a => Poly.ext (fun n => ring_zero_add (a.val n))
  add_left_neg := fun a => Poly.ext (fun n => ring_add_left_neg (a.val n))
  mul_assoc := fun a b c => Poly.ext (fun n => by
    change sumRange (n + 1) (fun k =>
        sumRange (k + 1) (fun i => a.val i * b.val (k - i)) * c.val (n - k)) =
      sumRange (n + 1) (fun i =>
        a.val i * sumRange (n - i + 1) (fun j => b.val j * c.val (n - i - j)))
    exact cauchy_assoc b.val c.val n a.val)
  mul_comm := fun a b => Poly.ext (fun n => by
    change sumRange (n + 1) (fun i => a.val i * b.val (n - i)) =
      sumRange (n + 1) (fun i => b.val i * a.val (n - i))
    rw [sumRange_rev n (fun i => a.val i * b.val (n - i))]
    apply sumRange_congr
    intro i hi
    have hsub : n - (n - i) = i := by omega
    rw [hsub, ring_mul_comm])
  one_mul := fun a => Poly.ext (fun n => by
    change sumRange (n + 1) (fun i => (polyC (1 : R)).val i * a.val (n - i)) = a.val n
    rw [sumRange_succ_left n]
    have h0 : (polyC (1 : R)).val 0 * a.val (n - 0) = a.val n := by
      change (1 : R) * a.val n = a.val n
      exact ring_one_mul (a.val n)
    have hrest : sumRange n (fun i => (polyC (1 : R)).val (i + 1) * a.val (n - (i + 1))) = 0 := by
      rw [sumRange_congr (g := fun _ => (0 : R))]
      · exact sumRange_zero_fn n
      · intro i _
        change (0 : R) * a.val (n - (i + 1)) = 0
        exact ring_zero_mul _
    rw [h0, hrest, ring_add_zero])
  left_distrib := fun a b c => Poly.ext (fun n => by
    change sumRange (n + 1) (fun i => a.val i * (b.val (n - i) + c.val (n - i))) =
      sumRange (n + 1) (fun i => a.val i * b.val (n - i)) +
      sumRange (n + 1) (fun i => a.val i * c.val (n - i))
    rw [← sumRange_add]
    exact sumRange_congr (fun i _ => ring_left_distrib _ _ _))

@[simp] theorem poly_zero_val (n : Nat) : (0 : Poly R).val n = 0 := rfl
@[simp] theorem poly_add_val (p q : Poly R) (n : Nat) : (p + q).val n = p.val n + q.val n := rfl
@[simp] theorem poly_neg_val (p : Poly R) (n : Nat) : (-p).val n = -p.val n := rfl
@[simp] theorem poly_sub_val (p q : Poly R) (n : Nat) : (p - q).val n = p.val n - q.val n := rfl

theorem polyC_mul_val (c : R) (p : Poly R) (n : Nat) :
    (polyC c * p).val n = c * p.val n := by
  change sumRange (n + 1) (fun i => (polyC c).val i * p.val (n - i)) = c * p.val n
  rw [sumRange_succ_left n]
  have hrest : sumRange n (fun i => (polyC c).val (i + 1) * p.val (n - (i + 1))) = 0 := by
    rw [sumRange_congr (g := fun _ => (0 : R))]
    · exact sumRange_zero_fn n
    · intro i _
      change (0 : R) * p.val (n - (i + 1)) = 0
      exact ring_zero_mul _
  rw [hrest, ring_add_zero]
  rfl

theorem polyC_add (a b : R) : polyC (a + b) = polyC a + polyC b := by
  apply Poly.ext
  intro k
  cases k with
  | zero => rfl
  | succ k =>
    change (0 : R) = 0 + 0
    symm
    exact ring_add_zero 0

theorem polyC_mul (a b : R) : polyC (a * b) = polyC a * polyC b := by
  apply Poly.ext
  intro k
  rw [polyC_mul_val]
  cases k with
  | zero => rfl
  | succ k =>
    change (0 : R) = a * 0
    symm
    exact ring_mul_zero a

def polyMonomial (d : Nat) (c : R) : Poly R :=
  ⟨fun k => if k = d then c else 0, d + 1, fun k hk => by
    have hne : k ≠ d := by omega
    simp [hne]⟩

def polyX : Poly R := polyMonomial 1 1

def polyShift (p : Poly R) : Poly R :=
  ⟨fun k => p.val (k + 1), by
    rcases p.property with ⟨Np, hp⟩
    exact ⟨Np, fun k hk => hp (k + 1) (by omega)⟩⟩

theorem polyMonomial_mul_val (d : Nat) (c : R) (h : Poly R) (m : Nat) :
    (polyMonomial d c * h).val m = if d ≤ m then c * h.val (m - d) else 0 := by
  change sumRange (m + 1) (fun i => (if i = d then c else 0) * h.val (m - i)) = _
  by_cases hdm : d ≤ m
  · simp [hdm]
    have hcongr : sumRange (m + 1) (fun i => (if i = d then c else 0) * h.val (m - i)) =
        sumRange (m + 1) (fun i => if i = d then c * h.val (m - d) else 0) := by
      apply sumRange_congr
      intro i _
      by_cases hid : i = d
      · subst hid; simp
      · simp [hid, ring_zero_mul]
    rw [hcongr]
    exact sumRange_single (m + 1) d (c * h.val (m - d)) (by omega)
  · simp [hdm]
    rw [sumRange_congr (g := fun _ => (0 : R))]
    · exact sumRange_zero_fn (m + 1)
    · intro i hi
      have hne : i ≠ d := by omega
      simp [hne, ring_zero_mul]

theorem poly_eq_const_add_X_mul_shift (p : Poly R) :
    p = polyC (p.val 0) + polyX * polyShift p := by
  apply Poly.ext
  intro k
  simp only [poly_add_val]
  rw [polyX, polyMonomial_mul_val]
  cases k with
  | zero =>
    have hnle : ¬ (1 ≤ 0) := by omega
    simp [polyC, hnle, ring_add_zero]
  | succ m =>
    have hle : 1 ≤ m + 1 := by omega
    have hsub : m + 1 - 1 = m := by omega
    simp [polyC, hle, hsub, polyShift, ring_zero_add, ring_one_mul]

theorem poly_mul_val_zero (p q : Poly R) : (p * q).val 0 = p.val 0 * q.val 0 := by
  change (0 : R) + p.val 0 * q.val 0 = p.val 0 * q.val 0
  exact ring_zero_add _

/-! ### Degree, Domain Preservation, and Pseudo-Division over an Integral Domain -/

def HasDegree (p : Poly R) (d : Nat) : Prop :=
  p.val d ≠ 0 ∧ ∀ k : Nat, d < k → p.val k = 0

theorem exists_degree_of_ne_zero {p : Poly R} (hp : p ≠ 0) :
    ∃ d : Nat, HasDegree p d := by
  rcases p.property with ⟨N, hN⟩
  have haux : ∀ B : Nat, (∀ k : Nat, B ≤ k → p.val k = 0) → ∃ d : Nat, HasDegree p d := by
    intro B
    induction B with
    | zero =>
      intro h0
      exfalso
      apply hp
      exact Poly.ext (fun k => h0 k (Nat.zero_le k))
    | succ B ih =>
      intro hB
      cases Classical.em (p.val B = 0) with
      | inr hnz =>
        exact ⟨B, hnz, fun k hk => hB k (by omega)⟩
      | inl hz =>
        apply ih
        intro k hk
        cases Nat.eq_or_lt_of_le hk with
        | inl heq => rw [← heq]; exact hz
        | inr hlt => exact hB k (by omega)
  exact haux N hN

theorem hasDegree_unique {p : Poly R} {d₁ d₂ : Nat}
    (h1 : HasDegree p d₁) (h2 : HasDegree p d₂) : d₁ = d₂ := by
  cases Nat.lt_or_ge d₁ d₂ with
  | inl hlt => exact False.elim (h2.1 (h1.2 d₂ hlt))
  | inr hge =>
    cases Nat.eq_or_lt_of_le hge with
    | inl heq => exact heq.symm
    | inr hlt => exact False.elim (h1.1 (h2.2 d₁ hlt))

theorem hasDegree_mul (hdom : IsIntegralDomain R) {p q : Poly R} {d₁ d₂ : Nat}
    (hp : HasDegree p d₁) (hq : HasDegree q d₂) :
    HasDegree (p * q) (d₁ + d₂) := by
  refine ⟨?_, ?_⟩
  · change sumRange (d₁ + d₂ + 1) (fun i => p.val i * q.val (d₁ + d₂ - i)) ≠ 0
    have hsingle : sumRange (d₁ + d₂ + 1) (fun i => p.val i * q.val (d₁ + d₂ - i)) =
        p.val d₁ * q.val d₂ := by
      rw [sumRange_congr (g := fun i => if i = d₁ then p.val d₁ * q.val d₂ else 0)]
      · exact sumRange_single (d₁ + d₂ + 1) d₁ (p.val d₁ * q.val d₂) (by omega)
      · intro i _
        by_cases hid : i = d₁
        · rw [hid]
          have hsub : d₁ + d₂ - d₁ = d₂ := by omega
          simp [hsub]
        · simp [hid]
          cases Nat.lt_or_gt_of_ne hid with
          | inl hlt =>
            rw [hq.2 (d₁ + d₂ - i) (by omega), ring_mul_zero]
          | inr hgt =>
            rw [hp.2 i hgt, ring_zero_mul]
    rw [hsingle]
    intro hz
    cases hdom (p.val d₁) (q.val d₂) hz with
    | inl h1 => exact hp.1 h1
    | inr h2 => exact hq.1 h2
  · intro k hk
    change sumRange (k + 1) (fun i => p.val i * q.val (k - i)) = 0
    rw [sumRange_congr (g := fun _ => (0 : R))]
    · exact sumRange_zero_fn (k + 1)
    · intro i _
      by_cases hi : d₁ < i
      · rw [hp.2 i hi, ring_zero_mul]
      · rw [hq.2 (k - i) (by omega), ring_mul_zero]

theorem poly_isIntegralDomain (hdom : IsIntegralDomain R) :
    IsIntegralDomain (Poly R) := by
  intro p q hpq
  cases Classical.em (p = 0) with
  | inl hp0 => exact Or.inl hp0
  | inr hp_nz =>
    cases Classical.em (q = 0) with
    | inl hq0 => exact Or.inr hq0
    | inr hq_nz =>
      rcases exists_degree_of_ne_zero hp_nz with ⟨d₁, hd₁⟩
      rcases exists_degree_of_ne_zero hq_nz with ⟨d₂, hd₂⟩
      have hdeg := hasDegree_mul hdom hd₁ hd₂
      rw [hpq] at hdeg
      exact False.elim (hdeg.1 rfl)

theorem poly_pseudo_div {h : Poly R} {d : Nat} (hd : HasDegree h d) (hd_pos : 1 ≤ d)
    (f : Poly R) :
    ∃ (k : Nat) (q r : Poly R),
      polyC (ringPow (h.val d) k) * f = q * h + r ∧
      (∀ m : Nat, d ≤ m → r.val m = 0) := by
  let c := h.val d
  have haux : ∀ (B : Nat) (g : Poly R),
      (∀ m : Nat, B ≤ m → g.val m = 0) →
      ∃ (k : Nat) (q r : Poly R),
        polyC (ringPow c k) * g = q * h + r ∧ (∀ m : Nat, d ≤ m → r.val m = 0) := by
    intro B
    induction B with
    | zero =>
      intro g hg
      refine ⟨0, 0, g, ?_, fun m _ => hg m (Nat.zero_le m)⟩
      change polyC 1 * g = 0 * h + g
      have h1 : polyC (1 : R) = 1 := rfl
      rw [h1, ring_one_mul, ring_zero_mul, ring_zero_add]
    | succ B ih =>
      intro g hg
      by_cases hdB : d ≤ B
      · let t : Poly R := polyMonomial (B - d) (g.val B)
        let g₁ : Poly R := polyC c * g - t * h
        have hg₁_bound : ∀ m : Nat, B ≤ m → g₁.val m = 0 := by
          intro m hm
          change (polyC c * g).val m - (t * h).val m = 0
          rw [polyC_mul_val, polyMonomial_mul_val]
          have hm_ge : B - d ≤ m := by omega
          simp [hm_ge]
          cases Nat.eq_or_lt_of_le hm with
          | inl heq =>
            subst heq
            have hsub : B - (B - d) = d := by omega
            rw [hsub, ring_mul_comm c (g.val B), ring_sub_self]
          | inr hlt =>
            have hg0 : g.val m = 0 := hg m (by omega)
            have hh0 : h.val (m - (B - d)) = 0 := hd.2 (m - (B - d)) (by omega)
            rw [hg0, hh0, ring_mul_zero, ring_mul_zero, ring_sub_self]
        rcases ih g₁ hg₁_bound with ⟨k', q', r', heq', hr'⟩
        refine ⟨k' + 1, polyC (ringPow c k') * t + q', r', ?_, hr'⟩
        have hpow : polyC (ringPow c (k' + 1)) * g =
            polyC (ringPow c k') * (polyC c * g) := by
          rw [ringPow_succ, ring_mul_comm c (ringPow c k'), polyC_mul, ring_mul_assoc]
        have hg1_split : polyC c * g = t * h + g₁ := by
          change polyC c * g = t * h + (polyC c * g + (-(t * h)))
          rw [ring_add_comm (polyC c * g) (-(t * h)), ← ring_add_assoc,
              ring_add_right_neg, ring_zero_add]
        calc
          polyC (ringPow c (k' + 1)) * g
            = polyC (ringPow c k') * (t * h + g₁) := by rw [hpow, hg1_split]
          _ = polyC (ringPow c k') * (t * h) + polyC (ringPow c k') * g₁ := ring_left_distrib _ _ _
          _ = (polyC (ringPow c k') * t) * h + (q' * h + r') := by rw [← ring_mul_assoc, heq']
          _ = ((polyC (ringPow c k') * t) * h + q' * h) + r' := by rw [← ring_add_assoc]
          _ = (polyC (ringPow c k') * t + q') * h + r' := by rw [← ring_right_distrib]
      · refine ⟨0, 0, g, ?_, fun m hm => hg m (by omega)⟩
        have h1 : polyC (1 : R) = 1 := rfl
        change polyC 1 * g = 0 * h + g
        rw [h1, ring_one_mul, ring_zero_mul, ring_zero_add]
  rcases f.property with ⟨Nf, hNf⟩
  exact haux Nf f hNf

theorem nat_exists_min {P : Nat → Prop} {n₀ : Nat} (hn₀ : P n₀) :
    ∃ m : Nat, P m ∧ ∀ k : Nat, k < m → ¬ P k := by
  have hstrong : ∀ n : Nat, (∀ k : Nat, k < n → ¬ P k) ∨
      (∃ m : Nat, m < n ∧ P m ∧ ∀ k : Nat, k < m → ¬ P k) := by
    intro n
    induction n with
    | zero => exact Or.inl (fun _ hk => by omega)
    | succ n ih =>
      cases ih with
      | inr hex =>
        rcases hex with ⟨m, hmn, hPm, hmin⟩
        exact Or.inr ⟨m, Nat.lt_succ_of_lt hmn, hPm, hmin⟩
      | inl hnone =>
        cases Classical.em (P n) with
        | inl hPn => exact Or.inr ⟨n, Nat.lt_succ_self n, hPn, hnone⟩
        | inr hnPn =>
          left
          intro k hk
          cases Nat.eq_or_lt_of_le (Nat.le_of_lt_succ hk) with
          | inl heq => rw [heq]; exact hnPn
          | inr hlt => exact hnone k hlt
  cases hstrong (n₀ + 1) with
  | inl hnone => exact False.elim (hnone n₀ (Nat.lt_succ_self n₀) hn₀)
  | inr hex =>
    rcases hex with ⟨m, _, hPm, hmin⟩
    exact ⟨m, hPm, hmin⟩

/-- Over an integral domain `R`, `Poly R` cannot have two strictly nested nonzero prime
    ideals `Q₁ ⊂ Q₂` that both intersect `R` trivially (`∀ c ≠ 0, ¬ Q₂.mem (polyC c)`). -/
theorem poly_no_nested_nonzero_primes_disjoint_base (hdom : IsIntegralDomain R)
    {Q₀ Q₁ Q₂ : Ideal (Poly R)}
    (hQ₁ : IsPrimeIdeal (Poly R) Q₁)
    (h01 : IdealStrictSubset Q₀ Q₁)
    (h12 : IdealStrictSubset Q₁ Q₂)
    (hdisj : ∀ c : R, c ≠ 0 → ¬ Q₂.mem (polyC c)) : False := by
  have hdisj₁ : ∀ c : R, c ≠ 0 → ¬ Q₁.mem (polyC c) :=
    fun c hc hmem => hdisj c hc (h12.1 _ hmem)
  rcases h01 with ⟨_, g₀, hg₀_Q1, hg₀_notQ0⟩
  have hg₀_nz : g₀ ≠ 0 := by
    intro hz
    rw [hz] at hg₀_notQ0
    exact hg₀_notQ0 Q₀.zero_mem
  rcases exists_degree_of_ne_zero hg₀_nz with ⟨dg₀, hdg₀⟩
  rcases nat_exists_min (P := fun d => ∃ g : Poly R, Q₁.mem g ∧ HasDegree g d)
    ⟨g₀, hg₀_Q1, hdg₀⟩ with ⟨d₁, ⟨g, hg_Q1, hdg⟩, hmin₁⟩
  rcases nat_exists_min (P := fun d => ∃ h : Poly R, Q₂.mem h ∧ HasDegree h d)
    ⟨g₀, h12.1 _ hg₀_Q1, hdg₀⟩ with ⟨d₂, ⟨h, hh_Q2, hdh⟩, hmin₂⟩

  have hd₂_pos : 1 ≤ d₂ := by
    cases d₂ with
    | zero =>
      exfalso
      have hh_eq : h = polyC (h.val 0) := by
        apply Poly.ext
        intro k
        cases k with
        | zero => rfl
        | succ m => exact hdh.2 (m + 1) (by omega)
      rw [hh_eq] at hh_Q2
      exact hdisj (h.val 0) hdh.1 hh_Q2
    | succ k => omega

  rcases poly_pseudo_div hdh hd₂_pos g with ⟨k, q, r, hdiv, hr_deg⟩
  have hr_Q2 : Q₂.mem r := by
    have h1 : Q₂.mem (polyC (ringPow (h.val d₂) k) * g) :=
      Q₂.mul_mem_left _ (h12.1 g hg_Q1)
    have h2 : Q₂.mem (q * h) := Q₂.mul_mem_left q hh_Q2
    have hr_eq : r = (q * h + r) - q * h :=
      (ring_add_sub_cancel (q * h) r).symm
    rw [hr_eq, ← hdiv]
    exact Q₂.sub_mem h1 h2
  have hr_zero : r = 0 := by
    cases Classical.em (r = 0) with
    | inl hz => exact hz
    | inr hr_nz =>
      rcases exists_degree_of_ne_zero hr_nz with ⟨dr, hdr⟩
      have hdr_lt : dr < d₂ := by
        cases Nat.lt_or_ge dr d₂ with
        | inl hlt => exact hlt
        | inr hge => exact False.elim (hdr.1 (hr_deg dr hge))
      exact False.elim (hmin₂ dr hdr_lt ⟨r, hr_Q2, hdr⟩)
  rw [hr_zero, ring_add_zero] at hdiv

  have hc_pow_nz : ringPow (h.val d₂) k ≠ 0 :=
    domain_ringPow_ne_zero hdom hdh.1 k
  have hc_deg : HasDegree (polyC (ringPow (h.val d₂) k)) 0 := by
    refine ⟨hc_pow_nz, fun m hm => ?_⟩
    have hne : m ≠ 0 := by omega
    simp [polyC, hne]
  have hlhs_deg : HasDegree (polyC (ringPow (h.val d₂) k) * g) (0 + d₁) :=
    hasDegree_mul hdom hc_deg hdg
  have hq_nz : q ≠ 0 := by
    intro hq0
    rw [hq0, ring_zero_mul] at hdiv
    rw [hdiv] at hlhs_deg
    exact hlhs_deg.1 rfl
  rcases exists_degree_of_ne_zero hq_nz with ⟨dq, hdq⟩
  have hrhs_deg : HasDegree (q * h) (dq + d₂) := hasDegree_mul hdom hdq hdh
  rw [hdiv] at hlhs_deg
  have hdeg_eq : 0 + d₁ = dq + d₂ := hasDegree_unique hlhs_deg hrhs_deg

  have hh_Q1 : Q₁.mem h := by
    cases Classical.em (Q₁.mem h) with
    | inl hh1 => exact hh1
    | inr hnh1 =>
      have hqh_Q1 : Q₁.mem (q * h) := by
        rw [← hdiv]
        exact Q₁.mul_mem_left _ hg_Q1
      cases hQ₁.2 q h hqh_Q1 with
      | inr hh1 => exact hh1
      | inl hq1 =>
        exact False.elim (hmin₁ dq (by omega) ⟨q, hq1, hdq⟩)

  rcases h12 with ⟨_, f, hf_Q2, hf_notQ1⟩
  rcases poly_pseudo_div hdh hd₂_pos f with ⟨kf, qf, rf, hdivf, hrf_deg⟩
  have hrf_Q2 : Q₂.mem rf := by
    have h1 : Q₂.mem (polyC (ringPow (h.val d₂) kf) * f) :=
      Q₂.mul_mem_left _ hf_Q2
    have h2 : Q₂.mem (qf * h) := Q₂.mul_mem_left qf hh_Q2
    have hrf_eq : rf = (qf * h + rf) - qf * h :=
      (ring_add_sub_cancel (qf * h) rf).symm
    rw [hrf_eq, ← hdivf]
    exact Q₂.sub_mem h1 h2
  have hrf_zero : rf = 0 := by
    cases Classical.em (rf = 0) with
    | inl hz => exact hz
    | inr hrf_nz =>
      rcases exists_degree_of_ne_zero hrf_nz with ⟨drf, hdrf⟩
      have hdrf_lt : drf < d₂ := by
        cases Nat.lt_or_ge drf d₂ with
        | inl hlt => exact hlt
        | inr hge => exact False.elim (hdrf.1 (hrf_deg drf hge))
      exact False.elim (hmin₂ drf hdrf_lt ⟨rf, hrf_Q2, hdrf⟩)
  rw [hrf_zero, ring_add_zero] at hdivf

  have hcf_pow_nz : ringPow (h.val d₂) kf ≠ 0 :=
    domain_ringPow_ne_zero hdom hdh.1 kf
  have hcf_notQ1 : ¬ Q₁.mem (polyC (ringPow (h.val d₂) kf)) :=
    hdisj₁ _ hcf_pow_nz
  have hprod_Q1 : Q₁.mem (polyC (ringPow (h.val d₂) kf) * f) := by
    rw [hdivf]
    exact Q₁.mul_mem_left qf hh_Q1
  cases hQ₁.2 _ f hprod_Q1 with
  | inl hc1 => exact hcf_notQ1 hc1
  | inr hf1 => exact hf_notQ1 hf1

end PolyStructure

/-! ### Bivariate Polynomial Ring `F2XY = (𝔽₂[y])[x]` and Exact Height `ht(x, y) = 2` -/

abbrev F2Y : Type := Poly F2
abbrev F2XY : Type := Poly F2Y

theorem f2y_isDomain : IsIntegralDomain F2Y :=
  poly_isIntegralDomain f2_isDomain

theorem f2xy_isDomain : IsIntegralDomain F2XY :=
  poly_isIntegralDomain f2y_isDomain

def idealY_in_F2Y : Ideal F2Y where
  mem := fun g => g.val 0 = 0
  zero_mem := rfl
  add_mem := fun ha hb => by simp [ha, hb, ring_add_zero]
  neg_mem := fun ha => by simp [ha, ring_neg_zero]
  mul_mem_left := fun r _ ha => by rw [poly_mul_val_zero, ha, ring_mul_zero]

theorem f2y_prime_sub_idealY_not_Y {I : Ideal F2Y} (hI : IsPrimeIdeal F2Y I)
    (hsub : IdealSubset I idealY_in_F2Y) (hnotY : ¬ I.mem (polyX (R := F2))) :
    ∀ g : F2Y, I.mem g → g = 0 := by
  have hcoeff : ∀ (n : Nat) (g : F2Y), I.mem g → g.val n = 0 := by
    intro n
    induction n with
    | zero =>
      intro g hg
      exact hsub g hg
    | succ n ih =>
      intro g hg
      have hg0 : g.val 0 = 0 := hsub g hg
      have hdecomp := poly_eq_const_add_X_mul_shift g
      have hc0 : polyC (g.val 0) = (0 : F2Y) := by
        apply Poly.ext
        intro k
        cases k <;> simp [polyC, hg0]
      rw [hc0, ring_zero_add] at hdecomp
      rw [hdecomp] at hg
      cases hI.2 (polyX (R := F2)) (polyShift g) hg with
      | inl hY => exact False.elim (hnotY hY)
      | inr hsh => exact ih (polyShift g) hsh
  intro g hg
  exact Poly.ext (fun n => hcoeff n g hg)

def idealX : Ideal F2XY where
  mem := fun f => f.val 0 = 0
  zero_mem := rfl
  add_mem := fun ha hb => by simp [ha, hb, ring_add_zero]
  neg_mem := fun ha => by simp [ha, ring_neg_zero]
  mul_mem_left := fun r _ ha => by rw [poly_mul_val_zero, ha, ring_mul_zero]

def idealXY : Ideal F2XY where
  mem := fun f => (f.val 0).val 0 = 0
  zero_mem := rfl
  add_mem := fun ha hb => by simp [ha, hb, ring_add_zero]
  neg_mem := fun ha => by simp [ha, ring_neg_zero]
  mul_mem_left := fun r _ ha => by
    rw [poly_mul_val_zero, poly_mul_val_zero, ha, ring_mul_zero]

def polyX_xy : F2XY := polyX (R := F2Y)
def polyY_xy : F2XY := polyC (polyX (R := F2))

theorem idealZero_f2xy_isPrime : IsPrimeIdeal F2XY (zeroIdeal F2XY) :=
  zeroIdeal_isPrime_iff_domain.mpr f2xy_isDomain

theorem idealX_isPrime : IsPrimeIdeal F2XY idealX := by
  refine ⟨?_, ?_⟩
  · intro h1
    exact ring_zero_ne_one h1.symm
  · intro a b hab
    change (a * b).val 0 = 0 at hab
    rw [poly_mul_val_zero] at hab
    exact f2y_isDomain (a.val 0) (b.val 0) hab

theorem idealXY_isPrime : IsPrimeIdeal F2XY idealXY := by
  refine ⟨?_, ?_⟩
  · intro h1
    exact ring_zero_ne_one h1.symm
  · intro a b hab
    change ((a * b).val 0).val 0 = 0 at hab
    rw [poly_mul_val_zero, poly_mul_val_zero] at hab
    exact f2_isDomain ((a.val 0).val 0) ((b.val 0).val 0) hab

theorem strictChain_zero_to_X : IdealStrictSubset (zeroIdeal F2XY) idealX := by
  refine ⟨?_, polyX_xy, rfl, ?_⟩
  · intro f hf
    change f = 0 at hf
    rw [hf]
    rfl
  · intro h0
    have h1 : polyX_xy.val 1 = 0 := congrFun (congrArg Subtype.val h0) 1
    exact ring_zero_ne_one h1.symm

theorem strictChain_X_to_XY : IdealStrictSubset idealX idealXY := by
  refine ⟨?_, polyY_xy, rfl, ?_⟩
  · intro f hf
    change f.val 0 = 0 at hf
    change (f.val 0).val 0 = 0
    rw [hf]
    rfl
  · intro h0
    have h1 : (polyY_xy.val 0).val 1 = 0 :=
      congrFun (congrArg Subtype.val h0) 1
    exact ring_zero_ne_one h1.symm

theorem f2xy_hasPrimeChain_len2_at_idealXY :
    HasPrimeChainEndingAt F2XY idealXY 2 :=
  HasPrimeChainEndingAt.step
    (HasPrimeChainEndingAt.step
      (HasPrimeChainEndingAt.zero idealZero_f2xy_isPrime)
      idealX_isPrime strictChain_zero_to_X)
    idealXY_isPrime strictChain_X_to_XY

def polyDivY (f : F2XY) : F2XY :=
  ⟨fun m => polyShift (f.val m), by
    rcases f.property with ⟨Nf, hNf⟩
    refine ⟨Nf, fun m hm => ?_⟩
    apply Poly.ext
    intro k
    change (f.val m).val (k + 1) = 0
    rw [hNf m hm]
    rfl⟩

theorem mul_polyY_xy_divY {f : F2XY} (h0 : ∀ m : Nat, (f.val m).val 0 = 0) :
    f = polyY_xy * polyDivY f := by
  apply Poly.ext
  intro m
  rw [polyY_xy, polyC_mul_val]
  have hdecomp := poly_eq_const_add_X_mul_shift (f.val m)
  have hc0 : polyC ((f.val m).val 0) = (0 : F2Y) := by
    apply Poly.ext
    intro k
    cases k <;> simp [polyC, h0 m]
  rw [hc0, ring_zero_add] at hdecomp
  exact hdecomp

theorem prime_strictSub_idealXY_with_Y {Q : Ideal F2XY}
    (hQ : IsPrimeIdeal F2XY Q) (hstrict : IdealStrictSubset Q idealXY)
    (hY : Q.mem polyY_xy) :
    ∀ f : F2XY, Q.mem f ↔ (∀ m : Nat, (f.val m).val 0 = 0) := by
  have hnotX : ¬ Q.mem polyX_xy := by
    intro hX
    rcases hstrict with ⟨_, g, hg_XY, hg_notQ⟩
    apply hg_notQ
    have hg_decomp := poly_eq_const_add_X_mul_shift g
    have hg0_decomp := poly_eq_const_add_X_mul_shift (g.val 0)
    have h00 : polyC ((g.val 0).val 0) = (0 : F2Y) := by
      apply Poly.ext
      intro k
      cases k <;> simp [polyC, show ((g.val 0).val 0) = 0 from hg_XY]
    rw [h00, ring_zero_add] at hg0_decomp
    have hc_mem : Q.mem (polyC (g.val 0)) := by
      rw [hg0_decomp, polyC_mul]
      exact Q.mul_mem_right _ hY
    have hx_mem : Q.mem (polyX_xy * polyShift g) := Q.mul_mem_right _ hX
    rw [hg_decomp]
    exact Q.add_mem hc_mem hx_mem
  have hfwd : ∀ (m : Nat) (f : F2XY), Q.mem f → (f.val m).val 0 = 0 := by
    intro m
    induction m with
    | zero =>
      intro f hf
      exact hstrict.1 f hf
    | succ m ih =>
      intro f hf
      have hf0 : (f.val 0).val 0 = 0 := hstrict.1 f hf
      have hf0_decomp := poly_eq_const_add_X_mul_shift (f.val 0)
      have h00 : polyC ((f.val 0).val 0) = (0 : F2Y) := by
        apply Poly.ext
        intro k
        cases k <;> simp [polyC, hf0]
      rw [h00, ring_zero_add] at hf0_decomp
      have hc_mem : Q.mem (polyC (f.val 0)) := by
        rw [hf0_decomp, polyC_mul]
        exact Q.mul_mem_right _ hY
      have hxsh_eq : polyX_xy * polyShift f = f - polyC (f.val 0) := by
        have hd : f = polyC (f.val 0) + polyX_xy * polyShift f :=
          poly_eq_const_add_X_mul_shift f
        calc
          polyX_xy * polyShift f
            = (polyC (f.val 0) + polyX_xy * polyShift f) - polyC (f.val 0) :=
              (ring_add_sub_cancel _ _).symm
          _ = f - polyC (f.val 0) := by rw [← hd]
      have hxsh_mem : Q.mem (polyX_xy * polyShift f) := by
        rw [hxsh_eq]
        exact Q.sub_mem hf hc_mem
      cases hQ.2 polyX_xy (polyShift f) hxsh_mem with
      | inl hX => exact False.elim (hnotX hX)
      | inr hsh => exact ih (polyShift f) hsh
  intro f
  constructor
  · intro hf m
    exact hfwd m f hf
  · intro hall
    rw [mul_polyY_xy_divY hall]
    exact Q.mul_mem_right (polyDivY f) hY

theorem f2xy_no_primeChain_len3_at_idealXY :
    ¬ HasPrimeChainEndingAt F2XY idealXY 3 := by
  intro h3
  cases h3 with
  | @step Q₂ _ _ h2 _ h23 =>
    cases h2 with
    | @step Q₁ _ _ h1 hQ₂ h12 =>
      cases h1 with
      | @step Q₀ _ _ h0 hQ₁ h01 =>
        cases h0 with
        | zero _ =>
          cases Classical.em (Q₂.mem polyY_xy) with
          | inl hY2 =>
            have hQ2_char := prime_strictSub_idealXY_with_Y hQ₂ h23 hY2
            have hnotY1 : ¬ Q₁.mem polyY_xy := by
              intro hY1
              have hstrict13 : IdealStrictSubset Q₁ idealXY :=
                ⟨fun z hz => h23.1 z (h12.1 z hz),
                 by rcases h23 with ⟨_, w, hw, hnw⟩
                    exact ⟨w, hw, fun hw1 => hnw (h12.1 w hw1)⟩⟩
              have hQ1_char := prime_strictSub_idealXY_with_Y hQ₁ hstrict13 hY1
              have heq : Q₁ = Q₂ := Ideal.ext (fun f => by rw [hQ1_char f, hQ2_char f])
              exact ((idealStrictSubset_iff_subset_and_ne _ _).mp h12).2 heq
            rcases h01 with ⟨_, g₀, hg₀_Q1, hg₀_notQ0⟩
            have hg₀_nz : g₀ ≠ 0 := by
              intro hz
              rw [hz] at hg₀_notQ0
              exact hg₀_notQ0 Q₀.zero_mem
            have hex_m : ∃ m₀ : Nat, g₀.val m₀ ≠ 0 := by
              cases Classical.em (∃ m₀ : Nat, g₀.val m₀ ≠ 0) with
              | inl hex => exact hex
              | inr hno =>
                exfalso
                apply hg₀_nz
                apply Poly.ext
                intro m
                cases Classical.em (g₀.val m = 0) with
                | inl hz => exact hz
                | inr hnz => exact False.elim (hno ⟨m, hnz⟩)
            rcases hex_m with ⟨m₀, hm₀⟩
            rcases exists_degree_of_ne_zero hm₀ with ⟨d₀, hd₀⟩
            rcases nat_exists_min
              (P := fun d => ∃ g : F2XY, Q₁.mem g ∧ HasDegree (g.val m₀) d)
              ⟨g₀, hg₀_Q1, hd₀⟩ with ⟨dmin, ⟨g, hg_Q1, hdg⟩, hmin⟩
            have hall_g : ∀ m : Nat, (g.val m).val 0 = 0 :=
              (hQ2_char g).mp (h12.1 g hg_Q1)
            have hg_div := mul_polyY_xy_divY hall_g
            rw [hg_div] at hg_Q1
            cases hQ₁.2 polyY_xy (polyDivY g) hg_Q1 with
            | inl hY1 => exact hnotY1 hY1
            | inr hdiv_Q1 =>
              cases dmin with
              | zero => exact hdg.1 (hall_g m₀)
              | succ d' =>
                have hsh_deg : HasDegree ((polyDivY g).val m₀) d' := by
                  refine ⟨hdg.1, fun k hk => ?_⟩
                  exact hdg.2 (k + 1) (by omega)
                exact hmin d' (Nat.lt_succ_self d') ⟨polyDivY g, hdiv_Q1, hsh_deg⟩
          | inr hnotY2 =>
            let I₂ : Ideal F2Y := {
              mem := fun c => Q₂.mem (polyC c)
              zero_mem := by
                have hz : polyC (0 : F2Y) = (0 : F2XY) := by
                  apply Poly.ext; intro k; cases k <;> rfl
                rw [hz]; exact Q₂.zero_mem
              add_mem := fun {a b} ha hb => by
                rw [polyC_add]; exact Q₂.add_mem ha hb
              neg_mem := fun {a} ha => by
                have hneg : polyC (-a) = -(polyC a : F2XY) := by
                  apply Poly.ext; intro k; cases k
                  · rfl
                  · change (0 : F2Y) = -0; symm; exact ring_neg_zero
                rw [hneg]; exact Q₂.neg_mem ha
              mul_mem_left := fun r {a} ha => by
                rw [polyC_mul]; exact Q₂.mul_mem_left (polyC r) ha
            }
            have hI₂_prime : IsPrimeIdeal F2Y I₂ := by
              refine ⟨hQ₂.1, fun a b hab => ?_⟩
              change Q₂.mem (polyC (a * b)) at hab
              rw [polyC_mul] at hab
              exact hQ₂.2 (polyC a) (polyC b) hab
            have hI₂_sub : IdealSubset I₂ idealY_in_F2Y := by
              intro c hc
              exact h23.1 (polyC c) hc
            have hdisj : ∀ c : F2Y, c ≠ 0 → ¬ Q₂.mem (polyC c) := by
              intro c hc hmem
              exact hc (f2y_prime_sub_idealY_not_Y hI₂_prime hI₂_sub hnotY2 c hmem)
            exact poly_no_nested_nonzero_primes_disjoint_base f2y_isDomain hQ₁ h01 h12 hdisj

theorem f2xy_idealXY_hasExactHeight_two : HasExactHeight F2XY idealXY 2 :=
  ⟨f2xy_hasPrimeChain_len2_at_idealXY, f2xy_no_primeChain_len3_at_idealXY⟩

theorem f2xy_hasPrimeChain_len2 : HasPrimeChainOfLength F2XY 2 :=
  ⟨idealXY, f2xy_hasPrimeChain_len2_at_idealXY⟩

theorem f2xy_dup_hasPrimeChain_len2 :
    HasPrimeChainOfLength (AmalgamatedDuplication F2XY idealXY) 2 :=
  lift_primeChainOfLength idealXY f2xy_hasPrimeChain_len2

theorem f2xy_dup_hasDiameter_two :
    HasGraphDiameter (AmalgamatedDuplication F2XY idealXY) 2 :=
  domain_chain_ge_one_diam_two f2xy_isDomain (by omega : 1 ≤ 2) f2xy_hasPrimeChain_len2_at_idealXY

theorem f2xy_dup_not_hasDiameter_three :
    ¬ HasGraphDiameter (AmalgamatedDuplication F2XY idealXY) 3 := by
  intro h3
  have heq := hasGraphDiameter_unique f2xy_dup_hasDiameter_two h3
  omega

end Polynomials

/-! ## Section 10. Non-Vacuity Witnesses and Complete Disproofs of Conjecture 00000002223 -/

/-- Non-vacuity witness certifying that `CommRing`, `IsPrimeIdeal`, `AmalgamatedDuplication`,
    `HasGraphDiameter` (at both `2` and `3`), `HasPrimeChainOfLength`, `HasPrimeChainEndingAt`,
    and `HasExactHeight` are all simultaneously inhabited and non-vacuous. -/
theorem non_vacuity_positive_witnesses :
    (IsPrimeIdeal (CounterexampleRingFamily 0) (CounterexamplePrimeFamily 0) ∧
     HasGraphDiameter (CounterexampleDupFamily 0) 3) ∧
    (IsPrimeIdeal F2XY idealXY ∧
     HasExactHeight F2XY idealXY 2 ∧
     HasPrimeChainOfLength F2XY 2 ∧
     HasPrimeChainOfLength (AmalgamatedDuplication F2XY idealXY) 2 ∧
     HasGraphDiameter (AmalgamatedDuplication F2XY idealXY) 2) :=
  ⟨⟨firstCoordZeroIdeal_isPrime 1, counterexampleDupFamily_hasDiameter_three 0⟩,
   ⟨idealXY_isPrime, f2xy_idealXY_hasExactHeight_two, f2xy_hasPrimeChain_len2,
    f2xy_dup_hasPrimeChain_len2, f2xy_dup_hasDiameter_two⟩⟩

/-! ### Formal Statements of Conjecture 00000002223 Under All Spectral Conventions -/

/-- Variant 1 (`Spec(R)` contains a prime chain of length 2). -/
def Conjecture2223_Iff_BaseChain2 : Prop :=
  ∀ (R : Type) [CommRing R] (P : Ideal R), IsPrimeIdeal R P →
    HasDiameterAtMost (AmalgamatedDuplication R P) 3 ∧
    (HasGraphDiameter (AmalgamatedDuplication R P) 3 ↔ HasPrimeChainOfLength R 2)

/-- Variant 2 (`Spec(R)` contains a prime chain of length 2 ending at `P`, i.e., `ht(P) ≥ 2`). -/
def Conjecture2223_Iff_IdealChain2 : Prop :=
  ∀ (R : Type) [CommRing R] (P : Ideal R), IsPrimeIdeal R P →
    HasDiameterAtMost (AmalgamatedDuplication R P) 3 ∧
    (HasGraphDiameter (AmalgamatedDuplication R P) 3 ↔ HasPrimeChainEndingAt R P 2)

/-- Variant 3 (`P` has exact height `ht(P) = 2` in `Spec(R)`). -/
def Conjecture2223_Iff_ExactHeight2 : Prop :=
  ∀ (R : Type) [CommRing R] (P : Ideal R), IsPrimeIdeal R P →
    HasDiameterAtMost (AmalgamatedDuplication R P) 3 ∧
    (HasGraphDiameter (AmalgamatedDuplication R P) 3 ↔ HasExactHeight R P 2)

/-- Variant 4 (`Spec(R ⋈ P)` contains a prime chain of length 2). -/
def Conjecture2223_Iff_DupChain2 : Prop :=
  ∀ (R : Type) [CommRing R] (P : Ideal R), IsPrimeIdeal R P →
    HasDiameterAtMost (AmalgamatedDuplication R P) 3 ∧
    (HasGraphDiameter (AmalgamatedDuplication R P) 3 ↔
      HasPrimeChainOfLength (AmalgamatedDuplication R P) 2)

/-- Variant 5 (1-indexed vertex-count convention: "prime chain of length two" read as a strict
    inclusion `Q₀ ⊂ Q₁` of two prime ideals in either `Spec(R)` or `Spec(R ⋈ P)`). -/
def Conjecture2223_Iff_Chain1_Base : Prop :=
  ∀ (R : Type) [CommRing R] (P : Ideal R), IsPrimeIdeal R P →
    HasDiameterAtMost (AmalgamatedDuplication R P) 3 ∧
    (HasGraphDiameter (AmalgamatedDuplication R P) 3 ↔ HasPrimeChainOfLength R 1)

def Conjecture2223_Iff_Chain1_Dup : Prop :=
  ∀ (R : Type) [CommRing R] (P : Ideal R), IsPrimeIdeal R P →
    HasDiameterAtMost (AmalgamatedDuplication R P) 3 ∧
    (HasGraphDiameter (AmalgamatedDuplication R P) 3 ↔
      HasPrimeChainOfLength (AmalgamatedDuplication R P) 1)

/-- One-way Necessity: `diam(Γ(R ⋈ P)) = 3` implies existence of a strict prime chain of length `≥ 1`
    in either `Spec(R)` or `Spec(R ⋈ P)`. -/
def Conjecture2223_Necessity_AnyStrictChain : Prop :=
  ∀ (R : Type) [CommRing R] (P : Ideal R), IsPrimeIdeal R P →
    HasGraphDiameter (AmalgamatedDuplication R P) 3 →
    HasPrimeChainOfLength R 1 ∨ HasPrimeChainOfLength (AmalgamatedDuplication R P) 1

/-- One-way Sufficiency: `HasExactHeight R P 2` (which simultaneously implies `HasPrimeChainEndingAt R P 2`,
    `HasPrimeChainOfLength R 2`, and `HasPrimeChainOfLength (R ⋈ P) 2`) implies `diam(Γ(R ⋈ P)) = 3`. -/
def Conjecture2223_Sufficiency_ExactHeight2 : Prop :=
  ∀ (R : Type) [CommRing R] (P : Ideal R), IsPrimeIdeal R P →
    HasExactHeight R P 2 →
    HasGraphDiameter (AmalgamatedDuplication R P) 3

theorem disproof_conjecture2223_iff_baseChain2 : ¬ Conjecture2223_Iff_BaseChain2 := by
  intro h
  have hiff := (h (CounterexampleRingFamily 0) (CounterexamplePrimeFamily 0)
    (firstCoordZeroIdeal_isPrime 1)).2
  exact counterexampleFamily_no_primeChain_base 0 (by omega : 1 ≤ 2)
    (hiff.mp (counterexampleDupFamily_hasDiameter_three 0))

theorem disproof_conjecture2223_iff_idealChain2 : ¬ Conjecture2223_Iff_IdealChain2 := by
  intro h
  have hiff := (h (CounterexampleRingFamily 0) (CounterexamplePrimeFamily 0)
    (firstCoordZeroIdeal_isPrime 1)).2
  have hch : HasPrimeChainEndingAt (CounterexampleRingFamily 0) (CounterexamplePrimeFamily 0) 2 :=
    hiff.mp (counterexampleDupFamily_hasDiameter_three 0)
  exact counterexampleFamily_no_primeChain_base 0 (by omega : 1 ≤ 2) ⟨_, hch⟩

theorem disproof_conjecture2223_iff_exactHeight2 : ¬ Conjecture2223_Iff_ExactHeight2 := by
  intro h
  have hiff := (h (CounterexampleRingFamily 0) (CounterexamplePrimeFamily 0)
    (firstCoordZeroIdeal_isPrime 1)).2
  have hex : HasExactHeight (CounterexampleRingFamily 0) (CounterexamplePrimeFamily 0) 2 :=
    hiff.mp (counterexampleDupFamily_hasDiameter_three 0)
  exact counterexampleFamily_no_primeChain_base 0 (by omega : 1 ≤ 2) ⟨_, hex.1⟩

theorem disproof_conjecture2223_iff_dupChain2 : ¬ Conjecture2223_Iff_DupChain2 := by
  intro h
  have hiff := (h (CounterexampleRingFamily 0) (CounterexamplePrimeFamily 0)
    (firstCoordZeroIdeal_isPrime 1)).2
  exact counterexampleFamily_no_primeChain_dup 0 (by omega : 1 ≤ 2)
    (hiff.mp (counterexampleDupFamily_hasDiameter_three 0))

theorem disproof_conjecture2223_iff_chain1_base : ¬ Conjecture2223_Iff_Chain1_Base := by
  intro h
  have hiff := (h (CounterexampleRingFamily 0) (CounterexamplePrimeFamily 0)
    (firstCoordZeroIdeal_isPrime 1)).2
  exact counterexampleFamily_no_primeChain_base 0 (Nat.le_refl 1)
    (hiff.mp (counterexampleDupFamily_hasDiameter_three 0))

theorem disproof_conjecture2223_iff_chain1_dup : ¬ Conjecture2223_Iff_Chain1_Dup := by
  intro h
  have hiff := (h (CounterexampleRingFamily 0) (CounterexamplePrimeFamily 0)
    (firstCoordZeroIdeal_isPrime 1)).2
  exact counterexampleFamily_no_primeChain_dup 0 (Nat.le_refl 1)
    (hiff.mp (counterexampleDupFamily_hasDiameter_three 0))

theorem disproof_necessity_anyStrictChain : ¬ Conjecture2223_Necessity_AnyStrictChain := by
  intro h
  cases h (CounterexampleRingFamily 0) (CounterexamplePrimeFamily 0)
      (firstCoordZeroIdeal_isPrime 1) (counterexampleDupFamily_hasDiameter_three 0) with
  | inl hb => exact counterexampleFamily_no_primeChain_base 0 (Nat.le_refl 1) hb
  | inr hd => exact counterexampleFamily_no_primeChain_dup 0 (Nat.le_refl 1) hd

theorem disproof_sufficiency_exactHeight2 : ¬ Conjecture2223_Sufficiency_ExactHeight2 := by
  intro h
  exact f2xy_dup_not_hasDiameter_three
    (h F2XY idealXY idealXY_isPrime f2xy_idealXY_hasExactHeight_two)

end Conjecture2223

/-! ## Axiom Footprint Audit -/

#print axioms Conjecture2223.non_vacuity_positive_witnesses
#print axioms Conjecture2223.hasGraphDiameter_unique
#print axioms Conjecture2223.exists_walk_le_iff_exists_simplePath_le
#print axioms Conjecture2223.zeroDivisorGraph_diameter_at_most_three
#print axioms Conjecture2223.amalgamatedDuplication_diameter_at_most_three
#print axioms Conjecture2223.boolean_prime_subset_eq
#print axioms Conjecture2223.boolean_no_prime_chain_ge_one
#print axioms Conjecture2223.hasCardinality_unique
#print axioms Conjecture2223.counterexampleRingFamily_pairwise_noniso
#print axioms Conjecture2223.counterexampleDupFamily_pairwise_noniso
#print axioms Conjecture2223.counterexampleDupFamily_hasDiameter_three
#print axioms Conjecture2223.counterexampleFamily_no_primeChain_base
#print axioms Conjecture2223.counterexampleFamily_no_primeChain_dup
#print axioms Conjecture2223.domain_nonzero_prime_duplication_diam_two
#print axioms Conjecture2223.f2xy_idealXY_hasExactHeight_two
#print axioms Conjecture2223.f2xy_dup_hasDiameter_two
#print axioms Conjecture2223.disproof_conjecture2223_iff_baseChain2
#print axioms Conjecture2223.disproof_conjecture2223_iff_idealChain2
#print axioms Conjecture2223.disproof_conjecture2223_iff_exactHeight2
#print axioms Conjecture2223.disproof_conjecture2223_iff_dupChain2
#print axioms Conjecture2223.disproof_conjecture2223_iff_chain1_base
#print axioms Conjecture2223.disproof_conjecture2223_iff_chain1_dup
#print axioms Conjecture2223.disproof_necessity_anyStrictChain
#print axioms Conjecture2223.disproof_sufficiency_exactHeight2

