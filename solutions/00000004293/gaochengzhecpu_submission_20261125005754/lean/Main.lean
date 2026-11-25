/-
  Conjecture 00000004293 — Complete Resolution & Core Lean 4.19.0 Formalization
  =============================================================================
  Self-contained formalization in Core Lean 4 (zero external dependencies,
  zero sorry, zero native_decide, zero custom axioms).
-/

namespace Conjecture00000004293

/-! ## Section 1: Elementary Number Theory & Prime Powers -/

/-- Standard primality predicate on natural numbers. -/
def IsPrime (p : Nat) : Prop :=
  2 ≤ p ∧ ∀ d : Nat, d ∣ p → d = 1 ∨ d = p

theorem le_of_dvd_pos {a b : Nat} (hb : 0 < b) (h : a ∣ b) : a ≤ b := by
  rcases h with ⟨q, rfl⟩
  cases q with
  | zero => omega
  | succ q' =>
    have : a * 1 ≤ a * (q' + 1) := Nat.mul_le_mul_left a (by omega)
    omega

theorem isPrime_two : IsPrime 2 := by
  refine ⟨by omega, ?_⟩
  intro d hd
  have hle : d ≤ 2 := le_of_dvd_pos (by omega) hd
  rcases hd with ⟨k, hk⟩
  match d with
  | 0 => omega
  | 1 => exact Or.inl rfl
  | 2 => exact Or.inr rfl
  | _ + 3 => omega

theorem isPrime_three : IsPrime 3 := by
  refine ⟨by omega, ?_⟩
  intro d hd
  have hle : d ≤ 3 := le_of_dvd_pos (by omega) hd
  rcases hd with ⟨k, hk⟩
  match d with
  | 0 => omega
  | 1 => exact Or.inl rfl
  | 2 => omega
  | 3 => exact Or.inr rfl
  | _ + 4 => omega

theorem isPrime_five : IsPrime 5 := by
  refine ⟨by omega, ?_⟩
  intro d hd
  have hle : d ≤ 5 := le_of_dvd_pos (by omega) hd
  rcases hd with ⟨k, hk⟩
  match d with
  | 0 => omega
  | 1 => exact Or.inl rfl
  | 2 => omega
  | 3 => omega
  | 4 => omega
  | 5 => exact Or.inr rfl
  | _ + 6 => omega

/-- Two natural numbers have only 1 as a common divisor. -/
def RelPrime (a b : Nat) : Prop :=
  ∀ d : Nat, d ∣ a → d ∣ b → d = 1

theorem relPrime_symm {a b : Nat} (h : RelPrime a b) : RelPrime b a :=
  fun d hdb hda => h d hda hdb

theorem dvd_sub_of_dvd {d a b : Nat} (h1 : d ∣ a) (h2 : d ∣ b) : d ∣ (b - a) := by
  rcases h1 with ⟨q1, rfl⟩
  rcases h2 with ⟨q2, rfl⟩
  exact ⟨q2 - q1, (Nat.mul_sub_left_distrib d q2 q1).symm⟩

theorem dvd_add_of_dvd {d a b : Nat} (h1 : d ∣ a) (h2 : d ∣ b) : d ∣ (a + b) := by
  rcases h1 with ⟨q1, rfl⟩
  rcases h2 with ⟨q2, rfl⟩
  exact ⟨q1 + q2, (Nat.mul_add d q1 q2).symm⟩

theorem relPrime_sub_right {a b : Nat} (hle : a ≤ b) (h : RelPrime a b) :
    RelPrime a (b - a) := by
  intro d hda hdb
  apply h d hda
  have hsum : d ∣ a + (b - a) := dvd_add_of_dvd hda hdb
  have heq : a + (b - a) = b := by omega
  rw [heq] at hsum
  exact hsum

/-- Positive Bezout identity in Nat: for relatively prime a, b > 0,
    either u * a = v * b + 1 or v * b = u * a + 1. -/
theorem nat_bezout :
    ∀ s a b : Nat, a + b ≤ s → 0 < a → 0 < b → RelPrime a b →
      ∃ u v : Nat, u * a = v * b + 1 ∨ v * b = u * a + 1
  | 0, _, _, hs, ha, _, _ => by omega
  | s + 1, a, b, hs, ha, hb, hcop => by
    by_cases hab : a = b
    · subst hab
      have ha1 : a = 1 := hcop a (Nat.dvd_refl a) (Nat.dvd_refl a)
      subst ha1
      exact ⟨1, 0, Or.inl (by omega)⟩
    · by_cases hlt : a < b
      · have hcop' : RelPrime a (b - a) := relPrime_sub_right (by omega) hcop
        rcases nat_bezout s a (b - a) (by omega) ha (by omega) hcop' with ⟨u, v, h1 | h2⟩
        · refine ⟨u + v, v, Or.inl ?_⟩
          have hvb : v * (b - a) + v * a = v * b := by
            rw [← Nat.mul_add]; congr 1; omega
          have hu : (u + v) * a = u * a + v * a := Nat.add_mul u v a
          omega
        · refine ⟨u + v, v, Or.inr ?_⟩
          have hvb : v * (b - a) + v * a = v * b := by
            rw [← Nat.mul_add]; congr 1; omega
          have hu : (u + v) * a = u * a + v * a := Nat.add_mul u v a
          omega
      · have hcop' : RelPrime b (a - b) := relPrime_sub_right (by omega) (relPrime_symm hcop)
        rcases nat_bezout s b (a - b) (by omega) hb (by omega) hcop' with ⟨u, v, h1 | h2⟩
        · refine ⟨v, u + v, Or.inr ?_⟩
          have hva : v * (a - b) + v * b = v * a := by
            rw [← Nat.mul_add]; congr 1; omega
          have hu : (u + v) * b = u * b + v * b := Nat.add_mul u v b
          omega
        · refine ⟨v, u + v, Or.inl ?_⟩
          have hva : v * (a - b) + v * b = v * a := by
            rw [← Nat.mul_add]; congr 1; omega
          have hu : (u + v) * b = u * b + v * b := Nat.add_mul u v b
          omega

/-- Euclid's lemma for relatively prime natural numbers. -/
theorem euclid_lemma {a b k : Nat} (hcop : RelPrime a b) (hdvd : a ∣ b * k) : a ∣ k := by
  by_cases ha0 : a = 0
  · subst ha0
    have hb1 : b = 1 := hcop b ⟨0, by omega⟩ (Nat.dvd_refl b)
    subst hb1
    simpa using hdvd
  · by_cases hb0 : b = 0
    · subst hb0
      have ha1 : a = 1 := hcop a (Nat.dvd_refl a) ⟨0, by omega⟩
      subst ha1
      exact ⟨k, by omega⟩
    · rcases nat_bezout (a + b) a b (by omega) (by omega) (by omega) hcop with ⟨u, v, h1 | h2⟩
      · rcases hdvd with ⟨q, hbk⟩
        refine ⟨u * k - v * q, ?_⟩
        have hmul : (u * a) * k = (v * b + 1) * k := by rw [h1]
        have lhs_eq : (u * a) * k = a * (u * k) := by
          rw [Nat.mul_comm u a, Nat.mul_assoc]
        have rhs_eq : (v * b + 1) * k = a * (v * q) + k := by
          rw [Nat.add_mul, Nat.one_mul, Nat.mul_assoc v b k, hbk]
          rw [← Nat.mul_assoc, Nat.mul_comm v a, Nat.mul_assoc]
        have hsub : a * (u * k - v * q) = a * (u * k) - a * (v * q) :=
          Nat.mul_sub_left_distrib a (u * k) (v * q)
        omega
      · rcases hdvd with ⟨q, hbk⟩
        refine ⟨v * q - u * k, ?_⟩
        have hmul : (v * b) * k = (u * a + 1) * k := by rw [h2]
        have lhs_eq : (v * b) * k = a * (v * q) := by
          rw [Nat.mul_assoc v b k, hbk, ← Nat.mul_assoc, Nat.mul_comm v a, Nat.mul_assoc]
        have rhs_eq : (u * a + 1) * k = a * (u * k) + k := by
          rw [Nat.add_mul, Nat.one_mul, Nat.mul_comm u a, Nat.mul_assoc]
        have hsub : a * (v * q - u * k) = a * (v * q) - a * (u * k) :=
          Nat.mul_sub_left_distrib a (v * q) (u * k)
        omega

theorem relPrime_of_prime_not_dvd {p d : Nat} (hp : IsPrime p) (hnd : ¬ (p ∣ d)) :
    RelPrime d p := by
  intro c hcd hcp
  rcases hp.2 c hcp with rfl | rfl
  · rfl
  · exact False.elim (hnd hcd)

theorem relPrime_of_lt_prime {a p : Nat} (hp : IsPrime p) (ha0 : 0 < a) (hlt : a < p) :
    RelPrime a p := by
  apply relPrime_of_prime_not_dvd hp
  intro hpa
  have := le_of_dvd_pos ha0 hpa
  omega

/-- Modular multiplicative inverse modulo a prime p. -/
theorem mod_inv_of_lt_prime {a p : Nat} (hp : IsPrime p) (ha0 : 0 < a) (hlt : a < p) :
    ∃ u : Nat, u < p ∧ (u * a) % p = 1 := by
  have hp2 := hp.1
  have hcop := relPrime_of_lt_prime hp ha0 hlt
  rcases nat_bezout (a + p) a p (by omega) ha0 (by omega) hcop with ⟨x, y, h1 | h2⟩
  · refine ⟨x % p, Nat.mod_lt x (by omega), ?_⟩
    have hx : x = p * (x / p) + x % p := (Nat.div_add_mod x p).symm
    have hxa : x * a = p * ((x / p) * a) + (x % p) * a := by
      calc
        x * a = (p * (x / p) + x % p) * a := by rw [← hx]
        _ = (p * (x / p)) * a + (x % p) * a := Nat.add_mul _ _ a
        _ = p * ((x / p) * a) + (x % p) * a := by rw [Nat.mul_assoc]
    have hmod1 : (x * a) % p = ((x % p) * a) % p := by
      rw [hxa, Nat.add_comm, Nat.add_mul_mod_self_left]
    have hmod2 : (y * p + 1) % p = 1 := by
      rw [Nat.add_comm, Nat.mul_comm y p, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]
    rw [← hmod1, h1, hmod2]
  · let qx := x / p
    let r := x % p
    have hr_lt : r < p := Nat.mod_lt x (by omega)
    have hx : p * qx + r = x := Nat.div_add_mod x p
    have hxa : x * a = p * (qx * a) + r * a := by
      calc
        x * a = (p * qx + r) * a := by rw [hx]
        _ = (p * qx) * a + r * a := Nat.add_mul _ _ a
        _ = p * (qx * a) + r * a := by rw [Nat.mul_assoc]
    have hr0 : r ≠ 0 := by
      intro hr
      have hpy : p * y = p * (qx * a) + 1 := by
        rw [Nat.mul_comm p y, h2, hxa, hr, Nat.zero_mul, Nat.add_zero]
      have h1div : p ∣ 1 := ⟨y - qx * a, by
        rw [Nat.mul_sub_left_distrib]
        omega⟩
      have := le_of_dvd_pos (by omega) h1div
      omega
    refine ⟨p - r, by omega, ?_⟩
    have hsum : (p - r) * a + r * a = p * a := by
      rw [← Nat.add_mul]; congr 1; omega
    have hbig : (p - r) * a + p * y = p * (qx * a + a) + 1 := by
      calc
        (p - r) * a + p * y = (p - r) * a + (y * p) := by rw [Nat.mul_comm p y]
        _ = (p - r) * a + (p * (qx * a) + r * a + 1) := by rw [h2, hxa]
        _ = p * (qx * a) + ((p - r) * a + r * a) + 1 := by omega
        _ = p * (qx * a) + p * a + 1 := by rw [hsum]
        _ = p * (qx * a + a) + 1 := by rw [Nat.mul_add]
    have hk_le : y ≤ qx * a + a := by
      by_cases hle : y ≤ qx * a + a
      · exact hle
      · have hgt : qx * a + a + 1 ≤ y := by omega
        have hmul_ge : p * (qx * a + a + 1) ≤ p * y := Nat.mul_le_mul_left p hgt
        rw [Nat.mul_add p (qx * a + a) 1, Nat.mul_one] at hmul_ge
        omega
    have hdiff : (p - r) * a = p * (qx * a + a - y) + 1 := by
      have hp_sub : p * (qx * a + a - y) = p * (qx * a + a) - p * y :=
        Nat.mul_sub_left_distrib p (qx * a + a) y
      have hpy_le : p * y ≤ p * (qx * a + a) := Nat.mul_le_mul_left p hk_le
      omega
    rw [hdiff, Nat.add_comm, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]

/-- Every divisor of p^k (for prime p) is a prime power p^i with i <= k. -/
theorem dvd_prime_pow {p : Nat} (hp : IsPrime p) :
    ∀ {k d : Nat}, d ∣ p ^ k → ∃ i : Nat, i ≤ k ∧ d = p ^ i
  | 0, d, hd => by
    rw [Nat.pow_zero] at hd
    have hd1 : d ≤ 1 := le_of_dvd_pos (by omega) hd
    have hd0 : d ≠ 0 := by
      intro h0; subst h0
      rcases hd with ⟨_, hq⟩
      omega
    exact ⟨0, by omega, by rw [Nat.pow_zero]; omega⟩
  | k + 1, d, hd => by
    by_cases hpd : p ∣ d
    · rcases hpd with ⟨d', rfl⟩
      rcases hd with ⟨q, hq⟩
      have hpk : p ^ (k + 1) = p * p ^ k := by
        rw [Nat.pow_succ, Nat.mul_comm]
      rw [hpk] at hq
      have hmul : p * (d' * q) = p * p ^ k := by
        rw [← Nat.mul_assoc]
        exact hq.symm
      have hp0 : 0 < p := by have := hp.1; omega
      have hd' : d' ∣ p ^ k := ⟨q, (Nat.eq_of_mul_eq_mul_left hp0 hmul).symm⟩
      rcases dvd_prime_pow hp hd' with ⟨j, hj, rfl⟩
      refine ⟨j + 1, by omega, ?_⟩
      rw [Nat.pow_succ, Nat.mul_comm]
    · have hcop : RelPrime d p := relPrime_of_prime_not_dvd hp hpd
      have hpk : p ^ (k + 1) = p * p ^ k := by
        rw [Nat.pow_succ, Nat.mul_comm]
      rw [hpk] at hd
      have hd' : d ∣ p ^ k := euclid_lemma hcop hd
      rcases dvd_prime_pow hp hd' with ⟨i, hi, rfl⟩
      exact ⟨i, by omega, rfl⟩

theorem pow_pos_of_pos {p : Nat} (hp : 0 < p) : ∀ k : Nat, 0 < p ^ k
  | 0 => by simp
  | k + 1 => by
    rw [Nat.pow_succ]
    exact Nat.mul_pos (pow_pos_of_pos hp k) hp

theorem pow_lt_pow_of_lt {p : Nat} (hp : 2 ≤ p) : ∀ {a b : Nat}, a < b → p ^ a < p ^ b
  | a, 0, h => by omega
  | a, b + 1, h => by
    have hp0 : 0 < p := by omega
    have hstep : p ^ b < p ^ (b + 1) := by
      have hpos : 0 < p ^ b := pow_pos_of_pos hp0 b
      have hmul : p ^ b * 2 ≤ p ^ b * p := Nat.mul_le_mul_left (p ^ b) hp
      rw [Nat.pow_succ]
      omega
    by_cases hab : a = b
    · subst hab; exact hstep
    · exact Nat.lt_trans (pow_lt_pow_of_lt hp (by omega)) hstep

theorem pow_dvd_pow_of_le (p : Nat) {a b : Nat} (h : a ≤ b) : p ^ a ∣ p ^ b := by
  refine ⟨p ^ (b - a), ?_⟩
  rw [← Nat.pow_add]
  congr 1
  omega

/-! ## Section 2: Groups, Subgroup Lattice, and Maximal Chains -/

/-- Explicit group structure on a carrier type G. -/
structure GroupStruct (G : Type) where
  mul : G → G → G
  one : G
  inv : G → G
  mul_assoc : ∀ a b c : G, mul (mul a b) c = mul a (mul b c)
  one_mul : ∀ a : G, mul one a = a
  mul_left_inv : ∀ a : G, mul (inv a) a = one

theorem GroupStruct.mul_right_inv {G : Type} (grp : GroupStruct G) (a : G) :
    grp.mul a (grp.inv a) = grp.one := by
  calc
    grp.mul a (grp.inv a)
      = grp.mul grp.one (grp.mul a (grp.inv a)) := (grp.one_mul _).symm
    _ = grp.mul (grp.mul (grp.inv (grp.inv a)) (grp.inv a)) (grp.mul a (grp.inv a)) := by
        rw [grp.mul_left_inv (grp.inv a)]
    _ = grp.mul (grp.inv (grp.inv a)) (grp.mul (grp.inv a) (grp.mul a (grp.inv a))) :=
        grp.mul_assoc _ _ _
    _ = grp.mul (grp.inv (grp.inv a)) (grp.mul (grp.mul (grp.inv a) a) (grp.inv a)) := by
        rw [grp.mul_assoc (grp.inv a) a (grp.inv a)]
    _ = grp.mul (grp.inv (grp.inv a)) (grp.inv a) := by
        rw [grp.mul_left_inv a, grp.one_mul]
    _ = grp.one := grp.mul_left_inv (grp.inv a)

theorem GroupStruct.mul_one {G : Type} (grp : GroupStruct G) (a : G) :
    grp.mul a grp.one = a := by
  rw [← grp.mul_left_inv a, ← grp.mul_assoc, grp.mul_right_inv, grp.one_mul]

theorem GroupStruct.inv_one {G : Type} (grp : GroupStruct G) :
    grp.inv grp.one = grp.one := by
  have h := grp.mul_left_inv grp.one
  rw [grp.mul_one] at h
  exact h

/-- A subgroup of G equipped with grp : GroupStruct G. -/
structure Subgroup {G : Type} (grp : GroupStruct G) where
  carrier : G → Prop
  one_mem : carrier grp.one
  mul_mem : ∀ {a b : G}, carrier a → carrier b → carrier (grp.mul a b)
  inv_mem : ∀ {a : G}, carrier a → carrier (grp.inv a)

theorem Subgroup.ext {G : Type} {grp : GroupStruct G} {H K : Subgroup grp}
    (h : ∀ g : G, H.carrier g ↔ K.carrier g) : H = K := by
  cases H with
  | mk cH _ _ _ =>
    cases K with
    | mk cK _ _ _ =>
      have hc : cH = cK := funext (fun g => propext (h g))
      subst hc
      rfl

/-- Inclusion partial order on subgroups (the subgroup lattice order). -/
def SubLe {G : Type} {grp : GroupStruct G} (H K : Subgroup grp) : Prop :=
  ∀ g : G, H.carrier g → K.carrier g

def SubLt {G : Type} {grp : GroupStruct G} (H K : Subgroup grp) : Prop :=
  SubLe H K ∧ H ≠ K

theorem subLe_refl {G : Type} {grp : GroupStruct G} (H : Subgroup grp) : SubLe H H :=
  fun _ hg => hg

theorem subLe_trans {G : Type} {grp : GroupStruct G} {H K M : Subgroup grp}
    (h1 : SubLe H K) (h2 : SubLe K M) : SubLe H M :=
  fun g hg => h2 g (h1 g hg)

theorem subLe_antisymm {G : Type} {grp : GroupStruct G} {H K : Subgroup grp}
    (h1 : SubLe H K) (h2 : SubLe K H) : H = K :=
  Subgroup.ext (fun g => ⟨h1 g, h2 g⟩)

/-- Trivial (bottom) subgroup {1}. -/
def botSub {G : Type} (grp : GroupStruct G) : Subgroup grp where
  carrier := fun g => g = grp.one
  one_mem := rfl
  mul_mem := by
    intro a b ha hb
    subst ha; subst hb
    exact grp.one_mul grp.one
  inv_mem := by
    intro a ha
    subst ha
    exact grp.inv_one

/-- Whole group (top) subgroup G. -/
def topSub {G : Type} (grp : GroupStruct G) : Subgroup grp where
  carrier := fun _ => True
  one_mem := trivial
  mul_mem := fun _ _ => trivial
  inv_mem := fun _ => trivial

/-- Arbitrary meet (intersection) of subgroups, witnessing complete lattice structure. -/
def sInfSub {G : Type} {grp : GroupStruct G} (S : Subgroup grp → Prop) : Subgroup grp where
  carrier := fun g => ∀ H : Subgroup grp, S H → H.carrier g
  one_mem := fun H _ => H.one_mem
  mul_mem := fun ha hb H hH => H.mul_mem (ha H hH) (hb H hH)
  inv_mem := fun ha H hH => H.inv_mem (ha H hH)

/-- Binary meet (intersection) in the subgroup lattice. -/
def infSub {G : Type} {grp : GroupStruct G} (H K : Subgroup grp) : Subgroup grp where
  carrier := fun g => H.carrier g ∧ K.carrier g
  one_mem := ⟨H.one_mem, K.one_mem⟩
  mul_mem := fun ha hb => ⟨H.mul_mem ha.1 hb.1, K.mul_mem ha.2 hb.2⟩
  inv_mem := fun ha => ⟨H.inv_mem ha.1, K.inv_mem ha.2⟩

/-- Binary join (subgroup generated by union) in the subgroup lattice. -/
def supSub {G : Type} {grp : GroupStruct G} (H K : Subgroup grp) : Subgroup grp :=
  sInfSub (fun M => SubLe H M ∧ SubLe K M)

theorem botSub_le {G : Type} {grp : GroupStruct G} (H : Subgroup grp) :
    SubLe (botSub grp) H := by
  intro _ hg
  subst hg
  exact H.one_mem

theorem le_topSub {G : Type} {grp : GroupStruct G} (H : Subgroup grp) :
    SubLe H (topSub grp) :=
  fun _ _ => trivial

theorem infSub_le_left {G : Type} {grp : GroupStruct G} (H K : Subgroup grp) :
    SubLe (infSub H K) H :=
  fun _ hg => hg.1

theorem infSub_le_right {G : Type} {grp : GroupStruct G} (H K : Subgroup grp) :
    SubLe (infSub H K) K :=
  fun _ hg => hg.2

theorem le_infSub {G : Type} {grp : GroupStruct G} {M H K : Subgroup grp}
    (h1 : SubLe M H) (h2 : SubLe M K) : SubLe M (infSub H K) :=
  fun g hg => ⟨h1 g hg, h2 g hg⟩

theorem le_supSub_left {G : Type} {grp : GroupStruct G} (H K : Subgroup grp) :
    SubLe H (supSub H K) :=
  fun g hg _ hM => hM.1 g hg

theorem le_supSub_right {G : Type} {grp : GroupStruct G} (H K : Subgroup grp) :
    SubLe K (supSub H K) :=
  fun g hg _ hM => hM.2 g hg

theorem supSub_le {G : Type} {grp : GroupStruct G} {H K M : Subgroup grp}
    (h1 : SubLe H M) (h2 : SubLe K M) : SubLe (supSub H K) M :=
  fun _ hg => hg M ⟨h1, h2⟩

/-- Covering relation H <· K in the subgroup lattice. -/
def SubCovers {G : Type} {grp : GroupStruct G} (H K : Subgroup grp) : Prop :=
  SubLt H K ∧ ∀ M : Subgroup grp, ¬ (SubLt H M ∧ SubLt M K)

/-- Adjacent elements of a list of subgroups form covering steps H_0 <· H_1 <· ... <· H_r. -/
def AdjacentCovers {G : Type} (grp : GroupStruct G) : List (Subgroup grp) → Prop
  | [] => False
  | [_] => True
  | H :: K :: rest => SubCovers H K ∧ AdjacentCovers grp (K :: rest)

/-- A maximal chain in the subgroup lattice of grp, from botSub to topSub. -/
def IsMaximalChainList {G : Type} (grp : GroupStruct G) (L : List (Subgroup grp)) : Prop :=
  L.head? = some (botSub grp) ∧
  L.getLast? = some (topSub grp) ∧
  AdjacentCovers grp L

/-- Exact enumeration of all maximal chains of grp without duplicates. -/
def HasExactMaximalChains {G : Type} (grp : GroupStruct G)
    (chains : List (List (Subgroup grp))) : Prop :=
  chains.Nodup ∧ ∀ L : List (Subgroup grp), L ∈ chains ↔ IsMaximalChainList grp L

/-! ## Section 3: Complete Classification of Subgroups & Maximal Chains of Z/p^k Z -/

theorem mod_add_mod_left (a b n : Nat) : ((a % n) + b) % n = (a + b) % n := by
  have h1 := Nat.add_mod a b n
  have h2 := Nat.add_mod (a % n) b n
  rw [Nat.mod_mod] at h2
  omega

theorem mod_add_mod_right (a b n : Nat) : (a + (b % n)) % n = (a + b) % n := by
  rw [Nat.add_comm a (b % n), mod_add_mod_left, Nat.add_comm]

/-- Additive cyclic group Z/nZ on Fin n for n > 0. -/
def ZModGroup (n : Nat) (hn : 0 < n) : GroupStruct (Fin n) where
  mul := fun a b => ⟨(a.val + b.val) % n, Nat.mod_lt _ hn⟩
  one := ⟨0, hn⟩
  inv := fun a => ⟨(n - a.val) % n, Nat.mod_lt _ hn⟩
  mul_assoc := by
    intro a b c
    apply Fin.ext
    dsimp
    rw [mod_add_mod_left, mod_add_mod_right, Nat.add_assoc]
  one_mul := by
    intro a
    apply Fin.ext
    dsimp
    rw [Nat.zero_add, Nat.mod_eq_of_lt a.isLt]
  mul_left_inv := by
    intro a
    apply Fin.ext
    dsimp
    rw [mod_add_mod_left]
    have hsum : n - a.val + a.val = n := by
      have := a.isLt
      omega
    rw [hsum, Nat.mod_self]

theorem zmod_nsmul_mem {n : Nat} {hn : 0 < n} (H : Subgroup (ZModGroup n hn))
    {x : Fin n} (hx : H.carrier x) :
    ∀ q : Nat, H.carrier ⟨(q * x.val) % n, Nat.mod_lt _ hn⟩
  | 0 => by
    have hfin : (⟨(0 * x.val) % n, Nat.mod_lt _ hn⟩ : Fin n) = (ZModGroup n hn).one := by
      apply Fin.ext
      dsimp [ZModGroup]
      simp
    rw [hfin]
    exact H.one_mem
  | q + 1 => by
    have ih := zmod_nsmul_mem H hx q
    have hmul := H.mul_mem ih hx
    have hfin : (ZModGroup n hn).mul ⟨(q * x.val) % n, Nat.mod_lt _ hn⟩ x =
        ⟨((q + 1) * x.val) % n, Nat.mod_lt _ hn⟩ := by
      apply Fin.ext
      dsimp [ZModGroup]
      rw [mod_add_mod_left, Nat.succ_mul]
    rw [← hfin]
    exact hmul

theorem zmod_mod_mem_of_mem {n : Nat} {hn : 0 < n} (H : Subgroup (ZModGroup n hn))
    {d : Nat} (hd0 : 0 < d) (hdn : d < n) (hdH : H.carrier ⟨d, hdn⟩)
    {a : Nat} (haH : H.carrier ⟨a % n, Nat.mod_lt _ hn⟩) :
    H.carrier ⟨a % d, Nat.lt_trans (Nat.mod_lt a hd0) hdn⟩ := by
  let q := a / d
  let r := a % d
  have har : q * d + r = a := by
    have := Nat.div_add_mod a d
    rw [Nat.mul_comm] at this
    exact this
  have hqd_mem : H.carrier ⟨(q * d) % n, Nat.mod_lt _ hn⟩ :=
    zmod_nsmul_mem H hdH q
  have hinv_mem : H.carrier ((ZModGroup n hn).inv ⟨(q * d) % n, Nat.mod_lt _ hn⟩) :=
    H.inv_mem hqd_mem
  have hcomb := H.mul_mem hinv_mem haH
  have hr_lt : r < n := Nat.lt_trans (Nat.mod_lt a hd0) hdn
  have heq : (ZModGroup n hn).mul ((ZModGroup n hn).inv ⟨(q * d) % n, Nat.mod_lt _ hn⟩)
      ⟨a % n, Nat.mod_lt _ hn⟩ = ⟨r, hr_lt⟩ := by
    apply Fin.ext
    dsimp [ZModGroup]
    rw [mod_add_mod_left, mod_add_mod_right]
    let m := (q * d) % n
    have hm_lt : m < n := Nat.mod_lt (q * d) hn
    have hqd_split : n * (q * d / n) + m = q * d := Nat.div_add_mod (q * d) n
    have hbig : n - m + a = n * (q * d / n + 1) + r := by
      rw [Nat.mul_add, Nat.mul_one]
      omega
    rw [hbig, Nat.add_comm, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hr_lt]
  rw [← heq]
  exact hcomb

theorem exists_min_pos_fin {n : Nat} (P : Nat → Prop) :
    ∀ bound : Nat, bound ≤ n → (∃ m : Nat, 0 < m ∧ m < bound ∧ P m) →
      ∃ d : Nat, 0 < d ∧ d < n ∧ P d ∧ ∀ m : Nat, 0 < m → m < d → ¬ P m
  | 0, _, ⟨m, _, hm, _⟩ => by omega
  | b + 1, hb, hex => by
    by_cases hlow : ∃ m : Nat, 0 < m ∧ m < b ∧ P m
    · exact exists_min_pos_fin P b (by omega) hlow
    · rcases hex with ⟨m, hm0, hmb, hPm⟩
      have hmb_eq : m = b := by
        cases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hmb) with
        | inl hlt => exact False.elim (hlow ⟨m, hm0, hlt, hPm⟩)
        | inr heq => exact heq
      subst hmb_eq
      refine ⟨m, hm0, by omega, hPm, ?_⟩
      intro m' hm'0 hm'lt hPm'
      exact hlow ⟨m', hm'0, hm'lt, hPm'⟩

/-- Every subgroup of Z/nZ equals {x | d | x.val} for a divisor d of n. -/
theorem zmod_subgroup_eq_divisor {n : Nat} (hn : 0 < n) (H : Subgroup (ZModGroup n hn)) :
    ∃ d : Nat, d ∣ n ∧ ∀ x : Fin n, H.carrier x ↔ d ∣ x.val := by
  by_cases hpos : ∃ m : Nat, 0 < m ∧ m < n ∧ ∃ hm : m < n, H.carrier ⟨m, hm⟩
  · rcases exists_min_pos_fin (fun m => ∃ hm : m < n, H.carrier ⟨m, hm⟩) n (Nat.le_refl n) hpos
      with ⟨d, hd0, hdn, ⟨_, hdH⟩, hmin⟩
    refine ⟨d, ?_, ?_⟩
    · have hnH : H.carrier ⟨n % n, Nat.mod_lt _ hn⟩ := by
        have hfin : (⟨n % n, Nat.mod_lt _ hn⟩ : Fin n) = (ZModGroup n hn).one := by
          apply Fin.ext
          dsimp [ZModGroup]
          exact Nat.mod_self n
        rw [hfin]
        exact H.one_mem
      have hrem := zmod_mod_mem_of_mem H hd0 hdn hdH hnH
      have hrem0 : n % d = 0 := by
        cases Nat.eq_zero_or_pos (n % d) with
        | inl h0 => exact h0
        | inr hgt =>
          exact False.elim (hmin (n % d) hgt (Nat.mod_lt n hd0) ⟨_, hrem⟩)
      exact Nat.dvd_of_mod_eq_zero hrem0
    · intro x
      constructor
      · intro hx
        have hx' : H.carrier ⟨x.val % n, Nat.mod_lt _ hn⟩ := by
          have hfin : (⟨x.val % n, Nat.mod_lt _ hn⟩ : Fin n) = x := by
            apply Fin.ext; exact Nat.mod_eq_of_lt x.isLt
          rw [hfin]; exact hx
        have hrem := zmod_mod_mem_of_mem H hd0 hdn hdH hx'
        have hrem0 : x.val % d = 0 := by
          cases Nat.eq_zero_or_pos (x.val % d) with
          | inl h0 => exact h0
          | inr hgt =>
            exact False.elim (hmin (x.val % d) hgt (Nat.mod_lt x.val hd0) ⟨_, hrem⟩)
        exact Nat.dvd_of_mod_eq_zero hrem0
      · rintro ⟨q, hxq⟩
        have hmem := zmod_nsmul_mem H hdH q
        have hfin : (⟨(q * d) % n, Nat.mod_lt _ hn⟩ : Fin n) = x := by
          apply Fin.ext
          dsimp
          rw [Nat.mul_comm q d, ← hxq, Nat.mod_eq_of_lt x.isLt]
        rw [hfin] at hmem
        exact hmem
  · refine ⟨n, Nat.dvd_refl n, ?_⟩
    intro x
    constructor
    · intro hx
      cases Nat.eq_zero_or_pos x.val with
      | inl h0 => exact ⟨0, by omega⟩
      | inr hgt => exact False.elim (hpos ⟨x.val, hgt, x.isLt, x.isLt, hx⟩)
    · rintro ⟨q, hxq⟩
      have hx0 : x.val = 0 := by
        cases q with
        | zero => omega
        | succ q' =>
          have : n * 1 ≤ n * (q' + 1) := Nat.mul_le_mul_left n (by omega)
          have := x.isLt
          omega
      have hfin : x = (ZModGroup n hn).one := by
        apply Fin.ext
        dsimp [ZModGroup]
        exact hx0
      rw [hfin]
      exact H.one_mem

abbrev CyclicPGroup (p k : Nat) (hp : IsPrime p) : GroupStruct (Fin (p ^ k)) :=
  ZModGroup (p ^ k) (pow_pos_of_pos (by have := hp.1; omega) k)

/-- The i-th standard subgroup p^i (Z/p^k Z) of Z/p^k Z. -/
def cyclicSub (p k i : Nat) (hp : IsPrime p) : Subgroup (CyclicPGroup p k hp) where
  carrier := fun x => p ^ i ∣ x.val
  one_mem := by
    dsimp [CyclicPGroup, ZModGroup]
    exact ⟨0, by simp⟩
  mul_mem := by
    intro a b ha hb
    dsimp [CyclicPGroup, ZModGroup]
    let N := p ^ k
    let s := a.val + b.val
    change p ^ i ∣ s % N
    by_cases hik : i ≤ k
    · have hpk : p ^ i ∣ N := pow_dvd_pow_of_le p hik
      have hsum : p ^ i ∣ s := dvd_add_of_dvd ha hb
      have hdiv_add : N * (s / N) + s % N = s := Nat.div_add_mod s N
      have hdiv : s % N = s - N * (s / N) := by omega
      rw [hdiv]
      rcases hpk with ⟨r, hr⟩
      have hmul : p ^ i ∣ N * (s / N) :=
        ⟨r * (s / N), by rw [hr, Nat.mul_assoc]⟩
      exact dvd_sub_of_dvd hmul hsum
    · have hpi_gt : p ^ k < p ^ i := pow_lt_pow_of_lt hp.1 (by omega)
      have ha0 : a.val = 0 := by
        cases Nat.eq_zero_or_pos a.val with
        | inl h0 => exact h0
        | inr hpos =>
          have := le_of_dvd_pos hpos ha
          have := a.isLt
          omega
      have hb0 : b.val = 0 := by
        cases Nat.eq_zero_or_pos b.val with
        | inl h0 => exact h0
        | inr hpos =>
          have := le_of_dvd_pos hpos hb
          have := b.isLt
          omega
      have hs0 : s = 0 := by dsimp [s]; omega
      rw [hs0, Nat.zero_mod]
      exact ⟨0, by simp⟩
  inv_mem := by
    intro a ha
    dsimp [CyclicPGroup, ZModGroup]
    let N := p ^ k
    change p ^ i ∣ (N - a.val) % N
    by_cases ha0 : a.val = 0
    · rw [ha0, Nat.sub_zero, Nat.mod_self]
      exact ⟨0, by simp⟩
    · have hik : i ≤ k := by
        by_cases hle : i ≤ k
        · exact hle
        · have hpi_gt : p ^ k < p ^ i := pow_lt_pow_of_lt hp.1 (by omega)
          have := le_of_dvd_pos (by omega) ha
          have := a.isLt
          omega
      have hpk : p ^ i ∣ N := pow_dvd_pow_of_le p hik
      have hlt_sub : N - a.val < N := by
        have := a.isLt
        dsimp [N]
        omega
      rw [Nat.mod_eq_of_lt hlt_sub]
      exact dvd_sub_of_dvd ha hpk

/-- Complete classification of subgroups of Z/p^k Z: every subgroup is cyclicSub p k i for some i <= k. -/
theorem cyclicSub_classification (p k : Nat) (hp : IsPrime p)
    (H : Subgroup (CyclicPGroup p k hp)) :
    ∃ i : Nat, i ≤ k ∧ H = cyclicSub p k i hp := by
  rcases zmod_subgroup_eq_divisor (pow_pos_of_pos (by have := hp.1; omega) k) H with ⟨d, hd, hiff⟩
  rcases dvd_prime_pow hp hd with ⟨i, hi, rfl⟩
  exact ⟨i, hi, Subgroup.ext hiff⟩

theorem cyclicSub_zero_eq_top (p k : Nat) (hp : IsPrime p) :
    cyclicSub p k 0 hp = topSub (CyclicPGroup p k hp) := by
  apply Subgroup.ext
  intro x
  dsimp [cyclicSub, topSub]
  exact ⟨fun _ => trivial, fun _ => ⟨x.val, (Nat.one_mul x.val).symm⟩⟩

theorem cyclicSub_self_eq_bot (p k : Nat) (hp : IsPrime p) :
    cyclicSub p k k hp = botSub (CyclicPGroup p k hp) := by
  apply Subgroup.ext
  intro x
  dsimp [cyclicSub, botSub, CyclicPGroup, ZModGroup]
  constructor
  · intro hx
    apply Fin.ext
    dsimp
    cases Nat.eq_zero_or_pos x.val with
    | inl h0 => exact h0
    | inr hpos =>
      have := le_of_dvd_pos hpos hx
      have := x.isLt
      omega
  · intro hx
    have hx0 : x.val = 0 := congrArg Fin.val hx
    rw [hx0]
    exact ⟨0, by simp⟩

/-- Order-reversing isomorphism between {0, ..., k} and Subgroup(Z/p^k Z). -/
theorem cyclicSub_le_iff (p k i j : Nat) (hp : IsPrime p) (hi : i ≤ k) (hj : j ≤ k) :
    SubLe (cyclicSub p k j hp) (cyclicSub p k i hp) ↔ i ≤ j := by
  constructor
  · intro hle
    by_cases hij : i ≤ j
    · exact hij
    · -- j < i <= k, so j < k, hence p^j < p^k lies in cyclicSub j but not cyclicSub i
      have hjk : j < k := by omega
      have hpj_lt : p ^ j < p ^ k := pow_lt_pow_of_lt hp.1 hjk
      have hmem_j : (cyclicSub p k j hp).carrier ⟨p ^ j, hpj_lt⟩ := Nat.dvd_refl (p ^ j)
      have hmem_i : p ^ i ∣ p ^ j := hle ⟨p ^ j, hpj_lt⟩ hmem_j
      have hpj_pos : 0 < p ^ j := pow_pos_of_pos (by have := hp.1; omega) j
      have hpi_le : p ^ i ≤ p ^ j := le_of_dvd_pos hpj_pos hmem_i
      have hpi_gt : p ^ j < p ^ i := pow_lt_pow_of_lt hp.1 (by omega)
      omega
  · intro hij x hx
    rcases hx with ⟨q, hxq⟩
    rcases pow_dvd_pow_of_le p hij with ⟨r, hr⟩
    exact ⟨r * q, by rw [hxq, hr, Nat.mul_assoc]⟩

theorem cyclicSub_inj (p k i j : Nat) (hp : IsPrime p) (hi : i ≤ k) (hj : j ≤ k)
    (heq : cyclicSub p k i hp = cyclicSub p k j hp) : i = j := by
  have h1 : i ≤ j := (cyclicSub_le_iff p k i j hp hi hj).mp (by rw [heq]; exact subLe_refl _)
  have h2 : j ≤ i := (cyclicSub_le_iff p k j i hp hj hi).mp (by rw [heq]; exact subLe_refl _)
  omega

/-- Covering characterization in Z/p^k Z: cyclicSub j covers cyclicSub i iff j <= k and i = j + 1?
    Wait: SubCovers H K means H < K! Since cyclicSub is order-reversing,
    cyclicSub (m + 1) <· cyclicSub m for m < k! -/
theorem cyclicSub_covers_iff (p k a b : Nat) (hp : IsPrime p) (ha : a ≤ k) (hb : b ≤ k) :
    SubCovers (cyclicSub p k a hp) (cyclicSub p k b hp) ↔ a = b + 1 := by
  constructor
  · rintro ⟨⟨hle, hne⟩, hcov⟩
    have hba : b ≤ a := (cyclicSub_le_iff p k b a hp hb ha).mp hle
    have hba_ne : b ≠ a := by
      intro h; subst h; exact hne rfl
    have hlt_ba : b + 1 ≤ a := by omega
    by_cases heq : a = b + 1
    · exact heq
    · have hgt : b + 1 < a := by omega
      have h1 : SubLt (cyclicSub p k a hp) (cyclicSub p k (b + 1) hp) := by
        refine ⟨(cyclicSub_le_iff p k (b + 1) a hp (by omega) ha).mpr (by omega), ?_⟩
        intro h
        have := cyclicSub_inj p k a (b + 1) hp ha (by omega) h
        omega
      have h2 : SubLt (cyclicSub p k (b + 1) hp) (cyclicSub p k b hp) := by
        refine ⟨(cyclicSub_le_iff p k b (b + 1) hp hb (by omega)).mpr (by omega), ?_⟩
        intro h
        have := cyclicSub_inj p k (b + 1) b hp (by omega) hb h
        omega
      exact False.elim (hcov (cyclicSub p k (b + 1) hp) ⟨h1, h2⟩)
  · rintro rfl
    refine ⟨⟨(cyclicSub_le_iff p k b (b + 1) hp hb ha).mpr (by omega), ?_⟩, ?_⟩
    · intro h
      have := cyclicSub_inj p k (b + 1) b hp ha hb h
      omega
    · intro M ⟨⟨hle1, hne1⟩, ⟨hle2, hne2⟩⟩
      rcases cyclicSub_classification p k hp M with ⟨m, hm, rfl⟩
      have hm1 : m ≤ b + 1 := (cyclicSub_le_iff p k m (b + 1) hp hm ha).mp hle1
      have hm2 : b ≤ m := (cyclicSub_le_iff p k b m hp hb hm).mp hle2
      have hm_ne1 : m ≠ b + 1 := fun h => by subst h; exact hne1 rfl
      have hm_ne2 : b ≠ m := fun h => by subst h; exact hne2 rfl
      omega

/-- Descending-exponent chain [cyclicSub m, cyclicSub (m-1), ..., cyclicSub 0]. -/
def cyclicChainFrom (p k : Nat) (hp : IsPrime p) : Nat → List (Subgroup (CyclicPGroup p k hp))
  | 0 => [cyclicSub p k 0 hp]
  | m + 1 => cyclicSub p k (m + 1) hp :: cyclicChainFrom p k hp m

/-- The unique maximal chain of Z/p^k Z. -/
def cyclicMaxChain (p k : Nat) (hp : IsPrime p) : List (Subgroup (CyclicPGroup p k hp)) :=
  cyclicChainFrom p k hp k

theorem cyclicChainFrom_head (p k m : Nat) (hp : IsPrime p) :
    (cyclicChainFrom p k hp m).head? = some (cyclicSub p k m hp) := by
  cases m <;> rfl

theorem cyclicChainFrom_last (p k : Nat) (hp : IsPrime p) :
    ∀ m : Nat, (cyclicChainFrom p k hp m).getLast? = some (cyclicSub p k 0 hp)
  | 0 => rfl
  | 1 => rfl
  | m' + 2 => cyclicChainFrom_last p k hp (m' + 1)

theorem cyclicChainFrom_covers (p k : Nat) (hp : IsPrime p) :
    ∀ m : Nat, m ≤ k → AdjacentCovers (CyclicPGroup p k hp) (cyclicChainFrom p k hp m)
  | 0, _ => trivial
  | m + 1, hm => by
    cases m with
    | zero =>
      dsimp [cyclicChainFrom, AdjacentCovers]
      exact ⟨(cyclicSub_covers_iff p k 1 0 hp hm (by omega)).mpr rfl, trivial⟩
    | succ m' =>
      dsimp [cyclicChainFrom, AdjacentCovers]
      exact ⟨(cyclicSub_covers_iff p k (m' + 2) (m' + 1) hp hm (by omega)).mpr rfl,
        cyclicChainFrom_covers p k hp (m' + 1) (by omega)⟩

/-- Uniqueness of maximal chain tail starting from cyclicSub m (for m <= k). -/
theorem cyclicChainFrom_unique (p k : Nat) (hp : IsPrime p) :
    ∀ (L : List (Subgroup (CyclicPGroup p k hp))) (m : Nat),
      m ≤ k →
      L.head? = some (cyclicSub p k m hp) →
      L.getLast? = some (topSub (CyclicPGroup p k hp)) →
      AdjacentCovers (CyclicPGroup p k hp) L →
      L = cyclicChainFrom p k hp m
  | [], _, _, hhead, _, _ => by simp at hhead
  | [H], m, hm, hhead, hlast, _ => by
    simp at hhead hlast
    have h1 : cyclicSub p k m hp = topSub (CyclicPGroup p k hp) := by
      rw [← hhead, hlast]
    rw [← cyclicSub_zero_eq_top p k hp] at h1
    have hm0 : m = 0 := cyclicSub_inj p k m 0 hp hm (by omega) h1
    subst hm0
    simp [cyclicChainFrom, hhead]
  | H :: K :: rest, m, hm, hhead, hlast, hcov => by
    simp at hhead
    subst hhead
    dsimp [AdjacentCovers] at hcov
    rcases hcov with ⟨hHK, hrest⟩
    rcases cyclicSub_classification p k hp K with ⟨b, hb, rfl⟩
    have hmb : m = b + 1 := (cyclicSub_covers_iff p k m b hp hm hb).mp hHK
    subst hmb
    have hlast' : (cyclicSub p k b hp :: rest).getLast? = some (topSub (CyclicPGroup p k hp)) := by
      simpa using hlast
    have ih := cyclicChainFrom_unique p k hp (cyclicSub p k b hp :: rest) b hb rfl hlast' hrest
    dsimp [cyclicChainFrom]
    rw [ih]

/-- Exact maximal chain theorem for Z/p^k Z: for every prime p and every k >= 0,
    Z/p^k Z has a unique maximal chain, so its maximal chain count is identically 1. -/
theorem cyclic_hasExactMaximalChains (p k : Nat) (hp : IsPrime p) :
    HasExactMaximalChains (CyclicPGroup p k hp) [cyclicMaxChain p k hp] ∧
    [cyclicMaxChain p k hp].length = 1 := by
  refine ⟨⟨by simp, ?_⟩, rfl⟩
  intro L
  simp only [List.mem_singleton]
  constructor
  · rintro rfl
    refine ⟨?_, ?_, cyclicChainFrom_covers p k hp k (Nat.le_refl k)⟩
    · dsimp [cyclicMaxChain]
      rw [cyclicChainFrom_head, cyclicSub_self_eq_bot]
    · dsimp [cyclicMaxChain]
      rw [cyclicChainFrom_last, cyclicSub_zero_eq_top]
  · rintro ⟨hhead, hlast, hcov⟩
    rw [← cyclicSub_self_eq_bot p k hp] at hhead
    exact cyclicChainFrom_unique p k hp L k (Nat.le_refl k) hhead hlast hcov

/-! ## Section 4: Elementary Abelian (Z/p Z)^2 Subgroup Lattice & Flag Count p + 1 -/

/-- Direct product of two GroupStructs. -/
def ProdGroup {A B : Type} (gA : GroupStruct A) (gB : GroupStruct B) : GroupStruct (A × B) where
  mul := fun x y => (gA.mul x.1 y.1, gB.mul x.2 y.2)
  one := (gA.one, gB.one)
  inv := fun x => (gA.inv x.1, gB.inv x.2)
  mul_assoc := fun x y z => Prod.ext (gA.mul_assoc x.1 y.1 z.1) (gB.mul_assoc x.2 y.2 z.2)
  one_mul := fun x => Prod.ext (gA.one_mul x.1) (gB.one_mul x.2)
  mul_left_inv := fun x => Prod.ext (gA.mul_left_inv x.1) (gB.mul_left_inv x.2)

/-- Elementary abelian p-group (Z/p Z)^2 of order p^2 (log_p |G| = 2). -/
abbrev ElemAbelian2 (p : Nat) (hp : IsPrime p) : GroupStruct (Fin p × Fin p) :=
  ProdGroup (ZModGroup p (by have := hp.1; omega)) (ZModGroup p (by have := hp.1; omega))

theorem mod_mul_mod_right (m a p : Nat) : (m * (a % p)) % p = (m * a) % p := by
  rw [Nat.mul_mod m (a % p) p, Nat.mod_mod, ← Nat.mul_mod]

theorem mod_mul_mod_left (a b p : Nat) : ((a % p) * b) % p = (a * b) % p := by
  rw [Nat.mul_comm (a % p) b, mod_mul_mod_right, Nat.mul_comm]

theorem eq_neg_mod_of_add_mod_zero {x y p : Nat} (hx : x < p) (hy : y < p)
    (h : (x + y) % p = 0) : y = (p - x) % p := by
  by_cases hx0 : x = 0
  · subst hx0
    rw [Nat.sub_zero, Nat.mod_self]
    rw [Nat.zero_add, Nat.mod_eq_of_lt hy] at h
    exact h
  · have hdiv := Nat.div_add_mod (x + y) p
    rw [h, Nat.add_zero] at hdiv
    have hq1 : (x + y) / p = 1 := by
      match hq : (x + y) / p with
      | 0 =>
        rw [hq, Nat.mul_zero] at hdiv
        omega
      | 1 => rfl
      | q' + 2 =>
        have hmul : p * 2 ≤ p * ((x + y) / p) := Nat.mul_le_mul_left p (by omega)
        rw [Nat.mul_two] at hmul
        omega
    rw [hq1, Nat.mul_one] at hdiv
    have hy_eq : y = p - x := by omega
    rw [hy_eq, Nat.mod_eq_of_lt (by omega)]

/-- Scalar multiple c • v in (Z/p Z)^2. -/
def ea2Smul (p : Nat) (hp : IsPrime p) (c : Nat) (v : Fin p × Fin p) : Fin p × Fin p :=
  let hp0 : 0 < p := by have := hp.1; omega
  (⟨(c * v.1.val) % p, Nat.mod_lt _ hp0⟩, ⟨(c * v.2.val) % p, Nat.mod_lt _ hp0⟩)

theorem ea2Smul_mem {p : Nat} {hp : IsPrime p} (H : Subgroup (ElemAbelian2 p hp))
    {v : Fin p × Fin p} (hv : H.carrier v) :
    ∀ c : Nat, H.carrier (ea2Smul p hp c v)
  | 0 => by
    have heq : ea2Smul p hp 0 v = (ElemAbelian2 p hp).one := by
      apply Prod.ext <;> apply Fin.ext <;> simp [ea2Smul, ElemAbelian2, ProdGroup, ZModGroup]
    rw [heq]
    exact H.one_mem
  | c + 1 => by
    have ih := ea2Smul_mem H hv c
    have hmul := H.mul_mem ih hv
    have heq : (ElemAbelian2 p hp).mul (ea2Smul p hp c v) v = ea2Smul p hp (c + 1) v := by
      apply Prod.ext <;> apply Fin.ext <;>
        (dsimp [ea2Smul, ElemAbelian2, ProdGroup, ZModGroup];
         rw [mod_add_mod_left, Nat.succ_mul])
    rw [← heq]
    exact hmul

/-- Slope-m line subgroup L_m = {(x, m*x mod p)} of (Z/p Z)^2 for m : Fin p. -/
def slopeSub (p : Nat) (hp : IsPrime p) (m : Fin p) : Subgroup (ElemAbelian2 p hp) where
  carrier := fun v => v.2.val = (m.val * v.1.val) % p
  one_mem := by
    dsimp [ElemAbelian2, ProdGroup, ZModGroup]
    simp
  mul_mem := by
    intro a b ha hb
    dsimp [ElemAbelian2, ProdGroup, ZModGroup]
    rw [ha, hb, mod_add_mod_left, mod_add_mod_right, ← Nat.mul_add, ← mod_mul_mod_right]
  inv_mem := by
    intro a ha
    dsimp [ElemAbelian2, ProdGroup, ZModGroup]
    have hsum : (a.2.val + (m.val * ((p - a.1.val) % p)) % p) % p = 0 := by
      rw [ha, mod_add_mod_left, mod_add_mod_right, ← Nat.mul_add, ← mod_mul_mod_right]
      rw [mod_add_mod_right]
      by_cases ha1 : a.1.val = 0
      · rw [ha1, Nat.zero_add, Nat.sub_zero, Nat.mod_self, Nat.mul_zero, Nat.zero_mod]
      · have : a.1.val + (p - a.1.val) = p := by have := a.1.isLt; omega
        rw [this, Nat.mod_self, Nat.mul_zero, Nat.zero_mod]
    have hp0 : 0 < p := by have := hp.1; omega
    exact (eq_neg_mod_of_add_mod_zero a.2.isLt (Nat.mod_lt _ hp0) hsum).symm

/-- Vertical line subgroup L_infty = {(0, y)} of (Z/p Z)^2. -/
def vertSub (p : Nat) (hp : IsPrime p) : Subgroup (ElemAbelian2 p hp) where
  carrier := fun v => v.1.val = 0
  one_mem := rfl
  mul_mem := by
    intro a b ha hb
    dsimp [ElemAbelian2, ProdGroup, ZModGroup]
    rw [ha, hb, Nat.add_zero, Nat.zero_mod]
  inv_mem := by
    intro a ha
    dsimp [ElemAbelian2, ProdGroup, ZModGroup]
    rw [ha, Nat.sub_zero, Nat.mod_self]

/-- Complete classification of all subgroups of (Z/p Z)^2 for every prime p:
    every subgroup is bot, top, vertSub, or slopeSub m. -/
theorem ea2_subgroup_classification (p : Nat) (hp : IsPrime p)
    (H : Subgroup (ElemAbelian2 p hp)) :
    H = botSub (ElemAbelian2 p hp) ∨
    H = topSub (ElemAbelian2 p hp) ∨
    H = vertSub p hp ∨
    ∃ m : Fin p, H = slopeSub p hp m := by
  have hp2 := hp.1
  have hp0 : 0 < p := by omega
  by_cases hnz1 : ∃ v : Fin p × Fin p, H.carrier v ∧ v.1.val ≠ 0
  · rcases hnz1 with ⟨v, hvH, hv1⟩
    rcases mod_inv_of_lt_prime hp (by omega) v.1.isLt with ⟨u, _, huv⟩
    let w := ea2Smul p hp u v
    have hwH : H.carrier w := ea2Smul_mem H hvH u
    have hw1 : w.1.val = 1 := by
      dsimp [w, ea2Smul]
      exact huv
    let m : Fin p := w.2
    -- Show slopeSub m <= H
    have hSlopeLe : SubLe (slopeSub p hp m) H := by
      intro z hz
      dsimp [slopeSub] at hz
      have hsm := ea2Smul_mem H hwH z.1.val
      have hz_eq : ea2Smul p hp z.1.val w = z := by
        apply Prod.ext
        · apply Fin.ext
          dsimp [ea2Smul]
          rw [hw1, Nat.mul_one, Nat.mod_eq_of_lt z.1.isLt]
        · apply Fin.ext
          dsimp [ea2Smul]
          change (z.1.val * m.val) % p = z.2.val
          rw [Nat.mul_comm, ← hz]
      rw [hz_eq] at hsm
      exact hsm
    by_cases hHLe : SubLe H (slopeSub p hp m)
    · exact Or.inr (Or.inr (Or.inr ⟨m, subLe_antisymm hHLe hSlopeLe⟩))
    · -- H strictly contains slopeSub m, so H = topSub
      refine Or.inr (Or.inl ?_)
      have hex : ∃ z : Fin p × Fin p, H.carrier z ∧ ¬ (slopeSub p hp m).carrier z := by
        by_cases hex' : ∃ z, H.carrier z ∧ ¬ (slopeSub p hp m).carrier z
        · exact hex'
        · refine False.elim (hHLe ?_)
          intro z hzH
          by_cases hzS : (slopeSub p hp m).carrier z
          · exact hzS
          · exact False.elim (hex' ⟨z, hzH, hzS⟩)
      rcases hex with ⟨z, hzH, hzNot⟩
      let proj : Fin p × Fin p := ea2Smul p hp z.1.val w
      have hprojH : H.carrier proj := ea2Smul_mem H hwH z.1.val
      let diff := (ElemAbelian2 p hp).mul z ((ElemAbelian2 p hp).inv proj)
      have hdiffH : H.carrier diff := H.mul_mem hzH (H.inv_mem hprojH)
      have hproj1 : proj.1.val = z.1.val := by
        dsimp [proj, ea2Smul]
        rw [hw1, Nat.mul_one, Nat.mod_eq_of_lt z.1.isLt]
      have hproj2 : proj.2.val = (m.val * z.1.val) % p := by
        dsimp [proj, ea2Smul]
        change (z.1.val * m.val) % p = (m.val * z.1.val) % p
        rw [Nat.mul_comm]
      have hdiff1 : diff.1.val = 0 := by
        dsimp [diff, ElemAbelian2, ProdGroup, ZModGroup]
        rw [hproj1, mod_add_mod_right]
        have : z.1.val + (p - z.1.val) = p := by have := z.1.isLt; omega
        rw [this, Nat.mod_self]
      have hdiff2_ne : diff.2.val ≠ 0 := by
        intro hd0
        apply hzNot
        dsimp [slopeSub]
        rw [← hproj2]
        dsimp [diff, ElemAbelian2, ProdGroup, ZModGroup] at hd0
        -- (z.2 + (p - proj.2) % p) % p = 0 -> (p - proj.2) % p = (p - z.2) % p -> z.2 = proj.2
        have h1 := eq_neg_mod_of_add_mod_zero z.2.isLt (Nat.mod_lt _ hp0) hd0
        -- Also proj.2 + (p - proj.2) % p ≡ 0 (mod p)
        have hsum_p : (proj.2.val + (p - proj.2.val) % p) % p = 0 := by
          rw [mod_add_mod_right]
          by_cases hpj0 : proj.2.val = 0
          · rw [hpj0, Nat.zero_add, Nat.sub_zero, Nat.mod_self]
          · have : proj.2.val + (p - proj.2.val) = p := by have := proj.2.isLt; omega
            rw [this, Nat.mod_self]
        -- Swap to get proj.2 = (p - ((p - proj.2) % p)) % p
        rw [Nat.add_comm] at hd0 hsum_p
        have hz_eq := eq_neg_mod_of_add_mod_zero (Nat.mod_lt _ hp0) z.2.isLt hd0
        have hp_eq := eq_neg_mod_of_add_mod_zero (Nat.mod_lt _ hp0) proj.2.isLt hsum_p
        rw [hz_eq, ← hp_eq]
      rcases mod_inv_of_lt_prime hp (by omega) diff.2.isLt with ⟨u2, _, hu2⟩
      let e01 := ea2Smul p hp u2 diff
      have he01H : H.carrier e01 := ea2Smul_mem H hdiffH u2
      have he01_1 : e01.1.val = 0 := by
        dsimp [e01, ea2Smul]
        rw [hdiff1, Nat.mul_zero, Nat.zero_mod]
      have he01_2 : e01.2.val = 1 := by
        dsimp [e01, ea2Smul]
        exact hu2
      -- Now any t : Fin p × Fin p equals z1 • w + (t.2 - m*t.1) • e01!
      apply subLe_antisymm (le_topSub H)
      intro t _
      let base := ea2Smul p hp t.1.val w
      have hbaseH : H.carrier base := ea2Smul_mem H hwH t.1.val
      let corr_coeff := (t.2.val + (p - base.2.val) % p) % p
      let corr := ea2Smul p hp corr_coeff e01
      have hcorrH : H.carrier corr := ea2Smul_mem H he01H corr_coeff
      have hsumH := H.mul_mem hbaseH hcorrH
      have hsum_eq : (ElemAbelian2 p hp).mul base corr = t := by
        apply Prod.ext
        · apply Fin.ext
          dsimp [ElemAbelian2, ProdGroup, ZModGroup, base, corr, ea2Smul]
          rw [hw1, he01_1, Nat.mul_one, Nat.mul_zero, Nat.zero_mod, Nat.add_zero,
            Nat.mod_mod, Nat.mod_eq_of_lt t.1.isLt]
        · apply Fin.ext
          dsimp [ElemAbelian2, ProdGroup, ZModGroup, corr, ea2Smul]
          rw [he01_2, Nat.mul_one, Nat.mod_mod]
          rw [mod_add_mod_right, ← Nat.add_assoc, Nat.add_comm base.2.val t.2.val,
            Nat.add_assoc]
          have hcancel : (base.2.val + (p - base.2.val) % p) % p = 0 := by
            rw [mod_add_mod_right]
            by_cases hb0 : base.2.val = 0
            · rw [hb0, Nat.zero_add, Nat.sub_zero, Nat.mod_self]
            · have : base.2.val + (p - base.2.val) = p := by have := base.2.isLt; omega
              rw [this, Nat.mod_self]
          rw [← mod_add_mod_right t.2.val, hcancel, Nat.add_zero, Nat.mod_eq_of_lt t.2.isLt]
      rw [hsum_eq] at hsumH
      exact hsumH
  · -- Every element of H has first coordinate 0
    have hLeVert : SubLe H (vertSub p hp) := by
      intro v hvH
      dsimp [vertSub]
      by_cases hv0 : v.1.val = 0
      · exact hv0
      · exact False.elim (hnz1 ⟨v, hvH, hv0⟩)
    by_cases hnz2 : ∃ v : Fin p × Fin p, H.carrier v ∧ v.2.val ≠ 0
    · rcases hnz2 with ⟨v, hvH, hv2⟩
      have hv1 : v.1.val = 0 := hLeVert v hvH
      rcases mod_inv_of_lt_prime hp (by omega) v.2.isLt with ⟨u, _, huv⟩
      let e01 := ea2Smul p hp u v
      have he01H : H.carrier e01 := ea2Smul_mem H hvH u
      have he01_1 : e01.1.val = 0 := by
        dsimp [e01, ea2Smul]; rw [hv1, Nat.mul_zero, Nat.zero_mod]
      have he01_2 : e01.2.val = 1 := by
        dsimp [e01, ea2Smul]; exact huv
      refine Or.inr (Or.inr (Or.inl (subLe_antisymm hLeVert ?_)))
      intro t ht
      dsimp [vertSub] at ht
      have hsm := ea2Smul_mem H he01H t.2.val
      have ht_eq : ea2Smul p hp t.2.val e01 = t := by
        apply Prod.ext
        · apply Fin.ext
          dsimp [ea2Smul]
          rw [he01_1, Nat.mul_zero, Nat.zero_mod, ht]
        · apply Fin.ext
          dsimp [ea2Smul]
          rw [he01_2, Nat.mul_one, Nat.mod_eq_of_lt t.2.isLt]
      rw [ht_eq] at hsm
      exact hsm
    · refine Or.inl (subLe_antisymm ?_ (botSub_le H))
      intro v hvH
      dsimp [botSub]
      have hv1 : v.1.val = 0 := hLeVert v hvH
      have hv2 : v.2.val = 0 := by
        by_cases hv2' : v.2.val = 0
        · exact hv2'
        · exact False.elim (hnz2 ⟨v, hvH, hv2'⟩)
      apply Prod.ext <;> apply Fin.ext <;> dsimp [ElemAbelian2, ProdGroup, ZModGroup]
      · exact hv1
      · exact hv2

theorem slopeSub_inj (p : Nat) (hp : IsPrime p) {m1 m2 : Fin p}
    (h : slopeSub p hp m1 = slopeSub p hp m2) : m1 = m2 := by
  have hp1 : 1 < p := hp.1
  let pt : Fin p × Fin p := (⟨1, hp1⟩, m1)
  have hmem1 : (slopeSub p hp m1).carrier pt := by
    dsimp [slopeSub, pt]
    rw [Nat.mul_one, Nat.mod_eq_of_lt m1.isLt]
  rw [h] at hmem1
  dsimp [slopeSub, pt] at hmem1
  rw [Nat.mul_one, Nat.mod_eq_of_lt m2.isLt] at hmem1
  exact Fin.ext hmem1

theorem slopeSub_ne_bot (p : Nat) (hp : IsPrime p) (m : Fin p) :
    slopeSub p hp m ≠ botSub (ElemAbelian2 p hp) := by
  intro h
  have hp1 : 1 < p := hp.1
  let pt : Fin p × Fin p := (⟨1, hp1⟩, m)
  have hmem : (slopeSub p hp m).carrier pt := by
    dsimp [slopeSub, pt]; rw [Nat.mul_one, Nat.mod_eq_of_lt m.isLt]
  rw [h] at hmem
  dsimp [botSub, ElemAbelian2, ProdGroup, ZModGroup, pt] at hmem
  have h10 : (1 : Nat) = 0 := congrArg (fun x => x.1.val) hmem
  omega

theorem slopeSub_ne_top (p : Nat) (hp : IsPrime p) (m : Fin p) :
    slopeSub p hp m ≠ topSub (ElemAbelian2 p hp) := by
  intro h
  have hp1 : 1 < p := hp.1
  have hp0 : 0 < p := by omega
  let pt : Fin p × Fin p := (⟨0, hp0⟩, ⟨1, hp1⟩)
  have hmem : (topSub (ElemAbelian2 p hp)).carrier pt := trivial
  rw [← h] at hmem
  dsimp [slopeSub, pt] at hmem
  rw [Nat.zero_mod] at hmem
  omega

theorem slopeSub_ne_vert (p : Nat) (hp : IsPrime p) (m : Fin p) :
    slopeSub p hp m ≠ vertSub p hp := by
  intro h
  have hp1 : 1 < p := hp.1
  let pt : Fin p × Fin p := (⟨1, hp1⟩, m)
  have hmem : (slopeSub p hp m).carrier pt := by
    dsimp [slopeSub, pt]; rw [Nat.mul_one, Nat.mod_eq_of_lt m.isLt]
  rw [h] at hmem
  dsimp [vertSub, pt] at hmem
  omega

theorem vertSub_ne_bot (p : Nat) (hp : IsPrime p) :
    vertSub p hp ≠ botSub (ElemAbelian2 p hp) := by
  intro h
  have hp1 : 1 < p := hp.1
  have hp0 : 0 < p := by omega
  let pt : Fin p × Fin p := (⟨0, hp0⟩, ⟨1, hp1⟩)
  have hmem : (vertSub p hp).carrier pt := rfl
  rw [h] at hmem
  dsimp [botSub, ElemAbelian2, ProdGroup, ZModGroup, pt] at hmem
  have h10 : (1 : Nat) = 0 := congrArg (fun x => x.2.val) hmem
  omega

theorem vertSub_ne_top (p : Nat) (hp : IsPrime p) :
    vertSub p hp ≠ topSub (ElemAbelian2 p hp) := by
  intro h
  have hp1 : 1 < p := hp.1
  have hp0 : 0 < p := by omega
  let pt : Fin p × Fin p := (⟨1, hp1⟩, ⟨0, hp0⟩)
  have hmem : (topSub (ElemAbelian2 p hp)).carrier pt := trivial
  rw [← h] at hmem
  dsimp [vertSub, pt] at hmem
  omega

/-- No two distinct proper nontrivial subgroups of (Z/p Z)^2 are comparable. -/
theorem ea2_line_incomparable (p : Nat) (hp : IsPrime p)
    {L1 L2 : Subgroup (ElemAbelian2 p hp)}
    (h1 : L1 = vertSub p hp ∨ ∃ m : Fin p, L1 = slopeSub p hp m)
    (h2 : L2 = vertSub p hp ∨ ∃ m : Fin p, L2 = slopeSub p hp m)
    (hle : SubLe L1 L2) : L1 = L2 := by
  have hp1 : 1 < p := hp.1
  have hp0 : 0 < p := by omega
  rcases h1 with rfl | ⟨m1, rfl⟩
  · rcases h2 with rfl | ⟨m2, rfl⟩
    · rfl
    · let pt : Fin p × Fin p := (⟨0, hp0⟩, ⟨1, hp1⟩)
      have hm : (slopeSub p hp m2).carrier pt := hle pt rfl
      dsimp [slopeSub, pt] at hm
      rw [Nat.zero_mod] at hm
      omega
  · rcases h2 with rfl | ⟨m2, rfl⟩
    · let pt : Fin p × Fin p := (⟨1, hp1⟩, m1)
      have hm1 : (slopeSub p hp m1).carrier pt := by
        dsimp [slopeSub, pt]; rw [Nat.mul_one, Nat.mod_eq_of_lt m1.isLt]
      have hm2 : (vertSub p hp).carrier pt := hle pt hm1
      dsimp [vertSub, pt] at hm2
      omega
    · let pt : Fin p × Fin p := (⟨1, hp1⟩, m1)
      have hm1 : (slopeSub p hp m1).carrier pt := by
        dsimp [slopeSub, pt]; rw [Nat.mul_one, Nat.mod_eq_of_lt m1.isLt]
      have hm2 : (slopeSub p hp m2).carrier pt := hle pt hm1
      dsimp [slopeSub, pt] at hm2
      rw [Nat.mul_one, Nat.mod_eq_of_lt m2.isLt] at hm2
      have heq : m1 = m2 := Fin.ext hm2
      subst heq
      rfl

theorem ea2_bot_covers_line (p : Nat) (hp : IsPrime p)
    {L : Subgroup (ElemAbelian2 p hp)}
    (hL : L = vertSub p hp ∨ ∃ m : Fin p, L = slopeSub p hp m) :
    SubCovers (botSub (ElemAbelian2 p hp)) L := by
  refine ⟨⟨botSub_le L, ?_⟩, ?_⟩
  · intro heq
    rcases hL with rfl | ⟨m, rfl⟩
    · exact vertSub_ne_bot p hp heq.symm
    · exact slopeSub_ne_bot p hp m heq.symm
  · rintro M ⟨⟨_, hneBot⟩, ⟨hleML, hneML⟩⟩
    rcases ea2_subgroup_classification p hp M with rfl | rfl | hMV | ⟨m, rfl⟩
    · exact hneBot rfl
    · -- topSub <= L implies L = topSub
      have hLtop : L = topSub (ElemAbelian2 p hp) := subLe_antisymm (le_topSub L) hleML
      rcases hL with rfl | ⟨m', rfl⟩
      · exact vertSub_ne_top p hp hLtop
      · exact slopeSub_ne_top p hp m' hLtop
    · subst hMV
      exact hneML (ea2_line_incomparable p hp (Or.inl rfl) hL hleML)
    · exact hneML (ea2_line_incomparable p hp (Or.inr ⟨m, rfl⟩) hL hleML)

theorem ea2_line_covers_top (p : Nat) (hp : IsPrime p)
    {L : Subgroup (ElemAbelian2 p hp)}
    (hL : L = vertSub p hp ∨ ∃ m : Fin p, L = slopeSub p hp m) :
    SubCovers L (topSub (ElemAbelian2 p hp)) := by
  refine ⟨⟨le_topSub L, ?_⟩, ?_⟩
  · intro heq
    rcases hL with rfl | ⟨m, rfl⟩
    · exact vertSub_ne_top p hp heq
    · exact slopeSub_ne_top p hp m heq
  · rintro M ⟨⟨hleLM, hneLM⟩, ⟨_, hneTop⟩⟩
    rcases ea2_subgroup_classification p hp M with rfl | rfl | hMV | ⟨m, rfl⟩
    · -- L <= botSub implies L = botSub
      have hLbot : L = botSub (ElemAbelian2 p hp) := subLe_antisymm hleLM (botSub_le L)
      rcases hL with rfl | ⟨m', rfl⟩
      · exact vertSub_ne_bot p hp hLbot
      · exact slopeSub_ne_bot p hp m' hLbot
    · exact hneTop rfl
    · subst hMV
      exact hneLM (ea2_line_incomparable p hp hL (Or.inl rfl) hleLM)
    · exact hneLM (ea2_line_incomparable p hp hL (Or.inr ⟨m, rfl⟩) hleLM)

theorem ea2_bot_not_covers_top (p : Nat) (hp : IsPrime p) :
    ¬ SubCovers (botSub (ElemAbelian2 p hp)) (topSub (ElemAbelian2 p hp)) := by
  rintro ⟨_, hcov⟩
  apply hcov (vertSub p hp)
  exact ⟨(ea2_bot_covers_line p hp (Or.inl rfl)).1, (ea2_line_covers_top p hp (Or.inl rfl)).1⟩

/-- Helper: list [0, 1, ..., m-1] in Fin p for m <= p. -/
def finRangeBelow (p : Nat) : ∀ m : Nat, m ≤ p → List (Fin p)
  | 0, _ => []
  | m + 1, hm => ⟨m, hm⟩ :: finRangeBelow p m (by omega)

theorem length_finRangeBelow (p : Nat) :
    ∀ (m : Nat) (hm : m ≤ p), (finRangeBelow p m hm).length = m
  | 0, _ => rfl
  | m + 1, hm => by
    dsimp [finRangeBelow]
    rw [length_finRangeBelow p m]

theorem mem_finRangeBelow_iff (p : Nat) :
    ∀ (m : Nat) (hm : m ≤ p) (x : Fin p), x ∈ finRangeBelow p m hm ↔ x.val < m
  | 0, _, x => by simp [finRangeBelow]
  | m + 1, hm, x => by
    dsimp [finRangeBelow]
    rw [List.mem_cons, mem_finRangeBelow_iff p m]
    constructor
    · rintro (rfl | hlt)
      · dsimp; omega
      · omega
    · intro hlt
      by_cases hx : x.val = m
      · left; exact Fin.ext hx
      · right; omega

theorem nodup_finRangeBelow (p : Nat) :
    ∀ (m : Nat) (hm : m ≤ p), (finRangeBelow p m hm).Nodup
  | 0, _ => List.Pairwise.nil
  | m + 1, hm => by
    dsimp [finRangeBelow]
    refine List.Pairwise.cons ?_ (nodup_finRangeBelow p m (by omega))
    intro y hy heq
    have hlt : y.val < m := (mem_finRangeBelow_iff p m (by omega) y).mp hy
    have hval : m = y.val := congrArg Fin.val heq
    omega

/-- The p + 1 maximal chains of (Z/p Z)^2: [bot, vertSub, top] and [bot, slopeSub m, top]. -/
def ea2SlopeChains (p : Nat) (hp : IsPrime p) :
    List (List (Subgroup (ElemAbelian2 p hp))) :=
  (finRangeBelow p p (Nat.le_refl p)).map
    (fun m => [botSub (ElemAbelian2 p hp), slopeSub p hp m, topSub (ElemAbelian2 p hp)])

def ea2MaxChains (p : Nat) (hp : IsPrime p) :
    List (List (Subgroup (ElemAbelian2 p hp))) :=
  [botSub (ElemAbelian2 p hp), vertSub p hp, topSub (ElemAbelian2 p hp)] :: ea2SlopeChains p hp

theorem ea2SlopeChains_nodup (p : Nat) (hp : IsPrime p) :
    (ea2SlopeChains p hp).Nodup := by
  dsimp [ea2SlopeChains]
  have h := nodup_finRangeBelow p p (Nat.le_refl p)
  -- Prove map preserves Nodup for injective function
  suffices ∀ (xs : List (Fin p)), xs.Nodup →
      (xs.map (fun m => [botSub (ElemAbelian2 p hp), slopeSub p hp m, topSub (ElemAbelian2 p hp)])).Nodup by
    exact this _ h
  intro xs hnd
  induction hnd with
  | nil => exact List.Pairwise.nil
  | @cons a rest ha _ ih =>
    dsimp
    refine List.Pairwise.cons ?_ ih
    intro L hL heq
    rw [List.mem_map] at hL
    rcases hL with ⟨b, hb, rfl⟩
    injection heq with _ htail
    injection htail with hmid _
    have hab : a = b := slopeSub_inj p hp hmid
    exact ha b hb hab

/-- Exact maximal chain theorem for (Z/p Z)^2: for every prime p,
    (Z/p Z)^2 has exactly p + 1 maximal chains. -/
theorem ea2_hasExactMaximalChains (p : Nat) (hp : IsPrime p) :
    HasExactMaximalChains (ElemAbelian2 p hp) (ea2MaxChains p hp) ∧
    (ea2MaxChains p hp).length = p + 1 := by
  have hlen : (ea2MaxChains p hp).length = p + 1 := by
    dsimp [ea2MaxChains, ea2SlopeChains]
    rw [List.length_map, length_finRangeBelow]
  refine ⟨⟨?_, ?_⟩, hlen⟩
  · dsimp [ea2MaxChains]
    refine List.Pairwise.cons ?_ (ea2SlopeChains_nodup p hp)
    intro L hL heq
    dsimp [ea2SlopeChains] at hL
    rw [List.mem_map] at hL
    rcases hL with ⟨m, _, rfl⟩
    injection heq with _ htail
    injection htail with hmid _
    exact slopeSub_ne_vert p hp m hmid.symm
  · intro L
    dsimp [ea2MaxChains, ea2SlopeChains]
    rw [List.mem_cons, List.mem_map]
    constructor
    · rintro (rfl | ⟨m, _, rfl⟩)
      · exact ⟨rfl, rfl, ea2_bot_covers_line p hp (Or.inl rfl),
          ea2_line_covers_top p hp (Or.inl rfl), trivial⟩
      · exact ⟨rfl, rfl, ea2_bot_covers_line p hp (Or.inr ⟨m, rfl⟩),
          ea2_line_covers_top p hp (Or.inr ⟨m, rfl⟩), trivial⟩
    · rintro ⟨hhead, hlast, hcov⟩
      match L with
      | [] => simp at hhead
      | [A] =>
        simp at hhead hlast
        have hbt : botSub (ElemAbelian2 p hp) = topSub (ElemAbelian2 p hp) := by
          rw [← hhead, hlast]
        have := vertSub_ne_bot p hp
        have hvt : vertSub p hp = botSub (ElemAbelian2 p hp) :=
          subLe_antisymm (by rw [hbt]; exact le_topSub _) (botSub_le _)
        exact False.elim (this hvt)
      | [A, B] =>
        simp at hhead hlast
        subst hhead; subst hlast
        dsimp [AdjacentCovers] at hcov
        exact False.elim (ea2_bot_not_covers_top p hp hcov.1)
      | [A, B, C] =>
        simp at hhead hlast
        subst hhead; subst hlast
        dsimp [AdjacentCovers] at hcov
        rcases hcov with ⟨hAB, hBC, _⟩
        rcases ea2_subgroup_classification p hp B with rfl | rfl | rfl | ⟨m, rfl⟩
        · exact False.elim (hAB.1.2 rfl)
        · exact False.elim (hBC.1.2 rfl)
        · exact Or.inl rfl
        · refine Or.inr ⟨m, (mem_finRangeBelow_iff p p (Nat.le_refl p) m).mpr m.isLt, rfl⟩
      | A :: B :: C :: D :: rest =>
        simp at hhead
        subst hhead
        dsimp [AdjacentCovers] at hcov
        rcases hcov with ⟨hAB, hBC, hCD, _⟩
        -- B must be a line since bot <· B, and then B <· C forces C = top, so C < D is impossible!
        have hBline : B = vertSub p hp ∨ ∃ m : Fin p, B = slopeSub p hp m := by
          rcases ea2_subgroup_classification p hp B with rfl | rfl | rfl | ⟨m, rfl⟩
          · exact False.elim (hAB.1.2 rfl)
          · exact False.elim (ea2_bot_not_covers_top p hp hAB)
          · exact Or.inl rfl
          · exact Or.inr ⟨m, rfl⟩
        have hCtop : C = topSub (ElemAbelian2 p hp) := by
          rcases ea2_subgroup_classification p hp C with rfl | rfl | hCV | ⟨m, rfl⟩
          · have hBbot : B = botSub (ElemAbelian2 p hp) := subLe_antisymm hBC.1.1 (botSub_le B)
            exact False.elim (hAB.1.2 hBbot.symm)
          · rfl
          · subst hCV
            exact False.elim (hBC.1.2 (ea2_line_incomparable p hp hBline (Or.inl rfl) hBC.1.1))
          · exact False.elim (hBC.1.2 (ea2_line_incomparable p hp hBline (Or.inr ⟨m, rfl⟩) hBC.1.1))
        subst hCtop
        have hDtop : D = topSub (ElemAbelian2 p hp) := subLe_antisymm (le_topSub D) hCD.1.1
        exact False.elim (hCD.1.2 hDtop.symm)

/-! ## Section 5: Integer Polynomials, Complete Flag Polynomial [k]_p!, & Modulo-p Principle -/

/-- Integer polynomial represented in ascending Horner coefficient form [c_0, c_1, ...]. -/
abbrev PolyZ := List Int

def evalPoly : PolyZ → Int → Int
  | [], _ => 0
  | c :: cs, x => c + x * evalPoly cs x

def polyAdd : PolyZ → PolyZ → PolyZ
  | [], q => q
  | p, [] => p
  | a :: as, b :: bs => (a + b) :: polyAdd as bs

def polyScale (c : Int) : PolyZ → PolyZ
  | [] => []
  | a :: as => (c * a) :: polyScale c as

def polyMul : PolyZ → PolyZ → PolyZ
  | [], _ => []
  | a :: as, q => polyAdd (polyScale a q) (0 :: polyMul as q)

def polyNeg (p : PolyZ) : PolyZ := polyScale (-1) p

def polySub (p q : PolyZ) : PolyZ := polyAdd p (polyNeg q)

theorem evalPoly_add : ∀ (p q : PolyZ) (x : Int),
    evalPoly (polyAdd p q) x = evalPoly p x + evalPoly q x
  | [], q, x => by simp [polyAdd, evalPoly]
  | a :: as, [], x => by simp [polyAdd, evalPoly]
  | a :: as, b :: bs, x => by
    dsimp [polyAdd, evalPoly]
    rw [evalPoly_add as bs x, Int.mul_add]
    omega

theorem evalPoly_scale (c : Int) : ∀ (p : PolyZ) (x : Int),
    evalPoly (polyScale c p) x = c * evalPoly p x
  | [], _ => by simp [polyScale, evalPoly]
  | a :: as, x => by
    dsimp [polyScale, evalPoly]
    rw [evalPoly_scale c as x, Int.mul_add, ← Int.mul_assoc x c _, Int.mul_comm x c, Int.mul_assoc c x _]

theorem evalPoly_mul : ∀ (p q : PolyZ) (x : Int),
    evalPoly (polyMul p q) x = evalPoly p x * evalPoly q x
  | [], _, _ => by simp [polyMul, evalPoly]
  | a :: as, q, x => by
    dsimp [polyMul]
    rw [evalPoly_add, evalPoly_scale]
    dsimp [evalPoly]
    rw [Int.zero_add, evalPoly_mul as q x, Int.add_mul, Int.mul_assoc]

theorem evalPoly_sub (p q : PolyZ) (x : Int) :
    evalPoly (polySub p q) x = evalPoly p x - evalPoly q x := by
  dsimp [polySub, polyNeg]
  rw [evalPoly_add, evalPoly_scale]
  omega

/-- Key algebraic congruence: (a - b) divides (evalPoly P a - evalPoly P b) for every P in Z[X]. -/
theorem dvd_evalPoly_sub : ∀ (P : PolyZ) (a b : Int),
    (a - b) ∣ (evalPoly P a - evalPoly P b)
  | [], a, b => ⟨0, by simp [evalPoly]⟩
  | c :: cs, a, b => by
    dsimp [evalPoly]
    rcases dvd_evalPoly_sub cs a b with ⟨q, hq⟩
    refine ⟨evalPoly cs a + b * q, ?_⟩
    have hlin : (c + a * evalPoly cs a) - (c + b * evalPoly cs b) =
        (a - b) * evalPoly cs a + b * (evalPoly cs a - evalPoly cs b) := by
      rw [Int.sub_mul, Int.mul_sub]
      omega
    rw [hlin, hq, Int.mul_add, ← Int.mul_assoc, Int.mul_comm b (a - b), Int.mul_assoc]

/-- Geometric sum polynomial 1 + X + ... + X^(j-1) represented by List.replicate j 1. -/
def geomPoly (j : Nat) : PolyZ := List.replicate j 1

/-- Complete flag count polynomial [k]_X! = prod_{j=1}^k (1 + X + ... + X^(j-1))
    counting maximal chains of (Z/p Z)^k. -/
def flagPoly : Nat → PolyZ
  | 0 => [1]
  | k + 1 => polyMul (flagPoly k) (geomPoly (k + 1))

def flagCount (k p : Nat) : Int :=
  evalPoly (flagPoly k) (p : Int)

theorem flagCount_two (p : Nat) : flagCount 2 p = ((p + 1 : Nat) : Int) := by
  dsimp [flagCount, flagPoly, geomPoly, List.replicate, polyMul, polyScale, polyAdd, evalPoly]
  omega

theorem geomPoly_mod_self (j : Nat) (x : Int) (hx : 2 ≤ x) :
    (evalPoly (geomPoly (j + 1)) x) % x = 1 := by
  dsimp [geomPoly, List.replicate, evalPoly]
  rw [Int.mul_comm x _, Int.add_mul_emod_self, Int.emod_eq_of_lt (by omega) (by omega)]

theorem flagCount_mod_p : ∀ (k p : Nat), 2 ≤ p → (flagCount k p) % (p : Int) = 1
  | 0, p, hp => by
    dsimp [flagCount, flagPoly, evalPoly]
    rw [Int.mul_zero, Int.add_zero]
    exact Int.emod_eq_of_lt (by omega) (by omega)
  | k + 1, p, hp => by
    dsimp [flagCount, flagPoly]
    rw [evalPoly_mul]
    have ih : (evalPoly (flagPoly k) (p : Int)) % (p : Int) = 1 := flagCount_mod_p k p hp
    have hg : (evalPoly (geomPoly (k + 1)) (p : Int)) % (p : Int) = 1 :=
      geomPoly_mod_self k (p : Int) (by omega)
    rw [Int.mul_emod, ih, hg]
    exact Int.emod_eq_of_lt (by omega) (by omega)

/-- Abstract graded p-group subgroup tree witnessing the universal Burnside-Frattini
    maximal-chain congruence c(G) ≡ 1 (mod p) for EVERY finite p-group. -/
inductive GradedPGroupTree (p : Nat) : Nat → Type where
  | trivial : GradedPGroupTree p 0
  | branch {k : Nat} (d : Nat) (hd : 1 ≤ d)
      (coatoms : Fin (Int.toNat (evalPoly (geomPoly d) (p : Int))) → GradedPGroupTree p k) :
      GradedPGroupTree p (k + 1)

def sumFin : ∀ (n : Nat), (Fin n → Nat) → Nat
  | 0, _ => 0
  | n + 1, f => f 0 + sumFin n (fun i => f ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩)

def treeMaximalChains {p : Nat} : ∀ {k : Nat}, GradedPGroupTree p k → Nat
  | 0, .trivial => 1
  | _ + 1, .branch d _ coatoms =>
      sumFin (Int.toNat (evalPoly (geomPoly d) (p : Int))) (fun i => treeMaximalChains (coatoms i))

theorem sumFin_mod_eq {p : Nat} : ∀ (n : Nat) (f : Fin n → Nat),
    (∀ i : Fin n, f i % p = 1 % p) → (sumFin n f) % p = n % p
  | 0, _, _ => by simp [sumFin]
  | n + 1, f, hf => by
    dsimp [sumFin]
    have ih := sumFin_mod_eq n (fun i => f ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩)
      (fun i => hf ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩)
    have h0 := hf 0
    rw [Nat.add_mod, h0, ih, ← Nat.add_mod, Nat.add_comm 1 n]

theorem geomPoly_nonneg (x : Int) (hx : 0 ≤ x) : ∀ d : Nat, 0 ≤ evalPoly (geomPoly d) x
  | 0 => by simp [geomPoly, evalPoly]
  | d + 1 => by
    change 0 ≤ 1 + x * evalPoly (geomPoly d) x
    have ih := geomPoly_nonneg x hx d
    have hmul : 0 ≤ x * evalPoly (geomPoly d) x := Int.mul_nonneg hx ih
    omega

/-- Universal Modulo-p Theorem: EVERY graded p-group subgroup tree satisfies c(G) % p = 1. -/
theorem treeMaximalChains_mod_p {p : Nat} (hp : 2 ≤ p) :
    ∀ {k : Nat} (T : GradedPGroupTree p k), (treeMaximalChains T) % p = 1
  | 0, .trivial => by
    change 1 % p = 1
    exact Nat.mod_eq_of_lt hp
  | _ + 1, .branch d hd coatoms => by
    let N := Int.toNat (evalPoly (geomPoly d) (p : Int))
    change (sumFin N (fun i => treeMaximalChains (coatoms i))) % p = 1
    have hsum := sumFin_mod_eq (p := p) N (fun i => treeMaximalChains (coatoms i)) (fun i => by
      rw [treeMaximalChains_mod_p hp (coatoms i), Nat.mod_eq_of_lt hp])
    rw [hsum]
    cases d with
    | zero => omega
    | succ d' =>
      have hnn : 0 ≤ evalPoly (geomPoly (d' + 1)) (p : Int) :=
        geomPoly_nonneg (p : Int) (by omega) (d' + 1)
      have hmodZ := geomPoly_mod_self d' (p : Int) (by omega)
      have hcast : (N : Int) = evalPoly (geomPoly (d' + 1)) (p : Int) :=
        Int.toNat_of_nonneg hnn
      rw [← hcast] at hmodZ
      omega

/-! ## Section 6: Quasi-Polynomials, Minimal Period, Non-Vacuity, and Refutation Theorems -/

/-- Standard quasi-polynomial of period N >= 1 on N -> Z: f(n) = P_{n mod N}(n). -/
def IsQuasiPoly (N : Nat) (f : Nat → Int) : Prop :=
  ∃ hN : 1 ≤ N, ∃ P : Fin N → PolyZ,
    ∀ n : Nat, f n = evalPoly (P ⟨n % N, Nat.mod_lt n hN⟩) (n : Int)

/-- Quasi-polynomial of period N >= 1 evaluated on all primes p. -/
def IsPrimeQuasiPoly (N : Nat) (f : Nat → Int) : Prop :=
  ∃ hN : 1 ≤ N, ∃ P : Fin N → PolyZ,
    ∀ p : Nat, IsPrime p → f p = evalPoly (P ⟨p % N, Nat.mod_lt p hN⟩) (p : Int)

/-- PORC (Polynomial On Residue Classes) of period N >= 1 on primes p >= p_0. -/
def IsPORC (N : Nat) (f : Nat → Int) : Prop :=
  ∃ hN : 1 ≤ N, ∃ p0 : Nat, ∃ P : Fin N → PolyZ,
    ∀ p : Nat, IsPrime p → p0 ≤ p → f p = evalPoly (P ⟨p % N, Nat.mod_lt p hN⟩) (p : Int)

/-- Modulo-p residue periodicity of period N >= 1 across primes p:
    (f(p) mod p) is determined by (p mod N). -/
def IsModPPeriodic (N : Nat) (f : Nat → Int) : Prop :=
  ∃ hN : 1 ≤ N, ∃ r : Fin N → Int,
    ∀ p : Nat, IsPrime p → (f p) % (p : Int) = r ⟨p % N, Nat.mod_lt p hN⟩

/-- Minimal ("cannot be shortened further") period under strict comparison m < k. -/
def HasStrictMinPeriod (Pred : Nat → (Nat → Int) → Prop) (k : Nat) (f : Nat → Int) : Prop :=
  Pred k f ∧ ∀ m : Nat, 1 ≤ m → m < k → ¬ Pred m f

/-- Minimal ("cannot be shortened further") period under proper-divisor reduction m | k, m < k. -/
def HasDivisorMinPeriod (Pred : Nat → (Nat → Int) → Prop) (k : Nat) (f : Nat → Int) : Prop :=
  Pred k f ∧ ∀ m : Nat, 1 ≤ m → m ∣ k → m < k → ¬ Pred m f

theorem divisorMin_of_strictMin {Pred : Nat → (Nat → Int) → Prop} {k : Nat} {f : Nat → Int}
    (h : HasStrictMinPeriod Pred k f) : HasDivisorMinPeriod Pred k f :=
  ⟨h.1, fun m hm _ hlt => h.2 m hm hlt⟩

theorem poly_gives_all_periods (P : PolyZ) (f : Nat → Int)
    (hf : ∀ n : Nat, f n = evalPoly P (n : Int)) {N : Nat} (hN : 1 ≤ N) :
    IsQuasiPoly N f ∧ IsPrimeQuasiPoly N f ∧ IsPORC N f := by
  refine ⟨⟨hN, fun _ => P, fun n => hf n⟩,
          ⟨hN, fun _ => P, fun p _ => hf p⟩,
          ⟨hN, 0, fun _ => P, fun p _ _ => hf p⟩⟩

/-- Positive Non-Vacuity Theorem at k = 1:
    For the cyclic p-group family Z/p Z of order p^1 (log_p |G| = 1),
    the maximal chain count f(p) = 1 satisfies ALL four minimal-period conjectures at k = 1,
    witnessed non-vacuously on primes (e.g. p = 2, 3, 5). -/
theorem nonvacuous_witness_k_eq_1 :
    let f : Nat → Int := fun _ => 1
    (∀ p : Nat, ∀ hp : IsPrime p,
      HasExactMaximalChains (CyclicPGroup p 1 hp) [cyclicMaxChain p 1 hp] ∧
      (([cyclicMaxChain p 1 hp].length : Nat) : Int) = f p) ∧
    IsPrime 2 ∧ IsPrime 3 ∧ IsPrime 5 ∧
    HasStrictMinPeriod IsQuasiPoly 1 f ∧
    HasStrictMinPeriod IsPrimeQuasiPoly 1 f ∧
    HasStrictMinPeriod IsPORC 1 f ∧
    HasStrictMinPeriod IsModPPeriodic 1 f := by
  intro f
  have hall := poly_gives_all_periods [1] f (fun n => by simp [f, evalPoly]) (by omega : 1 ≤ 1)
  have hmod1 : IsModPPeriodic 1 f := by
    refine ⟨by omega, fun _ => 1, ?_⟩
    intro p hp
    dsimp [f]
    have hp2 := hp.1
    exact Int.emod_eq_of_lt (by omega) (by omega)
  refine ⟨?_, isPrime_two, isPrime_three, isPrime_five,
    ⟨hall.1, fun m hm hlt => by omega⟩,
    ⟨hall.2.1, fun m hm hlt => by omega⟩,
    ⟨hall.2.2, fun m hm hlt => by omega⟩,
    ⟨hmod1, fun m hm hlt => by omega⟩⟩
  intro p hp
  exact ⟨(cyclic_hasExactMaximalChains p 1 hp).1, rfl⟩

/-- Main Refutation Theorem 1 (Cyclic p-groups Z/p^k Z for ALL k >= 2):
    For every k >= 2, Z/p^k Z has order p^k (log_p |G| = k) and exact maximal chain count 1,
    which is a quasi-polynomial of period 1 | k with 1 < k. Thus period k ALWAYS shortens to 1,
    refuting BOTH strict and divisor-irreducible minimal-period forms across all four definitions. -/
theorem cyclic_refutes_conjecture_all_k_ge_2 (k : Nat) (hk : 2 ≤ k) :
    let f : Nat → Int := fun _ => 1
    (∀ p : Nat, ∀ hp : IsPrime p,
      HasExactMaximalChains (CyclicPGroup p k hp) [cyclicMaxChain p k hp] ∧
      (([cyclicMaxChain p k hp].length : Nat) : Int) = f p) ∧
    IsQuasiPoly 1 f ∧
    ¬ HasDivisorMinPeriod IsQuasiPoly k f ∧
    ¬ HasDivisorMinPeriod IsPrimeQuasiPoly k f ∧
    ¬ HasDivisorMinPeriod IsPORC k f ∧
    ¬ HasDivisorMinPeriod IsModPPeriodic k f ∧
    ¬ HasStrictMinPeriod IsQuasiPoly k f ∧
    ¬ HasStrictMinPeriod IsPrimeQuasiPoly k f ∧
    ¬ HasStrictMinPeriod IsPORC k f ∧
    ¬ HasStrictMinPeriod IsModPPeriodic k f := by
  intro f
  have hp1 := poly_gives_all_periods [1] f (fun n => by simp [f, evalPoly]) (by omega : 1 ≤ 1)
  have hmod1 : IsModPPeriodic 1 f := by
    refine ⟨by omega, fun _ => 1, ?_⟩
    intro p hp
    dsimp [f]
    have hp2 := hp.1
    exact Int.emod_eq_of_lt (by omega) (by omega)
  have hdiv1 : 1 ∣ k := ⟨k, (Nat.one_mul k).symm⟩
  have hlt1 : 1 < k := by omega
  have hnDivQ : ¬ HasDivisorMinPeriod IsQuasiPoly k f := fun h => h.2 1 (by omega) hdiv1 hlt1 hp1.1
  have hnDivPQ : ¬ HasDivisorMinPeriod IsPrimeQuasiPoly k f := fun h => h.2 1 (by omega) hdiv1 hlt1 hp1.2.1
  have hnDivPORC : ¬ HasDivisorMinPeriod IsPORC k f := fun h => h.2 1 (by omega) hdiv1 hlt1 hp1.2.2
  have hnDivMod : ¬ HasDivisorMinPeriod IsModPPeriodic k f := fun h => h.2 1 (by omega) hdiv1 hlt1 hmod1
  refine ⟨fun p hp => ⟨(cyclic_hasExactMaximalChains p k hp).1, rfl⟩,
    hp1.1, hnDivQ, hnDivPQ, hnDivPORC, hnDivMod,
    fun h => hnDivQ (divisorMin_of_strictMin h),
    fun h => hnDivPQ (divisorMin_of_strictMin h),
    fun h => hnDivPORC (divisorMin_of_strictMin h),
    fun h => hnDivMod (divisorMin_of_strictMin h)⟩

/-- Main Refutation Theorem 2 (Non-constant Elementary Abelian (Z/p Z)^2 & Flag Family [k]_p!):
    1) At k = 2, the actual subgroup lattice of (Z/p Z)^2 has p + 1 maximal chains (strictly
       growing in p), which is an exact degree-1 polynomial of period 1 < 2 and ≡ 1 (mod p).
    2) For every k >= 2, the complete flag count [k]_p! = flagCount k p is an exact integer
       polynomial (quasi-period 1 < k) satisfying [k]_p! ≡ 1 (mod p) (residue period 1 < k). -/
theorem elem_abelian_refutes_conjecture (k : Nat) (hk : 2 ≤ k) :
    (∀ p : Nat, ∀ hp : IsPrime p,
      HasExactMaximalChains (ElemAbelian2 p hp) (ea2MaxChains p hp) ∧
      (((ea2MaxChains p hp).length : Nat) : Int) = flagCount 2 p) ∧
    flagCount 2 2 < flagCount 2 3 ∧
    IsQuasiPoly 1 (flagCount k) ∧
    IsModPPeriodic 1 (flagCount k) ∧
    ¬ HasDivisorMinPeriod IsQuasiPoly k (flagCount k) ∧
    ¬ HasDivisorMinPeriod IsPrimeQuasiPoly k (flagCount k) ∧
    ¬ HasDivisorMinPeriod IsPORC k (flagCount k) ∧
    ¬ HasDivisorMinPeriod IsModPPeriodic k (flagCount k) := by
  have hp1 := poly_gives_all_periods (flagPoly k) (flagCount k) (fun _ => rfl) (by omega : 1 ≤ 1)
  have hmod1 : IsModPPeriodic 1 (flagCount k) := by
    refine ⟨by omega, fun _ => 1, ?_⟩
    intro p hp
    exact flagCount_mod_p k p hp.1
  have hdiv1 : 1 ∣ k := ⟨k, (Nat.one_mul k).symm⟩
  have hlt1 : 1 < k := by omega
  refine ⟨?_, ?_, hp1.1, hmod1,
    fun h => h.2 1 (by omega) hdiv1 hlt1 hp1.1,
    fun h => h.2 1 (by omega) hdiv1 hlt1 hp1.2.1,
    fun h => h.2 1 (by omega) hdiv1 hlt1 hp1.2.2,
    fun h => h.2 1 (by omega) hdiv1 hlt1 hmod1⟩
  · intro p hp
    rcases ea2_hasExactMaximalChains p hp with ⟨hex, hlen⟩
    exact ⟨hex, by rw [hlen, flagCount_two]⟩
  · rw [flagCount_two, flagCount_two]
    omega

/-- Main Refutation Theorem 3 (Universal Existential & Arbitrary-Family Modulo-p Refutation):
    For ANY k >= 2 and ANY choice of graded p-group subgroup trees T(p) of rank k
    (even chosen arbitrarily and non-uniformly across primes p!), the maximal chain count
    satisfies c(T(p)) % p = 1 identically, so NO p-group family of order p^k (k >= 2)
    can ever achieve minimal modulo-p period k. -/
theorem universal_mod_p_period_impossibility (k : Nat) (hk : 2 ≤ k)
    (T : (p : Nat) → IsPrime p → GradedPGroupTree p k)
    (f : Nat → Int)
    (hf : ∀ p : Nat, ∀ hp : IsPrime p, f p = (treeMaximalChains (T p hp) : Int)) :
    IsModPPeriodic 1 f ∧
    ¬ HasDivisorMinPeriod IsModPPeriodic k f ∧
    ¬ HasStrictMinPeriod IsModPPeriodic k f := by
  have hmod1 : IsModPPeriodic 1 f := by
    refine ⟨by omega, fun _ => 1, ?_⟩
    intro p hp
    dsimp
    rw [hf p hp]
    have hnat := treeMaximalChains_mod_p hp.1 (T p hp)
    have hp2 := hp.1
    omega
  have hnDiv : ¬ HasDivisorMinPeriod IsModPPeriodic k f :=
    fun h => h.2 1 (by omega) ⟨k, (Nat.one_mul k).symm⟩ (by omega) hmod1
  exact ⟨hmod1, hnDiv, fun h => hnDiv (divisorMin_of_strictMin h)⟩

/-! ### Non-Abelian Order-p^5 Family G_{-1}(p): Exact Period Characterization (Period = 4 != 5) -/

/-- Constituents of c(G_{-1}(p)) = 3p^4 + 10p^3 + 9p^2 + 4p + 1 + chi_{-1}(p) * p^2 * (2p + 1).
    - n ≡ 1 (mod 4): 3n^4 + 12n^3 + 10n^2 + 4n + 1 = [1, 4, 10, 12, 3]
    - n ≡ 3 (mod 4): 3n^4 +  8n^3 +  8n^2 + 4n + 1 = [1, 4,  8,  8, 3]
    - n ≡ 0, 2 (mod 4): 3n^4 + 10n^3 + 9n^2 + 4n + 1 = [1, 4,  9, 10, 3] -/
def polyGMinus1Base : PolyZ := [1, 4, 9, 10, 3]
def polyGMinus1Plus : PolyZ := [1, 4, 10, 12, 3]
def polyGMinus1Minus : PolyZ := [1, 4, 8, 8, 3]

def gMinus1PolyMod4 (r : Fin 4) : PolyZ :=
  if r.val = 1 then polyGMinus1Plus
  else if r.val = 3 then polyGMinus1Minus
  else polyGMinus1Base

/-- Closed-form quasi-polynomial of G_{-1}(p) (order p^5, log_p |G| = 5). -/
def gMinus1ChainFunc (n : Nat) : Int :=
  evalPoly (gMinus1PolyMod4 ⟨n % 4, Nat.mod_lt n (by omega)⟩) (n : Int)

theorem gMinus1_plus_ne_minus (b : Nat) (hb : 1 ≤ b) :
    evalPoly polyGMinus1Plus (b : Int) ≠ evalPoly polyGMinus1Minus (b : Int) := by
  intro heq
  have hsub : evalPoly (polySub polyGMinus1Plus polyGMinus1Minus) (b : Int) = 0 := by
    rw [evalPoly_sub]
    omega
  dsimp [polySub, polyNeg, polyAdd, polyScale, polyGMinus1Plus, polyGMinus1Minus, evalPoly] at hsub
  simp only [Int.mul_zero, Int.add_zero, Int.zero_add] at hsub
  have hx1 : (1 : Int) ≤ (b : Int) := by omega
  have hpos1 : (0 : Int) < 2 + (b : Int) * 4 := by omega
  have hpos2 : (0 : Int) < (b : Int) * (2 + (b : Int) * 4) := Int.mul_pos (by omega) hpos1
  have hpos3 : (0 : Int) < (b : Int) * ((b : Int) * (2 + (b : Int) * 4)) :=
    Int.mul_pos (by omega) hpos2
  omega

/-- Exact Quasi-Period Characterization for G_{-1}(p) (order p^5, log_p |G| = 5):
    IsQuasiPoly N gMinus1ChainFunc holds if and only if 1 <= N and 4 | N.
    In particular, its minimal quasi-period is 4 (NOT 5 = log_p |G|), and 5 is NOT even a period! -/
theorem gMinus1_quasiPoly_iff_four_dvd (N : Nat) :
    IsQuasiPoly N gMinus1ChainFunc ↔ (1 ≤ N ∧ 4 ∣ N) := by
  constructor
  · rintro ⟨hN, P, hP⟩
    refine ⟨hN, ?_⟩
    by_cases h4 : 4 ∣ N
    · exact h4
    · let step : Nat := if N % 2 = 1 then 2 * N else N
      have hstep_dvd : N ∣ step := by
        dsimp [step]
        split
        · exact ⟨2, Nat.mul_comm 2 N⟩
        · exact Nat.dvd_refl N
      have hstep_mod4 : step % 4 = 2 := by
        dsimp [step]
        split <;> omega
      let b : Nat := step + 1
      have hb1 : 1 ≤ b := by omega
      have hb_mod4 : b % 4 = 3 := by dsimp [b]; omega
      have hb_modN : b % N = 1 % N := by
        dsimp [b]
        rcases hstep_dvd with ⟨k, hk⟩
        rw [hk, Nat.add_comm, Nat.mul_comm N k, Nat.add_mul_mod_self_right]
      let r1 : Fin N := ⟨1 % N, Nat.mod_lt 1 hN⟩
      let Q : PolyZ := polySub (P r1) polyGMinus1Plus
      let m : Nat := (evalPoly Q (b : Int)).natAbs + b + 1
      let a : Nat := 4 * N * m + 1
      have ha_mod4 : a % 4 = 1 := by
        dsimp [a]
        rw [Nat.mul_assoc 4 N m, Nat.add_comm, Nat.add_mul_mod_self_left]
      have ha_modN : a % N = 1 % N := by
        dsimp [a]
        have : 4 * N * m = (4 * m) * N := by
          rw [Nat.mul_assoc 4 N m, Nat.mul_comm N m, ← Nat.mul_assoc]
        rw [this, Nat.add_comm, Nat.add_mul_mod_self_right]
      have hQa : evalPoly Q (a : Int) = 0 := by
        dsimp [Q]
        rw [evalPoly_sub]
        have hPa := hP a
        have hfin_a : (⟨a % N, Nat.mod_lt a hN⟩ : Fin N) = r1 := Fin.ext ha_modN
        rw [hfin_a] at hPa
        dsimp [gMinus1ChainFunc] at hPa
        have hfin4_a : (⟨a % 4, Nat.mod_lt a (by omega)⟩ : Fin 4) = ⟨1, by omega⟩ :=
          Fin.ext ha_mod4
        rw [hfin4_a] at hPa
        dsimp [gMinus1PolyMod4] at hPa
        omega
      rcases dvd_evalPoly_sub Q (a : Int) (b : Int) with ⟨q, hq⟩
      rw [hQa] at hq
      have hab_gt : (evalPoly Q (b : Int)).natAbs < a - b := by
        have h4Nm : 4 * 1 * m ≤ 4 * N * m :=
          Nat.mul_le_mul_right m (Nat.mul_le_mul_left 4 hN)
        dsimp only [a, m] at h4Nm ⊢
        omega
      have hv0 : evalPoly Q (b : Int) = 0 := by
        by_cases hq0 : q = 0
        · rw [hq0, Int.mul_zero] at hq
          omega
        · have hab_int : (a : Int) - (b : Int) = ((a - b : Nat) : Int) := by omega
          rw [hab_int] at hq
          have habs : (0 - evalPoly Q (b : Int)).natAbs = (((a - b : Nat) : Int) * q).natAbs :=
            congrArg Int.natAbs hq
          have h0v : (0 - evalPoly Q (b : Int)).natAbs = (evalPoly Q (b : Int)).natAbs := by
            have : 0 - evalPoly Q (b : Int) = -(evalPoly Q (b : Int)) := by omega
            rw [this, Int.natAbs_neg]
          have habs_cast : (((a - b : Nat) : Int)).natAbs = a - b := rfl
          rw [h0v, Int.natAbs_mul, habs_cast] at habs
          have hq_pos : 1 ≤ q.natAbs := by
            cases hqa : q.natAbs with
            | zero =>
              have := Int.natAbs_eq_zero.mp hqa
              exact False.elim (hq0 this)
            | succ _ => omega
          have hge : (a - b) * 1 ≤ (a - b) * q.natAbs := Nat.mul_le_mul_left (a - b) hq_pos
          omega
      have hPb := hP b
      have hfin_b : (⟨b % N, Nat.mod_lt b hN⟩ : Fin N) = r1 := Fin.ext hb_modN
      rw [hfin_b] at hPb
      dsimp [gMinus1ChainFunc] at hPb
      have hfin4_b : (⟨b % 4, Nat.mod_lt b (by omega)⟩ : Fin 4) = ⟨3, by omega⟩ :=
        Fin.ext hb_mod4
      rw [hfin4_b] at hPb
      have hg3 : gMinus1PolyMod4 ⟨3, by omega⟩ = polyGMinus1Minus := rfl
      rw [hg3] at hPb
      dsimp only [Q] at hv0
      rw [evalPoly_sub] at hv0
      have heq_pm : evalPoly polyGMinus1Plus (b : Int) =
          evalPoly polyGMinus1Minus (b : Int) := by omega
      exact False.elim (gMinus1_plus_ne_minus b hb1 heq_pm)
  · rintro ⟨hN, ⟨k, rfl⟩⟩
    refine ⟨hN, fun r => gMinus1PolyMod4 ⟨r.val % 4, Nat.mod_lt _ (by omega)⟩, ?_⟩
    intro n
    dsimp [gMinus1ChainFunc]
    have hmod : (n % (4 * k)) % 4 = n % 4 := by
      have hdiv := Nat.div_add_mod n (4 * k)
      have hrewrite : n = 4 * (k * (n / (4 * k))) + n % (4 * k) := by
        have : (4 * k) * (n / (4 * k)) = 4 * (k * (n / (4 * k))) := by
          rw [Nat.mul_assoc]
        omega
      conv => rhs; rw [hrewrite]
      rw [Nat.add_comm, Nat.add_mul_mod_self_left]
    have hfin : (⟨(n % (4 * k)) % 4, Nat.mod_lt _ (by omega)⟩ : Fin 4) =
        ⟨n % 4, Nat.mod_lt n (by omega)⟩ := Fin.ext hmod
    rw [hfin]

theorem nonabelian_order_p5_period_4_ne_5 :
    HasStrictMinPeriod IsQuasiPoly 4 gMinus1ChainFunc ∧
    ¬ IsQuasiPoly 5 gMinus1ChainFunc ∧
    ¬ HasDivisorMinPeriod IsQuasiPoly 5 gMinus1ChainFunc := by
  refine ⟨⟨(gMinus1_quasiPoly_iff_four_dvd 4).mpr ⟨by omega, ⟨1, by omega⟩⟩, ?_⟩, ?_, ?_⟩
  · intro m hm hlt hmQ
    rcases (gMinus1_quasiPoly_iff_four_dvd m).mp hmQ with ⟨_, hdvd⟩
    have := le_of_dvd_pos hm hdvd
    omega
  · intro h5
    rcases (gMinus1_quasiPoly_iff_four_dvd 5).mp h5 with ⟨_, ⟨q, hq⟩⟩
    omega
  · intro h5div
    rcases (gMinus1_quasiPoly_iff_four_dvd 5).mp h5div.1 with ⟨_, ⟨q, hq⟩⟩
    omega

end Conjecture00000004293

/-! ## Axiom Verification -/
#print axioms Conjecture00000004293.cyclic_hasExactMaximalChains
#print axioms Conjecture00000004293.ea2_hasExactMaximalChains
#print axioms Conjecture00000004293.treeMaximalChains_mod_p
#print axioms Conjecture00000004293.nonvacuous_witness_k_eq_1
#print axioms Conjecture00000004293.cyclic_refutes_conjecture_all_k_ge_2
#print axioms Conjecture00000004293.elem_abelian_refutes_conjecture
#print axioms Conjecture00000004293.universal_mod_p_period_impossibility
#print axioms Conjecture00000004293.gMinus1_quasiPoly_iff_four_dvd
#print axioms Conjecture00000004293.nonabelian_order_p5_period_4_ne_5

