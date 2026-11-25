/-!
# Formal Disproof of Conjecture 00000000472

Self-contained Core Lean 4.19.0 formalization constructing `Q` (rationals), `R` (Cauchy
real numbers with the polynomial Intermediate Value Theorem), `Complex` (`R[i]`),
polynomials and formal derivatives, Simion's interlacing operator, multiset Eulerian
polynomials (defined combinatorially via distinct multiset permutations and descents),
and multiple polylogarithm Eulerian polynomials.
-/

namespace Conjecture00000000472

/-! ## 1. Constructive Rational Numbers `Q` -/

structure RawQ where
  num : Int
  den : Int
  den_pos : 0 < den

namespace RawQ

def equiv (a b : RawQ) : Prop :=
  a.num * b.den = b.num * a.den

theorem equiv_refl (a : RawQ) : equiv a a := rfl
theorem equiv_symm {a b : RawQ} (h : equiv a b) : equiv b a := h.symm

theorem int_mul_cancel_right {x y z : Int} (hz : 0 < z) (h : x * z = y * z) : x = y := by
  have hsub : (x - y) * z = 0 := by rw [Int.sub_mul, h, Int.sub_self]
  rcases Int.mul_eq_zero.mp hsub with hxy | hz0 <;> omega

theorem int_mul_pos {x y : Int} (hx : 0 < x) (hy : 0 < y) : 0 < x * y :=
  Int.mul_pos hx hy

theorem equiv_trans {a b c : RawQ} (hab : equiv a b) (hbc : equiv b c) : equiv a c := by
  unfold equiv at *
  apply int_mul_cancel_right b.den_pos
  calc
    (a.num * c.den) * b.den = (a.num * b.den) * c.den := by
      simp only [Int.mul_assoc, Int.mul_left_comm, Int.mul_comm]
    _ = (b.num * a.den) * c.den := by rw [hab]
    _ = (b.num * c.den) * a.den := by
      simp only [Int.mul_assoc, Int.mul_left_comm, Int.mul_comm]
    _ = (c.num * b.den) * a.den := by rw [hbc]
    _ = (c.num * a.den) * b.den := by
      simp only [Int.mul_assoc, Int.mul_left_comm, Int.mul_comm]

def setoid : Setoid RawQ where
  r := equiv
  iseqv := ⟨equiv_refl, equiv_symm, equiv_trans⟩

def ofInt (n : Int) : RawQ := ⟨n, 1, by omega⟩

def add (a b : RawQ) : RawQ :=
  ⟨a.num * b.den + b.num * a.den, a.den * b.den, int_mul_pos a.den_pos b.den_pos⟩

def neg (a : RawQ) : RawQ :=
  ⟨-a.num, a.den, a.den_pos⟩

def mul (a b : RawQ) : RawQ :=
  ⟨a.num * b.num, a.den * b.den, int_mul_pos a.den_pos b.den_pos⟩

def inv (a : RawQ) : RawQ :=
  if h : 0 < a.num then
    ⟨a.den, a.num, h⟩
  else if _ : a.num < 0 then
    ⟨-a.den, -a.num, by omega⟩
  else
    ofInt 0

def abs (a : RawQ) : RawQ :=
  ⟨if 0 ≤ a.num then a.num else -a.num, a.den, a.den_pos⟩

def lt (a b : RawQ) : Prop :=
  a.num * b.den < b.num * a.den

theorem add_congr {a₁ a₂ b₁ b₂ : RawQ} (ha : equiv a₁ a₂) (hb : equiv b₁ b₂) :
    equiv (add a₁ b₁) (add a₂ b₂) := by
  unfold equiv add at *; dsimp only
  calc
    (a₁.num * b₁.den + b₁.num * a₁.den) * (a₂.den * b₂.den)
        = (a₁.num * a₂.den) * (b₁.den * b₂.den) + (b₁.num * b₂.den) * (a₁.den * a₂.den) := by
          rw [Int.add_mul]
          congr 1 <;> simp only [Int.mul_assoc, Int.mul_left_comm, Int.mul_comm]
    _ = (a₂.num * a₁.den) * (b₁.den * b₂.den) + (b₂.num * b₁.den) * (a₁.den * a₂.den) := by
          rw [ha, hb]
    _ = (a₂.num * b₂.den + b₂.num * a₂.den) * (a₁.den * b₁.den) := by
          rw [Int.add_mul]
          congr 1 <;> simp only [Int.mul_assoc, Int.mul_left_comm, Int.mul_comm]

theorem neg_congr {a₁ a₂ : RawQ} (ha : equiv a₁ a₂) : equiv (neg a₁) (neg a₂) := by
  unfold equiv neg at *; dsimp only
  rw [Int.neg_mul, Int.neg_mul, ha]

theorem mul_congr {a₁ a₂ b₁ b₂ : RawQ} (ha : equiv a₁ a₂) (hb : equiv b₁ b₂) :
    equiv (mul a₁ b₁) (mul a₂ b₂) := by
  unfold equiv mul at *; dsimp only
  calc
    (a₁.num * b₁.num) * (a₂.den * b₂.den)
        = (a₁.num * a₂.den) * (b₁.num * b₂.den) := by
          simp only [Int.mul_assoc, Int.mul_left_comm, Int.mul_comm]
    _ = (a₂.num * a₁.den) * (b₂.num * b₁.den) := by rw [ha, hb]
    _ = (a₂.num * b₂.num) * (a₁.den * b₁.den) := by
          simp only [Int.mul_assoc, Int.mul_left_comm, Int.mul_comm]

theorem sign_of_equiv {a b : RawQ} (h : equiv a b) :
    (0 < a.num ↔ 0 < b.num) ∧ (a.num < 0 ↔ b.num < 0) ∧ (a.num = 0 ↔ b.num = 0) := by
  unfold equiv at h
  have ha : 0 < a.den := a.den_pos
  have hb : 0 < b.den := b.den_pos
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · intro hp
    have h1 : 0 < a.num * b.den := int_mul_pos hp hb
    rw [h] at h1
    rcases Int.lt_trichotomy 0 b.num with hpos | hz | hneg
    · exact hpos
    · rw [← hz, Int.zero_mul] at h1; omega
    · have := Int.mul_neg_of_neg_of_pos hneg ha; omega
  · intro hp
    have h1 : 0 < b.num * a.den := int_mul_pos hp ha
    rw [← h] at h1
    rcases Int.lt_trichotomy 0 a.num with hpos | hz | hneg
    · exact hpos
    · rw [← hz, Int.zero_mul] at h1; omega
    · have := Int.mul_neg_of_neg_of_pos hneg hb; omega
  · intro hn
    have h1 : a.num * b.den < 0 := Int.mul_neg_of_neg_of_pos hn hb
    rw [h] at h1
    rcases Int.lt_trichotomy 0 b.num with hpos | hz | hneg
    · have := int_mul_pos hpos ha; omega
    · rw [← hz, Int.zero_mul] at h1; omega
    · exact hneg
  · intro hn
    have h1 : b.num * a.den < 0 := Int.mul_neg_of_neg_of_pos hn ha
    rw [← h] at h1
    rcases Int.lt_trichotomy 0 a.num with hpos | hz | hneg
    · have := int_mul_pos hpos hb; omega
    · rw [← hz, Int.zero_mul] at h1; omega
    · exact hneg
  · intro hz; rw [hz, Int.zero_mul] at h; symm at h
    rcases Int.mul_eq_zero.mp h with hbz | haz <;> omega
  · intro hz; rw [hz, Int.zero_mul] at h
    rcases Int.mul_eq_zero.mp h with haz | hbz <;> omega

theorem inv_congr {a₁ a₂ : RawQ} (ha : equiv a₁ a₂) : equiv (inv a₁) (inv a₂) := by
  have hs := sign_of_equiv ha
  unfold inv
  by_cases hp1 : 0 < a₁.num
  · have hp2 : 0 < a₂.num := hs.1.mp hp1
    rw [dif_pos hp1, dif_pos hp2]
    unfold equiv at *; dsimp only
    rw [Int.mul_comm a₁.den a₂.num, ← ha, Int.mul_comm]
  · have hp2 : ¬ (0 < a₂.num) := fun h => hp1 (hs.1.mpr h)
    rw [dif_neg hp1, dif_neg hp2]
    by_cases hn1 : a₁.num < 0
    · have hn2 : a₂.num < 0 := hs.2.1.mp hn1
      rw [dif_pos hn1, dif_pos hn2]
      unfold equiv at *; dsimp only
      rw [Int.neg_mul_neg, Int.neg_mul_neg, Int.mul_comm a₁.den a₂.num, ← ha, Int.mul_comm]
    · have hn2 : ¬ (a₂.num < 0) := fun h => hn1 (hs.2.1.mpr h)
      rw [dif_neg hn1, dif_neg hn2]
      rfl

theorem abs_congr {a₁ a₂ : RawQ} (ha : equiv a₁ a₂) : equiv (abs a₁) (abs a₂) := by
  have hs := sign_of_equiv ha
  unfold abs equiv at *; dsimp only
  by_cases h1 : 0 ≤ a₁.num
  · have h2 : 0 ≤ a₂.num := by
      rcases Int.lt_trichotomy 0 a₁.num with hp | hz | hn
      · have := hs.1.mp hp; omega
      · have := hs.2.2.mp hz.symm; omega
      · omega
    rw [if_pos h1, if_pos h2, ha]
  · have hn1 : a₁.num < 0 := by omega
    have hn2 : a₂.num < 0 := hs.2.1.mp hn1
    have h2 : ¬ (0 ≤ a₂.num) := by omega
    rw [if_neg h1, if_neg h2, Int.neg_mul, Int.neg_mul, ha]

theorem lt_iff_of_equiv {a₁ a₂ b₁ b₂ : RawQ} (ha : equiv a₁ a₂) (hb : equiv b₁ b₂) :
    lt a₁ b₁ ↔ lt a₂ b₂ := by
  unfold lt equiv at *
  have hd : 0 < a₁.den * b₁.den := int_mul_pos a₁.den_pos b₁.den_pos
  have hd2 : 0 < a₂.den * b₂.den := int_mul_pos a₂.den_pos b₂.den_pos
  have hid : (b₁.num * a₁.den - a₁.num * b₁.den) * (a₂.den * b₂.den) =
             (b₂.num * a₂.den - a₂.num * b₂.den) * (a₁.den * b₁.den) := by
    rw [Int.sub_mul, Int.sub_mul]
    congr 1
    · calc
        (b₁.num * a₁.den) * (a₂.den * b₂.den)
            = (b₁.num * b₂.den) * (a₁.den * a₂.den) := by
              simp only [Int.mul_assoc, Int.mul_left_comm, Int.mul_comm]
        _ = (b₂.num * b₁.den) * (a₁.den * a₂.den) := by rw [hb]
        _ = (b₂.num * a₂.den) * (a₁.den * b₁.den) := by
              simp only [Int.mul_assoc, Int.mul_left_comm, Int.mul_comm]
    · calc
        (a₁.num * b₁.den) * (a₂.den * b₂.den)
            = (a₁.num * a₂.den) * (b₁.den * b₂.den) := by
              simp only [Int.mul_assoc, Int.mul_left_comm, Int.mul_comm]
        _ = (a₂.num * a₁.den) * (b₁.den * b₂.den) := by rw [ha]
        _ = (a₂.num * b₂.den) * (a₁.den * b₁.den) := by
              simp only [Int.mul_assoc, Int.mul_left_comm, Int.mul_comm]
  constructor
  · intro h1
    have hp : 0 < (b₁.num * a₁.den - a₁.num * b₁.den) * (a₂.den * b₂.den) :=
      int_mul_pos (by omega) hd2
    rw [hid] at hp
    rcases Int.lt_trichotomy 0 (b₂.num * a₂.den - a₂.num * b₂.den) with hpos | hz | hneg
    · omega
    · rw [← hz, Int.zero_mul] at hp; omega
    · have := Int.mul_neg_of_neg_of_pos hneg hd; omega
  · intro h2
    have hp : 0 < (b₂.num * a₂.den - a₂.num * b₂.den) * (a₁.den * b₁.den) :=
      int_mul_pos (by omega) hd
    rw [← hid] at hp
    rcases Int.lt_trichotomy 0 (b₁.num * a₁.den - a₁.num * b₁.den) with hpos | hz | hneg
    · omega
    · rw [← hz, Int.zero_mul] at hp; omega
    · have := Int.mul_neg_of_neg_of_pos hneg hd2; omega

end RawQ

def Q : Type := Quotient RawQ.setoid

namespace Q

def mk (r : RawQ) : Q := Quotient.mk RawQ.setoid r
def ofInt (n : Int) : Q := mk (RawQ.ofInt n)
def ofNat (n : Nat) : Q := ofInt (Int.ofNat n)

instance (n : Nat) : OfNat Q n := ⟨ofNat n⟩

theorem sound {a b : RawQ} (h : RawQ.equiv a b) : mk a = mk b := Quotient.sound h
theorem exact {a b : RawQ} (h : mk a = mk b) : RawQ.equiv a b := Quotient.exact h

def add : Q → Q → Q :=
  Quotient.lift₂ (fun a b => mk (RawQ.add a b)) (fun _ _ _ _ ha hb => sound (RawQ.add_congr ha hb))

def neg : Q → Q :=
  Quotient.lift (fun a => mk (RawQ.neg a)) (fun _ _ ha => sound (RawQ.neg_congr ha))

def sub (a b : Q) : Q := add a (neg b)

def mul : Q → Q → Q :=
  Quotient.lift₂ (fun a b => mk (RawQ.mul a b)) (fun _ _ _ _ ha hb => sound (RawQ.mul_congr ha hb))

def inv : Q → Q :=
  Quotient.lift (fun a => mk (RawQ.inv a)) (fun _ _ ha => sound (RawQ.inv_congr ha))

def abs : Q → Q :=
  Quotient.lift (fun a => mk (RawQ.abs a)) (fun _ _ ha => sound (RawQ.abs_congr ha))

def lt : Q → Q → Prop :=
  Quotient.lift₂ RawQ.lt (fun _ _ _ _ ha hb => propext (RawQ.lt_iff_of_equiv ha hb))

def le (a b : Q) : Prop := ¬ lt b a

instance : Add Q := ⟨add⟩
instance : Neg Q := ⟨neg⟩
instance : Sub Q := ⟨sub⟩
instance : Mul Q := ⟨mul⟩
instance : LT Q := ⟨lt⟩
instance : LE Q := ⟨le⟩

theorem add_comm (x y : Q) : x + y = y + x := by
  induction x using Quotient.ind; induction y using Quotient.ind
  apply sound; unfold RawQ.equiv RawQ.add; dsimp only
  simp only [Int.mul_assoc, Int.mul_left_comm, Int.mul_comm, Int.add_comm]

theorem add_assoc (x y z : Q) : (x + y) + z = x + (y + z) := by
  induction x using Quotient.ind; induction y using Quotient.ind; induction z using Quotient.ind
  rename_i a b c
  apply sound; unfold RawQ.equiv RawQ.add; dsimp only
  have h1 : (a.num * b.den + b.num * a.den) * c.den + c.num * (a.den * b.den) =
            a.num * (b.den * c.den) + (b.num * c.den + c.num * b.den) * a.den := by
    rw [Int.add_mul, Int.add_mul]
    simp only [Int.mul_assoc, Int.mul_left_comm, Int.mul_comm, Int.add_assoc]
  rw [h1, Int.mul_assoc]

theorem add_left_comm (x y z : Q) : x + (y + z) = y + (x + z) := by
  rw [← add_assoc, add_comm x y, add_assoc]

theorem zero_add (x : Q) : (0 : Q) + x = x := by
  induction x using Quotient.ind
  apply sound; unfold RawQ.equiv RawQ.add RawQ.ofInt; dsimp only
  simp

theorem add_zero (x : Q) : x + (0 : Q) = x := by rw [add_comm, zero_add]

theorem neg_add_cancel (x : Q) : (-x) + x = 0 := by
  induction x using Quotient.ind
  apply sound; unfold RawQ.equiv RawQ.add RawQ.neg RawQ.ofInt; dsimp only
  rw [Int.neg_mul, Int.add_left_neg]
  simp

theorem add_neg_cancel (x : Q) : x + (-x) = 0 := by rw [add_comm, neg_add_cancel]

theorem add_neg_cancel_left (x y : Q) : x + (-x + y) = y := by
  rw [← add_assoc, add_neg_cancel, zero_add]

theorem neg_add_cancel_left (x y : Q) : -x + (x + y) = y := by
  rw [← add_assoc, neg_add_cancel, zero_add]

theorem sub_eq_add_neg (x y : Q) : x - y = x + (-y) := rfl

theorem sub_self (x : Q) : x - x = 0 := add_neg_cancel x

theorem neg_neg (x : Q) : -(-x) = x := by
  induction x using Quotient.ind
  apply sound; unfold RawQ.equiv RawQ.neg; dsimp only; rw [Int.neg_neg]

theorem neg_add (x y : Q) : -(x + y) = -x + (-y) := by
  induction x using Quotient.ind; induction y using Quotient.ind
  apply sound; unfold RawQ.equiv RawQ.add RawQ.neg; dsimp only
  rw [Int.neg_add, Int.neg_mul, Int.neg_mul]

theorem neg_sub (x y : Q) : -(x - y) = y - x := by
  rw [sub_eq_add_neg, neg_add, neg_neg, add_comm]; rfl

theorem mul_comm (x y : Q) : x * y = y * x := by
  induction x using Quotient.ind; induction y using Quotient.ind
  apply sound; unfold RawQ.equiv RawQ.mul; dsimp only
  simp only [Int.mul_assoc, Int.mul_left_comm, Int.mul_comm]

theorem mul_assoc (x y z : Q) : (x * y) * z = x * (y * z) := by
  induction x using Quotient.ind; induction y using Quotient.ind; induction z using Quotient.ind
  apply sound; unfold RawQ.equiv RawQ.mul; dsimp only
  simp only [Int.mul_assoc]

theorem mul_left_comm (x y z : Q) : x * (y * z) = y * (x * z) := by
  rw [← mul_assoc, mul_comm x y, mul_assoc]

theorem one_mul (x : Q) : (1 : Q) * x = x := by
  induction x using Quotient.ind
  apply sound; unfold RawQ.equiv RawQ.mul RawQ.ofInt; dsimp only; simp

theorem mul_one (x : Q) : x * (1 : Q) = x := by rw [mul_comm, one_mul]

theorem zero_mul (x : Q) : (0 : Q) * x = 0 := by
  induction x using Quotient.ind
  apply sound; unfold RawQ.equiv RawQ.mul RawQ.ofInt; dsimp only; simp

theorem mul_zero (x : Q) : x * (0 : Q) = 0 := by rw [mul_comm, zero_mul]

theorem neg_mul (x y : Q) : (-x) * y = -(x * y) := by
  induction x using Quotient.ind; induction y using Quotient.ind
  apply sound; unfold RawQ.equiv RawQ.mul RawQ.neg; dsimp only
  rw [Int.neg_mul]

theorem mul_neg (x y : Q) : x * (-y) = -(x * y) := by
  rw [mul_comm, neg_mul, mul_comm]

theorem left_distrib (x y z : Q) : x * (y + z) = x * y + x * z := by
  induction x using Quotient.ind; induction y using Quotient.ind; induction z using Quotient.ind
  rename_i a b c
  apply sound; unfold RawQ.equiv RawQ.mul RawQ.add; dsimp only
  calc
    (a.num * (b.num * c.den + c.num * b.den)) * ((a.den * b.den) * (a.den * c.den))
        = a.num * b.num * c.den * (a.den * b.den * (a.den * c.den)) +
          a.num * c.num * b.den * (a.den * b.den * (a.den * c.den)) := by
          rw [Int.mul_add, Int.add_mul, Int.mul_assoc a.num b.num c.den, Int.mul_assoc a.num c.num b.den]
    _ = ((a.num * b.num) * (a.den * c.den) + (a.num * c.num) * (a.den * b.den)) *
          (a.den * (b.den * c.den)) := by
          rw [Int.add_mul]
          congr 1 <;> simp only [Int.mul_assoc, Int.mul_left_comm, Int.mul_comm]

theorem right_distrib (x y z : Q) : (x + y) * z = x * z + y * z := by
  rw [mul_comm, left_distrib, mul_comm z x, mul_comm z y]

theorem sub_mul (x y z : Q) : (x - y) * z = x * z - y * z := by
  rw [sub_eq_add_neg, right_distrib, neg_mul]; rfl

theorem mul_sub (x y z : Q) : x * (y - z) = x * y - x * z := by
  rw [sub_eq_add_neg, left_distrib, mul_neg]; rfl

theorem one_ne_zero : (1 : Q) ≠ (0 : Q) := by
  intro h
  have he : RawQ.equiv (RawQ.ofInt 1) (RawQ.ofInt 0) := exact h
  unfold RawQ.equiv RawQ.ofInt at he; dsimp only at he
  omega

theorem mul_inv_cancel {x : Q} (hx : x ≠ 0) : x * inv x = 1 := by
  induction x using Quotient.ind
  rename_i a
  apply sound; unfold RawQ.inv
  by_cases hp : 0 < a.num
  · rw [dif_pos hp]; unfold RawQ.equiv RawQ.mul RawQ.ofInt; dsimp only
    simp [Int.mul_comm]
  · rw [dif_neg hp]
    by_cases hn : a.num < 0
    · rw [dif_pos hn]; unfold RawQ.equiv RawQ.mul RawQ.ofInt; dsimp only
      simp [Int.mul_neg, Int.mul_comm]
    · exfalso; apply hx; apply sound
      unfold RawQ.equiv RawQ.ofInt; dsimp only
      have hz : a.num = 0 := by omega
      rw [hz]; simp

theorem lt_irrefl (x : Q) : ¬ (x < x) := by
  induction x using Quotient.ind
  rename_i a
  change ¬ (a.num * a.den < a.num * a.den); omega

theorem lt_trans {x y z : Q} (hab : x < y) (hbc : y < z) : x < z := by
  induction x using Quotient.ind; induction y using Quotient.ind; induction z using Quotient.ind
  rename_i a b c
  change a.num * b.den < b.num * a.den at hab
  change b.num * c.den < c.num * b.den at hbc
  change a.num * c.den < c.num * a.den
  have h1 : (b.num * a.den - a.num * b.den) * c.den > 0 := RawQ.int_mul_pos (by omega) c.den_pos
  have h2 : (c.num * b.den - b.num * c.den) * a.den > 0 := RawQ.int_mul_pos (by omega) a.den_pos
  have hsum : (c.num * a.den - a.num * c.den) * b.den =
              (b.num * a.den - a.num * b.den) * c.den + (c.num * b.den - b.num * c.den) * a.den := by
    rw [Int.sub_mul, Int.sub_mul, Int.sub_mul]
    simp only [Int.mul_assoc, Int.mul_left_comm, Int.mul_comm]
    omega
  have hpos : (c.num * a.den - a.num * c.den) * b.den > 0 := by omega
  rcases Int.lt_trichotomy 0 (c.num * a.den - a.num * c.den) with hp | hz | hn
  · omega
  · rw [← hz, Int.zero_mul] at hpos; omega
  · have := Int.mul_neg_of_neg_of_pos hn b.den_pos; omega

theorem lt_trichotomy (x y : Q) : x < y ∨ x = y ∨ y < x := by
  induction x using Quotient.ind; induction y using Quotient.ind
  rename_i a b
  rcases Int.lt_trichotomy (a.num * b.den) (b.num * a.den) with hlt | heq | hgt
  · exact Or.inl hlt
  · exact Or.inr (Or.inl (sound heq))
  · exact Or.inr (Or.inr hgt)

theorem le_iff_lt_or_eq {x y : Q} : x ≤ y ↔ x < y ∨ x = y := by
  change ¬ (y < x) ↔ x < y ∨ x = y
  constructor
  · intro h
    rcases lt_trichotomy x y with hlt | heq | hgt
    · exact Or.inl hlt
    · exact Or.inr heq
    · exact False.elim (h hgt)
  · rintro (hlt | rfl)
    · exact fun hgt => lt_irrefl x (lt_trans hlt hgt)
    · exact lt_irrefl x

theorem le_refl (x : Q) : x ≤ x := le_iff_lt_or_eq.mpr (Or.inr rfl)

theorem le_of_lt {x y : Q} (h : x < y) : x ≤ y := le_iff_lt_or_eq.mpr (Or.inl h)

theorem le_antisymm {x y : Q} (h1 : x ≤ y) (h2 : y ≤ x) : x = y := by
  rcases le_iff_lt_or_eq.mp h1 with hlt | heq
  · exact False.elim (h2 hlt)
  · exact heq

theorem lt_of_lt_of_le {x y z : Q} (h1 : x < y) (h2 : y ≤ z) : x < z := by
  rcases le_iff_lt_or_eq.mp h2 with hlt | rfl
  · exact lt_trans h1 hlt
  · exact h1

theorem lt_of_le_of_lt {x y z : Q} (h1 : x ≤ y) (h2 : y < z) : x < z := by
  rcases le_iff_lt_or_eq.mp h1 with hlt | rfl
  · exact lt_trans hlt h2
  · exact h2

theorem le_trans {x y z : Q} (h1 : x ≤ y) (h2 : y ≤ z) : x ≤ z := by
  rcases le_iff_lt_or_eq.mp h1 with hlt | rfl
  · exact le_of_lt (lt_of_lt_of_le hlt h2)
  · exact h2

theorem not_le_iff_lt {x y : Q} : ¬ (x ≤ y) ↔ y < x := by
  change ¬ ¬ (y < x) ↔ y < x
  rcases lt_trichotomy y x with hlt | rfl | hgt
  · exact ⟨fun _ => hlt, fun _ h => h hlt⟩
  · exact ⟨fun h => False.elim (h (lt_irrefl y)), fun h => False.elim (lt_irrefl y h)⟩
  · have hn : ¬ (y < x) := fun h => lt_irrefl x (lt_trans hgt h)
    exact ⟨fun h => False.elim (h hn), fun h => False.elim (hn h)⟩

theorem add_lt_add_left {x y : Q} (h : x < y) (z : Q) : z + x < z + y := by
  induction x using Quotient.ind; induction y using Quotient.ind; induction z using Quotient.ind
  rename_i a b c
  change a.num * b.den < b.num * a.den at h
  change (c.num * a.den + a.num * c.den) * (c.den * b.den) <
         (c.num * b.den + b.num * c.den) * (c.den * a.den)
  have hc2 : 0 < c.den * c.den := RawQ.int_mul_pos c.den_pos c.den_pos
  have hp : 0 < (b.num * a.den - a.num * b.den) * (c.den * c.den) :=
    RawQ.int_mul_pos (by omega) hc2
  have hid : (c.num * b.den + b.num * c.den) * (c.den * a.den) -
             (c.num * a.den + a.num * c.den) * (c.den * b.den) =
             (b.num * a.den - a.num * b.den) * (c.den * c.den) := by
    rw [Int.add_mul, Int.add_mul, Int.sub_mul]
    simp only [Int.mul_assoc, Int.mul_left_comm, Int.mul_comm]
    omega
  omega

theorem add_lt_add_right {x y : Q} (h : x < y) (z : Q) : x + z < y + z := by
  rw [add_comm x z, add_comm y z]; exact add_lt_add_left h z

theorem add_lt_add {a b c d : Q} (h1 : a < b) (h2 : c < d) : a + c < b + d :=
  lt_trans (add_lt_add_right h1 c) (add_lt_add_left h2 b)

theorem add_le_add {a b c d : Q} (h1 : a ≤ b) (h2 : c ≤ d) : a + c ≤ b + d := by
  rcases le_iff_lt_or_eq.mp h1 with hlt1 | rfl
  · rcases le_iff_lt_or_eq.mp h2 with hlt2 | rfl
    · exact le_of_lt (add_lt_add hlt1 hlt2)
    · exact le_of_lt (add_lt_add_right hlt1 c)
  · rcases le_iff_lt_or_eq.mp h2 with hlt2 | rfl
    · exact le_of_lt (add_lt_add_left hlt2 a)
    · exact le_refl _

theorem add_lt_of_lt_of_le {a b c d : Q} (h1 : a < b) (h2 : c ≤ d) : a + c < b + d := by
  rcases le_iff_lt_or_eq.mp h2 with hlt2 | rfl
  · exact add_lt_add h1 hlt2
  · exact add_lt_add_right h1 c

theorem sub_pos {x y : Q} : (0 : Q) < y - x ↔ x < y := by
  constructor
  · intro h
    have h1 := add_lt_add_left h x
    rw [add_zero, sub_eq_add_neg, ← add_assoc, add_comm x y, add_assoc, add_neg_cancel, add_zero] at h1
    exact h1
  · intro h
    have h1 := add_lt_add_right h (-x)
    rw [add_neg_cancel] at h1
    exact h1

theorem sub_nonneg {x y : Q} : (0 : Q) ≤ y - x ↔ x ≤ y := by
  constructor
  · intro h hlt
    have hp : (0 : Q) < x - y := sub_pos.mpr hlt
    have hn : -(y - x) = x - y := neg_sub y x
    have hsum := add_lt_of_lt_of_le hp h
    rw [← hn, neg_add_cancel, zero_add] at hsum
    exact lt_irrefl 0 hsum
  · intro h hlt
    have hp : (0 : Q) < x - y := by
      have h1 := add_lt_add_right hlt (-(y - x))
      rw [add_neg_cancel, zero_add, neg_sub] at h1
      exact h1
    exact h (sub_pos.mp hp)

theorem mul_pos {x y : Q} (hx : (0 : Q) < x) (hy : (0 : Q) < y) : (0 : Q) < x * y := by
  induction x using Quotient.ind; induction y using Quotient.ind
  rename_i a b
  change 0 * a.den < a.num * 1 at hx
  change 0 * b.den < b.num * 1 at hy
  change 0 * (a.den * b.den) < (a.num * b.num) * 1
  simp only [Int.zero_mul, Int.mul_one] at *
  exact RawQ.int_mul_pos hx hy

theorem mul_nonneg {x y : Q} (hx : (0 : Q) ≤ x) (hy : (0 : Q) ≤ y) : (0 : Q) ≤ x * y := by
  rcases le_iff_lt_or_eq.mp hx with hxp | rfl
  · rcases le_iff_lt_or_eq.mp hy with hyp | rfl
    · exact le_of_lt (mul_pos hxp hyp)
    · rw [mul_zero]; exact le_refl 0
  · rw [zero_mul]; exact le_refl 0

theorem mul_lt_mul_of_pos_left {a b c : Q} (h : a < b) (hc : (0 : Q) < c) : c * a < c * b := by
  rw [← sub_pos, ← mul_sub]
  exact mul_pos hc (sub_pos.mpr h)

theorem mul_le_mul_of_nonneg_left {a b c : Q} (h : a ≤ b) (hc : (0 : Q) ≤ c) : c * a ≤ c * b := by
  rw [← sub_nonneg, ← mul_sub]
  exact mul_nonneg hc (sub_nonneg.mpr h)

theorem abs_of_nonneg {x : Q} (hx : (0 : Q) ≤ x) : abs x = x := by
  induction x using Quotient.ind
  rename_i a
  have ha : 0 ≤ a.num := by
    rcases Int.lt_trichotomy a.num 0 with hneg | hz | hpos
    · exfalso; apply hx
      change a.num * 1 < 0 * a.den; omega
    · omega
    · omega
  apply sound; unfold RawQ.abs RawQ.equiv; dsimp only
  rw [if_pos ha]

theorem abs_of_neg {x : Q} (hx : x < (0 : Q)) : abs x = -x := by
  induction x using Quotient.ind
  rename_i a
  change a.num * 1 < 0 * a.den at hx
  have ha : ¬ (0 ≤ a.num) := by omega
  apply sound; unfold RawQ.abs RawQ.neg RawQ.equiv; dsimp only
  rw [if_neg ha]

theorem abs_nonneg (x : Q) : (0 : Q) ≤ abs x := by
  rcases lt_trichotomy x 0 with hn | rfl | hp
  · rw [abs_of_neg hn]
    have h1 := add_lt_add_right hn (-x)
    rw [add_neg_cancel, zero_add] at h1
    exact le_of_lt h1
  · rw [abs_of_nonneg (le_refl 0)]; exact le_refl 0
  · rw [abs_of_nonneg (le_of_lt hp)]; exact le_of_lt hp

theorem abs_neg (x : Q) : abs (-x) = abs x := by
  induction x using Quotient.ind
  rename_i a
  apply sound; unfold RawQ.abs RawQ.neg RawQ.equiv; dsimp only
  by_cases h1 : 0 ≤ a.num
  · by_cases h2 : a.num = 0
    · rw [h2]; simp
    · have hn : ¬ (0 ≤ -a.num) := by omega
      rw [if_pos h1, if_neg hn, Int.neg_neg]
  · have hp : 0 ≤ -a.num := by omega
    rw [if_neg h1, if_pos hp]

theorem abs_sub_comm (x y : Q) : abs (x - y) = abs (y - x) := by
  rw [← neg_sub x y, abs_neg]

theorem le_abs_self (x : Q) : x ≤ abs x := by
  rcases lt_trichotomy x 0 with hn | rfl | hp
  · exact le_trans (le_of_lt hn) (abs_nonneg x)
  · rw [abs_of_nonneg (le_refl 0)]; exact le_refl 0
  · rw [abs_of_nonneg (le_of_lt hp)]; exact le_refl x

theorem neg_le_abs_self (x : Q) : -x ≤ abs x := by
  rw [← abs_neg]; exact le_abs_self (-x)

theorem abs_le_iff {x c : Q} : abs x ≤ c ↔ -c ≤ x ∧ x ≤ c := by
  constructor
  · intro h
    refine ⟨?_, le_trans (le_abs_self x) h⟩
    have h1 : -x ≤ c := le_trans (neg_le_abs_self x) h
    have h2 := add_le_add h1 (le_refl (x + (-c)))
    have hl : -x + (x + (-c)) = -c := by rw [← add_assoc, neg_add_cancel, zero_add]
    have hr : c + (x + (-c)) = x := by rw [add_comm x (-c), ← add_assoc, add_neg_cancel, zero_add]
    rw [hl, hr] at h2; exact h2
  · rintro ⟨h1, h2⟩
    rcases lt_trichotomy x 0 with hn | rfl | hp
    · rw [abs_of_neg hn]
      have h3 := add_le_add h1 (le_refl (c + (-x)))
      have hl : -c + (c + (-x)) = -x := by rw [← add_assoc, neg_add_cancel, zero_add]
      have hr : x + (c + (-x)) = c := by rw [add_comm c (-x), ← add_assoc, add_neg_cancel, zero_add]
      rw [hl, hr] at h3; exact h3
    · rw [abs_of_nonneg (le_refl 0)]; exact h2
    · rw [abs_of_nonneg (le_of_lt hp)]; exact h2

theorem abs_lt_iff {x c : Q} : abs x < c ↔ -c < x ∧ x < c := by
  constructor
  · intro h
    rcases lt_trichotomy x 0 with hn | rfl | hp
    · rw [abs_of_neg hn] at h
      have h1 := add_lt_add_right h (x + (-c))
      have hl : -x + (x + (-c)) = -c := by rw [← add_assoc, neg_add_cancel, zero_add]
      have hr : c + (x + (-c)) = x := by rw [add_comm x (-c), ← add_assoc, add_neg_cancel, zero_add]
      rw [hl, hr] at h1
      exact ⟨h1, lt_of_lt_of_le hn (le_trans (abs_nonneg x) (le_of_lt (by rw [abs_of_neg hn]; exact h)))⟩
    · rw [abs_of_nonneg (le_refl 0)] at h
      have h1 := add_lt_add_right h (-c)
      rw [zero_add, add_neg_cancel] at h1
      exact ⟨h1, h⟩
    · rw [abs_of_nonneg (le_of_lt hp)] at h
      have hc : (0 : Q) < c := lt_trans hp h
      have hnc : -c < 0 := by
        have := add_lt_add_right hc (-c); rw [zero_add, add_neg_cancel] at this; exact this
      exact ⟨lt_trans hnc hp, h⟩
  · rintro ⟨h1, h2⟩
    rcases lt_trichotomy x 0 with hn | rfl | hp
    · rw [abs_of_neg hn]
      have h3 := add_lt_add_right h1 (c + (-x))
      have hl : -c + (c + (-x)) = -x := by rw [← add_assoc, neg_add_cancel, zero_add]
      have hr : x + (c + (-x)) = c := by rw [add_comm c (-x), ← add_assoc, add_neg_cancel, zero_add]
      rw [hl, hr] at h3; exact h3
    · rw [abs_of_nonneg (le_refl 0)]; exact h2
    · rw [abs_of_nonneg (le_of_lt hp)]; exact h2

theorem abs_add (x y : Q) : abs (x + y) ≤ abs x + abs y := by
  rw [abs_le_iff]
  rw [neg_add]
  exact ⟨add_le_add (by have := (abs_le_iff.mp (le_refl (abs x))).1; exact this)
                    (by have := (abs_le_iff.mp (le_refl (abs y))).1; exact this),
         add_le_add (le_abs_self x) (le_abs_self y)⟩

theorem abs_mul (x y : Q) : abs (x * y) = abs x * abs y := by
  rcases lt_trichotomy x 0 with hx | rfl | hx
  · rcases lt_trichotomy y 0 with hy | rfl | hy
    · have hxy : (0 : Q) < x * y := by
        have hnx : (0 : Q) < -x := by have := add_lt_add_right hx (-x); rw [add_neg_cancel, zero_add] at this; exact this
        have hny : (0 : Q) < -y := by have := add_lt_add_right hy (-y); rw [add_neg_cancel, zero_add] at this; exact this
        have hp := mul_pos hnx hny
        rw [neg_mul, mul_neg, neg_neg] at hp; exact hp
      rw [abs_of_neg hx, abs_of_neg hy, abs_of_nonneg (le_of_lt hxy), neg_mul, mul_neg, neg_neg]
    · rw [mul_zero, abs_of_nonneg (le_refl 0), mul_zero]
    · have hnx : (0 : Q) < -x := by have := add_lt_add_right hx (-x); rw [add_neg_cancel, zero_add] at this; exact this
      have hxy : x * y < 0 := by
        have hp := mul_pos hnx hy; rw [neg_mul] at hp
        have := add_lt_add_right hp (x * y)
        rw [zero_add, neg_add_cancel] at this; exact this
      rw [abs_of_neg hx, abs_of_nonneg (le_of_lt hy), abs_of_neg hxy, neg_mul]
  · rw [zero_mul, abs_of_nonneg (le_refl 0), zero_mul]
  · rcases lt_trichotomy y 0 with hy | rfl | hy
    · have hny : (0 : Q) < -y := by have := add_lt_add_right hy (-y); rw [add_neg_cancel, zero_add] at this; exact this
      have hxy : x * y < 0 := by
        have hp := mul_pos hx hny; rw [mul_neg] at hp
        have := add_lt_add_right hp (x * y)
        rw [zero_add, neg_add_cancel] at this; exact this
      rw [abs_of_nonneg (le_of_lt hx), abs_of_neg hy, abs_of_neg hxy, mul_neg]
    · rw [mul_zero, abs_of_nonneg (le_refl 0), mul_zero]
    · rw [abs_of_nonneg (le_of_lt hx), abs_of_nonneg (le_of_lt hy),
          abs_of_nonneg (le_of_lt (mul_pos hx hy))]

def intPow2 : Nat → Int
  | 0 => 1
  | k + 1 => 2 * intPow2 k

theorem intPow2_pos : ∀ k : Nat, 0 < intPow2 k
  | 0 => by decide
  | k + 1 => by unfold intPow2; have := intPow2_pos k; omega

theorem intPow2_gt_nat : ∀ k : Nat, (k : Int) < intPow2 k
  | 0 => by decide
  | k + 1 => by
    unfold intPow2
    have ih := intPow2_gt_nat k
    have hp := intPow2_pos k
    omega

theorem intPow2_add : ∀ j k : Nat, intPow2 (j + k) = intPow2 j * intPow2 k
  | 0, k => by rw [Nat.zero_add]; simp [intPow2]
  | j + 1, k => by
    rw [Nat.succ_add]
    simp only [intPow2, intPow2_add j k, Int.mul_assoc]

def twoPow (k : Nat) : Q := mk ⟨intPow2 k, 1, by omega⟩
def pow2 (k : Nat) : Q := mk ⟨1, intPow2 k, intPow2_pos k⟩

theorem pow2_pos (k : Nat) : (0 : Q) < pow2 k := by
  change 0 * intPow2 k < 1 * 1
  have := intPow2_pos k; omega

theorem twoPow_pos (k : Nat) : (0 : Q) < twoPow k := by
  change 0 * 1 < intPow2 k * 1
  have := intPow2_pos k; omega

theorem twoPow_mul_pow2 (k : Nat) : twoPow k * pow2 k = 1 := by
  apply sound; unfold RawQ.equiv RawQ.mul RawQ.ofInt; dsimp only
  simp

theorem pow2_add (j k : Nat) : pow2 (j + k) = pow2 j * pow2 k := by
  apply sound; unfold RawQ.equiv RawQ.mul; dsimp only
  rw [Int.one_mul, Int.one_mul, Int.one_mul, intPow2_add]

theorem pow2_succ_double (k : Nat) : pow2 (k + 1) + pow2 (k + 1) = pow2 k := by
  apply sound; unfold RawQ.equiv RawQ.add; dsimp only
  change (1 * (2 * intPow2 k) + 1 * (2 * intPow2 k)) * intPow2 k =
         1 * ((2 * intPow2 k) * (2 * intPow2 k))
  have h22 : (2 * intPow2 k + 2 * intPow2 k) = 4 * intPow2 k := by omega
  rw [Int.one_mul, Int.one_mul, h22, Int.mul_assoc]
  have hR : (2 * intPow2 k) * (2 * intPow2 k) = 4 * (intPow2 k * intPow2 k) := by
    calc
      (2 * intPow2 k) * (2 * intPow2 k) = (2 * 2) * (intPow2 k * intPow2 k) := by
        simp only [Int.mul_assoc, Int.mul_left_comm, Int.mul_comm]
      _ = 4 * (intPow2 k * intPow2 k) := rfl
  rw [hR]

theorem pow2_le_of_le {j k : Nat} (h : j ≤ k) : pow2 k ≤ pow2 j := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  change ¬ (1 * intPow2 (j + d) < 1 * intPow2 j)
  rw [intPow2_add, Int.one_mul, Int.one_mul]
  have hp1 := intPow2_pos j
  have hp2 := intPow2_pos d
  have hge : intPow2 j * 1 ≤ intPow2 j * intPow2 d := Int.mul_le_mul_of_nonneg_left (by omega) (by omega)
  omega

theorem exists_twoPow_gt (x : Q) : ∃ B : Nat, abs x < twoPow B := by
  induction x using Quotient.ind
  rename_i a
  let n : Nat := a.num.natAbs
  refine ⟨n, ?_⟩
  have hgt := intPow2_gt_nat n
  have hd : 1 ≤ a.den := a.den_pos
  change (if 0 ≤ a.num then a.num else -a.num) * 1 < intPow2 n * a.den
  have habs : (if 0 ≤ a.num then a.num else -a.num) = (n : Int) := by
    by_cases h : 0 ≤ a.num <;> simp [h, n] <;> omega
  rw [habs, Int.mul_one]
  have hle : intPow2 n * 1 ≤ intPow2 n * a.den :=
    Int.mul_le_mul_of_nonneg_left hd (by have := intPow2_pos n; omega)
  omega

theorem exists_pow2_lt {ε : Q} (hε : (0 : Q) < ε) : ∃ k : Nat, pow2 k < ε := by
  induction ε using Quotient.ind
  rename_i a
  change 0 * a.den < a.num * 1 at hε
  have hnum : 1 ≤ a.num := by omega
  let k : Nat := a.den.toNat
  refine ⟨k, ?_⟩
  change 1 * a.den < a.num * intPow2 k
  have hk : (k : Int) = a.den := Int.toNat_of_nonneg (by have := a.den_pos; omega)
  have hgt : a.den < intPow2 k := by rw [← hk]; exact intPow2_gt_nat k
  have hle : 1 * intPow2 k ≤ a.num * intPow2 k :=
    Int.mul_le_mul_of_nonneg_right hnum (by have := intPow2_pos k; omega)
  omega

def half (x : Q) : Q := x * pow2 1

theorem half_add_half (x : Q) : half x + half x = x := by
  unfold half
  rw [← left_distrib, (pow2_succ_double 0 : pow2 1 + pow2 1 = pow2 0)]
  have hp0 : pow2 0 = 1 := by apply sound; rfl
  rw [hp0, mul_one]

theorem sub_half_midpoint (u v : Q) :
    half (u + v) - u = (v - u) * pow2 1 ∧ v - half (u + v) = (v - u) * pow2 1 := by
  have hp0 : pow2 0 = 1 := by apply sound; rfl
  have h2 : pow2 1 + pow2 1 = 1 := by rw [pow2_succ_double 0, hp0]
  have hu : u = u * pow2 1 + u * pow2 1 := by rw [← left_distrib, h2, mul_one]
  have hv : v = v * pow2 1 + v * pow2 1 := by rw [← left_distrib, h2, mul_one]
  constructor
  · unfold half
    rw [right_distrib, sub_eq_add_neg, sub_mul, sub_eq_add_neg]
    calc
      (u * pow2 1 + v * pow2 1) + (-u)
          = (v * pow2 1 + u * pow2 1) + (-(u * pow2 1 + u * pow2 1)) := by
            rw [add_comm (u * pow2 1), ← hu]
      _ = v * pow2 1 + ((u * pow2 1 + (-(u * pow2 1))) + (-(u * pow2 1))) := by
            rw [neg_add]; simp only [add_assoc]
      _ = v * pow2 1 + (-(u * pow2 1)) := by rw [add_neg_cancel, zero_add]
  · unfold half
    rw [right_distrib, sub_eq_add_neg, sub_mul, sub_eq_add_neg]
    calc
      v + (-(u * pow2 1 + v * pow2 1))
          = (v * pow2 1 + v * pow2 1) + (-(v * pow2 1) + (-(u * pow2 1))) := by
            rw [← hv, add_comm (u * pow2 1), neg_add]
      _ = v * pow2 1 + ((v * pow2 1 + (-(v * pow2 1))) + (-(u * pow2 1))) := by
            simp only [add_assoc]
      _ = v * pow2 1 + (-(u * pow2 1)) := by rw [add_neg_cancel, zero_add]

end Q



/-! ## 2. Constructive Cauchy Reals `R` and Complex Field `C = R[i]` -/

structure CauchySeq where
  seq : Nat → Q
  isCauchy : ∀ k : Nat, ∃ N : Nat, ∀ m ≥ N, ∀ n ≥ N, Q.abs (seq m - seq n) < Q.pow2 k

namespace CauchySeq

theorem sub_rearrange4 (a b c d : Q) : (a + b) - (c + d) = (a - c) + (b - d) := by
  simp only [Q.sub_eq_add_neg, Q.neg_add, Q.add_assoc, Q.add_left_comm, Q.add_comm]

theorem sub_triangle (a b c : Q) : Q.abs (a - c) ≤ Q.abs (a - b) + Q.abs (b - c) := by
  have hid : a - c = (a - b) + (b - c) := by
    simp only [Q.sub_eq_add_neg, Q.add_assoc, Q.add_left_comm, Q.add_comm,
               Q.add_neg_cancel, Q.neg_add_cancel, Q.add_neg_cancel_left, Q.neg_add_cancel_left,
               Q.add_zero, Q.zero_add]
  rw [hid]
  exact Q.abs_add (a - b) (b - c)

def const (q : Q) : CauchySeq where
  seq _ := q
  isCauchy k := ⟨0, fun _ _ _ _ => by
    rw [Q.sub_self, Q.abs_of_nonneg (Q.le_refl 0)]
    exact Q.pow2_pos k⟩

def add (f g : CauchySeq) : CauchySeq where
  seq n := f.seq n + g.seq n
  isCauchy k := by
    obtain ⟨N₁, h₁⟩ := f.isCauchy (k + 1)
    obtain ⟨N₂, h₂⟩ := g.isCauchy (k + 1)
    refine ⟨Nat.max N₁ N₂, fun m hm n hn => ?_⟩
    rw [sub_rearrange4]
    have hle := Q.abs_add (f.seq m - f.seq n) (g.seq m - g.seq n)
    have hlt := Q.add_lt_add (h₁ m (Nat.le_trans (Nat.le_max_left _ _) hm) n (Nat.le_trans (Nat.le_max_left _ _) hn))
                             (h₂ m (Nat.le_trans (Nat.le_max_right _ _) hm) n (Nat.le_trans (Nat.le_max_right _ _) hn))
    rw [Q.pow2_succ_double] at hlt
    exact Q.lt_of_le_of_lt hle hlt

def neg (f : CauchySeq) : CauchySeq where
  seq n := -f.seq n
  isCauchy k := by
    obtain ⟨N, h⟩ := f.isCauchy k
    refine ⟨N, fun m hm n hn => ?_⟩
    have hid : (-f.seq m) - (-f.seq n) = -(f.seq m - f.seq n) := by
      simp only [Q.sub_eq_add_neg, Q.neg_add, Q.neg_neg, Q.add_comm]
    rw [hid, Q.abs_neg]
    exact h m hm n hn

def sub (f g : CauchySeq) : CauchySeq := add f (neg g)

def prefixBound (s : Nat → Q) : Nat → Q
  | 0 => Q.abs (s 0) + 1
  | n + 1 => prefixBound s n + Q.abs (s (n + 1))

theorem prefixBound_pos (s : Nat → Q) : ∀ n : Nat, (0 : Q) < prefixBound s n
  | 0 => by
    unfold prefixBound
    have h0 : (0 : Q) ≤ Q.abs (s 0) := Q.abs_nonneg _
    have h1 : (0 : Q) < 1 := Q.pow2_pos 0
    have hle : (0 : Q) ≤ Q.abs (s 0) + 0 := by
      have := Q.add_le_add h0 (Q.le_refl 0); rw [Q.add_zero 0] at this; exact this
    exact Q.lt_of_le_of_lt hle (Q.add_lt_add_left h1 _)
  | n + 1 => by
    unfold prefixBound
    have ih := prefixBound_pos s n
    have h0 := Q.abs_nonneg (s (n + 1))
    exact Q.lt_of_lt_of_le ih (by
      have := Q.add_le_add (Q.le_refl (prefixBound s n)) h0
      rw [Q.add_zero] at this; exact this)

theorem le_prefixBound (s : Nat → Q) : ∀ N i : Nat, i ≤ N → Q.abs (s i) ≤ prefixBound s N
  | 0, i, hi => by
    have : i = 0 := by omega
    subst this
    unfold prefixBound
    have h1 : (0 : Q) ≤ 1 := Q.le_of_lt (Q.pow2_pos 0)
    have := Q.add_le_add (Q.le_refl (Q.abs (s 0))) h1
    rw [Q.add_zero] at this; exact this
  | N + 1, i, hi => by
    unfold prefixBound
    by_cases h : i ≤ N
    · exact Q.le_trans (le_prefixBound s N i h) (by
        have := Q.add_le_add (Q.le_refl (prefixBound s N)) (Q.abs_nonneg (s (N + 1)))
        rw [Q.add_zero] at this; exact this)
    · have : i = N + 1 := by omega
      subst this
      have hp : (0 : Q) ≤ prefixBound s N := Q.le_of_lt (prefixBound_pos s N)
      have := Q.add_le_add hp (Q.le_refl (Q.abs (s (N + 1))))
      rw [Q.zero_add] at this; exact this

theorem bounded (f : CauchySeq) : ∃ B : Nat, ∀ n : Nat, Q.abs (f.seq n) ≤ Q.twoPow B := by
  obtain ⟨N, hN⟩ := f.isCauchy 0
  let M : Q := prefixBound f.seq N + 1
  obtain ⟨B, hB⟩ := Q.exists_twoPow_gt M
  refine ⟨B, fun n => ?_⟩
  have hMpos : (0 : Q) ≤ M := by
    have hp := Q.le_of_lt (prefixBound_pos f.seq N)
    have h1 := Q.le_of_lt (Q.pow2_pos 0)
    have := Q.add_le_add hp h1; rw [Q.add_zero] at this; exact this
  have hMB : M ≤ Q.twoPow B := by
    rw [← Q.abs_of_nonneg hMpos]; exact Q.le_of_lt hB
  apply Q.le_trans _ hMB
  by_cases hn : n ≤ N
  · have h1 := le_prefixBound f.seq N n hn
    have h2 : (0 : Q) ≤ 1 := Q.le_of_lt (Q.pow2_pos 0)
    have := Q.add_le_add h1 h2; rw [Q.add_zero] at this; exact this
  · have hge : N ≤ n := by omega
    have hdiff : Q.abs (f.seq n - f.seq N) < 1 := by
      have hp0 : Q.pow2 0 = 1 := by apply Q.sound; rfl
      rw [← hp0]; exact hN n hge N (Nat.le_refl N)
    have htri : Q.abs (f.seq n) ≤ Q.abs (f.seq N) + Q.abs (f.seq n - f.seq N) := by
      have hid : f.seq n = f.seq N + (f.seq n - f.seq N) := by
        simp only [Q.sub_eq_add_neg, Q.add_assoc, Q.add_left_comm, Q.add_comm,
                   Q.add_neg_cancel, Q.neg_add_cancel, Q.add_neg_cancel_left, Q.neg_add_cancel_left,
                   Q.add_zero, Q.zero_add]
      conv => lhs; rw [hid]
      exact Q.abs_add _ _
    exact Q.le_trans htri (Q.add_le_add (le_prefixBound f.seq N N (Nat.le_refl N)) (Q.le_of_lt hdiff))

def mul (f g : CauchySeq) : CauchySeq where
  seq n := f.seq n * g.seq n
  isCauchy k := by
    obtain ⟨Bf, hBf⟩ := bounded f
    obtain ⟨Bg, hBg⟩ := bounded g
    obtain ⟨N₁, h₁⟩ := f.isCauchy ((k + 1) + Bg)
    obtain ⟨N₂, h₂⟩ := g.isCauchy ((k + 1) + Bf)
    refine ⟨Nat.max N₁ N₂, fun m hm n hn => ?_⟩
    have hm1 : N₁ ≤ m := Nat.le_trans (Nat.le_max_left _ _) hm
    have hn1 : N₁ ≤ n := Nat.le_trans (Nat.le_max_left _ _) hn
    have hm2 : N₂ ≤ m := Nat.le_trans (Nat.le_max_right _ _) hm
    have hn2 : N₂ ≤ n := Nat.le_trans (Nat.le_max_right _ _) hn
    have hid : f.seq m * g.seq m - f.seq n * g.seq n =
               (f.seq m - f.seq n) * g.seq m + f.seq n * (g.seq m - g.seq n) := by
      rw [Q.sub_mul, Q.mul_sub]
      simp only [Q.sub_eq_add_neg, Q.add_assoc, Q.add_left_comm, Q.add_comm,
                 Q.add_neg_cancel, Q.neg_add_cancel, Q.add_neg_cancel_left, Q.neg_add_cancel_left,
                 Q.add_zero, Q.zero_add]
    rw [hid]
    have htri := Q.abs_add ((f.seq m - f.seq n) * g.seq m) (f.seq n * (g.seq m - g.seq n))
    rw [Q.abs_mul, Q.abs_mul] at htri
    have ht1 : Q.abs (f.seq m - f.seq n) * Q.abs (g.seq m) < Q.pow2 (k + 1) := by
      have ha := Q.mul_le_mul_of_nonneg_left (hBg m) (Q.abs_nonneg (f.seq m - f.seq n))
      have hb := Q.mul_lt_mul_of_pos_left (h₁ m hm1 n hn1) (Q.twoPow_pos Bg)
      rw [Q.mul_comm (Q.twoPow Bg) (Q.abs (f.seq m - f.seq n))] at hb
      have hc : Q.twoPow Bg * Q.pow2 ((k + 1) + Bg) = Q.pow2 (k + 1) := by
        rw [Q.pow2_add, Q.mul_comm (Q.pow2 (k + 1)), ← Q.mul_assoc, Q.twoPow_mul_pow2, Q.one_mul]
      rw [hc] at hb
      exact Q.lt_of_le_of_lt ha hb
    have ht2 : Q.abs (f.seq n) * Q.abs (g.seq m - g.seq n) < Q.pow2 (k + 1) := by
      have ha := Q.mul_le_mul_of_nonneg_left (hBf n) (Q.abs_nonneg (g.seq m - g.seq n))
      rw [Q.mul_comm (Q.abs (g.seq m - g.seq n)) (Q.abs (f.seq n))] at ha
      have hb := Q.mul_lt_mul_of_pos_left (h₂ m hm2 n hn2) (Q.twoPow_pos Bf)
      rw [Q.mul_comm (Q.abs (g.seq m - g.seq n)) (Q.twoPow Bf)] at ha
      have hc : Q.twoPow Bf * Q.pow2 ((k + 1) + Bf) = Q.pow2 (k + 1) := by
        rw [Q.pow2_add, Q.mul_comm (Q.pow2 (k + 1)), ← Q.mul_assoc, Q.twoPow_mul_pow2, Q.one_mul]
      rw [hc] at hb
      exact Q.lt_of_le_of_lt ha hb
    have hsum := Q.add_lt_add ht1 ht2
    rw [Q.pow2_succ_double] at hsum
    exact Q.lt_of_le_of_lt htri hsum

def equiv (f g : CauchySeq) : Prop :=
  ∀ k : Nat, ∃ N : Nat, ∀ n ≥ N, Q.abs (f.seq n - g.seq n) < Q.pow2 k

theorem equiv_of_pointwise {f g : CauchySeq} (h : ∀ n : Nat, f.seq n = g.seq n) : equiv f g := by
  intro k; refine ⟨0, fun n _ => ?_⟩
  rw [h n, Q.sub_self, Q.abs_of_nonneg (Q.le_refl 0)]
  exact Q.pow2_pos k

theorem equiv_refl (f : CauchySeq) : equiv f f := equiv_of_pointwise (fun _ => rfl)

theorem equiv_symm {f g : CauchySeq} (h : equiv f g) : equiv g f := by
  intro k; obtain ⟨N, hN⟩ := h k
  refine ⟨N, fun n hn => ?_⟩
  rw [Q.abs_sub_comm]; exact hN n hn

theorem equiv_trans {f g h : CauchySeq} (hfg : equiv f g) (hgh : equiv g h) : equiv f h := by
  intro k
  obtain ⟨N₁, h₁⟩ := hfg (k + 1)
  obtain ⟨N₂, h₂⟩ := hgh (k + 1)
  refine ⟨Nat.max N₁ N₂, fun n hn => ?_⟩
  have htri := sub_triangle (f.seq n) (g.seq n) (h.seq n)
  have hlt := Q.add_lt_add (h₁ n (Nat.le_trans (Nat.le_max_left _ _) hn))
                           (h₂ n (Nat.le_trans (Nat.le_max_right _ _) hn))
  rw [Q.pow2_succ_double] at hlt
  exact Q.lt_of_le_of_lt htri hlt

def setoid : Setoid CauchySeq where
  r := equiv
  iseqv := ⟨equiv_refl, equiv_symm, equiv_trans⟩

def posSeq (f : CauchySeq) : Prop :=
  ∃ k : Nat, ∃ N : Nat, ∀ n ≥ N, Q.pow2 k ≤ f.seq n

theorem posSeq_congr {f g : CauchySeq} (hfg : equiv f g) : posSeq f ↔ posSeq g := by
  have imp : ∀ {u v : CauchySeq}, equiv u v → posSeq u → posSeq v := by
    intro u v huv ⟨k, N₁, hN₁⟩
    obtain ⟨N₂, hN₂⟩ := huv (k + 1)
    refine ⟨k + 1, Nat.max N₁ N₂, fun n hn => ?_⟩
    have hu := hN₁ n (Nat.le_trans (Nat.le_max_left _ _) hn)
    have hd := hN₂ n (Nat.le_trans (Nat.le_max_right _ _) hn)
    rw [Q.abs_sub_comm] at hd
    have hlt := (Q.abs_lt_iff.mp hd).1
    -- -pow2(k+1) < v n - u n, and pow2(k+1) + pow2(k+1) = pow2 k ≤ u n
    have hsum := Q.add_lt_of_lt_of_le hlt hu
    have hl : -Q.pow2 (k + 1) + Q.pow2 k = Q.pow2 (k + 1) := by
      rw [← Q.pow2_succ_double k, ← Q.add_assoc, Q.neg_add_cancel, Q.zero_add]
    have hr : (v.seq n - u.seq n) + u.seq n = v.seq n := by
      simp only [Q.sub_eq_add_neg, Q.add_assoc, Q.neg_add_cancel, Q.add_zero]
    rw [hl, hr] at hsum
    exact Q.le_of_lt hsum
  exact ⟨imp hfg, imp (equiv_symm hfg)⟩

theorem trichotomy_zero (f : CauchySeq) : posSeq f ∨ equiv f (const 0) ∨ posSeq (neg f) := by
  open Classical in
  by_cases hp : posSeq f
  · exact Or.inl hp
  · by_cases hn : posSeq (neg f)
    · exact Or.inr (Or.inr hn)
    · refine Or.inr (Or.inl (fun k => ?_))
      obtain ⟨N, hN⟩ := f.isCauchy (k + 2)
      refine ⟨N, fun m hm => ?_⟩
      change Q.abs (f.seq m - 0) < Q.pow2 k
      have hsub0 : f.seq m - 0 = f.seq m := by
        have hz : -(0 : Q) = 0 := by have := Q.add_neg_cancel 0; rw [Q.zero_add] at this; exact this
        rw [Q.sub_eq_add_neg, hz, Q.add_zero]
      rw [hsub0]
      rcases Q.lt_trichotomy (Q.abs (f.seq m)) (Q.pow2 k) with hlt | heq | hgt
      · exact hlt
      · exfalso
        have hge : Q.pow2 k ≤ Q.abs (f.seq m) := by rw [heq]; exact Q.le_refl _
        have hp2 : Q.pow2 (k + 2) < Q.pow2 (k + 1) := by
          have := Q.add_lt_add_left (Q.pow2_pos (k + 2)) (Q.pow2 (k + 2))
          rw [Q.add_zero, Q.pow2_succ_double] at this; exact this
        have hneg2 : -Q.pow2 (k + 1) < -Q.pow2 (k + 2) := by
          have hha := Q.add_lt_add_right hp2 (-Q.pow2 (k + 1) + (-Q.pow2 (k + 2)))
          have h1' : Q.pow2 (k + 2) + (-Q.pow2 (k + 1) + -Q.pow2 (k + 2)) = -Q.pow2 (k + 1) := by
            simp only [Q.add_assoc, Q.add_left_comm, Q.add_comm, Q.add_neg_cancel, Q.neg_add_cancel,
                       Q.add_neg_cancel_left, Q.neg_add_cancel_left, Q.add_zero, Q.zero_add]
          have h2' : Q.pow2 (k + 1) + (-Q.pow2 (k + 1) + -Q.pow2 (k + 2)) = -Q.pow2 (k + 2) := by
            simp only [Q.add_assoc, Q.add_left_comm, Q.add_comm, Q.add_neg_cancel, Q.neg_add_cancel,
                       Q.add_neg_cancel_left, Q.neg_add_cancel_left, Q.add_zero, Q.zero_add]
          rw [h1', h2'] at hha; exact hha
        rcases Q.lt_trichotomy (f.seq m) 0 with hfm_neg | hfm_z | hfm_pos
        · rw [Q.abs_of_neg hfm_neg] at hge
          apply hn; refine ⟨k + 1, N, fun n hn' => ?_⟩
          change Q.pow2 (k + 1) ≤ -f.seq n
          have hd2 := (Q.abs_lt_iff.mp (hN m hm n hn')).1
          have hs2 := Q.add_lt_of_lt_of_le (Q.lt_trans hneg2 hd2) hge
          have hl : (f.seq m - f.seq n) + (-f.seq m) = -f.seq n := by
            simp only [Q.sub_eq_add_neg, Q.add_assoc, Q.add_left_comm, Q.add_comm,
                       Q.add_neg_cancel, Q.neg_add_cancel, Q.add_neg_cancel_left, Q.neg_add_cancel_left,
                       Q.add_zero, Q.zero_add]
          have hl2 : -Q.pow2 (k + 1) + Q.pow2 k = Q.pow2 (k + 1) := by
            rw [← Q.pow2_succ_double k, ← Q.add_assoc, Q.neg_add_cancel, Q.zero_add]
          rw [hl, hl2] at hs2; exact Q.le_of_lt hs2
        · rw [hfm_z, Q.abs_of_nonneg (Q.le_refl 0)] at hge
          exact hge (Q.pow2_pos k)
        · rw [Q.abs_of_nonneg (Q.le_of_lt hfm_pos)] at hge
          apply hp; refine ⟨k + 1, N, fun n hn' => ?_⟩
          have hd := (Q.abs_lt_iff.mp (by rw [Q.abs_sub_comm]; exact hN m hm n hn')).1
          have hs2 := Q.add_lt_of_lt_of_le (Q.lt_trans hneg2 hd) hge
          have hl2 : -Q.pow2 (k + 1) + Q.pow2 k = Q.pow2 (k + 1) := by
            rw [← Q.pow2_succ_double k, ← Q.add_assoc, Q.neg_add_cancel, Q.zero_add]
          have hr2 : (f.seq n - f.seq m) + f.seq m = f.seq n := by
            simp only [Q.sub_eq_add_neg, Q.add_assoc, Q.neg_add_cancel, Q.add_zero]
          rw [hl2, hr2] at hs2; exact Q.le_of_lt hs2
      · exfalso
        have hge : Q.pow2 k ≤ Q.abs (f.seq m) := Q.le_of_lt hgt
        have hp2 : Q.pow2 (k + 2) < Q.pow2 (k + 1) := by
          have := Q.add_lt_add_left (Q.pow2_pos (k + 2)) (Q.pow2 (k + 2))
          rw [Q.add_zero, Q.pow2_succ_double] at this; exact this
        have hneg2 : -Q.pow2 (k + 1) < -Q.pow2 (k + 2) := by
          have hha := Q.add_lt_add_right hp2 (-Q.pow2 (k + 1) + (-Q.pow2 (k + 2)))
          have h1' : Q.pow2 (k + 2) + (-Q.pow2 (k + 1) + -Q.pow2 (k + 2)) = -Q.pow2 (k + 1) := by
            simp only [Q.add_assoc, Q.add_left_comm, Q.add_comm, Q.add_neg_cancel, Q.neg_add_cancel,
                       Q.add_neg_cancel_left, Q.neg_add_cancel_left, Q.add_zero, Q.zero_add]
          have h2' : Q.pow2 (k + 1) + (-Q.pow2 (k + 1) + -Q.pow2 (k + 2)) = -Q.pow2 (k + 2) := by
            simp only [Q.add_assoc, Q.add_left_comm, Q.add_comm, Q.add_neg_cancel, Q.neg_add_cancel,
                       Q.add_neg_cancel_left, Q.neg_add_cancel_left, Q.add_zero, Q.zero_add]
          rw [h1', h2'] at hha; exact hha
        rcases Q.lt_trichotomy (f.seq m) 0 with hfm_neg | hfm_z | hfm_pos
        · rw [Q.abs_of_neg hfm_neg] at hge
          apply hn; refine ⟨k + 1, N, fun n hn' => ?_⟩
          change Q.pow2 (k + 1) ≤ -f.seq n
          have hd2 := (Q.abs_lt_iff.mp (hN m hm n hn')).1
          have hs2 := Q.add_lt_of_lt_of_le (Q.lt_trans hneg2 hd2) hge
          have hl : (f.seq m - f.seq n) + (-f.seq m) = -f.seq n := by
            simp only [Q.sub_eq_add_neg, Q.add_assoc, Q.add_left_comm, Q.add_comm,
                       Q.add_neg_cancel, Q.neg_add_cancel, Q.add_neg_cancel_left, Q.neg_add_cancel_left,
                       Q.add_zero, Q.zero_add]
          have hl2 : -Q.pow2 (k + 1) + Q.pow2 k = Q.pow2 (k + 1) := by
            rw [← Q.pow2_succ_double k, ← Q.add_assoc, Q.neg_add_cancel, Q.zero_add]
          rw [hl, hl2] at hs2; exact Q.le_of_lt hs2
        · rw [hfm_z, Q.abs_of_nonneg (Q.le_refl 0)] at hge
          exact hge (Q.pow2_pos k)
        · rw [Q.abs_of_nonneg (Q.le_of_lt hfm_pos)] at hge
          apply hp; refine ⟨k + 1, N, fun n hn' => ?_⟩
          have hd := (Q.abs_lt_iff.mp (by rw [Q.abs_sub_comm]; exact hN m hm n hn')).1
          have hs2 := Q.add_lt_of_lt_of_le (Q.lt_trans hneg2 hd) hge
          have hl2 : -Q.pow2 (k + 1) + Q.pow2 k = Q.pow2 (k + 1) := by
            rw [← Q.pow2_succ_double k, ← Q.add_assoc, Q.neg_add_cancel, Q.zero_add]
          have hr2 : (f.seq n - f.seq m) + f.seq m = f.seq n := by
            simp only [Q.sub_eq_add_neg, Q.add_assoc, Q.neg_add_cancel, Q.add_zero]
          rw [hl2, hr2] at hs2; exact Q.le_of_lt hs2

theorem add_congr {f₁ f₂ g₁ g₂ : CauchySeq} (hf : equiv f₁ f₂) (hg : equiv g₁ g₂) :
    equiv (add f₁ g₁) (add f₂ g₂) := by
  intro k
  obtain ⟨N₁, h₁⟩ := hf (k + 1)
  obtain ⟨N₂, h₂⟩ := hg (k + 1)
  refine ⟨Nat.max N₁ N₂, fun n hn => ?_⟩
  change Q.abs ((f₁.seq n + g₁.seq n) - (f₂.seq n + g₂.seq n)) < Q.pow2 k
  rw [sub_rearrange4]
  have hle := Q.abs_add (f₁.seq n - f₂.seq n) (g₁.seq n - g₂.seq n)
  have hlt := Q.add_lt_add (h₁ n (Nat.le_trans (Nat.le_max_left _ _) hn))
                           (h₂ n (Nat.le_trans (Nat.le_max_right _ _) hn))
  rw [Q.pow2_succ_double] at hlt
  exact Q.lt_of_le_of_lt hle hlt

theorem neg_congr {f₁ f₂ : CauchySeq} (hf : equiv f₁ f₂) : equiv (neg f₁) (neg f₂) := by
  intro k; obtain ⟨N, h⟩ := hf k
  refine ⟨N, fun n hn => ?_⟩
  change Q.abs (-f₁.seq n - (-f₂.seq n)) < Q.pow2 k
  have hid : -f₁.seq n - (-f₂.seq n) = -(f₁.seq n - f₂.seq n) := by
    simp only [Q.sub_eq_add_neg, Q.neg_add, Q.neg_neg, Q.add_comm]
  rw [hid, Q.abs_neg]; exact h n hn

theorem mul_congr {f₁ f₂ g₁ g₂ : CauchySeq} (hf : equiv f₁ f₂) (hg : equiv g₁ g₂) :
    equiv (mul f₁ g₁) (mul f₂ g₂) := by
  obtain ⟨Bf, hBf⟩ := bounded f₂
  obtain ⟨Bg, hBg⟩ := bounded g₁
  intro k
  obtain ⟨N₁, h₁⟩ := hf ((k + 1) + Bg)
  obtain ⟨N₂, h₂⟩ := hg ((k + 1) + Bf)
  refine ⟨Nat.max N₁ N₂, fun n hn => ?_⟩
  change Q.abs (f₁.seq n * g₁.seq n - f₂.seq n * g₂.seq n) < Q.pow2 k
  have hid : f₁.seq n * g₁.seq n - f₂.seq n * g₂.seq n =
             (f₁.seq n - f₂.seq n) * g₁.seq n + f₂.seq n * (g₁.seq n - g₂.seq n) := by
    rw [Q.sub_mul, Q.mul_sub]
    simp only [Q.sub_eq_add_neg, Q.add_assoc, Q.add_left_comm, Q.add_comm,
               Q.add_neg_cancel, Q.neg_add_cancel, Q.add_neg_cancel_left, Q.neg_add_cancel_left,
               Q.add_zero, Q.zero_add]
  rw [hid]
  have htri := Q.abs_add ((f₁.seq n - f₂.seq n) * g₁.seq n) (f₂.seq n * (g₁.seq n - g₂.seq n))
  rw [Q.abs_mul, Q.abs_mul] at htri
  have ht1 : Q.abs (f₁.seq n - f₂.seq n) * Q.abs (g₁.seq n) < Q.pow2 (k + 1) := by
    have ha := Q.mul_le_mul_of_nonneg_left (hBg n) (Q.abs_nonneg (f₁.seq n - f₂.seq n))
    have hb := Q.mul_lt_mul_of_pos_left (h₁ n (Nat.le_trans (Nat.le_max_left _ _) hn)) (Q.twoPow_pos Bg)
    rw [Q.mul_comm (Q.twoPow Bg) (Q.abs (f₁.seq n - f₂.seq n))] at hb
    have hc : Q.twoPow Bg * Q.pow2 ((k + 1) + Bg) = Q.pow2 (k + 1) := by
      rw [Q.pow2_add, Q.mul_comm (Q.pow2 (k + 1)), ← Q.mul_assoc, Q.twoPow_mul_pow2, Q.one_mul]
    rw [hc] at hb; exact Q.lt_of_le_of_lt ha hb
  have ht2 : Q.abs (f₂.seq n) * Q.abs (g₁.seq n - g₂.seq n) < Q.pow2 (k + 1) := by
    have ha := Q.mul_le_mul_of_nonneg_left (hBf n) (Q.abs_nonneg (g₁.seq n - g₂.seq n))
    rw [Q.mul_comm (Q.abs (g₁.seq n - g₂.seq n)) (Q.abs (f₂.seq n)),
        Q.mul_comm (Q.abs (g₁.seq n - g₂.seq n)) (Q.twoPow Bf)] at ha
    have hb := Q.mul_lt_mul_of_pos_left (h₂ n (Nat.le_trans (Nat.le_max_right _ _) hn)) (Q.twoPow_pos Bf)
    have hc : Q.twoPow Bf * Q.pow2 ((k + 1) + Bf) = Q.pow2 (k + 1) := by
      rw [Q.pow2_add, Q.mul_comm (Q.pow2 (k + 1)), ← Q.mul_assoc, Q.twoPow_mul_pow2, Q.one_mul]
    rw [hc] at hb; exact Q.lt_of_le_of_lt ha hb
  have hsum := Q.add_lt_add ht1 ht2
  rw [Q.pow2_succ_double] at hsum
  exact Q.lt_of_le_of_lt htri hsum

theorem sep_from_zero {f : CauchySeq} (hne : ¬ equiv f (const 0)) :
    ∃ k : Nat, ∃ N : Nat, ∀ n ≥ N, Q.pow2 k ≤ Q.abs (f.seq n) := by
  rcases trichotomy_zero f with ⟨k, N, hN⟩ | heq | ⟨k, N, hN⟩
  · exact ⟨k, N, fun n hn => Q.le_trans (hN n hn) (Q.le_abs_self _)⟩
  · exact False.elim (hne heq)
  · refine ⟨k, N, fun n hn => ?_⟩
    have := hN n hn
    change Q.pow2 k ≤ -f.seq n at this
    exact Q.le_trans this (Q.neg_le_abs_self _)

theorem q_inv_sub_inv {a b : Q} (ha : a ≠ 0) (hb : b ≠ 0) :
    Q.inv a - Q.inv b = (b - a) * (Q.inv a * Q.inv b) := by
  have hprod : (b - a) * (Q.inv a * Q.inv b) = b * (Q.inv a * Q.inv b) - a * (Q.inv a * Q.inv b) :=
    Q.sub_mul b a (Q.inv a * Q.inv b)
  have h1 : b * (Q.inv a * Q.inv b) = Q.inv a := by
    calc
      b * (Q.inv a * Q.inv b) = Q.inv a * (b * Q.inv b) := by
        simp only [Q.mul_assoc, Q.mul_left_comm, Q.mul_comm]
      _ = Q.inv a * 1 := by rw [Q.mul_inv_cancel hb]
      _ = Q.inv a := Q.mul_one _
  have h2 : a * (Q.inv a * Q.inv b) = Q.inv b := by
    calc
      a * (Q.inv a * Q.inv b) = (a * Q.inv a) * Q.inv b := (Q.mul_assoc _ _ _).symm
      _ = 1 * Q.inv b := by rw [Q.mul_inv_cancel ha]
      _ = Q.inv b := Q.one_mul _
  rw [hprod, h1, h2]

theorem q_abs_inv_le_twoPow {a : Q} {k : Nat} (ha : Q.pow2 k ≤ Q.abs a) :
    Q.abs (Q.inv a) ≤ Q.twoPow k := by
  have hpos : (0 : Q) < Q.abs a := Q.lt_of_lt_of_le (Q.pow2_pos k) ha
  have hne : a ≠ 0 := by
    intro hz; rw [hz, Q.abs_of_nonneg (Q.le_refl 0)] at hpos
    exact Q.lt_irrefl 0 hpos
  have hprod : Q.abs a * Q.abs (Q.inv a) = 1 := by
    have hp0 : Q.pow2 0 = 1 := by apply Q.sound; rfl
    have h1pos : (0 : Q) ≤ 1 := by rw [← hp0]; exact Q.le_of_lt (Q.pow2_pos 0)
    rw [← Q.abs_mul, Q.mul_inv_cancel hne, Q.abs_of_nonneg h1pos]
  have hle := Q.mul_le_mul_of_nonneg_left ha (Q.abs_nonneg (Q.inv a))
  rw [Q.mul_comm _ (Q.abs a), hprod] at hle
  have hmul := Q.mul_le_mul_of_nonneg_left hle (Q.le_of_lt (Q.twoPow_pos k))
  rw [Q.mul_one, Q.mul_comm (Q.abs (Q.inv a)), ← Q.mul_assoc, Q.twoPow_mul_pow2, Q.one_mul] at hmul
  exact hmul

noncomputable def inv (f : CauchySeq) : CauchySeq :=
  open Classical in
  if h : equiv f (const 0) then
    const 0
  else
    let k0 := Classical.choose (sep_from_zero h)
    let N0 := Classical.choose (Classical.choose_spec (sep_from_zero h))
    have hN0 : ∀ n ≥ N0, Q.pow2 k0 ≤ Q.abs (f.seq n) :=
      Classical.choose_spec (Classical.choose_spec (sep_from_zero h))
    { seq := fun n => if n < N0 then 0 else Q.inv (f.seq n)
      isCauchy := fun j => by
        obtain ⟨N₁, h₁⟩ := f.isCauchy (j + (k0 + k0))
        refine ⟨Nat.max N0 N₁, fun m hm n hn => ?_⟩
        have hm0 : N0 ≤ m := Nat.le_trans (Nat.le_max_left _ _) hm
        have hn0 : N0 ≤ n := Nat.le_trans (Nat.le_max_left _ _) hn
        have hm1 : N₁ ≤ m := Nat.le_trans (Nat.le_max_right _ _) hm
        have hn1 : N₁ ≤ n := Nat.le_trans (Nat.le_max_right _ _) hn
        have hmlt : ¬ (m < N0) := by omega
        have hnlt : ¬ (n < N0) := by omega
        rw [if_neg hmlt, if_neg hnlt]
        have hfm_ne : f.seq m ≠ 0 := by
          intro hz; have hp := Q.lt_of_lt_of_le (Q.pow2_pos k0) (hN0 m hm0)
          rw [hz, Q.abs_of_nonneg (Q.le_refl 0)] at hp; exact Q.lt_irrefl 0 hp
        have hfn_ne : f.seq n ≠ 0 := by
          intro hz; have hp := Q.lt_of_lt_of_le (Q.pow2_pos k0) (hN0 n hn0)
          rw [hz, Q.abs_of_nonneg (Q.le_refl 0)] at hp; exact Q.lt_irrefl 0 hp
        rw [q_inv_sub_inv hfm_ne hfn_ne, Q.abs_mul, Q.abs_mul]
        have him := q_abs_inv_le_twoPow (hN0 m hm0)
        have hin := q_abs_inv_le_twoPow (hN0 n hn0)
        have hprod_le : Q.abs (Q.inv (f.seq m)) * Q.abs (Q.inv (f.seq n)) ≤ Q.twoPow k0 * Q.twoPow k0 := by
          have ha := Q.mul_le_mul_of_nonneg_left hin (Q.abs_nonneg (Q.inv (f.seq m)))
          have hb := Q.mul_le_mul_of_nonneg_left him (Q.le_of_lt (Q.twoPow_pos k0))
          rw [Q.mul_comm (Q.twoPow k0) (Q.abs (Q.inv (f.seq m)))] at hb
          exact Q.le_trans ha hb
        have hstep1 := Q.mul_le_mul_of_nonneg_left hprod_le (Q.abs_nonneg (f.seq n - f.seq m))
        have hstep2 := Q.mul_lt_mul_of_pos_left (h₁ n hn1 m hm1)
                         (Q.mul_pos (Q.twoPow_pos k0) (Q.twoPow_pos k0))
        have hcancel : (Q.twoPow k0 * Q.twoPow k0) * Q.pow2 (j + (k0 + k0)) = Q.pow2 j := by
          rw [Q.pow2_add j (k0 + k0), Q.pow2_add k0 k0]
          calc
            (Q.twoPow k0 * Q.twoPow k0) * (Q.pow2 j * (Q.pow2 k0 * Q.pow2 k0))
                = Q.pow2 j * ((Q.twoPow k0 * Q.pow2 k0) * (Q.twoPow k0 * Q.pow2 k0)) := by
                  simp only [Q.mul_assoc, Q.mul_left_comm, Q.mul_comm]
            _ = Q.pow2 j := by rw [Q.twoPow_mul_pow2, Q.one_mul, Q.mul_one]
        rw [hcancel] at hstep2
        rw [Q.mul_comm (Q.twoPow k0 * Q.twoPow k0) (Q.abs (f.seq n - f.seq m))] at hstep2
        exact Q.lt_of_le_of_lt hstep1 hstep2 }

theorem mul_inv_equiv_one {f : CauchySeq} (hne : ¬ equiv f (const 0)) :
    equiv (mul f (inv f)) (const 1) := by
  unfold inv
  rw [dif_neg hne]
  let k0 := Classical.choose (sep_from_zero hne)
  let N0 := Classical.choose (Classical.choose_spec (sep_from_zero hne))
  have hN0 : ∀ n ≥ N0, Q.pow2 k0 ≤ Q.abs (f.seq n) :=
    Classical.choose_spec (Classical.choose_spec (sep_from_zero hne))
  intro j
  refine ⟨N0, fun n hn => ?_⟩
  have hnlt : ¬ (n < N0) := by omega
  change Q.abs (f.seq n * (if n < N0 then 0 else Q.inv (f.seq n)) - 1) < Q.pow2 j
  rw [if_neg hnlt]
  have hfn_ne : f.seq n ≠ 0 := by
    intro hz; have hp := Q.lt_of_lt_of_le (Q.pow2_pos k0) (hN0 n hn)
    rw [hz, Q.abs_of_nonneg (Q.le_refl 0)] at hp; exact Q.lt_irrefl 0 hp
  rw [Q.mul_inv_cancel hfn_ne, Q.sub_self, Q.abs_of_nonneg (Q.le_refl 0)]
  exact Q.pow2_pos j

theorem inv_congr {f g : CauchySeq} (hfg : equiv f g) : equiv (inv f) (inv g) := by
  open Classical in
  by_cases hf0 : equiv f (const 0)
  · have hg0 : equiv g (const 0) := equiv_trans (equiv_symm hfg) hf0
    unfold inv; rw [dif_pos hf0, dif_pos hg0]; exact equiv_refl _
  · have hg0 : ¬ equiv g (const 0) := fun h => hf0 (equiv_trans hfg h)
    -- inv f ≈ inv f * (g * inv g) ≈ (inv f * f) * inv g ≈ inv g
    have h1 : equiv (inv f) (mul (inv f) (mul g (inv g))) := by
      have hm := mul_congr (equiv_refl (inv f)) (equiv_symm (mul_inv_equiv_one hg0))
      exact equiv_trans (equiv_of_pointwise (fun n => (Q.mul_one _).symm)) hm
    have h2 : equiv (mul (inv f) (mul g (inv g))) (mul (mul f (inv f)) (inv g)) := by
      have ha : equiv (mul (inv f) (mul g (inv g))) (mul (mul (inv f) g) (inv g)) :=
        equiv_of_pointwise (fun n => (Q.mul_assoc _ _ _).symm)
      have hb : equiv (mul (mul (inv f) g) (inv g)) (mul (mul (inv f) f) (inv g)) :=
        mul_congr (mul_congr (equiv_refl _) (equiv_symm hfg)) (equiv_refl _)
      have hc : equiv (mul (mul (inv f) f) (inv g)) (mul (mul f (inv f)) (inv g)) :=
        equiv_of_pointwise (fun n => by
          change ((inv f).seq n * f.seq n) * (inv g).seq n = (f.seq n * (inv f).seq n) * (inv g).seq n
          rw [Q.mul_comm ((inv f).seq n) (f.seq n)])
      exact equiv_trans ha (equiv_trans hb hc)
    have h3 : equiv (mul (mul f (inv f)) (inv g)) (inv g) :=
      equiv_trans (mul_congr (mul_inv_equiv_one hf0) (equiv_refl _))
                  (equiv_of_pointwise (fun n => Q.one_mul _))
    exact equiv_trans h1 (equiv_trans h2 h3)

end CauchySeq

def R : Type := Quotient CauchySeq.setoid

namespace R

def mk (f : CauchySeq) : R := Quotient.mk CauchySeq.setoid f
def ofQ (q : Q) : R := mk (CauchySeq.const q)
def ofInt (n : Int) : R := ofQ (Q.ofInt n)
def ofNat (n : Nat) : R := ofQ (Q.ofNat n)

instance (n : Nat) : OfNat R n := ⟨ofNat n⟩

theorem sound {f g : CauchySeq} (h : CauchySeq.equiv f g) : mk f = mk g := Quotient.sound h
theorem exact {f g : CauchySeq} (h : mk f = mk g) : CauchySeq.equiv f g := Quotient.exact h

def add : R → R → R :=
  Quotient.lift₂ (fun f g => mk (CauchySeq.add f g)) (fun _ _ _ _ hf hg => sound (CauchySeq.add_congr hf hg))

def neg : R → R :=
  Quotient.lift (fun f => mk (CauchySeq.neg f)) (fun _ _ hf => sound (CauchySeq.neg_congr hf))

def sub (x y : R) : R := add x (neg y)

def mul : R → R → R :=
  Quotient.lift₂ (fun f g => mk (CauchySeq.mul f g)) (fun _ _ _ _ hf hg => sound (CauchySeq.mul_congr hf hg))

noncomputable def inv : R → R :=
  Quotient.lift (fun f => mk (CauchySeq.inv f)) (fun _ _ hf => sound (CauchySeq.inv_congr hf))

def lt : R → R → Prop :=
  Quotient.lift₂ (fun f g => CauchySeq.posSeq (CauchySeq.sub g f))
    (fun _ _ _ _ hf hg => propext (CauchySeq.posSeq_congr (CauchySeq.add_congr hg (CauchySeq.neg_congr hf))))

def le (x y : R) : Prop := ¬ lt y x

instance : Add R := ⟨add⟩
instance : Neg R := ⟨neg⟩
instance : Sub R := ⟨sub⟩
instance : Mul R := ⟨mul⟩
instance : LT R := ⟨lt⟩
instance : LE R := ⟨le⟩

theorem add_comm (x y : R) : x + y = y + x := by
  induction x using Quotient.ind; induction y using Quotient.ind
  exact sound (CauchySeq.equiv_of_pointwise (fun _ => Q.add_comm _ _))

theorem add_assoc (x y z : R) : (x + y) + z = x + (y + z) := by
  induction x using Quotient.ind; induction y using Quotient.ind; induction z using Quotient.ind
  exact sound (CauchySeq.equiv_of_pointwise (fun _ => Q.add_assoc _ _ _))

theorem add_left_comm (x y z : R) : x + (y + z) = y + (x + z) := by
  rw [← add_assoc, add_comm x y, add_assoc]

theorem zero_add (x : R) : (0 : R) + x = x := by
  induction x using Quotient.ind
  exact sound (CauchySeq.equiv_of_pointwise (fun _ => Q.zero_add _))

theorem add_zero (x : R) : x + (0 : R) = x := by rw [add_comm, zero_add]

theorem neg_add_cancel (x : R) : (-x) + x = 0 := by
  induction x using Quotient.ind
  exact sound (CauchySeq.equiv_of_pointwise (fun _ => Q.neg_add_cancel _))

theorem add_neg_cancel (x : R) : x + (-x) = 0 := by rw [add_comm, neg_add_cancel]

theorem add_neg_cancel_left (x y : R) : x + (-x + y) = y := by
  rw [← add_assoc, add_neg_cancel, zero_add]

theorem neg_add_cancel_left (x y : R) : -x + (x + y) = y := by
  rw [← add_assoc, neg_add_cancel, zero_add]

theorem sub_eq_add_neg (x y : R) : x - y = x + (-y) := rfl
theorem sub_self (x : R) : x - x = 0 := add_neg_cancel x

theorem neg_neg (x : R) : -(-x) = x := by
  induction x using Quotient.ind
  exact sound (CauchySeq.equiv_of_pointwise (fun _ => Q.neg_neg _))

theorem neg_add (x y : R) : -(x + y) = -x + (-y) := by
  induction x using Quotient.ind; induction y using Quotient.ind
  exact sound (CauchySeq.equiv_of_pointwise (fun _ => Q.neg_add _ _))

theorem neg_sub (x y : R) : -(x - y) = y - x := by
  rw [sub_eq_add_neg, neg_add, neg_neg, add_comm]; rfl

theorem mul_comm (x y : R) : x * y = y * x := by
  induction x using Quotient.ind; induction y using Quotient.ind
  exact sound (CauchySeq.equiv_of_pointwise (fun _ => Q.mul_comm _ _))

theorem mul_assoc (x y z : R) : (x * y) * z = x * (y * z) := by
  induction x using Quotient.ind; induction y using Quotient.ind; induction z using Quotient.ind
  exact sound (CauchySeq.equiv_of_pointwise (fun _ => Q.mul_assoc _ _ _))

theorem mul_left_comm (x y z : R) : x * (y * z) = y * (x * z) := by
  rw [← mul_assoc, mul_comm x y, mul_assoc]

theorem one_mul (x : R) : (1 : R) * x = x := by
  induction x using Quotient.ind
  exact sound (CauchySeq.equiv_of_pointwise (fun _ => Q.one_mul _))

theorem mul_one (x : R) : x * (1 : R) = x := by rw [mul_comm, one_mul]

theorem zero_mul (x : R) : (0 : R) * x = 0 := by
  induction x using Quotient.ind
  exact sound (CauchySeq.equiv_of_pointwise (fun _ => Q.zero_mul _))

theorem mul_zero (x : R) : x * (0 : R) = 0 := by rw [mul_comm, zero_mul]

theorem neg_mul (x y : R) : (-x) * y = -(x * y) := by
  induction x using Quotient.ind; induction y using Quotient.ind
  exact sound (CauchySeq.equiv_of_pointwise (fun _ => Q.neg_mul _ _))

theorem mul_neg (x y : R) : x * (-y) = -(x * y) := by rw [mul_comm, neg_mul, mul_comm]

theorem left_distrib (x y z : R) : x * (y + z) = x * y + x * z := by
  induction x using Quotient.ind; induction y using Quotient.ind; induction z using Quotient.ind
  exact sound (CauchySeq.equiv_of_pointwise (fun _ => Q.left_distrib _ _ _))

theorem right_distrib (x y z : R) : (x + y) * z = x * z + y * z := by
  rw [mul_comm, left_distrib, mul_comm z x, mul_comm z y]

theorem sub_mul (x y z : R) : (x - y) * z = x * z - y * z := by
  rw [sub_eq_add_neg, right_distrib, neg_mul]; rfl

theorem mul_sub (x y z : R) : x * (y - z) = x * y - x * z := by
  rw [sub_eq_add_neg, left_distrib, mul_neg]; rfl

theorem one_ne_zero : (1 : R) ≠ (0 : R) := by
  intro h
  obtain ⟨N, hN⟩ := exact h 1
  have hd := hN N (Nat.le_refl N)
  change Q.abs ((1 : Q) - 0) < Q.pow2 1 at hd
  have h10 : (1 : Q) - 0 = 1 := by
    have hz : -(0 : Q) = 0 := by have := Q.add_neg_cancel 0; rw [Q.zero_add] at this; exact this
    rw [Q.sub_eq_add_neg, hz, Q.add_zero]
  have hp0 : Q.pow2 0 = 1 := by apply Q.sound; rfl
  have h1pos : (0 : Q) ≤ 1 := by rw [← hp0]; exact Q.le_of_lt (Q.pow2_pos 0)
  rw [h10, Q.abs_of_nonneg h1pos] at hd
  have hgt : Q.pow2 1 < 1 := by
    have := Q.add_lt_add_left (Q.pow2_pos 1) (Q.pow2 1)
    rw [Q.add_zero, Q.pow2_succ_double, hp0] at this; exact this
  exact Q.lt_irrefl 1 (Q.lt_trans hd hgt)

theorem mul_inv_cancel {x : R} (hx : x ≠ 0) : x * inv x = 1 := by
  induction x using Quotient.ind
  rename_i f
  have hne : ¬ CauchySeq.equiv f (CauchySeq.const 0) := fun h => hx (sound h)
  exact sound (CauchySeq.mul_inv_equiv_one hne)

theorem mul_eq_zero {x y : R} (h : x * y = 0) : x = 0 ∨ y = 0 := by
  open Classical in
  by_cases hx : x = 0
  · exact Or.inl hx
  · refine Or.inr ?_
    calc
      y = (inv x * x) * y := by rw [mul_comm (inv x) x, mul_inv_cancel hx, one_mul]
      _ = inv x * (x * y) := mul_assoc _ _ _
      _ = 0 := by rw [h, mul_zero]

theorem lt_irrefl (x : R) : ¬ (x < x) := by
  induction x using Quotient.ind
  rename_i f
  rintro ⟨k, N, hN⟩
  have h := hN N (Nat.le_refl N)
  change Q.pow2 k ≤ f.seq N + (-f.seq N) at h
  rw [Q.add_neg_cancel] at h
  exact h (Q.pow2_pos k)

theorem lt_trans {x y z : R} (hab : x < y) (hbc : y < z) : x < z := by
  induction x using Quotient.ind; induction y using Quotient.ind; induction z using Quotient.ind
  rename_i f g h
  rcases hab with ⟨k₁, N₁, h₁⟩
  rcases hbc with ⟨k₂, N₂, h₂⟩
  refine ⟨k₁ + k₂, Nat.max N₁ N₂, fun n hn => ?_⟩
  have ha := h₁ n (Nat.le_trans (Nat.le_max_left _ _) hn)
  have hb := h₂ n (Nat.le_trans (Nat.le_max_right _ _) hn)
  change Q.pow2 k₁ ≤ g.seq n + -f.seq n at ha
  change Q.pow2 k₂ ≤ h.seq n + -g.seq n at hb
  change Q.pow2 (k₁ + k₂) ≤ h.seq n + -f.seq n
  have hsum := Q.add_le_add ha hb
  have hr : (g.seq n + -f.seq n) + (h.seq n + -g.seq n) = h.seq n + -f.seq n := by
    simp only [Q.add_assoc, Q.add_left_comm, Q.add_comm, Q.add_neg_cancel, Q.neg_add_cancel,
               Q.add_neg_cancel_left, Q.neg_add_cancel_left, Q.add_zero, Q.zero_add]
  rw [hr] at hsum
  have hl : Q.pow2 (k₁ + k₂) ≤ Q.pow2 k₁ + Q.pow2 k₂ := by
    have hp1 : Q.pow2 (k₁ + k₂) ≤ Q.pow2 k₁ := Q.pow2_le_of_le (Nat.le_add_right _ _)
    have hp2 : (0 : Q) ≤ Q.pow2 k₂ := Q.le_of_lt (Q.pow2_pos k₂)
    have := Q.add_le_add hp1 hp2
    rw [Q.add_zero] at this; exact this
  exact Q.le_trans hl hsum

theorem lt_trichotomy (x y : R) : x < y ∨ x = y ∨ y < x := by
  induction x using Quotient.ind; induction y using Quotient.ind
  rename_i f g
  rcases CauchySeq.trichotomy_zero (CauchySeq.sub g f) with hp | hz | hn
  · exact Or.inl hp
  · refine Or.inr (Or.inl (sound ?_))
    intro k; obtain ⟨N, hN⟩ := hz k
    refine ⟨N, fun n hn => ?_⟩
    have hd := hN n hn
    change Q.abs ((g.seq n + -f.seq n) - 0) < Q.pow2 k at hd
    have hid : (g.seq n + -f.seq n) - 0 = -(f.seq n - g.seq n) := by
      have hz0 : -(0 : Q) = 0 := by have := Q.add_neg_cancel 0; rw [Q.zero_add] at this; exact this
      simp only [Q.sub_eq_add_neg, hz0, Q.add_zero, Q.zero_add, Q.neg_add, Q.neg_neg, Q.add_comm]
    rw [hid, Q.abs_neg] at hd; exact hd
  · refine Or.inr (Or.inr ?_)
    have heq : CauchySeq.equiv (CauchySeq.neg (CauchySeq.sub g f)) (CauchySeq.sub f g) :=
      CauchySeq.equiv_of_pointwise (fun n => by
        change -(g.seq n + -f.seq n) = f.seq n + -g.seq n
        rw [Q.neg_add, Q.neg_neg, Q.add_comm])
    exact (CauchySeq.posSeq_congr heq).mp hn

theorem le_iff_lt_or_eq {x y : R} : x ≤ y ↔ x < y ∨ x = y := by
  change ¬ (y < x) ↔ x < y ∨ x = y
  constructor
  · intro h
    rcases lt_trichotomy x y with hlt | heq | hgt
    · exact Or.inl hlt
    · exact Or.inr heq
    · exact False.elim (h hgt)
  · rintro (hlt | rfl)
    · exact fun hgt => lt_irrefl x (lt_trans hlt hgt)
    · exact lt_irrefl x

theorem le_refl (x : R) : x ≤ x := le_iff_lt_or_eq.mpr (Or.inr rfl)
theorem le_of_lt {x y : R} (h : x < y) : x ≤ y := le_iff_lt_or_eq.mpr (Or.inl h)

theorem le_antisymm {x y : R} (h1 : x ≤ y) (h2 : y ≤ x) : x = y := by
  rcases le_iff_lt_or_eq.mp h1 with hlt | heq
  · exact False.elim (h2 hlt)
  · exact heq

theorem lt_of_lt_of_le {x y z : R} (h1 : x < y) (h2 : y ≤ z) : x < z := by
  rcases le_iff_lt_or_eq.mp h2 with hlt | rfl
  · exact lt_trans h1 hlt
  · exact h1

theorem lt_of_le_of_lt {x y z : R} (h1 : x ≤ y) (h2 : y < z) : x < z := by
  rcases le_iff_lt_or_eq.mp h1 with hlt | rfl
  · exact lt_trans hlt h2
  · exact h2

theorem le_trans {x y z : R} (h1 : x ≤ y) (h2 : y ≤ z) : x ≤ z := by
  rcases le_iff_lt_or_eq.mp h1 with hlt | rfl
  · exact le_of_lt (lt_of_lt_of_le hlt h2)
  · exact h2

theorem add_lt_add_left {x y : R} (h : x < y) (z : R) : z + x < z + y := by
  induction x using Quotient.ind; induction y using Quotient.ind; induction z using Quotient.ind
  rename_i f g w
  rcases h with ⟨k, N, hN⟩
  refine ⟨k, N, fun n hn => ?_⟩
  change Q.pow2 k ≤ (w.seq n + g.seq n) + -(w.seq n + f.seq n)
  have hid : (w.seq n + g.seq n) + -(w.seq n + f.seq n) = g.seq n + -f.seq n := by
    rw [Q.neg_add]
    simp only [Q.add_assoc, Q.add_left_comm, Q.add_comm, Q.add_neg_cancel, Q.neg_add_cancel,
               Q.add_neg_cancel_left, Q.neg_add_cancel_left, Q.add_zero, Q.zero_add]
  rw [hid]; exact hN n hn

theorem add_lt_add_right {x y : R} (h : x < y) (z : R) : x + z < y + z := by
  rw [add_comm x z, add_comm y z]; exact add_lt_add_left h z

theorem add_lt_add {a b c d : R} (h1 : a < b) (h2 : c < d) : a + c < b + d :=
  lt_trans (add_lt_add_right h1 c) (add_lt_add_left h2 b)

theorem add_le_add {a b c d : R} (h1 : a ≤ b) (h2 : c ≤ d) : a + c ≤ b + d := by
  rcases le_iff_lt_or_eq.mp h1 with hlt1 | rfl
  · rcases le_iff_lt_or_eq.mp h2 with hlt2 | rfl
    · exact le_of_lt (add_lt_add hlt1 hlt2)
    · exact le_of_lt (add_lt_add_right hlt1 c)
  · rcases le_iff_lt_or_eq.mp h2 with hlt2 | rfl
    · exact le_of_lt (add_lt_add_left hlt2 a)
    · exact le_refl _

theorem sub_pos {x y : R} : (0 : R) < y - x ↔ x < y := by
  constructor
  · intro h
    have h1 := add_lt_add_left h x
    rw [add_zero, sub_eq_add_neg, ← add_assoc, add_comm x y, add_assoc, add_neg_cancel, add_zero] at h1
    exact h1
  · intro h
    have h1 := add_lt_add_right h (-x)
    rw [add_neg_cancel] at h1; exact h1

theorem mul_pos {x y : R} (hx : (0 : R) < x) (hy : (0 : R) < y) : (0 : R) < x * y := by
  induction x using Quotient.ind; induction y using Quotient.ind
  rename_i f g
  rcases hx with ⟨k₁, N₁, h₁⟩
  rcases hy with ⟨k₂, N₂, h₂⟩
  refine ⟨k₁ + k₂, Nat.max N₁ N₂, fun n hn => ?_⟩
  have hf := h₁ n (Nat.le_trans (Nat.le_max_left _ _) hn)
  have hg := h₂ n (Nat.le_trans (Nat.le_max_right _ _) hn)
  have hz0 : -(0 : Q) = 0 := by have := Q.add_neg_cancel 0; rw [Q.zero_add] at this; exact this
  change Q.pow2 k₁ ≤ f.seq n + -(0 : Q) at hf
  change Q.pow2 k₂ ≤ g.seq n + -(0 : Q) at hg
  rw [hz0, Q.add_zero] at hf hg
  change Q.pow2 (k₁ + k₂) ≤ f.seq n * g.seq n + -(0 : Q)
  rw [hz0, Q.add_zero, Q.pow2_add]
  have ha := Q.mul_le_mul_of_nonneg_left hg (Q.le_trans (Q.le_of_lt (Q.pow2_pos k₁)) hf)
  have hb := Q.mul_le_mul_of_nonneg_left hf (Q.le_of_lt (Q.pow2_pos k₂))
  rw [Q.mul_comm (Q.pow2 k₂) (f.seq n), Q.mul_comm (Q.pow2 k₂) (Q.pow2 k₁)] at hb
  exact Q.le_trans hb ha

theorem mul_nonneg {x y : R} (hx : (0 : R) ≤ x) (hy : (0 : R) ≤ y) : (0 : R) ≤ x * y := by
  rcases le_iff_lt_or_eq.mp hx with hxp | rfl
  · rcases le_iff_lt_or_eq.mp hy with hyp | rfl
    · exact le_of_lt (mul_pos hxp hyp)
    · rw [mul_zero]; exact le_refl 0
  · rw [zero_mul]; exact le_refl 0

theorem mul_lt_mul_of_pos_left {a b c : R} (h : a < b) (hc : (0 : R) < c) : c * a < c * b := by
  rw [← sub_pos, ← mul_sub]
  exact mul_pos hc (sub_pos.mpr h)

theorem mul_le_mul_of_nonneg_left {a b c : R} (h : a ≤ b) (hc : (0 : R) ≤ c) : c * a ≤ c * b := by
  rcases le_iff_lt_or_eq.mp hc with hcp | rfl
  · rcases le_iff_lt_or_eq.mp h with hab | rfl
    · exact le_of_lt (mul_lt_mul_of_pos_left hab hcp)
    · exact le_refl _
  · rw [zero_mul, zero_mul]; exact le_refl 0

theorem ofQ_add (a b : Q) : ofQ (a + b) = ofQ a + ofQ b :=
  sound (CauchySeq.equiv_refl _)

theorem ofQ_neg (a : Q) : ofQ (-a) = -ofQ a :=
  sound (CauchySeq.equiv_refl _)

theorem ofQ_sub (a b : Q) : ofQ (a - b) = ofQ a - ofQ b :=
  sound (CauchySeq.equiv_refl _)

theorem ofQ_mul (a b : Q) : ofQ (a * b) = ofQ a * ofQ b :=
  sound (CauchySeq.equiv_refl _)

theorem ofQ_lt_iff {a b : Q} : ofQ a < ofQ b ↔ a < b := by
  constructor
  · rintro ⟨k, N, hN⟩
    have h := hN N (Nat.le_refl N)
    change Q.pow2 k ≤ b - a at h
    exact Q.sub_pos.mp (Q.lt_of_lt_of_le (Q.pow2_pos k) h)
  · intro h
    obtain ⟨k, hk⟩ := Q.exists_pow2_lt (Q.sub_pos.mpr h)
    exact ⟨k, 0, fun _ _ => Q.le_of_lt hk⟩

theorem ofQ_le_iff {a b : Q} : ofQ a ≤ ofQ b ↔ a ≤ b := by
  change ¬ (ofQ b < ofQ a) ↔ ¬ (b < a)
  rw [ofQ_lt_iff]

noncomputable def abs (x : R) : R :=
  open Classical in if (0 : R) ≤ x then x else -x

theorem abs_of_nonneg {x : R} (hx : (0 : R) ≤ x) : abs x = x := by
  unfold abs; rw [if_pos hx]

theorem abs_of_neg {x : R} (hx : x < (0 : R)) : abs x = -x := by
  unfold abs
  have hn : ¬ ((0 : R) ≤ x) := fun h => h hx
  rw [if_neg hn]

theorem abs_nonneg (x : R) : (0 : R) ≤ abs x := by
  rcases lt_trichotomy x 0 with hn | rfl | hp
  · rw [abs_of_neg hn]
    have h1 := add_lt_add_right hn (-x)
    rw [add_neg_cancel, zero_add] at h1; exact le_of_lt h1
  · rw [abs_of_nonneg (le_refl 0)]; exact le_refl 0
  · rw [abs_of_nonneg (le_of_lt hp)]; exact le_of_lt hp

theorem le_abs_self (x : R) : x ≤ abs x := by
  rcases lt_trichotomy x 0 with hn | rfl | hp
  · exact le_trans (le_of_lt hn) (abs_nonneg x)
  · rw [abs_of_nonneg (le_refl 0)]; exact le_refl 0
  · rw [abs_of_nonneg (le_of_lt hp)]; exact le_refl x

theorem neg_le_abs_self (x : R) : -x ≤ abs x := by
  rcases lt_trichotomy x 0 with hn | rfl | hp
  · rw [abs_of_neg hn]; exact le_refl _
  · have hz : -(0 : R) = 0 := by have := add_neg_cancel 0; rw [zero_add] at this; exact this
    rw [hz, abs_of_nonneg (le_refl 0)]; exact le_refl 0
  · rw [abs_of_nonneg (le_of_lt hp)]
    have hnx : -x < 0 := by
      have := add_lt_add_right hp (-x); rw [zero_add, add_neg_cancel] at this; exact this
    exact le_of_lt (lt_trans hnx hp)

theorem abs_neg (x : R) : abs (-x) = abs x := by
  rcases lt_trichotomy x 0 with hn | rfl | hp
  · have hnx : (0 : R) < -x := by
      have := add_lt_add_right hn (-x); rw [add_neg_cancel, zero_add] at this; exact this
    rw [abs_of_nonneg (le_of_lt hnx), abs_of_neg hn]
  · have hz : -(0 : R) = 0 := by have := add_neg_cancel 0; rw [zero_add] at this; exact this
    rw [hz]
  · have hnx : -x < 0 := by
      have := add_lt_add_right hp (-x); rw [zero_add, add_neg_cancel] at this; exact this
    rw [abs_of_neg hnx, neg_neg, abs_of_nonneg (le_of_lt hp)]

theorem abs_add (x y : R) : abs (x + y) ≤ abs x + abs y := by
  rcases lt_trichotomy (x + y) 0 with hn | hz | hp
  · rw [abs_of_neg hn, neg_add]
    exact add_le_add (neg_le_abs_self x) (neg_le_abs_self y)
  · rw [hz, abs_of_nonneg (le_refl 0)]
    have := add_le_add (abs_nonneg x) (abs_nonneg y)
    rw [zero_add] at this; exact this
  · rw [abs_of_nonneg (le_of_lt hp)]
    exact add_le_add (le_abs_self x) (le_abs_self y)

theorem abs_mul (x y : R) : abs (x * y) = abs x * abs y := by
  rcases lt_trichotomy x 0 with hx | rfl | hx
  · rcases lt_trichotomy y 0 with hy | rfl | hy
    · have hnx : (0 : R) < -x := by have := add_lt_add_right hx (-x); rw [add_neg_cancel, zero_add] at this; exact this
      have hny : (0 : R) < -y := by have := add_lt_add_right hy (-y); rw [add_neg_cancel, zero_add] at this; exact this
      have hxy : (0 : R) < x * y := by
        have hp := mul_pos hnx hny; rw [neg_mul, mul_neg, neg_neg] at hp; exact hp
      rw [abs_of_neg hx, abs_of_neg hy, abs_of_nonneg (le_of_lt hxy), neg_mul, mul_neg, neg_neg]
    · rw [mul_zero, abs_of_nonneg (le_refl 0), mul_zero]
    · have hnx : (0 : R) < -x := by have := add_lt_add_right hx (-x); rw [add_neg_cancel, zero_add] at this; exact this
      have hxy : x * y < 0 := by
        have hp := mul_pos hnx hy; rw [neg_mul] at hp
        have := add_lt_add_right hp (x * y); rw [zero_add, neg_add_cancel] at this; exact this
      rw [abs_of_neg hx, abs_of_nonneg (le_of_lt hy), abs_of_neg hxy, neg_mul]
  · rw [zero_mul, abs_of_nonneg (le_refl 0), zero_mul]
  · rcases lt_trichotomy y 0 with hy | rfl | hy
    · have hny : (0 : R) < -y := by have := add_lt_add_right hy (-y); rw [add_neg_cancel, zero_add] at this; exact this
      have hxy : x * y < 0 := by
        have hp := mul_pos hx hny; rw [mul_neg] at hp
        have := add_lt_add_right hp (x * y); rw [zero_add, neg_add_cancel] at this; exact this
      rw [abs_of_nonneg (le_of_lt hx), abs_of_neg hy, abs_of_neg hxy, mul_neg]
    · rw [mul_zero, abs_of_nonneg (le_refl 0), mul_zero]
    · rw [abs_of_nonneg (le_of_lt hx), abs_of_nonneg (le_of_lt hy), abs_of_nonneg (le_of_lt (mul_pos hx hy))]

theorem dense_ofQ {x y : R} (h : x < y) : ∃ q : Q, x < ofQ q ∧ ofQ q < y := by
  induction x using Quotient.ind; induction y using Quotient.ind
  rename_i f g
  rcases h with ⟨k, N₀, hN₀⟩
  obtain ⟨N₁, hf⟩ := f.isCauchy (k + 2)
  obtain ⟨N₂, hg⟩ := g.isCauchy (k + 2)
  let M := Nat.max N₀ (Nat.max N₁ N₂)
  have hM0 : N₀ ≤ M := Nat.le_max_left _ _
  have hM1 : N₁ ≤ M := Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _)
  have hM2 : N₂ ≤ M := Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _)
  let q : Q := f.seq M + Q.pow2 (k + 1)
  refine ⟨q, ?_, ?_⟩
  · refine ⟨k + 2, M, fun n hn => ?_⟩
    change Q.pow2 (k + 2) ≤ (f.seq M + Q.pow2 (k + 1)) + -f.seq n
    have hd := (Q.abs_lt_iff.mp (hf M hM1 n (Nat.le_trans hM1 hn))).1
    -- -pow2(k+2) < f M - f n, add pow2(k+1) = pow2(k+2) + pow2(k+2)
    have hsum := Q.add_lt_add_right hd (Q.pow2 (k + 1))
    have hl : -Q.pow2 (k + 2) + Q.pow2 (k + 1) = Q.pow2 (k + 2) := by
      rw [← Q.pow2_succ_double (k + 1), ← Q.add_assoc, Q.neg_add_cancel, Q.zero_add]
    have hr : (f.seq M - f.seq n) + Q.pow2 (k + 1) = (f.seq M + Q.pow2 (k + 1)) + -f.seq n := by
      simp only [Q.sub_eq_add_neg, Q.add_assoc, Q.add_left_comm, Q.add_comm]
    rw [hl, hr] at hsum; exact Q.le_of_lt hsum
  · refine ⟨k + 2, M, fun n hn => ?_⟩
    change Q.pow2 (k + 2) ≤ g.seq n + -(f.seq M + Q.pow2 (k + 1))
    have hsep : Q.pow2 k ≤ g.seq M + -f.seq M := hN₀ M hM0
    have hd := (Q.abs_lt_iff.mp (hg n (Nat.le_trans hM2 hn) M hM2)).1
    -- -pow2(k+2) < g n - g M, and pow2(k+1) ≤ (g M - f M) - pow2(k+1)
    have hsep' : Q.pow2 (k + 1) ≤ (g.seq M + -f.seq M) + -Q.pow2 (k + 1) := by
      have := Q.add_le_add hsep (Q.le_refl (-Q.pow2 (k + 1)))
      have hl : Q.pow2 k + -Q.pow2 (k + 1) = Q.pow2 (k + 1) := by
        rw [← Q.pow2_succ_double k, Q.add_assoc, Q.add_neg_cancel, Q.add_zero]
      rw [hl] at this; exact this
    have hsum := Q.add_lt_of_lt_of_le hd hsep'
    have hl : -Q.pow2 (k + 2) + Q.pow2 (k + 1) = Q.pow2 (k + 2) := by
      rw [← Q.pow2_succ_double (k + 1), ← Q.add_assoc, Q.neg_add_cancel, Q.zero_add]
    have hr : (g.seq n - g.seq M) + ((g.seq M + -f.seq M) + -Q.pow2 (k + 1)) =
              g.seq n + -(f.seq M + Q.pow2 (k + 1)) := by
      rw [Q.neg_add]
      simp only [Q.sub_eq_add_neg, Q.add_assoc, Q.add_left_comm, Q.add_comm,
                 Q.add_neg_cancel, Q.neg_add_cancel, Q.add_neg_cancel_left, Q.neg_add_cancel_left,
                 Q.add_zero, Q.zero_add]
    rw [hl, hr] at hsum; exact Q.le_of_lt hsum

theorem exists_pow2_lt {ε : R} (hε : (0 : R) < ε) : ∃ k : Nat, ofQ (Q.pow2 k) < ε := by
  obtain ⟨q, h0q, hqε⟩ := dense_ofQ hε
  have hqp : (0 : Q) < q := ofQ_lt_iff.mp h0q
  obtain ⟨k, hk⟩ := Q.exists_pow2_lt hqp
  exact ⟨k, lt_trans (ofQ_lt_iff.mpr hk) hqε⟩

theorem exists_twoPow_gt (x : R) : ∃ B : Nat, x < ofQ (Q.twoPow B) := by
  have hx1 : x < x + 1 := by
    have h01 : (0 : R) < 1 := ofQ_lt_iff.mpr (Q.pow2_pos 0)
    have := add_lt_add_left h01 x; rw [add_zero] at this; exact this
  obtain ⟨q, hxq, _⟩ := dense_ofQ hx1
  obtain ⟨B, hB⟩ := Q.exists_twoPow_gt q
  have hqB : q < Q.twoPow B := Q.lt_of_le_of_lt (Q.le_abs_self q) hB
  exact ⟨B, lt_trans hxq (ofQ_lt_iff.mpr hqB)⟩

end R

/-! ### Complex Field `C = R × R` -/

structure Complex where
  re : R
  im : R

namespace Complex

def ofR (r : R) : Complex := ⟨r, 0⟩
def ofInt (n : Int) : Complex := ofR (R.ofInt n)

instance (n : Nat) : OfNat Complex n := ⟨ofR (R.ofNat n)⟩

def add (z w : Complex) : Complex := ⟨z.re + w.re, z.im + w.im⟩
def neg (z : Complex) : Complex := ⟨-z.re, -z.im⟩
def sub (z w : Complex) : Complex := add z (neg w)
def mul (z w : Complex) : Complex := ⟨z.re * w.re - z.im * w.im, z.re * w.im + z.im * w.re⟩

instance : Add Complex := ⟨add⟩
instance : Neg Complex := ⟨neg⟩
instance : Sub Complex := ⟨sub⟩
instance : Mul Complex := ⟨mul⟩

theorem ext {z w : Complex} (hre : z.re = w.re) (him : z.im = w.im) : z = w := by
  cases z; cases w; dsimp only at *; subst hre; subst him; rfl

theorem add_comm (z w : Complex) : z + w = w + z := ext (R.add_comm _ _) (R.add_comm _ _)
theorem add_assoc (u v w : Complex) : (u + v) + w = u + (v + w) := ext (R.add_assoc _ _ _) (R.add_assoc _ _ _)
theorem zero_add (z : Complex) : (0 : Complex) + z = z := ext (R.zero_add _) (R.zero_add _)
theorem add_zero (z : Complex) : z + (0 : Complex) = z := ext (R.add_zero _) (R.add_zero _)
theorem add_neg_cancel (z : Complex) : z + (-z) = 0 := ext (R.add_neg_cancel _) (R.add_neg_cancel _)

theorem mul_comm (z w : Complex) : z * w = w * z :=
  ext (by change z.re * w.re - z.im * w.im = w.re * z.re - w.im * z.im; rw [R.mul_comm z.re, R.mul_comm z.im])
      (by change z.re * w.im + z.im * w.re = w.re * z.im + w.im * z.re; rw [R.mul_comm z.re, R.mul_comm z.im, R.add_comm])

theorem mul_assoc (u v w : Complex) : (u * v) * w = u * (v * w) := by
  apply ext
  · change (u.re * v.re - u.im * v.im) * w.re - (u.re * v.im + u.im * v.re) * w.im =
           u.re * (v.re * w.re - v.im * w.im) - u.im * (v.re * w.im + v.im * w.re)
    rw [R.sub_mul, R.right_distrib, R.mul_sub, R.left_distrib]
    simp only [R.sub_eq_add_neg, R.neg_add, R.mul_assoc, R.add_assoc, R.add_left_comm, R.add_comm]
  · change (u.re * v.re - u.im * v.im) * w.im + (u.re * v.im + u.im * v.re) * w.re =
           u.re * (v.re * w.im + v.im * w.re) + u.im * (v.re * w.re - v.im * w.im)
    rw [R.sub_mul, R.right_distrib, R.left_distrib, R.mul_sub]
    simp only [R.sub_eq_add_neg, R.mul_assoc, R.add_assoc, R.add_left_comm, R.add_comm]

theorem one_mul (z : Complex) : (1 : Complex) * z = z := by
  apply ext
  · change (1 : R) * z.re - (0 : R) * z.im = z.re
    rw [R.one_mul, R.zero_mul, R.sub_eq_add_neg]
    have hz : -(0 : R) = 0 := by have := R.add_neg_cancel 0; rw [R.zero_add] at this; exact this
    rw [hz, R.add_zero]
  · change (1 : R) * z.im + (0 : R) * z.re = z.im
    rw [R.one_mul, R.zero_mul, R.add_zero]

theorem mul_one (z : Complex) : z * (1 : Complex) = z := by rw [mul_comm, one_mul]

theorem left_distrib (u v w : Complex) : u * (v + w) = u * v + u * w := by
  apply ext
  · change u.re * (v.re + w.re) - u.im * (v.im + w.im) =
           (u.re * v.re - u.im * v.im) + (u.re * w.re - u.im * w.im)
    rw [R.left_distrib, R.left_distrib]
    simp only [R.sub_eq_add_neg, R.neg_add, R.add_assoc, R.add_left_comm, R.add_comm]
  · change u.re * (v.im + w.im) + u.im * (v.re + w.re) =
           (u.re * v.im + u.im * v.re) + (u.re * w.im + u.im * w.re)
    rw [R.left_distrib, R.left_distrib]
    simp only [R.add_assoc, R.add_left_comm, R.add_comm]

theorem right_distrib (u v w : Complex) : (u + v) * w = u * w + v * w := by
  rw [mul_comm, left_distrib, mul_comm w u, mul_comm w v]

def normSq (z : Complex) : R := z.re * z.re + z.im * z.im

theorem sq_nonneg (x : R) : (0 : R) ≤ x * x := by
  have hsq : R.abs x * R.abs x = x * x := by
    rcases R.lt_trichotomy x 0 with hx | rfl | hx
    · rw [R.abs_of_neg hx, R.neg_mul, R.mul_neg, R.neg_neg]
    · rw [R.abs_of_nonneg (R.le_refl 0)]
    · rw [R.abs_of_nonneg (R.le_of_lt hx)]
  have hnn := R.mul_nonneg (R.abs_nonneg x) (R.abs_nonneg x)
  rw [hsq] at hnn; exact hnn

theorem normSq_pos_of_ne_zero {z : Complex} (hz : z ≠ 0) : (0 : R) < normSq z := by
  unfold normSq
  have hre := sq_nonneg z.re
  have him := sq_nonneg z.im
  rcases R.le_iff_lt_or_eq.mp hre with hrep | hrez
  · have := R.add_le_add (R.le_refl (z.re * z.re)) him
    rw [R.add_zero] at this
    exact R.lt_of_lt_of_le hrep this
  · rcases R.le_iff_lt_or_eq.mp him with himp | himz
    · rw [← hrez, R.zero_add]; exact himp
    · exfalso; apply hz
      have zr : z.re = 0 := by rcases R.mul_eq_zero hrez.symm with h | h <;> exact h
      have zi : z.im = 0 := by rcases R.mul_eq_zero himz.symm with h | h <;> exact h
      exact ext zr zi

theorem mul_eq_zero {z w : Complex} (h : z * w = 0) : z = 0 ∨ w = 0 := by
  open Classical in
  by_cases hz : z = 0
  · exact Or.inl hz
  · by_cases hw : w = 0
    · exact Or.inr hw
    · exfalso
      -- normSq (z * w) = normSq z * normSq w
      have hn : normSq (z * w) = normSq z * normSq w := by
        unfold normSq; change (z.re * w.re - z.im * w.im) * (z.re * w.re - z.im * w.im) +
                              (z.re * w.im + z.im * w.re) * (z.re * w.im + z.im * w.re) =
                              (z.re * z.re + z.im * z.im) * (w.re * w.re + w.im * w.im)
        let a := z.re * (z.re * (w.re * w.re))
        let b := w.re * (w.re * (z.im * z.im))
        let c := z.re * (z.re * (w.im * w.im))
        let d := z.im * (z.im * (w.im * w.im))
        let m := z.re * (w.re * (z.im * w.im))
        have hL : (z.re * w.re - z.im * w.im) * (z.re * w.re - z.im * w.im) +
                  (z.re * w.im + z.im * w.re) * (z.re * w.im + z.im * w.re) =
                  ((a + d) + (-m + -m)) + ((c + b) + (m + m)) := by
          rw [R.sub_mul, R.mul_sub, R.mul_sub, R.right_distrib, R.left_distrib, R.left_distrib]
          simp only [R.sub_eq_add_neg, R.neg_add, R.neg_neg, R.mul_assoc, R.mul_left_comm, R.mul_comm]
          simp only [a, b, c, d, m, R.add_assoc, R.add_left_comm, R.add_comm]
        have hR : (z.re * z.re + z.im * z.im) * (w.re * w.re + w.im * w.im) =
                  (a + c) + (b + d) := by
          rw [R.right_distrib, R.left_distrib, R.left_distrib]
          simp only [R.mul_assoc, R.mul_left_comm, R.mul_comm]
          simp only [a, b, c, d, R.add_assoc, R.add_left_comm, R.add_comm]
        rw [hL, hR]
        calc
          ((a + d) + (-m + -m)) + ((c + b) + (m + m))
              = ((a + c) + (b + d)) + ((m + -m) + (m + -m)) := by
                simp only [R.add_assoc, R.add_left_comm, R.add_comm]
          _ = (a + c) + (b + d) := by rw [R.add_neg_cancel, R.add_zero, R.add_zero]
      have hz0 : normSq (z * w) = 0 := by
        rw [h]; unfold normSq; change (0 : R) * 0 + (0 : R) * 0 = 0
        rw [R.zero_mul, R.add_zero]
      have hp : (0 : R) < normSq z * normSq w :=
        R.mul_pos (normSq_pos_of_ne_zero hz) (normSq_pos_of_ne_zero hw)
      rw [← hn, hz0] at hp
      exact R.lt_irrefl 0 hp

theorem ofR_add (a b : R) : ofR (a + b) = ofR a + ofR b :=
  ext rfl (R.add_zero 0).symm

theorem ofR_neg (a : R) : ofR (-a) = -ofR a := by
  apply ext rfl
  have hz : -(0 : R) = 0 := by have := R.add_neg_cancel 0; rw [R.zero_add] at this; exact this
  exact hz.symm

theorem ofR_sub (a b : R) : ofR (a - b) = ofR a - ofR b := by
  change ofR (a + (-b)) = ofR a + (-ofR b)
  rw [ofR_add, ofR_neg]

theorem ofR_mul (a b : R) : ofR (a * b) = ofR a * ofR b := by
  apply ext
  · change a * b = a * b - (0 : R) * 0
    rw [R.zero_mul, R.sub_eq_add_neg]
    have hz : -(0 : R) = 0 := by have := R.add_neg_cancel 0; rw [R.zero_add] at this; exact this
    rw [hz, R.add_zero]
  · change (0 : R) = a * 0 + (0 : R) * b
    rw [R.mul_zero, R.zero_mul, R.add_zero]

theorem ofR_eq_zero {a : R} : ofR a = 0 ↔ a = 0 :=
  ⟨fun h => congrArg Complex.re h, fun h => by subst h; rfl⟩

end Complex

/-! ## 3. Polynomials over `R` and `Complex`, Formal Derivative, Factorization, and IVT -/

inductive ListNodup {α : Type u} : List α → Prop where
  | nil : ListNodup []
  | cons {x : α} {xs : List α} : (∀ y ∈ xs, x ≠ y) → ListNodup xs → ListNodup (x :: xs)

abbrev Poly := List R

namespace Poly

def coeff : Poly → Nat → R
  | [], _ => 0
  | c :: _, 0 => c
  | _ :: cs, k + 1 => coeff cs k

def PolyEq (P Q : Poly) : Prop :=
  ∀ k : Nat, coeff P k = coeff Q k

theorem polyEq_refl (P : Poly) : PolyEq P P := fun _ => rfl
theorem polyEq_symm {P Q : Poly} (h : PolyEq P Q) : PolyEq Q P := fun k => (h k).symm
theorem polyEq_trans {P Q S : Poly} (h1 : PolyEq P Q) (h2 : PolyEq Q S) : PolyEq P S :=
  fun k => (h1 k).trans (h2 k)

def eval : Poly → R → R
  | [], _ => 0
  | c :: cs, x => c + x * eval cs x

def evalC : Poly → Complex → Complex
  | [], _ => 0
  | c :: cs, z => Complex.ofR c + z * evalC cs z

theorem evalC_ofR : ∀ (P : Poly) (x : R), evalC P (Complex.ofR x) = Complex.ofR (eval P x)
  | [], _ => rfl
  | c :: cs, x => by
    unfold evalC eval
    rw [evalC_ofR cs x, ← Complex.ofR_mul, ← Complex.ofR_add]

theorem eval_eq_zero_of_coeff_zero : ∀ (P : Poly) (x : R), (∀ k : Nat, coeff P k = 0) → eval P x = 0
  | [], _, _ => rfl
  | c :: cs, x, h => by
    unfold eval
    have hc : c = 0 := h 0
    have ih := eval_eq_zero_of_coeff_zero cs x (fun k => h (k + 1))
    rw [hc, ih, R.mul_zero, R.add_zero]

theorem evalC_eq_zero_of_coeff_zero : ∀ (P : Poly) (z : Complex), (∀ k : Nat, coeff P k = 0) → evalC P z = 0
  | [], _, _ => rfl
  | c :: cs, z, h => by
    unfold evalC
    have hc : c = 0 := h 0
    have ih := evalC_eq_zero_of_coeff_zero cs z (fun k => h (k + 1))
    have hz : z * 0 = 0 := by
      apply Complex.ext
      · change z.re * 0 - z.im * 0 = 0; rw [R.mul_zero, R.mul_zero, R.sub_self]
      · change z.re * 0 + z.im * 0 = 0; rw [R.mul_zero, R.mul_zero, R.add_zero]
    rw [hc, ih, hz]; exact Complex.add_zero 0

theorem eval_eq_of_polyEq : ∀ {P Q : Poly}, PolyEq P Q → ∀ x : R, eval P x = eval Q x
  | [], Q, h, x => (eval_eq_zero_of_coeff_zero Q x (fun k => (h k).symm)).symm
  | P, [], h, x => eval_eq_zero_of_coeff_zero P x h
  | c :: cs, d :: ds, h, x => by
    unfold eval
    have hc : c = d := h 0
    have ih := eval_eq_of_polyEq (P := cs) (Q := ds) (fun k => h (k + 1)) x
    rw [hc, ih]

theorem evalC_eq_of_polyEq : ∀ {P Q : Poly}, PolyEq P Q → ∀ z : Complex, evalC P z = evalC Q z
  | [], Q, h, z => (evalC_eq_zero_of_coeff_zero Q z (fun k => (h k).symm)).symm
  | P, [], h, z => evalC_eq_zero_of_coeff_zero P z h
  | c :: cs, d :: ds, h, z => by
    unfold evalC
    have hc : c = d := h 0
    have ih := evalC_eq_of_polyEq (P := cs) (Q := ds) (fun k => h (k + 1)) z
    rw [hc, ih]

def add : Poly → Poly → Poly
  | [], Q => Q
  | P, [] => P
  | c :: cs, d :: ds => (c + d) :: add cs ds

def scale (s : R) : Poly → Poly
  | [] => []
  | c :: cs => (s * c) :: scale s cs

def neg (P : Poly) : Poly := scale (-1) P
def sub (P Q : Poly) : Poly := add P (neg Q)
def mulX (P : Poly) : Poly := 0 :: P
def mulLinear (r : R) (P : Poly) : Poly := sub (mulX P) (scale r P)

theorem coeff_add : ∀ (P Q : Poly) (k : Nat), coeff (add P Q) k = coeff P k + coeff Q k
  | [], Q, k => by cases Q <;> (unfold add; change coeff _ k = 0 + coeff _ k; rw [R.zero_add])
  | c :: cs, [], 0 => by unfold add coeff; rw [R.add_zero]
  | c :: cs, [], k + 1 => by unfold add coeff; change coeff cs k = coeff cs k + 0; rw [R.add_zero]
  | c :: cs, d :: ds, 0 => rfl
  | c :: cs, d :: ds, k + 1 => coeff_add cs ds k

theorem coeff_scale (s : R) : ∀ (P : Poly) (k : Nat), coeff (scale s P) k = s * coeff P k
  | [], _ => by unfold scale coeff; rw [R.mul_zero]
  | _ :: _, 0 => rfl
  | _ :: cs, k + 1 => coeff_scale s cs k

theorem coeff_neg (P : Poly) (k : Nat) : coeff (neg P) k = -coeff P k := by
  unfold neg; rw [coeff_scale, R.neg_mul, R.one_mul]

theorem coeff_sub (P Q : Poly) (k : Nat) : coeff (sub P Q) k = coeff P k - coeff Q k := by
  unfold sub; rw [coeff_add, coeff_neg]; rfl

theorem coeff_mulX (P : Poly) : coeff (mulX P) 0 = 0 ∧ ∀ k : Nat, coeff (mulX P) (k + 1) = coeff P k :=
  ⟨rfl, fun _ => rfl⟩

theorem eval_add : ∀ (P Q : Poly) (x : R), eval (add P Q) x = eval P x + eval Q x
  | [], Q, x => by cases Q <;> (unfold add; change eval _ x = 0 + eval _ x; rw [R.zero_add])
  | c :: cs, [], x => by unfold add; change eval (c :: cs) x = eval (c :: cs) x + 0; rw [R.add_zero]
  | c :: cs, d :: ds, x => by
    unfold add eval
    rw [eval_add cs ds x, R.left_distrib]
    simp only [R.add_assoc, R.add_left_comm, R.add_comm]

theorem eval_scale (s : R) : ∀ (P : Poly) (x : R), eval (scale s P) x = s * eval P x
  | [], _ => by unfold scale eval; rw [R.mul_zero]
  | c :: cs, x => by
    unfold scale eval
    rw [eval_scale s cs x, R.left_distrib]
    simp only [R.mul_assoc, R.mul_left_comm, R.mul_comm]

theorem eval_neg (P : Poly) (x : R) : eval (neg P) x = -eval P x := by
  unfold neg; rw [eval_scale, R.neg_mul, R.one_mul]

theorem eval_sub (P Q : Poly) (x : R) : eval (sub P Q) x = eval P x - eval Q x := by
  unfold sub; rw [eval_add, eval_neg]; rfl

theorem eval_mulX (P : Poly) (x : R) : eval (mulX P) x = x * eval P x := by
  change (0 : R) + x * eval P x = x * eval P x; rw [R.zero_add]

theorem eval_mulLinear (r : R) (P : Poly) (x : R) : eval (mulLinear r P) x = (x - r) * eval P x := by
  unfold mulLinear; rw [eval_sub, eval_mulX, eval_scale, R.sub_mul]

theorem evalC_add : ∀ (P Q : Poly) (z : Complex), evalC (add P Q) z = evalC P z + evalC Q z
  | [], Q, z => by cases Q <;> (unfold add; change evalC _ z = 0 + evalC _ z; rw [Complex.zero_add])
  | c :: cs, [], z => by unfold add; change evalC (c :: cs) z = evalC (c :: cs) z + 0; rw [Complex.add_zero]
  | c :: cs, d :: ds, z => by
    unfold add evalC
    rw [evalC_add cs ds z, Complex.ofR_add, Complex.left_distrib]
    have ha : ∀ a b u v : Complex, (a + b) + (u + v) = (a + u) + (b + v) := fun a b u v => by
      rw [Complex.add_assoc, ← Complex.add_assoc b u v, Complex.add_comm b u,
          Complex.add_assoc u b v, ← Complex.add_assoc]
    exact ha _ _ _ _

theorem evalC_scale (s : R) : ∀ (P : Poly) (z : Complex), evalC (scale s P) z = Complex.ofR s * evalC P z
  | [], _ => by
    change (0 : Complex) = Complex.ofR s * (0 : Complex)
    apply Complex.ext
    · change (0 : R) = s * 0 - (0 : R) * 0; rw [R.mul_zero, R.mul_zero, R.sub_self]
    · change (0 : R) = s * 0 + (0 : R) * 0; rw [R.mul_zero, R.mul_zero, R.add_zero]
  | c :: cs, z => by
    unfold scale evalC
    rw [evalC_scale s cs z, Complex.ofR_mul, Complex.left_distrib]
    rw [← Complex.mul_assoc z (Complex.ofR s), Complex.mul_comm z (Complex.ofR s), Complex.mul_assoc]

theorem evalC_neg (P : Poly) (z : Complex) : evalC (neg P) z = -evalC P z := by
  unfold neg; rw [evalC_scale]
  apply Complex.ext
  · change (-1 : R) * (evalC P z).re - (0 : R) * (evalC P z).im = -(evalC P z).re
    rw [R.zero_mul, R.sub_eq_add_neg, R.neg_mul, R.one_mul]
    have hz : -(0 : R) = 0 := by have := R.add_neg_cancel 0; rw [R.zero_add] at this; exact this
    rw [hz, R.add_zero]
  · change (-1 : R) * (evalC P z).im + (0 : R) * (evalC P z).re = -(evalC P z).im
    rw [R.zero_mul, R.add_zero, R.neg_mul, R.one_mul]

theorem evalC_mulX (P : Poly) (z : Complex) : evalC (mulX P) z = z * evalC P z := by
  change (0 : Complex) + z * evalC P z = z * evalC P z; exact Complex.zero_add _

theorem evalC_mulLinear (r : R) (P : Poly) (z : Complex) :
    evalC (mulLinear r P) z = (z - Complex.ofR r) * evalC P z := by
  unfold mulLinear sub
  rw [evalC_add, evalC_mulX, evalC_neg, evalC_scale]
  apply Complex.ext
  · change z.re * (evalC P z).re - z.im * (evalC P z).im +
           -(r * (evalC P z).re - (0 : R) * (evalC P z).im) =
           (z.re + -r) * (evalC P z).re - (z.im + -(0 : R)) * (evalC P z).im
    have hz : -(0 : R) = 0 := by have := R.add_neg_cancel 0; rw [R.zero_add] at this; exact this
    rw [R.zero_mul, R.sub_eq_add_neg (r * _) 0, hz, R.add_zero, R.add_zero, R.right_distrib, R.neg_mul]
    simp only [R.sub_eq_add_neg, R.add_assoc, R.add_left_comm, R.add_comm]
  · change z.re * (evalC P z).im + z.im * (evalC P z).re +
           -(r * (evalC P z).im + (0 : R) * (evalC P z).re) =
           (z.re + -r) * (evalC P z).im + (z.im + -(0 : R)) * (evalC P z).re
    have hz : -(0 : R) = 0 := by have := R.add_neg_cancel 0; rw [R.zero_add] at this; exact this
    rw [R.zero_mul, R.add_zero, hz, R.add_zero, R.right_distrib, R.neg_mul]
    simp only [R.add_assoc, R.add_left_comm, R.add_comm]

def natR : Nat → R
  | 0 => 0
  | k + 1 => natR k + 1

theorem natR_pos : ∀ k : Nat, (0 : R) < natR (k + 1)
  | 0 => by
    change (0 : R) < (0 : R) + 1; rw [R.zero_add]
    exact R.ofQ_lt_iff.mpr (Q.pow2_pos 0)
  | k + 1 => by
    change (0 : R) < natR (k + 1) + 1
    have ih := natR_pos k
    have h1 : (0 : R) < 1 := R.ofQ_lt_iff.mpr (Q.pow2_pos 0)
    have := R.add_lt_add ih h1; rw [R.add_zero] at this; exact this

theorem natR_eq_ofNat : ∀ k : Nat, natR k = R.ofNat k
  | 0 => rfl
  | k + 1 => by
    change natR k + 1 = R.ofNat (k + 1)
    rw [natR_eq_ofNat k]
    change R.ofQ (Q.ofNat k) + R.ofQ (Q.ofNat 1) = R.ofQ (Q.ofNat (k + 1))
    rw [← R.ofQ_add]
    apply congrArg R.ofQ
    apply Q.sound
    unfold RawQ.equiv RawQ.add RawQ.ofInt; dsimp only
    simp

/-- Formal derivative via Horner's rule: `(c + t Q)' = Q + t Q'`. -/
def deriv : Poly → Poly
  | [] => []
  | _ :: cs => add cs (mulX (deriv cs))

theorem coeff_deriv : ∀ (P : Poly) (k : Nat), coeff (deriv P) k = natR (k + 1) * coeff P (k + 1)
  | [], _ => by unfold deriv coeff; rw [R.mul_zero]
  | _ :: cs, 0 => by
    unfold deriv; rw [coeff_add, (coeff_mulX _).1, R.add_zero]
    change coeff cs 0 = ((0 : R) + 1) * coeff cs 0
    rw [R.zero_add, R.one_mul]
  | _ :: cs, k + 1 => by
    unfold deriv; rw [coeff_add, (coeff_mulX _).2, coeff_deriv cs k]
    change coeff cs (k + 1) + natR (k + 1) * coeff cs (k + 1) =
           (natR (k + 1) + 1) * coeff cs (k + 1)
    rw [R.right_distrib, R.one_mul, R.add_comm]

theorem deriv_polyEq {P Q : Poly} (h : PolyEq P Q) : PolyEq (deriv P) (deriv Q) := by
  intro k; rw [coeff_deriv, coeff_deriv, h (k + 1)]

theorem deriv_add (P Q : Poly) : PolyEq (deriv (add P Q)) (add (deriv P) (deriv Q)) := by
  intro k; rw [coeff_deriv, coeff_add, coeff_add, coeff_deriv, coeff_deriv, R.left_distrib]

theorem deriv_scale (s : R) (P : Poly) : PolyEq (deriv (scale s P)) (scale s (deriv P)) := by
  intro k; rw [coeff_deriv, coeff_scale, coeff_scale, coeff_deriv]
  simp only [R.mul_assoc, R.mul_left_comm, R.mul_comm]

theorem deriv_mulX (P : Poly) : PolyEq (deriv (mulX P)) (add P (mulX (deriv P))) := by
  cases P with
  | nil =>
    intro k
    cases k <;> rfl
  | cons _ _ => exact polyEq_refl _

theorem deriv_mulLinear (r : R) (P : Poly) :
    PolyEq (deriv (mulLinear r P)) (add P (mulLinear r (deriv P))) := by
  intro k
  unfold mulLinear sub
  rw [(deriv_add (mulX P) (neg (scale r P))) k, coeff_add, (deriv_mulX P) k]
  have hneg : coeff (deriv (neg (scale r P))) k = - (r * coeff (deriv P) k) := by
    unfold neg
    rw [(deriv_scale (-1) (scale r P)) k, coeff_scale, (deriv_scale r P) k, coeff_scale,
        R.neg_mul, R.one_mul]
  rw [coeff_add, hneg, coeff_add, coeff_add, coeff_neg, coeff_scale]
  simp only [R.add_assoc, R.add_left_comm, R.add_comm]

theorem eval_deriv_mulLinear (r : R) (P : Poly) (x : R) :
    eval (deriv (mulLinear r P)) x = eval P x + (x - r) * eval (deriv P) x := by
  rw [eval_eq_of_polyEq (deriv_mulLinear r P), eval_add, eval_mulLinear]

theorem evalC_deriv_mulLinear (r : R) (P : Poly) (z : Complex) :
    evalC (deriv (mulLinear r P)) z = evalC P z + (z - Complex.ofR r) * evalC (deriv P) z := by
  rw [evalC_eq_of_polyEq (deriv_mulLinear r P), evalC_add, evalC_mulLinear]

/-- Synthetic division of `P` by `(t - r)`. -/
def divLinear (r : R) : Poly → Poly
  | [] => []
  | _ :: cs => add [eval cs r] (mulX (divLinear r cs))

theorem mulLinear_add (r : R) (A B : Poly) :
    PolyEq (mulLinear r (add A B)) (add (mulLinear r A) (mulLinear r B)) := by
  intro k
  unfold mulLinear
  rw [coeff_sub, coeff_add, coeff_sub, coeff_sub, coeff_scale, coeff_add, R.left_distrib]
  cases k with
  | zero =>
    rw [(coeff_mulX _).1, (coeff_mulX _).1, (coeff_mulX _).1, coeff_scale, coeff_scale]
    simp only [R.sub_eq_add_neg, R.neg_add, R.zero_add, R.add_assoc, R.add_left_comm, R.add_comm]
  | succ j =>
    rw [(coeff_mulX _).2, (coeff_mulX _).2, (coeff_mulX _).2, coeff_add, coeff_scale, coeff_scale]
    simp only [R.sub_eq_add_neg, R.neg_add, R.add_assoc, R.add_left_comm, R.add_comm]

theorem mulLinear_mulX (r : R) (A : Poly) :
    PolyEq (mulLinear r (mulX A)) (mulX (mulLinear r A)) := by
  intro k
  unfold mulLinear
  cases k with
  | zero =>
    rw [coeff_sub, (coeff_mulX _).1, coeff_scale, (coeff_mulX _).1, (coeff_mulX _).1, R.mul_zero, R.sub_self]
  | succ j =>
    rw [coeff_sub, (coeff_mulX _).2, coeff_scale, (coeff_mulX _).2, (coeff_mulX _).2, coeff_sub, coeff_scale]

theorem polyEq_divLinear : ∀ (r : R) (P : Poly),
    PolyEq P (add (mulLinear r (divLinear r P)) [eval P r])
  | r, [] => by
    intro k; unfold divLinear mulLinear sub scale mulX eval
    cases k with
    | zero =>
      change (0 : R) = ((0 : R) + (-1 : R) * 0) + 0
      rw [R.mul_zero, R.add_zero, R.add_zero]
    | succ _ =>
      change (0 : R) = 0 + 0
      rw [R.add_zero]
  | r, c :: cs => by
    intro k
    have ih := polyEq_divLinear r cs
    unfold divLinear
    rw [coeff_add, mulLinear_add, coeff_add, mulLinear_mulX]
    cases k with
    | zero =>
      rw [mulLinear, coeff_sub, (coeff_mulX _).1, coeff_scale, (coeff_mulX _).1]
      have h0a : coeff [eval cs r] 0 = eval cs r := rfl
      have h0b : coeff [eval (c :: cs) r] 0 = c + r * eval cs r := rfl
      have h0c : coeff (c :: cs) 0 = c := rfl
      rw [h0a, h0b, h0c]
      simp only [R.sub_eq_add_neg, R.zero_add, R.add_zero, R.add_assoc, R.add_left_comm, R.add_comm,
                 R.add_neg_cancel, R.neg_add_cancel, R.add_neg_cancel_left, R.neg_add_cancel_left]
    | succ j =>
      have hc0 : coeff [eval (c :: cs) r] (j + 1) = 0 := by cases j <;> rfl
      rw [hc0, R.add_zero, (coeff_mulX _).2]
      have hl : coeff (mulLinear r [eval cs r]) (j + 1) = coeff [eval cs r] j := by
        unfold mulLinear
        rw [coeff_sub, (coeff_mulX _).2, coeff_scale]
        have h1 : coeff [eval cs r] (j + 1) = 0 := by cases j <;> rfl
        have hz : -(0 : R) = 0 := by have := R.add_neg_cancel 0; rw [R.zero_add] at this; exact this
        rw [h1, R.mul_zero, R.sub_eq_add_neg, hz, R.add_zero]
      rw [hl]
      change coeff cs j = coeff [eval cs r] j + coeff (mulLinear r (divLinear r cs)) j
      rw [ih j, coeff_add, R.add_comm]

def DegLe (P : Poly) (d : Nat) : Prop :=
  ∀ k : Nat, d < k → coeff P k = 0

theorem coeff_eq_zero_of_ge_length : ∀ (P : Poly) (k : Nat), P.length ≤ k → coeff P k = 0
  | [], _, _ => rfl
  | _ :: _, 0, h => by simp at h
  | _ :: cs, k + 1, h => coeff_eq_zero_of_ge_length cs k (by simp at h; omega)

theorem length_add : ∀ (P Q : Poly), (add P Q).length = Nat.max P.length Q.length
  | [], Q => by cases Q <;> simp [add]
  | c :: cs, [] => by simp [add]
  | c :: cs, d :: ds => by unfold add; simp [length_add cs ds, Nat.succ_max_succ]

theorem length_divLinear (r : R) : ∀ (P : Poly), (divLinear r P).length ≤ P.length
  | [] => Nat.le_refl 0
  | _ :: cs => by
    unfold divLinear
    rw [length_add]
    have ih := length_divLinear r cs
    have h1 : ([eval cs r] : Poly).length = 1 := rfl
    have h2 : (mulX (divLinear r cs)).length = (divLinear r cs).length + 1 := rfl
    rw [h1, h2, List.length_cons]
    exact Nat.max_le.mpr ⟨by omega, by omega⟩

theorem coeff_divLinear_rel (r : R) (P : Poly) (k : Nat) :
    coeff P (k + 1) = coeff (divLinear r P) k - r * coeff (divLinear r P) (k + 1) := by
  rw [(polyEq_divLinear r P) (k + 1), coeff_add]
  have h0 : coeff [eval P r] (k + 1) = 0 := by cases k <;> rfl
  rw [h0, R.add_zero, mulLinear, coeff_sub, (coeff_mulX _).2, coeff_scale]

theorem degLe_divLinear (r : R) (P : Poly) (d : Nat) (hdeg : DegLe P (d + 1)) :
    DegLe (divLinear r P) d ∧ coeff (divLinear r P) d = coeff P (d + 1) := by
  have hzero : ∀ m : Nat, ∀ k : Nat, P.length ≤ k + m → d < k → coeff (divLinear r P) k = 0 := by
    intro m
    induction m with
    | zero =>
      intro k hk _
      exact coeff_eq_zero_of_ge_length _ k (Nat.le_trans (length_divLinear r P) (by omega))
    | succ m ih =>
      intro k hk hdk
      have hrel := coeff_divLinear_rel r P k
      have hpz : coeff P (k + 1) = 0 := hdeg (k + 1) (by omega)
      have hnext : coeff (divLinear r P) (k + 1) = 0 := ih (k + 1) (by omega) (by omega)
      rw [hpz, hnext, R.mul_zero, R.sub_eq_add_neg] at hrel
      have hz : -(0 : R) = 0 := by have := R.add_neg_cancel 0; rw [R.zero_add] at this; exact this
      rw [hz, R.add_zero] at hrel
      exact hrel.symm
  have hd : DegLe (divLinear r P) d := fun k hdk =>
    hzero P.length k (by omega) hdk
  refine ⟨hd, ?_⟩
  have hrel := coeff_divLinear_rel r P d
  rw [hd (d + 1) (by omega), R.mul_zero, R.sub_eq_add_neg] at hrel
  have hz : -(0 : R) = 0 := by have := R.add_neg_cancel 0; rw [R.zero_add] at this; exact this
  rw [hz, R.add_zero] at hrel
  exact hrel.symm

def prodLinear (c : R) : List R → Poly
  | [] => [c]
  | r :: rs => mulLinear r (prodLinear c rs)

theorem eval_prodLinear_zero (c : R) : ∀ (rs : List R) (x : R),
    x ∈ rs → eval (prodLinear c rs) x = 0
  | [], _, hx => nomatch hx
  | r :: rs, x, hx => by
    unfold prodLinear; rw [eval_mulLinear]
    cases hx with
    | head => rw [R.sub_self, R.zero_mul]
    | tail _ hm => rw [eval_prodLinear_zero c rs x hm, R.mul_zero]

theorem evalC_prodLinear_eq_zero_iff {c : R} (hc : c ≠ 0) :
    ∀ (rs : List R) (z : Complex), evalC (prodLinear c rs) z = 0 ↔ ∃ r ∈ rs, z = Complex.ofR r
  | [], z => by
    change Complex.ofR c + z * (0 : Complex) = 0 ↔ ∃ r ∈ ([] : List R), z = Complex.ofR r
    have hz0 : z * (0 : Complex) = 0 := by
      apply Complex.ext
      · change z.re * 0 - z.im * 0 = 0; rw [R.mul_zero, R.mul_zero, R.sub_self]
      · change z.re * 0 + z.im * 0 = 0; rw [R.mul_zero, R.mul_zero, R.add_zero]
    rw [hz0, Complex.add_zero]
    constructor
    · intro h; exact False.elim (hc (Complex.ofR_eq_zero.mp h))
    · rintro ⟨_, hm, _⟩; nomatch hm
  | r :: rs, z => by
    unfold prodLinear; rw [evalC_mulLinear]
    constructor
    · intro h
      rcases Complex.mul_eq_zero h with h1 | h2
      · refine ⟨r, List.Mem.head rs, ?_⟩
        have ha : (z - Complex.ofR r) + Complex.ofR r = 0 + Complex.ofR r :=
          congrArg (· + Complex.ofR r) h1
        rw [Complex.zero_add] at ha
        have hl : (z - Complex.ofR r) + Complex.ofR r = z := by
          change (z + -Complex.ofR r) + Complex.ofR r = z
          rw [Complex.add_assoc, Complex.add_comm (-Complex.ofR r), Complex.add_neg_cancel, Complex.add_zero]
        rw [hl] at ha; exact ha
      · obtain ⟨u, hu, hzu⟩ := (evalC_prodLinear_eq_zero_iff hc rs z).mp h2
        exact ⟨u, List.Mem.tail r hu, hzu⟩
    · rintro ⟨u, hu, rfl⟩
      cases hu with
      | head =>
        have h0 : Complex.ofR r - Complex.ofR r = 0 := by
          change Complex.ofR r + -Complex.ofR r = 0; exact Complex.add_neg_cancel _
        rw [h0]
        apply Complex.ext
        · change (0 : R) * _ - (0 : R) * _ = 0; rw [R.zero_mul, R.zero_mul, R.sub_self]
        · change (0 : R) * _ + (0 : R) * _ = 0; rw [R.zero_mul, R.zero_mul, R.add_zero]
      | tail _ hm =>
        rw [(evalC_prodLinear_eq_zero_iff hc rs (Complex.ofR u)).mpr ⟨u, hm, rfl⟩]
        apply Complex.ext
        · change _ * (0 : R) - _ * (0 : R) = 0; rw [R.mul_zero, R.mul_zero, R.sub_self]
        · change _ * (0 : R) + _ * (0 : R) = 0; rw [R.mul_zero, R.mul_zero, R.add_zero]

theorem factor_of_nodup_roots : ∀ (rs : List R) (P : Poly),
    ListNodup rs → DegLe P rs.length → (∀ r ∈ rs, eval P r = 0) →
    PolyEq P (prodLinear (coeff P rs.length) rs)
  | [], P, _, hdeg, _ => by
    intro k
    cases k with
    | zero => rfl
    | succ j =>
      have hj : ([] : List R).length < j + 1 := by simp
      rw [hdeg (j + 1) hj]
      unfold prodLinear
      cases j <;> rfl
  | r :: rs, P, ListNodup.cons hnotmem hnd, hdeg, hroots => by
    have hpr : eval P r = 0 := hroots r (List.Mem.head rs)
    have hdiv := polyEq_divLinear r P
    have hd := degLe_divLinear r P rs.length hdeg
    have hqroots : ∀ u ∈ rs, eval (divLinear r P) u = 0 := by
      intro u hu
      have hpu : eval P u = 0 := hroots u (List.Mem.tail r hu)
      rw [eval_eq_of_polyEq hdiv, eval_add, hpr] at hpu
      have he0 : eval [0] u = 0 := by change (0 : R) + u * 0 = 0; rw [R.mul_zero, R.add_zero]
      rw [he0, R.add_zero, eval_mulLinear] at hpu
      rcases R.mul_eq_zero hpu with hur | hqu
      · exfalso; apply hnotmem u hu
        have ha : (u - r) + r = 0 + r := congrArg (· + r) hur
        rw [R.zero_add, R.sub_eq_add_neg, R.add_assoc, R.neg_add_cancel, R.add_zero] at ha
        exact ha.symm
      · exact hqu
    have ih := factor_of_nodup_roots rs (divLinear r P) hnd hd.1 hqroots
    have hlen : (r :: rs).length = rs.length + 1 := rfl
    rw [hd.2, ← hlen] at ih
    intro k
    rw [hdiv k, hpr, coeff_add]
    have hc0 : coeff [0] k = 0 := by cases k <;> rfl
    rw [hc0, R.add_zero]
    unfold prodLinear mulLinear
    rw [coeff_sub, coeff_sub, coeff_scale, coeff_scale, ih k]
    cases k with
    | zero => rw [(coeff_mulX _).1, (coeff_mulX _).1]
    | succ j => rw [(coeff_mulX _).2, (coeff_mulX _).2, ih j]

/-! ### Polynomial Lipschitz Continuity and Intermediate Value Theorem on `R` -/

noncomputable def polyBound : Poly → R → R
  | [], _ => 0
  | c :: cs, M => R.abs c + M * polyBound cs M

noncomputable def polyLip : Poly → R → R
  | [], _ => 0
  | _ :: cs, M => polyBound cs M + M * polyLip cs M

theorem polyBound_nonneg : ∀ (P : Poly) {M : R}, (0 : R) ≤ M → (0 : R) ≤ polyBound P M
  | [], _, _ => R.le_refl 0
  | c :: cs, _, hM => by
    unfold polyBound
    have := R.add_le_add (R.abs_nonneg c) (R.mul_nonneg hM (polyBound_nonneg cs hM))
    rw [R.add_zero] at this; exact this

theorem polyLip_nonneg : ∀ (P : Poly) {M : R}, (0 : R) ≤ M → (0 : R) ≤ polyLip P M
  | [], _, _ => R.le_refl 0
  | _ :: cs, _, hM => by
    unfold polyLip
    have := R.add_le_add (polyBound_nonneg cs hM) (R.mul_nonneg hM (polyLip_nonneg cs hM))
    rw [R.add_zero] at this; exact this

theorem abs_eval_le_polyBound : ∀ (P : Poly) {x M : R},
    (0 : R) ≤ M → R.abs x ≤ M → R.abs (eval P x) ≤ polyBound P M
  | [], _, _, _, _ => by unfold eval polyBound; rw [R.abs_of_nonneg (R.le_refl 0)]; exact R.le_refl 0
  | c :: cs, x, M, hM, hx => by
    unfold eval polyBound
    have htri := R.abs_add c (x * eval cs x)
    rw [R.abs_mul] at htri
    have ih := abs_eval_le_polyBound cs hM hx
    have hprod : R.abs x * R.abs (eval cs x) ≤ M * polyBound cs M := by
      have ha := R.mul_le_mul_of_nonneg_left ih (R.abs_nonneg x)
      have hb := R.mul_le_mul_of_nonneg_left hx (polyBound_nonneg cs hM)
      rw [R.mul_comm (polyBound cs M) (R.abs x), R.mul_comm (polyBound cs M) M] at hb
      exact R.le_trans ha hb
    exact R.le_trans htri (R.add_le_add (R.le_refl _) hprod)

theorem bilinear_diff (c fx fy x y : R) :
    (c + x * fx) - (c + y * fy) = fx * (x - y) + y * (fx - fy) := by
  have hL : (c + x * fx) - (c + y * fy) = fx * x + -(fy * y) := by
    rw [R.sub_eq_add_neg, R.neg_add, R.mul_comm x fx, R.mul_comm y fy,
        R.add_comm c (fx * x), R.add_assoc, ← R.add_assoc c (-c),
        R.add_neg_cancel, R.zero_add]
  have hR : fx * (x - y) + y * (fx - fy) = fx * x + -(fy * y) := by
    rw [R.mul_sub, R.mul_sub, R.mul_comm y fx, R.mul_comm y fy,
        R.sub_eq_add_neg, R.sub_eq_add_neg, R.add_assoc, R.neg_add_cancel_left]
  rw [hL, hR]

theorem abs_eval_sub_le_polyLip : ∀ (P : Poly) {x y M : R},
    (0 : R) ≤ M → R.abs x ≤ M → R.abs y ≤ M →
    R.abs (eval P x - eval P y) ≤ polyLip P M * R.abs (x - y)
  | [], x, y, _, _, _, _ => by
    unfold eval polyLip
    rw [R.sub_self, R.zero_mul, R.abs_of_nonneg (R.le_refl 0)]
    exact R.le_refl 0
  | c :: cs, x, y, M, hM, hx, hy => by
    unfold eval polyLip
    rw [bilinear_diff c (eval cs x) (eval cs y) x y]
    have htri := R.abs_add (eval cs x * (x - y)) (y * (eval cs x - eval cs y))
    rw [R.abs_mul, R.abs_mul] at htri
    have hbnd := abs_eval_le_polyBound cs hM hx
    have hlip := abs_eval_sub_le_polyLip cs hM hx hy
    have ht1 : R.abs (eval cs x) * R.abs (x - y) ≤ polyBound cs M * R.abs (x - y) := by
      have := R.mul_le_mul_of_nonneg_left hbnd (R.abs_nonneg (x - y))
      rw [R.mul_comm (R.abs (x - y)), R.mul_comm (R.abs (x - y))] at this; exact this
    have ht2 : R.abs y * R.abs (eval cs x - eval cs y) ≤ (M * polyLip cs M) * R.abs (x - y) := by
      have ha := R.mul_le_mul_of_nonneg_left hlip (R.abs_nonneg y)
      have hb := R.mul_le_mul_of_nonneg_left hy
                   (R.mul_nonneg (polyLip_nonneg cs hM) (R.abs_nonneg (x - y)))
      rw [R.mul_comm (polyLip cs M * R.abs (x - y)) (R.abs y),
          R.mul_comm (polyLip cs M * R.abs (x - y)) M] at hb
      rw [← R.mul_assoc M (polyLip cs M) (R.abs (x - y))] at hb
      exact R.le_trans ha hb
    rw [R.right_distrib]
    exact R.le_trans htri (R.add_le_add ht1 ht2)

theorem r_one_pos : (0 : R) < 1 := R.ofQ_lt_iff.mpr (Q.pow2_pos 0)

theorem r_neg_pos {x : R} (hx : x < 0) : (0 : R) < -x := by
  have := R.add_lt_add_right hx (-x); rw [R.add_neg_cancel, R.zero_add] at this; exact this

theorem r_neg_le_neg {a b : R} (h : a ≤ b) : -b ≤ -a := by
  have hsum := R.add_le_add h (R.le_refl (-a + -b))
  have hl : a + (-a + -b) = -b := R.add_neg_cancel_left a (-b)
  have hr : b + (-a + -b) = -a := by
    rw [R.add_comm (-a) (-b), R.add_neg_cancel_left]
  rw [hl, hr] at hsum; exact hsum

theorem r_cancel_inv2 {L T x : R} (hL : L ≠ 0) (hT : T ≠ 0) :
    L * (T * (x * (R.inv L * R.inv T))) = x := by
  calc
    L * (T * (x * (R.inv L * R.inv T)))
        = x * ((L * R.inv L) * (T * R.inv T)) := by
          simp only [R.mul_assoc, R.mul_left_comm, R.mul_comm]
    _ = x := by rw [R.mul_inv_cancel hL, R.mul_inv_cancel hT, R.one_mul, R.mul_one]

theorem r_inv_pos {x : R} (hx : (0 : R) < x) : (0 : R) < R.inv x := by
  have hne : x ≠ 0 := fun h => R.lt_irrefl 0 (h ▸ hx)
  rcases R.lt_trichotomy (R.inv x) 0 with hn | hz | hp
  · exfalso
    have hm := R.mul_pos hx (r_neg_pos hn)
    rw [R.mul_neg, R.mul_inv_cancel hne] at hm
    have h1 := R.add_lt_add_right hm 1
    rw [R.zero_add, R.neg_add_cancel] at h1
    exact R.lt_irrefl 0 (R.lt_trans r_one_pos h1)
  · exfalso
    have hm : x * R.inv x = 0 := by rw [hz, R.mul_zero]
    rw [R.mul_inv_cancel hne] at hm
    exact R.one_ne_zero hm
  · exact hp

theorem abs_le_interval {a b x : R} (hax : a ≤ x) (hxb : x ≤ b) :
    R.abs x ≤ R.abs a + R.abs b := by
  rcases R.lt_trichotomy x 0 with hxn | rfl | hxp
  · rw [R.abs_of_neg hxn]
    have hna : -x ≤ -a := r_neg_le_neg hax
    have h1 : -a ≤ R.abs a := R.neg_le_abs_self a
    have h2 := R.add_le_add (R.le_trans hna h1) (R.abs_nonneg b)
    rw [R.add_zero] at h2; exact h2
  · rw [R.abs_of_nonneg (R.le_refl 0)]
    have := R.add_le_add (R.abs_nonneg a) (R.abs_nonneg b)
    rw [R.add_zero] at this; exact this
  · rw [R.abs_of_nonneg (R.le_of_lt hxp)]
    have h1 := R.le_trans hxb (R.le_abs_self b)
    have h2 := R.add_le_add (R.abs_nonneg a) h1
    rw [R.zero_add] at h2; exact h2

theorem exists_rat_right_neg (P : Poly) {a b : R} (hab : a < b) (ha : eval P a < 0) :
    ∃ u : Q, a < R.ofQ u ∧ R.ofQ u < b ∧ eval P (R.ofQ u) < 0 := by
  let M : R := R.abs a + R.abs b
  have hM : (0 : R) ≤ M := by
    have := R.add_le_add (R.abs_nonneg a) (R.abs_nonneg b)
    rw [R.add_zero] at this; exact this
  let L : R := polyLip P M + 1
  have hLpos : (0 : R) < L := by
    have := R.add_le_add (polyLip_nonneg P hM) (R.le_refl 1)
    rw [R.zero_add] at this
    exact R.lt_of_lt_of_le r_one_pos this
  have hLne : L ≠ 0 := fun h => R.lt_irrefl 0 (h ▸ hLpos)
  let δ : R := (-eval P a) * R.inv L
  have hδpos : (0 : R) < δ := R.mul_pos (r_neg_pos ha) (r_inv_pos hLpos)
  have haδ : a < a + δ := by
    have := R.add_lt_add_left hδpos a; rw [R.add_zero] at this; exact this
  open Classical in
  let b' : R := if b < a + δ then b else a + δ
  have hab' : a < b' := by
    dsimp only [b']; split
    · exact hab
    · exact haδ
  obtain ⟨u, hau, hub'⟩ := R.dense_ofQ hab'
  have hub : R.ofQ u < b := by
    dsimp only [b'] at hub'; split at hub'
    · exact hub'
    · next hnb => exact R.lt_of_lt_of_le hub' hnb
  refine ⟨u, hau, hub, ?_⟩
  have huM : R.abs (R.ofQ u) ≤ M := abs_le_interval (R.le_of_lt hau) (R.le_of_lt hub)
  have haM : R.abs a ≤ M := abs_le_interval (R.le_refl a) (R.le_of_lt hab)
  have hlip := abs_eval_sub_le_polyLip P hM huM haM
  have hdiff_pos : (0 : R) < R.ofQ u - a := R.sub_pos.mpr hau
  have hdiff_lt : R.ofQ u - a < δ := by
    have hlt_aδ : R.ofQ u < a + δ := by
      dsimp only [b'] at hub'; split at hub'
      · next hlt => exact R.lt_trans hub' hlt
      · exact hub'
    have := R.add_lt_add_right hlt_aδ (-a)
    have hr : (a + δ) + -a = δ := by
      rw [R.add_comm a δ, R.add_assoc, R.add_neg_cancel, R.add_zero]
    rw [hr] at this; exact this
  rw [R.abs_of_nonneg (R.le_of_lt hdiff_pos)] at hlip
  have hstep1 : polyLip P M * (R.ofQ u - a) ≤ L * (R.ofQ u - a) := by
    have hleL : polyLip P M ≤ L := by
      have := R.add_le_add (R.le_refl (polyLip P M)) (R.le_of_lt r_one_pos)
      rw [R.add_zero] at this; exact this
    have hm := R.mul_le_mul_of_nonneg_left hleL (R.le_of_lt hdiff_pos)
    rw [R.mul_comm (R.ofQ u - a), R.mul_comm (R.ofQ u - a)] at hm; exact hm
  have hstep2 : L * (R.ofQ u - a) < -eval P a := by
    have hm := R.mul_lt_mul_of_pos_left hdiff_lt hLpos
    have hc : L * δ = -eval P a := by
      dsimp only [δ]
      calc
        L * ((-eval P a) * R.inv L) = (-eval P a) * (L * R.inv L) := by
          simp only [R.mul_assoc, R.mul_left_comm, R.mul_comm]
        _ = -eval P a := by rw [R.mul_inv_cancel hLne, R.mul_one]
    rw [hc] at hm; exact hm
  have hbound : eval P (R.ofQ u) - eval P a < -eval P a :=
    R.lt_of_le_of_lt (R.le_trans (R.le_abs_self _) (R.le_trans hlip hstep1)) hstep2
  have hfin := R.add_lt_add_right hbound (eval P a)
  have hl : (eval P (R.ofQ u) - eval P a) + eval P a = eval P (R.ofQ u) := by
    simp only [R.sub_eq_add_neg, R.add_assoc, R.neg_add_cancel, R.add_zero]
  rw [hl, R.neg_add_cancel] at hfin
  exact hfin

theorem exists_rat_left_pos (P : Poly) {a b : R} (hab : a < b) (hb : 0 < eval P b) :
    ∃ v : Q, a < R.ofQ v ∧ R.ofQ v < b ∧ 0 < eval P (R.ofQ v) := by
  let M : R := R.abs a + R.abs b
  have hM : (0 : R) ≤ M := by
    have := R.add_le_add (R.abs_nonneg a) (R.abs_nonneg b)
    rw [R.add_zero] at this; exact this
  let L : R := polyLip P M + 1
  have hLpos : (0 : R) < L := by
    have := R.add_le_add (polyLip_nonneg P hM) (R.le_refl 1)
    rw [R.zero_add] at this
    exact R.lt_of_lt_of_le r_one_pos this
  have hLne : L ≠ 0 := fun h => R.lt_irrefl 0 (h ▸ hLpos)
  let δ : R := eval P b * R.inv L
  have hδpos : (0 : R) < δ := R.mul_pos hb (r_inv_pos hLpos)
  have hbδ : b - δ < b := by
    have hnδ : -δ < 0 := by
      have := R.add_lt_add_right hδpos (-δ); rw [R.zero_add, R.add_neg_cancel] at this; exact this
    have := R.add_lt_add_left hnδ b; rw [R.add_zero] at this; exact this
  open Classical in
  let a' : R := if a < b - δ then b - δ else a
  have ha'b : a' < b := by
    dsimp only [a']; split
    · exact hbδ
    · exact hab
  obtain ⟨v, ha'v, hvb⟩ := R.dense_ofQ ha'b
  have hav : a < R.ofQ v := by
    dsimp only [a'] at ha'v; split at ha'v
    · next hlt => exact R.lt_trans hlt ha'v
    · exact ha'v
  refine ⟨v, hav, hvb, ?_⟩
  have hvM : R.abs (R.ofQ v) ≤ M := abs_le_interval (R.le_of_lt hav) (R.le_of_lt hvb)
  have hbM : R.abs b ≤ M := abs_le_interval (R.le_of_lt hab) (R.le_refl b)
  have hlip := abs_eval_sub_le_polyLip P hM hbM hvM
  have hdiff_pos : (0 : R) < b - R.ofQ v := R.sub_pos.mpr hvb
  have hdiff_lt : b - R.ofQ v < δ := by
    have hgt : b - δ < R.ofQ v := by
      dsimp only [a'] at ha'v; split at ha'v
      · exact ha'v
      · next hna => exact R.lt_of_le_of_lt hna ha'v
    have := R.add_lt_add_right hgt (δ + -R.ofQ v)
    have hl : (b - δ) + (δ + -R.ofQ v) = b - R.ofQ v := by
      rw [R.sub_eq_add_neg, R.add_assoc, R.neg_add_cancel_left]; rfl
    have hr : R.ofQ v + (δ + -R.ofQ v) = δ := by
      rw [R.add_comm δ (-R.ofQ v), R.add_neg_cancel_left]
    rw [hl, hr] at this; exact this
  rw [R.abs_of_nonneg (R.le_of_lt hdiff_pos)] at hlip
  have hstep1 : polyLip P M * (b - R.ofQ v) ≤ L * (b - R.ofQ v) := by
    have hleL : polyLip P M ≤ L := by
      have := R.add_le_add (R.le_refl (polyLip P M)) (R.le_of_lt r_one_pos)
      rw [R.add_zero] at this; exact this
    have hm := R.mul_le_mul_of_nonneg_left hleL (R.le_of_lt hdiff_pos)
    rw [R.mul_comm (b - R.ofQ v), R.mul_comm (b - R.ofQ v)] at hm; exact hm
  have hstep2 : L * (b - R.ofQ v) < eval P b := by
    have hm := R.mul_lt_mul_of_pos_left hdiff_lt hLpos
    have hc : L * δ = eval P b := by
      dsimp only [δ]
      calc
        L * (eval P b * R.inv L) = eval P b * (L * R.inv L) := by
          simp only [R.mul_assoc, R.mul_left_comm, R.mul_comm]
        _ = eval P b := by rw [R.mul_inv_cancel hLne, R.mul_one]
    rw [hc] at hm; exact hm
  have hbound : eval P b - eval P (R.ofQ v) < eval P b :=
    R.lt_of_le_of_lt (R.le_trans (R.le_abs_self _) (R.le_trans hlip hstep1)) hstep2
  have hfin := R.add_lt_add_right hbound (eval P (R.ofQ v) + -eval P b)
  have hl : (eval P b - eval P (R.ofQ v)) + (eval P (R.ofQ v) + -eval P b) = 0 := by
    rw [R.sub_eq_add_neg, R.add_assoc, R.neg_add_cancel_left, R.add_neg_cancel]
  have hr : eval P b + (eval P (R.ofQ v) + -eval P b) = eval P (R.ofQ v) := by
    rw [R.add_comm (eval P (R.ofQ v)) (-eval P b), R.add_neg_cancel_left]
  rw [hl, hr] at hfin
  exact hfin

noncomputable def bisectStep (P : Poly) (uv : Q × Q) : Q × Q :=
  let m := Q.half (uv.1 + uv.2)
  open Classical in
  if eval P (R.ofQ m) ≤ 0 then (m, uv.2) else (uv.1, m)

noncomputable def bisect (P : Poly) (u₀ v₀ : Q) : Nat → Q × Q
  | 0 => (u₀, v₀)
  | n + 1 => bisectStep P (bisect P u₀ v₀ n)

theorem bisect_props (P : Poly) {u₀ v₀ : Q} (huv : u₀ < v₀)
    (hu₀ : eval P (R.ofQ u₀) ≤ 0) (hv₀ : 0 < eval P (R.ofQ v₀)) :
    ∀ n : Nat,
      let p := bisect P u₀ v₀ n
      u₀ ≤ p.1 ∧ p.1 < p.2 ∧ p.2 ≤ v₀ ∧
      p.2 - p.1 = (v₀ - u₀) * Q.pow2 n ∧
      eval P (R.ofQ p.1) ≤ 0 ∧ 0 < eval P (R.ofQ p.2) := by
  intro n
  induction n with
  | zero =>
    dsimp only [bisect]
    have hp0 : Q.pow2 0 = 1 := by apply Q.sound; rfl
    rw [hp0, Q.mul_one]
    exact ⟨Q.le_refl u₀, huv, Q.le_refl v₀, rfl, hu₀, hv₀⟩
  | succ n ih =>
    let u := (bisect P u₀ v₀ n).1
    let v := (bisect P u₀ v₀ n).2
    rcases ih with ⟨hu_ge, huv_n, hv_le, hlen, hpu, hpv⟩
    let m := Q.half (u + v)
    have hmid := Q.sub_half_midpoint u v
    have hpos_d : (0 : Q) < (v - u) * Q.pow2 1 := Q.mul_pos (Q.sub_pos.mpr huv_n) (Q.pow2_pos 1)
    have hum : u < m := Q.sub_pos.mp (by dsimp only [m]; rw [hmid.1]; exact hpos_d)
    have hmv : m < v := Q.sub_pos.mp (by dsimp only [m]; rw [hmid.2]; exact hpos_d)
    change u₀ ≤ (bisectStep P (u, v)).1 ∧ (bisectStep P (u, v)).1 < (bisectStep P (u, v)).2 ∧
           (bisectStep P (u, v)).2 ≤ v₀ ∧
           (bisectStep P (u, v)).2 - (bisectStep P (u, v)).1 = (v₀ - u₀) * Q.pow2 (n + 1) ∧
           eval P (R.ofQ (bisectStep P (u, v)).1) ≤ 0 ∧ 0 < eval P (R.ofQ (bisectStep P (u, v)).2)
    unfold bisectStep; dsimp only
    split
    · next hpm =>
      refine ⟨Q.le_trans hu_ge (Q.le_of_lt hum), hmv, hv_le, ?_, hpm, hpv⟩
      rw [hmid.2, hlen, Q.mul_assoc, ← Q.pow2_add n 1]
    · next hpm =>
      have hpm_pos : 0 < eval P (R.ofQ m) := by
        rcases R.lt_trichotomy 0 (eval P (R.ofQ m)) with hp | hz | hn
        · exact hp
        · exact False.elim (hpm (by rw [← hz]; exact R.le_refl 0))
        · exact False.elim (hpm (R.le_of_lt hn))
      refine ⟨hu_ge, hum, Q.le_trans (Q.le_of_lt hmv) hv_le, ?_, hpu, hpm_pos⟩
      rw [hmid.1, hlen, Q.mul_assoc, ← Q.pow2_add n 1]

theorem bisect_mono (P : Poly) {u₀ v₀ : Q} (huv : u₀ < v₀)
    (hu₀ : eval P (R.ofQ u₀) ≤ 0) (hv₀ : 0 < eval P (R.ofQ v₀)) :
    ∀ {n m : Nat}, n ≤ m →
      (bisect P u₀ v₀ n).1 ≤ (bisect P u₀ v₀ m).1 ∧
      (bisect P u₀ v₀ m).2 ≤ (bisect P u₀ v₀ n).2 := by
  intro n m hnm
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hnm
  clear hnm
  induction k with
  | zero => exact ⟨Q.le_refl _, Q.le_refl _⟩
  | succ k ih =>
    rcases ih with ⟨h1, h2⟩
    have hstep := bisect_props P huv hu₀ hv₀ (n + k)
    let u := (bisect P u₀ v₀ (n + k)).1
    let v := (bisect P u₀ v₀ (n + k)).2
    have huv_nk : u < v := hstep.2.1
    let mid := Q.half (u + v)
    have hmid := Q.sub_half_midpoint u v
    have hpos_d : (0 : Q) < (v - u) * Q.pow2 1 := Q.mul_pos (Q.sub_pos.mpr huv_nk) (Q.pow2_pos 1)
    have hum : u ≤ mid := Q.le_of_lt (Q.sub_pos.mp (by dsimp only [mid]; rw [hmid.1]; exact hpos_d))
    have hmv : mid ≤ v := Q.le_of_lt (Q.sub_pos.mp (by dsimp only [mid]; rw [hmid.2]; exact hpos_d))
    change (bisect P u₀ v₀ n).1 ≤ (bisectStep P (u, v)).1 ∧
           (bisectStep P (u, v)).2 ≤ (bisect P u₀ v₀ n).2
    unfold bisectStep; dsimp only
    split
    · exact ⟨Q.le_trans h1 hum, h2⟩
    · exact ⟨h1, Q.le_trans hmv h2⟩

/-- Intermediate Value Theorem for polynomials over `R`. -/
theorem poly_ivt (P : Poly) {a b : R} (hab : a < b) (ha : eval P a < 0) (hb : 0 < eval P b) :
    ∃ r : R, a < r ∧ r < b ∧ eval P r = 0 := by
  obtain ⟨q_mid, haq, hqb⟩ := R.dense_ofQ hab
  obtain ⟨u₀, hau₀, hu₀q, hpu₀⟩ := exists_rat_right_neg P haq ha
  obtain ⟨v₀, hqv₀, hv₀b, hpv₀⟩ := exists_rat_left_pos P hqb hb
  have huv : u₀ < v₀ := R.ofQ_lt_iff.mp (R.lt_trans hu₀q hqv₀)
  have hu₀_le : eval P (R.ofQ u₀) ≤ 0 := R.le_of_lt hpu₀
  obtain ⟨B, hB⟩ := Q.exists_twoPow_gt (v₀ - u₀)
  have hvu_pos : (0 : Q) < v₀ - u₀ := Q.sub_pos.mpr huv
  have hvu_le : v₀ - u₀ ≤ Q.twoPow B := by
    rw [← Q.abs_of_nonneg (Q.le_of_lt hvu_pos)]; exact Q.le_of_lt hB
  let uSeq : CauchySeq := {
    seq := fun n => (bisect P u₀ v₀ n).1
    isCauchy := fun k => by
      refine ⟨k + B, fun m hm n hn => ?_⟩
      by_cases hmn : n ≤ m
      · have hm1 := (bisect_mono P huv hu₀_le hpv₀ hmn).1
        have hm2 := (bisect_mono P huv hu₀_le hpv₀ hmn).2
        have hp_m := bisect_props P huv hu₀_le hpv₀ m
        have hp_n := bisect_props P huv hu₀_le hpv₀ n
        have hnonneg : (0 : Q) ≤ (bisect P u₀ v₀ m).1 - (bisect P u₀ v₀ n).1 := Q.sub_nonneg.mpr hm1
        rw [Q.abs_of_nonneg hnonneg]
        have hlt_v : (bisect P u₀ v₀ m).1 < (bisect P u₀ v₀ n).2 :=
          Q.lt_of_lt_of_le hp_m.2.1 hm2
        have hdiff_lt : (bisect P u₀ v₀ m).1 - (bisect P u₀ v₀ n).1 <
                        (bisect P u₀ v₀ n).2 - (bisect P u₀ v₀ n).1 :=
          Q.add_lt_add_right hlt_v (-(bisect P u₀ v₀ n).1)
        rw [hp_n.2.2.2.1] at hdiff_lt
        have hn_pow : Q.pow2 n ≤ Q.pow2 (k + B) := Q.pow2_le_of_le hn
        have hprod1 := Q.mul_le_mul_of_nonneg_left hn_pow (Q.le_of_lt hvu_pos)
        have hprod2 := Q.mul_le_mul_of_nonneg_left hvu_le (Q.le_of_lt (Q.pow2_pos (k + B)))
        rw [Q.mul_comm (Q.pow2 (k + B)) (v₀ - u₀), Q.mul_comm (Q.pow2 (k + B)) (Q.twoPow B)] at hprod2
        have hc : Q.twoPow B * Q.pow2 (k + B) = Q.pow2 k := by
          rw [Q.pow2_add k B, Q.mul_comm (Q.pow2 k), ← Q.mul_assoc, Q.twoPow_mul_pow2, Q.one_mul]
        rw [hc] at hprod2
        exact Q.lt_of_lt_of_le hdiff_lt (Q.le_trans hprod1 hprod2)
      · have hnm : m ≤ n := by omega
        have hm1 := (bisect_mono P huv hu₀_le hpv₀ hnm).1
        have hm2 := (bisect_mono P huv hu₀_le hpv₀ hnm).2
        have hp_n := bisect_props P huv hu₀_le hpv₀ n
        have hp_m := bisect_props P huv hu₀_le hpv₀ m
        rw [Q.abs_sub_comm]
        have hnonneg : (0 : Q) ≤ (bisect P u₀ v₀ n).1 - (bisect P u₀ v₀ m).1 := Q.sub_nonneg.mpr hm1
        rw [Q.abs_of_nonneg hnonneg]
        have hlt_v : (bisect P u₀ v₀ n).1 < (bisect P u₀ v₀ m).2 :=
          Q.lt_of_lt_of_le hp_n.2.1 hm2
        have hdiff_lt : (bisect P u₀ v₀ n).1 - (bisect P u₀ v₀ m).1 <
                        (bisect P u₀ v₀ m).2 - (bisect P u₀ v₀ m).1 :=
          Q.add_lt_add_right hlt_v (-(bisect P u₀ v₀ m).1)
        rw [hp_m.2.2.2.1] at hdiff_lt
        have hm_pow : Q.pow2 m ≤ Q.pow2 (k + B) := Q.pow2_le_of_le hm
        have hprod1 := Q.mul_le_mul_of_nonneg_left hm_pow (Q.le_of_lt hvu_pos)
        have hprod2 := Q.mul_le_mul_of_nonneg_left hvu_le (Q.le_of_lt (Q.pow2_pos (k + B)))
        rw [Q.mul_comm (Q.pow2 (k + B)) (v₀ - u₀), Q.mul_comm (Q.pow2 (k + B)) (Q.twoPow B)] at hprod2
        have hc : Q.twoPow B * Q.pow2 (k + B) = Q.pow2 k := by
          rw [Q.pow2_add k B, Q.mul_comm (Q.pow2 k), ← Q.mul_assoc, Q.twoPow_mul_pow2, Q.one_mul]
        rw [hc] at hprod2
        exact Q.lt_of_lt_of_le hdiff_lt (Q.le_trans hprod1 hprod2)
  }
  let r : R := R.mk uSeq
  have hr_bounds : ∀ n : Nat, R.ofQ (bisect P u₀ v₀ n).1 ≤ r ∧ r ≤ R.ofQ (bisect P u₀ v₀ n).2 := by
    intro n
    constructor
    · rintro ⟨k, N, hN⟩
      let m := Nat.max n N
      have h1 := hN m (Nat.le_max_right _ _)
      change Q.pow2 k ≤ (bisect P u₀ v₀ n).1 + -(bisect P u₀ v₀ m).1 at h1
      have hmono := (bisect_mono P huv hu₀_le hpv₀ (Nat.le_max_left n N)).1
      have hnonpos : (bisect P u₀ v₀ n).1 + -(bisect P u₀ v₀ m).1 ≤ 0 := by
        have := Q.add_le_add hmono (Q.le_refl (-(bisect P u₀ v₀ m).1))
        rw [Q.add_neg_cancel] at this; exact this
      exact Q.lt_irrefl 0 (Q.lt_of_lt_of_le (Q.pow2_pos k) (Q.le_trans h1 hnonpos))
    · rintro ⟨k, N, hN⟩
      let m := Nat.max n N
      have h1 := hN m (Nat.le_max_right _ _)
      change Q.pow2 k ≤ (bisect P u₀ v₀ m).1 + -(bisect P u₀ v₀ n).2 at h1
      have hmono := (bisect_mono P huv hu₀_le hpv₀ (Nat.le_max_left n N)).2
      have hlt_m := (bisect_props P huv hu₀_le hpv₀ m).2.1
      have hle_n : (bisect P u₀ v₀ m).1 ≤ (bisect P u₀ v₀ n).2 := Q.le_trans (Q.le_of_lt hlt_m) hmono
      have hnonpos : (bisect P u₀ v₀ m).1 + -(bisect P u₀ v₀ n).2 ≤ 0 := by
        have := Q.add_le_add hle_n (Q.le_refl (-(bisect P u₀ v₀ n).2))
        rw [Q.add_neg_cancel] at this; exact this
      exact Q.lt_irrefl 0 (Q.lt_of_lt_of_le (Q.pow2_pos k) (Q.le_trans h1 hnonpos))
  have har : a < r := R.lt_of_lt_of_le hau₀ (hr_bounds 0).1
  have hrb : r < b := R.lt_of_le_of_lt (hr_bounds 0).2 hv₀b
  refine ⟨r, har, hrb, ?_⟩
  let M : R := R.abs (R.ofQ u₀) + R.abs (R.ofQ v₀)
  have hM : (0 : R) ≤ M := by
    have := R.add_le_add (R.abs_nonneg (R.ofQ u₀)) (R.abs_nonneg (R.ofQ v₀))
    rw [R.add_zero] at this; exact this
  have hrM : R.abs r ≤ M := abs_le_interval (hr_bounds 0).1 (hr_bounds 0).2
  let L : R := polyLip P M + 1
  have hLpos : (0 : R) < L := by
    have := R.add_le_add (polyLip_nonneg P hM) (R.le_refl 1); rw [R.zero_add] at this
    exact R.lt_of_lt_of_le r_one_pos this
  have hLne : L ≠ 0 := fun h => R.lt_irrefl 0 (h ▸ hLpos)
  rcases R.lt_trichotomy (eval P r) 0 with hneg | heq | hpos
  · -- eval P r < 0 contradicts 0 < eval P (ofQ v_n) for large n
    exfalso
    let ε : R := (-eval P r) * (R.inv L * R.inv (R.ofQ (Q.twoPow B)))
    have h2pos : (0 : R) < R.ofQ (Q.twoPow B) := R.ofQ_lt_iff.mpr (Q.twoPow_pos B)
    have h2ne : R.ofQ (Q.twoPow B) ≠ 0 := fun h => R.lt_irrefl 0 (h ▸ h2pos)
    have hεpos : (0 : R) < ε :=
      R.mul_pos (r_neg_pos hneg) (R.mul_pos (r_inv_pos hLpos) (r_inv_pos h2pos))
    obtain ⟨n, hn⟩ := R.exists_pow2_lt hεpos
    have hp_n := bisect_props P huv hu₀_le hpv₀ n
    have hvM : R.abs (R.ofQ (bisect P u₀ v₀ n).2) ≤ M :=
      abs_le_interval (R.ofQ_le_iff.mpr (Q.le_trans hp_n.1 (Q.le_of_lt hp_n.2.1)))
                      (R.ofQ_le_iff.mpr hp_n.2.2.1)
    have hlip := abs_eval_sub_le_polyLip P hM hvM hrM
    have hvr_nonneg : (0 : R) ≤ R.ofQ (bisect P u₀ v₀ n).2 - r := by
      intro hlt
      have := R.add_lt_add_right hlt r
      have hl : (R.ofQ (bisect P u₀ v₀ n).2 - r) + r = R.ofQ (bisect P u₀ v₀ n).2 := by
        rw [R.sub_eq_add_neg, R.add_assoc, R.neg_add_cancel, R.add_zero]
      rw [hl, R.zero_add] at this
      exact (hr_bounds n).2 this
    rw [R.abs_of_nonneg hvr_nonneg] at hlip
    have hvr_le : R.ofQ (bisect P u₀ v₀ n).2 - r ≤ R.ofQ (Q.twoPow B) * R.ofQ (Q.pow2 n) := by
      have h1 : R.ofQ (bisect P u₀ v₀ n).2 - r ≤
                R.ofQ (bisect P u₀ v₀ n).2 - R.ofQ (bisect P u₀ v₀ n).1 :=
        R.add_le_add (R.le_refl _) (r_neg_le_neg (hr_bounds n).1)
      rw [← R.ofQ_sub, hp_n.2.2.2.1, R.ofQ_mul] at h1
      have h2 := R.mul_le_mul_of_nonneg_left (R.ofQ_le_iff.mpr hvu_le)
                   (R.le_of_lt (R.ofQ_lt_iff.mpr (Q.pow2_pos n)))
      rw [R.mul_comm (R.ofQ (Q.pow2 n)), R.mul_comm (R.ofQ (Q.pow2 n))] at h2
      exact R.le_trans h1 h2
    have hstep1 : polyLip P M * (R.ofQ (bisect P u₀ v₀ n).2 - r) ≤
                  L * (R.ofQ (Q.twoPow B) * R.ofQ (Q.pow2 n)) := by
      have hleL : polyLip P M ≤ L := by
        have := R.add_le_add (R.le_refl (polyLip P M)) (R.le_of_lt r_one_pos)
        rw [R.add_zero] at this; exact this
      have ha := R.mul_le_mul_of_nonneg_left hvr_le (polyLip_nonneg P hM)
      have hb := R.mul_le_mul_of_nonneg_left hleL
                   (R.mul_nonneg (R.le_of_lt h2pos) (R.le_of_lt (R.ofQ_lt_iff.mpr (Q.pow2_pos n))))
      rw [R.mul_comm (R.ofQ (Q.twoPow B) * R.ofQ (Q.pow2 n)) (polyLip P M),
          R.mul_comm (R.ofQ (Q.twoPow B) * R.ofQ (Q.pow2 n)) L] at hb
      exact R.le_trans ha hb
    have hstep2 : L * (R.ofQ (Q.twoPow B) * R.ofQ (Q.pow2 n)) < -eval P r := by
      have hm := R.mul_lt_mul_of_pos_left hn (R.mul_pos hLpos h2pos)
      rw [R.mul_assoc L (R.ofQ (Q.twoPow B)) (R.ofQ (Q.pow2 n)),
          R.mul_assoc L (R.ofQ (Q.twoPow B)) ε] at hm
      rw [r_cancel_inv2 hLne h2ne] at hm
      exact hm
    have hlt_neg : eval P (R.ofQ (bisect P u₀ v₀ n).2) - eval P r < -eval P r :=
      R.lt_of_le_of_lt (R.le_trans (R.le_abs_self _) (R.le_trans hlip hstep1)) hstep2
    have hfin := R.add_lt_add_right hlt_neg (eval P r)
    have hl : (eval P (R.ofQ (bisect P u₀ v₀ n).2) - eval P r) + eval P r =
              eval P (R.ofQ (bisect P u₀ v₀ n).2) := by
      rw [R.sub_eq_add_neg, R.add_assoc, R.neg_add_cancel, R.add_zero]
    rw [hl, R.neg_add_cancel] at hfin
    exact R.lt_irrefl 0 (R.lt_trans hp_n.2.2.2.2.2 hfin)
  · exact heq
  · -- 0 < eval P r contradicts eval P (ofQ u_n) ≤ 0 for large n
    exfalso
    let ε : R := eval P r * (R.inv L * R.inv (R.ofQ (Q.twoPow B)))
    have h2pos : (0 : R) < R.ofQ (Q.twoPow B) := R.ofQ_lt_iff.mpr (Q.twoPow_pos B)
    have h2ne : R.ofQ (Q.twoPow B) ≠ 0 := fun h => R.lt_irrefl 0 (h ▸ h2pos)
    have hεpos : (0 : R) < ε :=
      R.mul_pos hpos (R.mul_pos (r_inv_pos hLpos) (r_inv_pos h2pos))
    obtain ⟨n, hn⟩ := R.exists_pow2_lt hεpos
    have hp_n := bisect_props P huv hu₀_le hpv₀ n
    have huM : R.abs (R.ofQ (bisect P u₀ v₀ n).1) ≤ M :=
      abs_le_interval (R.ofQ_le_iff.mpr hp_n.1)
                      (R.ofQ_le_iff.mpr (Q.le_trans (Q.le_of_lt hp_n.2.1) hp_n.2.2.1))
    have hlip := abs_eval_sub_le_polyLip P hM hrM huM
    have hru_nonneg : (0 : R) ≤ r - R.ofQ (bisect P u₀ v₀ n).1 := by
      intro hlt
      have := R.add_lt_add_right hlt (R.ofQ (bisect P u₀ v₀ n).1)
      have hl : (r - R.ofQ (bisect P u₀ v₀ n).1) + R.ofQ (bisect P u₀ v₀ n).1 = r := by
        rw [R.sub_eq_add_neg, R.add_assoc, R.neg_add_cancel, R.add_zero]
      rw [hl, R.zero_add] at this
      exact (hr_bounds n).1 this
    rw [R.abs_of_nonneg hru_nonneg] at hlip
    have hru_le : r - R.ofQ (bisect P u₀ v₀ n).1 ≤ R.ofQ (Q.twoPow B) * R.ofQ (Q.pow2 n) := by
      have h1 : r - R.ofQ (bisect P u₀ v₀ n).1 ≤
                R.ofQ (bisect P u₀ v₀ n).2 - R.ofQ (bisect P u₀ v₀ n).1 :=
        R.add_le_add (hr_bounds n).2 (R.le_refl _)
      rw [← R.ofQ_sub, hp_n.2.2.2.1, R.ofQ_mul] at h1
      have h2 := R.mul_le_mul_of_nonneg_left (R.ofQ_le_iff.mpr hvu_le)
                   (R.le_of_lt (R.ofQ_lt_iff.mpr (Q.pow2_pos n)))
      rw [R.mul_comm (R.ofQ (Q.pow2 n)), R.mul_comm (R.ofQ (Q.pow2 n))] at h2
      exact R.le_trans h1 h2
    have hstep1 : polyLip P M * (r - R.ofQ (bisect P u₀ v₀ n).1) ≤
                  L * (R.ofQ (Q.twoPow B) * R.ofQ (Q.pow2 n)) := by
      have hleL : polyLip P M ≤ L := by
        have := R.add_le_add (R.le_refl (polyLip P M)) (R.le_of_lt r_one_pos)
        rw [R.add_zero] at this; exact this
      have ha := R.mul_le_mul_of_nonneg_left hru_le (polyLip_nonneg P hM)
      have hb := R.mul_le_mul_of_nonneg_left hleL
                   (R.mul_nonneg (R.le_of_lt h2pos) (R.le_of_lt (R.ofQ_lt_iff.mpr (Q.pow2_pos n))))
      rw [R.mul_comm (R.ofQ (Q.twoPow B) * R.ofQ (Q.pow2 n)) (polyLip P M),
          R.mul_comm (R.ofQ (Q.twoPow B) * R.ofQ (Q.pow2 n)) L] at hb
      exact R.le_trans ha hb
    have hstep2 : L * (R.ofQ (Q.twoPow B) * R.ofQ (Q.pow2 n)) < eval P r := by
      have hm := R.mul_lt_mul_of_pos_left hn (R.mul_pos hLpos h2pos)
      rw [R.mul_assoc L (R.ofQ (Q.twoPow B)) (R.ofQ (Q.pow2 n)),
          R.mul_assoc L (R.ofQ (Q.twoPow B)) ε] at hm
      rw [r_cancel_inv2 hLne h2ne] at hm
      exact hm
    have hlt_pos : eval P r - eval P (R.ofQ (bisect P u₀ v₀ n).1) < eval P r :=
      R.lt_of_le_of_lt (R.le_trans (R.le_abs_self _) (R.le_trans hlip hstep1)) hstep2
    have hfin := R.add_lt_add_right hlt_pos (eval P (R.ofQ (bisect P u₀ v₀ n).1) + -eval P r)
    have hl : (eval P r - eval P (R.ofQ (bisect P u₀ v₀ n).1)) +
              (eval P (R.ofQ (bisect P u₀ v₀ n).1) + -eval P r) = 0 := by
      rw [R.sub_eq_add_neg, R.add_assoc, R.neg_add_cancel_left, R.add_neg_cancel]
    have hr : eval P r + (eval P (R.ofQ (bisect P u₀ v₀ n).1) + -eval P r) =
              eval P (R.ofQ (bisect P u₀ v₀ n).1) := by
      rw [R.add_comm (eval P (R.ofQ (bisect P u₀ v₀ n).1)) (-eval P r), R.add_neg_cancel_left]
    rw [hl, hr] at hfin
    exact hp_n.2.2.2.2.1 hfin

theorem poly_ivt_opp (P : Poly) {a b : R} (hab : a < b) (ha : 0 < eval P a) (hb : eval P b < 0) :
    ∃ r : R, a < r ∧ r < b ∧ eval P r = 0 := by
  have hna : eval (neg P) a < 0 := by
    rw [eval_neg]
    have := R.add_lt_add_right ha (-eval P a)
    rw [R.zero_add, R.add_neg_cancel] at this; exact this
  have hnb : 0 < eval (neg P) b := by rw [eval_neg]; exact r_neg_pos hb
  obtain ⟨r, har, hrb, hz⟩ := poly_ivt (neg P) hab hna hnb
  rw [eval_neg] at hz
  have hzr : eval P r = 0 := by
    have ha' : (-eval P r) + eval P r = 0 + eval P r := congrArg (· + eval P r) hz
    rw [R.neg_add_cancel, R.zero_add] at ha'; exact ha'.symm
  exact ⟨r, har, hrb, hzr⟩

end Poly





/-! ## 4. Simple Real Roots Criteria and Simion's Master Interlacing Operator -/

namespace Poly

/-- Standard complex-root definition: `P` is nonzero and every complex root `z ∈ C` of `P`
    is real (`z.im = 0`) and simple (`P'(z) ≠ 0`). -/
def HasAllRealSimpleRoots (P : Poly) : Prop :=
  (∃ k : Nat, coeff P k ≠ 0) ∧
  ∀ z : Complex, evalC P z = 0 → z.im = 0 ∧ evalC (deriv P) z ≠ 0

/-- Complete linear factorization over `R` into pairwise distinct real roots. -/
def SplitsIntoDistinctRealRoots (P : Poly) : Prop :=
  ∃ (c : R) (rs : List R), c ≠ 0 ∧ ListNodup rs ∧ PolyEq P (prodLinear c rs)

/-- Strictly decreasing list of negative real numbers `0 > r₁ > r₂ > ... > r_d`. -/
inductive StrictlyDecNeg : List R → Prop where
  | nil : StrictlyDecNeg []
  | single {r : R} : r < 0 → StrictlyDecNeg [r]
  | cons {r₁ r₂ : R} {rs : List R} :
      r₁ < 0 → r₂ < r₁ → StrictlyDecNeg (r₂ :: rs) → StrictlyDecNeg (r₁ :: r₂ :: rs)

theorem strictlyDecNeg_neg : ∀ {rs : List R}, StrictlyDecNeg rs → ∀ x ∈ rs, x < 0
  | _, .nil, _, hx => nomatch hx
  | _, .single hr, _, hx => by
    cases hx with
    | head => exact hr
    | tail _ hm => nomatch hm
  | _, .cons hr₁ _ hrest, x, hx => by
    cases hx with
    | head => exact hr₁
    | tail _ hm => exact strictlyDecNeg_neg hrest x hm

theorem strictlyDecNeg_lt_tail : ∀ {r₁ : R} {rs : List R},
    StrictlyDecNeg (r₁ :: rs) → ∀ y ∈ rs, y < r₁
  | _, [], _, _, hy => nomatch hy
  | _, _ :: _, .cons _ hlt hrest, y, hy => by
    cases hy with
    | head => exact hlt
    | tail _ hm => exact R.lt_trans (strictlyDecNeg_lt_tail hrest y hm) hlt

theorem strictlyDecNeg_nodup : ∀ {rs : List R}, StrictlyDecNeg rs → ListNodup rs
  | [], .nil => ListNodup.nil
  | [_], .single _ => ListNodup.cons (fun _ hy => nomatch hy) ListNodup.nil
  | _ :: _ :: _, h@(.cons _ _ hrest) =>
    ListNodup.cons
      (fun y hy heq => R.lt_irrefl y (heq ▸ strictlyDecNeg_lt_tail h y hy))
      (strictlyDecNeg_nodup hrest)

theorem prodLinear_degLe_and_lead (c : R) : ∀ (rs : List R),
    DegLe (prodLinear c rs) rs.length ∧ coeff (prodLinear c rs) rs.length = c
  | [] => ⟨fun k hk => by unfold prodLinear; cases k with | zero => omega | succ j => cases j <;> rfl, rfl⟩
  | r :: rs => by
    obtain ⟨hdeg, hlead⟩ := prodLinear_degLe_and_lead c rs
    refine ⟨fun k hk => ?_, ?_⟩
    · unfold prodLinear mulLinear
      cases k with
      | zero => simp at hk
      | succ j =>
        have hj : rs.length < j := by simp at hk; omega
        rw [coeff_sub, (coeff_mulX _).2, coeff_scale, hdeg j hj, hdeg (j + 1) (by omega),
            R.mul_zero, R.sub_self]
    · unfold prodLinear mulLinear
      change coeff (sub (mulX (prodLinear c rs)) (scale r (prodLinear c rs))) (rs.length + 1) = c
      rw [coeff_sub, (coeff_mulX _).2, coeff_scale, hlead, hdeg (rs.length + 1) (by omega),
          R.mul_zero, R.sub_eq_add_neg]
      have hz : -(0 : R) = 0 := by have := R.add_neg_cancel 0; rw [R.zero_add] at this; exact this
      rw [hz, R.add_zero]

theorem eval_prodLinear_ne_zero {c : R} (hc : c ≠ 0) :
    ∀ {rs : List R} {x : R}, (∀ u ∈ rs, x ≠ u) → eval (prodLinear c rs) x ≠ 0
  | [], x, _ => by
    change c + x * 0 ≠ 0
    rw [R.mul_zero, R.add_zero]; exact hc
  | r :: rs, x, hne => by
    unfold prodLinear; rw [eval_mulLinear]
    intro hz
    rcases R.mul_eq_zero hz with h1 | h2
    · apply hne r (List.Mem.head rs)
      have ha : (x - r) + r = 0 + r := congrArg (· + r) h1
      rw [R.zero_add, R.sub_eq_add_neg, R.add_assoc, R.neg_add_cancel, R.add_zero] at ha
      exact ha
    · exact eval_prodLinear_ne_zero hc (fun u hu => hne u (List.Mem.tail r hu)) h2

theorem eval_deriv_prodLinear_ne_zero {c : R} (hc : c ≠ 0) :
    ∀ {rs : List R}, ListNodup rs → ∀ r ∈ rs, eval (deriv (prodLinear c rs)) r ≠ 0
  | [], _, _, hr => nomatch hr
  | u :: rs, ListNodup.cons hnotmem hnd, r, hr => by
    unfold prodLinear; rw [eval_deriv_mulLinear]
    cases hr with
    | head =>
      rw [R.sub_self, R.zero_mul, R.add_zero]
      exact eval_prodLinear_ne_zero hc hnotmem
    | tail _ hm =>
      rw [eval_prodLinear_zero c rs r hm, R.zero_add]
      intro hz
      rcases R.mul_eq_zero hz with hru | hder
      · apply hnotmem r hm
        have ha : (r - u) + u = 0 + u := congrArg (· + u) hru
        rw [R.zero_add, R.sub_eq_add_neg, R.add_assoc, R.neg_add_cancel, R.add_zero] at ha
        exact ha.symm
      · exact eval_deriv_prodLinear_ne_zero hc hnd r hm hder

/-- Every polynomial that splits into distinct real linear factors has all real simple complex roots. -/
theorem allRealSimple_of_splits {P : Poly} (h : SplitsIntoDistinctRealRoots P) :
    HasAllRealSimpleRoots P := by
  rcases h with ⟨c, rs, hc, hnd, hpeq⟩
  refine ⟨⟨rs.length, ?_⟩, ?_⟩
  · rw [hpeq rs.length, (prodLinear_degLe_and_lead c rs).2]; exact hc
  · intro z hz
    rw [evalC_eq_of_polyEq hpeq] at hz
    obtain ⟨r, hr, rfl⟩ := (evalC_prodLinear_eq_zero_iff hc rs z).mp hz
    refine ⟨rfl, ?_⟩
    rw [evalC_eq_of_polyEq (deriv_polyEq hpeq), evalC_ofR]
    intro hdz
    exact eval_deriv_prodLinear_ne_zero hc hnd r hr (Complex.ofR_eq_zero.mp hdz)

/-- Conversely, any double real root `P(x) = P'(x) = 0` refutes both `HasAllRealSimpleRoots`
    and `SplitsIntoDistinctRealRoots`. -/
theorem not_allRealSimple_of_double_root {P : Poly} {x : R}
    (hp : eval P x = 0) (hdp : eval (deriv P) x = 0) :
    ¬ HasAllRealSimpleRoots P ∧ ¬ SplitsIntoDistinctRealRoots P := by
  have hn : ¬ HasAllRealSimpleRoots P := by
    intro ⟨_, hall⟩
    have h := hall (Complex.ofR x) (by rw [evalC_ofR, hp]; rfl)
    apply h.2
    rw [evalC_ofR, hdp]; rfl
  exact ⟨hn, fun hs => hn (allRealSimple_of_splits hs)⟩

/-- `P` splits into `d` distinct strictly negative real linear factors with positive leading coeff. -/
def SplitsNegSimple (P : Poly) (d : Nat) : Prop :=
  ∃ (c : R) (rs : List R), 0 < c ∧ rs.length = d ∧ StrictlyDecNeg rs ∧ PolyEq P (prodLinear c rs)

theorem splits_of_splitsNegSimple {P : Poly} {d : Nat} (h : SplitsNegSimple P d) :
    SplitsIntoDistinctRealRoots P := by
  rcases h with ⟨c, rs, hc, _, hdec, hpeq⟩
  exact ⟨c, rs, fun hz => R.lt_irrefl 0 (hz ▸ hc), strictlyDecNeg_nodup hdec, hpeq⟩

theorem allRealSimple_of_splitsNegSimple {P : Poly} {d : Nat} (h : SplitsNegSimple P d) :
    HasAllRealSimpleRoots P :=
  allRealSimple_of_splits (splits_of_splitsNegSimple h)

theorem splits_mulX_of_splitsNegSimple {P : Poly} {d : Nat} (h : SplitsNegSimple P d) :
    SplitsIntoDistinctRealRoots (mulX P) ∧ HasAllRealSimpleRoots (mulX P) := by
  rcases h with ⟨c, rs, hc, _, hdec, hpeq⟩
  have hne : c ≠ 0 := fun hz => R.lt_irrefl 0 (hz ▸ hc)
  have hnd : ListNodup (0 :: rs) :=
    ListNodup.cons
      (fun y hy hz => R.lt_irrefl 0 (hz ▸ strictlyDecNeg_neg hdec y hy))
      (strictlyDecNeg_nodup hdec)
  have hpeqX : PolyEq (mulX P) (prodLinear c (0 :: rs)) := by
    intro k
    unfold prodLinear mulLinear
    rw [coeff_sub, coeff_scale, R.zero_mul, R.sub_eq_add_neg]
    have hz : -(0 : R) = 0 := by have := R.add_neg_cancel 0; rw [R.zero_add] at this; exact this
    rw [hz, R.add_zero]
    cases k with
    | zero => rfl
    | succ j => exact hpeq j
  have hs : SplitsIntoDistinctRealRoots (mulX P) := ⟨c, 0 :: rs, hne, hnd, hpeqX⟩
  exact ⟨hs, allRealSimple_of_splits hs⟩

/-! ### Alternating-Sign Chains and Master Interlacing Operator `interlaceOp` -/

def AltSigns (pos : Bool) (Q : Poly) : List R → Prop
  | [] => True
  | [x] => if pos then 0 < eval Q x else eval Q x < 0
  | x :: y :: ys =>
      y < x ∧ (if pos then 0 < eval Q x else eval Q x < 0) ∧ AltSigns (!pos) Q (y :: ys)

theorem altSigns_polyEq {pos : Bool} {P Q : Poly} (h : PolyEq P Q) :
    ∀ (pts : List R), AltSigns pos P pts ↔ AltSigns pos Q pts
  | [] => Iff.rfl
  | [x] => by unfold AltSigns; rw [eval_eq_of_polyEq h x]
  | x :: y :: ys => by
    unfold AltSigns
    rw [eval_eq_of_polyEq h x, altSigns_polyEq h (y :: ys)]

theorem eval_prodLinear_pos_of_gt {c : R} (hc : 0 < c) :
    ∀ {rs : List R} {x : R}, (∀ u ∈ rs, u < x) → 0 < eval (prodLinear c rs) x
  | [], x, _ => by
    change 0 < c + x * 0; rw [R.mul_zero, R.add_zero]; exact hc
  | r :: rs, x, hgt => by
    unfold prodLinear; rw [eval_mulLinear]
    exact R.mul_pos (R.sub_pos.mpr (hgt r (List.Mem.head rs)))
                    (eval_prodLinear_pos_of_gt hc (fun u hu => hgt u (List.Mem.tail r hu)))

theorem altSigns_mulLinear_deriv {r : R} {P : Poly} :
    ∀ (pos : Bool) (pts : List R),
      (∀ u ∈ pts, u < r) → (∀ u ∈ pts, eval P u = 0) →
      AltSigns pos (deriv P) pts → AltSigns (!pos) (deriv (mulLinear r P)) pts
  | _, [], _, _, _ => trivial
  | pos, [u], hlt, hzero, halt => by
    unfold AltSigns at halt ⊢
    rw [eval_deriv_mulLinear, hzero u (List.Mem.head []), R.zero_add]
    have hur_neg : u - r < 0 := by
      have hp : 0 < r - u := R.sub_pos.mpr (hlt u (List.Mem.head []))
      have := R.add_lt_add_right hp (u - r)
      have hr : (r - u) + (u - r) = 0 := by
        rw [R.sub_eq_add_neg, R.sub_eq_add_neg, R.add_assoc, R.neg_add_cancel_left, R.add_neg_cancel]
      rw [R.zero_add, hr] at this; exact this
    cases pos with
    | true =>
      have hp := R.mul_pos (r_neg_pos hur_neg) halt
      rw [R.neg_mul] at hp
      have := R.add_lt_add_right hp ((u - r) * eval (deriv P) u)
      rw [R.zero_add, R.neg_add_cancel] at this; exact this
    | false =>
      have hp := R.mul_pos (r_neg_pos hur_neg) (r_neg_pos halt)
      rw [R.neg_mul, R.mul_neg, R.neg_neg] at hp; exact hp
  | pos, u :: v :: ys, hlt, hzero, ⟨hvu, hu_sign, hrest⟩ => by
    refine ⟨hvu, ?_, altSigns_mulLinear_deriv (!pos) (v :: ys)
      (fun w hw => hlt w (List.Mem.tail u hw))
      (fun w hw => hzero w (List.Mem.tail u hw)) hrest⟩
    rw [eval_deriv_mulLinear, hzero u (List.Mem.head _), R.zero_add]
    have hur_neg : u - r < 0 := by
      have hp : 0 < r - u := R.sub_pos.mpr (hlt u (List.Mem.head _))
      have := R.add_lt_add_right hp (u - r)
      have hr : (r - u) + (u - r) = 0 := by
        rw [R.sub_eq_add_neg, R.sub_eq_add_neg, R.add_assoc, R.neg_add_cancel_left, R.add_neg_cancel]
      rw [R.zero_add, hr] at this; exact this
    cases pos with
    | true =>
      have hp := R.mul_pos (r_neg_pos hur_neg) hu_sign
      rw [R.neg_mul] at hp
      have := R.add_lt_add_right hp ((u - r) * eval (deriv P) u)
      rw [R.zero_add, R.neg_add_cancel] at this; exact this
    | false =>
      have hp := R.mul_pos (r_neg_pos hur_neg) (r_neg_pos hu_sign)
      rw [R.neg_mul, R.mul_neg, R.neg_neg] at hp; exact hp

theorem deriv_prodLinear_altSigns {c : R} (hc : 0 < c) :
    ∀ {rs : List R}, StrictlyDecNeg rs → AltSigns true (deriv (prodLinear c rs)) rs
  | [], .nil => trivial
  | [r], .single _ => by
    unfold AltSigns prodLinear
    change 0 < eval (deriv (mulLinear r [c])) r
    rw [eval_deriv_mulLinear, R.sub_self, R.zero_mul, R.add_zero]
    change 0 < c + r * 0; rw [R.mul_zero, R.add_zero]; exact hc
  | r₁ :: r₂ :: rs, h@(.cons _ hr₂₁ hrest) => by
    have ih := deriv_prodLinear_altSigns hc hrest
    have hgt : ∀ u ∈ r₂ :: rs, u < r₁ := strictlyDecNeg_lt_tail h
    have hzero : ∀ u ∈ r₂ :: rs, eval (prodLinear c (r₂ :: rs)) u = 0 :=
      fun u hu => eval_prodLinear_zero c (r₂ :: rs) u hu
    have htail := altSigns_mulLinear_deriv true (r₂ :: rs) hgt hzero ih
    unfold prodLinear AltSigns
    refine ⟨hr₂₁, ?_, htail⟩
    change 0 < eval (deriv (mulLinear r₁ (prodLinear c (r₂ :: rs)))) r₁
    rw [eval_deriv_mulLinear, R.sub_self, R.zero_mul, R.add_zero]
    exact eval_prodLinear_pos_of_gt hc hgt

/-- Master differential operator `T_{r,s}(P)(t) = t(1 - t) P'(t) + (r + s t) P(t)`. -/
def interlaceOp (r s : R) (P : Poly) : Poly :=
  add (sub (mulX (deriv P)) (mulX (mulX (deriv P))))
      (add (scale r P) (scale s (mulX P)))

theorem eval_interlaceOp (r s : R) (P : Poly) (x : R) :
    eval (interlaceOp r s P) x = x * (1 - x) * eval (deriv P) x + (r + s * x) * eval P x := by
  unfold interlaceOp
  rw [eval_add, eval_sub, eval_mulX, eval_mulX, eval_mulX, eval_add, eval_scale, eval_scale, eval_mulX]
  have h1 : x * eval (deriv P) x - x * (x * eval (deriv P) x) = x * (1 - x) * eval (deriv P) x := by
    rw [R.mul_sub, R.mul_one, R.sub_mul, R.mul_assoc]
  have h2 : r * eval P x + s * (x * eval P x) = (r + s * x) * eval P x := by
    rw [R.right_distrib, R.mul_assoc]
  rw [h1, h2]

theorem interlaceOp_polyEq (r s : R) {P Q : Poly} (h : PolyEq P Q) :
    PolyEq (interlaceOp r s P) (interlaceOp r s Q) := by
  have hd := deriv_polyEq h
  intro k
  unfold interlaceOp
  rw [coeff_add (sub _ _), coeff_add (sub _ _), coeff_sub, coeff_sub,
      coeff_add (scale r P), coeff_add (scale r Q),
      coeff_scale, coeff_scale, coeff_scale, coeff_scale, h k]
  cases k with
  | zero =>
    rw [(coeff_mulX _).1, (coeff_mulX _).1, (coeff_mulX _).1,
        (coeff_mulX _).1, (coeff_mulX _).1, (coeff_mulX _).1]
  | succ j =>
    rw [(coeff_mulX _).2, (coeff_mulX _).2, (coeff_mulX _).2, (coeff_mulX _).2,
        (coeff_mulX _).2, (coeff_mulX _).2, h j, hd j]
    cases j with
    | zero => rw [(coeff_mulX _).1, (coeff_mulX _).1]
    | succ i => rw [(coeff_mulX _).2, (coeff_mulX _).2, hd i]

theorem interlaceOp_degLe_and_lead (r s : R) {P : Poly} {d : Nat} (hdeg : DegLe P d) :
    DegLe (interlaceOp r s P) (d + 1) ∧
    coeff (interlaceOp r s P) (d + 1) = (s - natR d) * coeff P d := by
  have hz0 : -(0 : R) = 0 := by have := R.add_neg_cancel 0; rw [R.zero_add] at this; exact this
  refine ⟨fun k hk => ?_, ?_⟩
  · unfold interlaceOp
    rw [coeff_add, coeff_sub, coeff_add, coeff_scale, coeff_scale]
    cases k with
    | zero => omega
    | succ j =>
      cases j with
      | zero => omega
      | succ i =>
        have hi1 : d < i + 1 := by omega
        have hi2 : d < i + 2 := by omega
        rw [(coeff_mulX _).2, (coeff_mulX _).2, (coeff_mulX _).2, (coeff_mulX _).2,
            coeff_deriv, coeff_deriv, hdeg (i + 2) hi2, hdeg (i + 1) hi1]
        simp only [R.mul_zero, R.sub_self, R.add_zero]
  · unfold interlaceOp
    rw [coeff_add, coeff_sub, coeff_add, coeff_scale, coeff_scale,
        (coeff_mulX _).2, (coeff_mulX _).2, (coeff_mulX _).2,
        coeff_deriv, hdeg (d + 1) (by omega), R.mul_zero, R.mul_zero, R.zero_add]
    cases d with
    | zero =>
      rw [(coeff_mulX _).1, R.sub_self, R.zero_add]
      change s * coeff P 0 = (s - 0) * coeff P 0
      rw [R.sub_eq_add_neg, hz0, R.add_zero]
    | succ m =>
      rw [(coeff_mulX _).2, coeff_deriv]
      rw [R.sub_mul, R.sub_eq_add_neg, R.zero_add, R.sub_eq_add_neg, R.add_comm]

theorem interlaceOp_altSigns_on_roots (r s : R) {c : R} (hc : 0 < c) :
    ∀ {rs : List R}, StrictlyDecNeg rs →
      AltSigns false (interlaceOp r s (prodLinear c rs)) rs := by
  intro rs hdec
  have hder := deriv_prodLinear_altSigns hc hdec
  have hneg : ∀ u ∈ rs, u < 0 := strictlyDecNeg_neg hdec
  have hzero : ∀ u ∈ rs, eval (prodLinear c rs) u = 0 := fun u hu => eval_prodLinear_zero c rs u hu
  have helper : ∀ (pos : Bool) (pts : List R),
      (∀ u ∈ pts, u < 0) → (∀ u ∈ pts, eval (prodLinear c rs) u = 0) →
      AltSigns pos (deriv (prodLinear c rs)) pts →
      AltSigns (!pos) (interlaceOp r s (prodLinear c rs)) pts := by
    intro pos pts hlt hz halt
    induction pts generalizing pos with
    | nil => trivial
    | cons u rest ih =>
      have hu_neg : u < 0 := hlt u (List.Mem.head rest)
      have h1mu_pos : 0 < 1 - u := by
        have hp := R.add_lt_add_left (r_neg_pos hu_neg) 1
        rw [R.add_zero] at hp
        exact R.lt_trans r_one_pos hp
      have hu1mu_neg : u * (1 - u) < 0 := by
        have hp := R.mul_pos (r_neg_pos hu_neg) h1mu_pos
        rw [R.neg_mul] at hp
        have := R.add_lt_add_right hp (u * (1 - u))
        rw [R.zero_add, R.neg_add_cancel] at this; exact this
      have hev : eval (interlaceOp r s (prodLinear c rs)) u =
                 (u * (1 - u)) * eval (deriv (prodLinear c rs)) u := by
        rw [eval_interlaceOp, hz u (List.Mem.head rest), R.mul_zero, R.add_zero]
      cases rest with
      | nil =>
        unfold AltSigns at halt ⊢
        rw [hev]
        cases pos with
        | true =>
          have hp := R.mul_pos (r_neg_pos hu1mu_neg) halt
          rw [R.neg_mul] at hp
          have := R.add_lt_add_right hp ((u * (1 - u)) * eval (deriv (prodLinear c rs)) u)
          rw [R.zero_add, R.neg_add_cancel] at this; exact this
        | false =>
          have hp := R.mul_pos (r_neg_pos hu1mu_neg) (r_neg_pos halt)
          rw [R.neg_mul, R.mul_neg, R.neg_neg] at hp; exact hp
      | cons v ys =>
        rcases halt with ⟨hvu, hu_s, htail⟩
        refine ⟨hvu, ?_, ih (!pos) (fun w hw => hlt w (List.Mem.tail u hw))
                                  (fun w hw => hz w (List.Mem.tail u hw)) htail⟩
        rw [hev]
        cases pos with
        | true =>
          have hp := R.mul_pos (r_neg_pos hu1mu_neg) hu_s
          rw [R.neg_mul] at hp
          have := R.add_lt_add_right hp ((u * (1 - u)) * eval (deriv (prodLinear c rs)) u)
          rw [R.zero_add, R.neg_add_cancel] at this; exact this
        | false =>
          have hp := R.mul_pos (r_neg_pos hu1mu_neg) (r_neg_pos hu_s)
          rw [R.neg_mul, R.mul_neg, R.neg_neg] at hp; exact hp
  exact helper true rs hneg hzero hder

theorem interlaceOp_altSigns_zero_cons {r : R} (hr : 0 < r) (s : R) {c : R} (hc : 0 < c)
    {rs : List R} (hdec : StrictlyDecNeg rs) :
    AltSigns true (interlaceOp r s (prodLinear c rs)) (0 :: rs) := by
  have hp0 : 0 < eval (prodLinear c rs) 0 :=
    eval_prodLinear_pos_of_gt hc (strictlyDecNeg_neg hdec)
  have hq0 : 0 < eval (interlaceOp r s (prodLinear c rs)) 0 := by
    rw [eval_interlaceOp, R.zero_mul, R.zero_mul, R.zero_add, R.mul_zero, R.add_zero]
    exact R.mul_pos hr hp0
  cases rs with
  | nil => exact hq0
  | cons r₁ rest =>
    refine ⟨strictlyDecNeg_neg hdec r₁ (List.Mem.head rest), hq0, ?_⟩
    exact interlaceOp_altSigns_on_roots r s hc hdec

/-- Every alternating-sign chain `x₀ > x₁ > ... > x_m` with `x₀ ≤ 0` yields `m` strictly
    decreasing negative roots of `Q` strictly inside the intervals `(x_k, x_{k-1})`. -/
theorem roots_of_altSigns_cons (Q : Poly) :
    ∀ (pos : Bool) (x₀ : R) (rest : List R),
      x₀ ≤ 0 → AltSigns pos Q (x₀ :: rest) →
      ∃ etas : List R,
        etas.length = rest.length ∧
        StrictlyDecNeg etas ∧
        (∀ η ∈ etas, eval Q η = 0) ∧
        (match rest, etas with
         | [], _ => True
         | _ :: _, [] => False
         | x₁ :: _, η₁ :: _ => x₁ < η₁ ∧ η₁ < x₀)
  | _, _, [], _, _ => by
    refine ⟨[], rfl, .nil, ?_, trivial⟩
    intro _ h; nomatch h
  | pos, x₀, x₁ :: ys, hx₀, ⟨hx₁₀, hx₀_sign, hrest⟩ => by
    have hx₁_le : x₁ ≤ 0 := R.le_trans (R.le_of_lt hx₁₀) hx₀
    obtain ⟨etas', hlen', hdec', hroots', hhead'⟩ :=
      roots_of_altSigns_cons Q (!pos) x₁ ys hx₁_le hrest
    have hx₁_sign : if !pos then 0 < eval Q x₁ else eval Q x₁ < 0 := by
      cases ys with
      | nil => exact hrest
      | cons _ _ => exact hrest.2.1
    have hivt : ∃ η₁ : R, x₁ < η₁ ∧ η₁ < x₀ ∧ eval Q η₁ = 0 := by
      cases pos with
      | true => exact poly_ivt Q hx₁₀ hx₁_sign hx₀_sign
      | false => exact poly_ivt_opp Q hx₁₀ hx₁_sign hx₀_sign
    obtain ⟨η₁, hη₁_gt, hη₁_lt, hη₁_z⟩ := hivt
    have hη₁_neg : η₁ < 0 := R.lt_of_lt_of_le hη₁_lt hx₀
    refine ⟨η₁ :: etas', congrArg (· + 1) hlen', ?_, ?_, ⟨hη₁_gt, hη₁_lt⟩⟩
    · cases ys with
      | nil =>
        have he : etas' = [] := by cases etas' with | nil => rfl | cons _ _ => simp at hlen'
        subst he
        exact .single hη₁_neg
      | cons _ _ =>
        cases etas' with
        | nil => exfalso; exact hhead'
        | cons _ _ =>
          exact .cons hη₁_neg (R.lt_trans hhead'.2 hη₁_gt) hdec'
    · intro η hη
      cases hη with
      | head => exact hη₁_z
      | tail _ hm => exact hroots' η hm

/-- Monomial `t^k` and real power `x^k` for negative-infinity sign analysis. -/
def powR (x : R) : Nat → R
  | 0 => 1
  | k + 1 => x * powR x k

def monomial : Nat → Poly
  | 0 => [1]
  | k + 1 => mulX (monomial k)

theorem eval_monomial (x : R) : ∀ k : Nat, eval (monomial k) x = powR x k
  | 0 => by change (1 : R) + x * 0 = 1; rw [R.mul_zero, R.add_zero]
  | k + 1 => by unfold monomial powR; rw [eval_mulX, eval_monomial x k]

theorem coeff_monomial : ∀ d k : Nat, coeff (monomial d) k = if k = d then 1 else 0
  | 0, 0 => rfl
  | 0, k + 1 => by unfold monomial; cases k <;> rfl
  | d + 1, 0 => rfl
  | d + 1, k + 1 => by
    unfold monomial; rw [(coeff_mulX _).2, coeff_monomial d k]
    by_cases h : k = d <;> simp [h]

theorem powR_pos {u : R} (hu : 0 < u) : ∀ k : Nat, 0 < powR u k
  | 0 => r_one_pos
  | k + 1 => R.mul_pos hu (powR_pos hu k)

theorem powR_ge_one {u : R} (hu : (1 : R) ≤ u) : ∀ k : Nat, (1 : R) ≤ powR u k
  | 0 => R.le_refl 1
  | k + 1 => by
    unfold powR
    have hpos : 0 < u := R.lt_of_lt_of_le r_one_pos hu
    have ih := powR_ge_one hu k
    have h1 := R.mul_le_mul_of_nonneg_left ih (R.le_of_lt hpos)
    rw [R.mul_one] at h1
    exact R.le_trans hu h1

theorem powR_neg_sign (u : R) : ∀ k : Nat,
    powR (-u) k = if k % 2 = 0 then powR u k else -powR u k
  | 0 => rfl
  | k + 1 => by
    unfold powR
    rw [powR_neg_sign u k]
    by_cases h : k % 2 = 0
    · have h1 : (k + 1) % 2 = 1 := by omega
      simp [h, h1, R.neg_mul]
    · have h0 : k % 2 = 1 := by omega
      have h1 : (k + 1) % 2 = 0 := by omega
      simp [h0, h1, R.neg_mul, R.mul_neg, R.neg_neg]

noncomputable def coeffAbsSum (P : Poly) : Nat → R
  | 0 => R.abs (coeff P 0)
  | d + 1 => coeffAbsSum P d + R.abs (coeff P (d + 1))

theorem coeffAbsSum_nonneg (P : Poly) : ∀ d : Nat, (0 : R) ≤ coeffAbsSum P d
  | 0 => R.abs_nonneg _
  | d + 1 => by
    unfold coeffAbsSum
    have := R.add_le_add (coeffAbsSum_nonneg P d) (R.abs_nonneg (coeff P (d + 1)))
    rw [R.add_zero] at this; exact this

theorem abs_eval_le_coeffAbsSum_pow : ∀ (d : Nat) (P : Poly) {x : R},
    DegLe P d → (1 : R) ≤ R.abs x → R.abs (eval P x) ≤ coeffAbsSum P d * powR (R.abs x) d
  | 0, P, x, hdeg, _ => by
    have hpeq : PolyEq P [coeff P 0] := by
      intro k; cases k with
      | zero => rfl
      | succ j => rw [hdeg (j + 1) (by omega)]; cases j <;> rfl
    rw [eval_eq_of_polyEq hpeq, coeffAbsSum, powR, R.mul_one]
    have he0 : eval [coeff P 0] x = coeff P 0 := by
      change coeff P 0 + x * 0 = coeff P 0; rw [R.mul_zero, R.add_zero]
    rw [he0]; exact R.le_refl _
  | d + 1, P, x, hdeg, hx1 => by
    let Q := sub P (scale (coeff P (d + 1)) (monomial (d + 1)))
    have hQdeg : DegLe Q d := by
      intro k hk
      unfold Q; rw [coeff_sub, coeff_scale, coeff_monomial]
      by_cases hkd : k = d + 1
      · subst hkd; simp [R.mul_one, R.sub_self]
      · have hgt : d + 1 < k := by omega
        simp [hkd, hdeg k hgt, R.mul_zero, R.sub_self]
    have hQcoeff : ∀ j ≤ d, coeff Q j = coeff P j := by
      intro j hj
      unfold Q; rw [coeff_sub, coeff_scale, coeff_monomial]
      have hne : j ≠ d + 1 := by omega
      have hz0 : -(0 : R) = 0 := by have := R.add_neg_cancel 0; rw [R.zero_add] at this; exact this
      simp [hne, R.mul_zero, R.sub_eq_add_neg, hz0, R.add_zero]
    have hsum_eq : coeffAbsSum Q d = coeffAbsSum P d := by
      have aux : ∀ m ≤ d, coeffAbsSum Q m = coeffAbsSum P m := by
        intro m hm; induction m with
        | zero => unfold coeffAbsSum; rw [hQcoeff 0 (by omega)]
        | succ m ih => unfold coeffAbsSum; rw [ih (by omega), hQcoeff (m + 1) hm]
      exact aux d (Nat.le_refl d)
    have ih := abs_eval_le_coeffAbsSum_pow d Q hQdeg hx1
    rw [hsum_eq] at ih
    have hev : eval P x = eval Q x + coeff P (d + 1) * powR x (d + 1) := by
      have : eval Q x = eval P x - coeff P (d + 1) * powR x (d + 1) := by
        unfold Q; rw [eval_sub, eval_scale, eval_monomial]
      rw [this, R.sub_eq_add_neg, R.add_assoc, R.neg_add_cancel, R.add_zero]
    rw [hev]
    have htri := R.abs_add (eval Q x) (coeff P (d + 1) * powR x (d + 1))
    have habs_pow : ∀ k : Nat, R.abs (powR x k) = powR (R.abs x) k := by
      intro k; induction k with
      | zero => unfold powR; exact R.abs_of_nonneg (R.le_of_lt r_one_pos)
      | succ k ihk => unfold powR; rw [R.abs_mul, ihk]
    rw [R.abs_mul, habs_pow] at htri
    have hxpos : 0 < R.abs x := R.lt_of_lt_of_le r_one_pos hx1
    have hpow_le : powR (R.abs x) d ≤ powR (R.abs x) (d + 1) := by
      change powR (R.abs x) d ≤ R.abs x * powR (R.abs x) d
      have hm := R.mul_le_mul_of_nonneg_left hx1 (R.le_of_lt (powR_pos hxpos d))
      rw [R.mul_comm _ (R.abs x), R.mul_comm _ (1 : R), R.one_mul] at hm
      exact hm
    have ht1 : coeffAbsSum P d * powR (R.abs x) d ≤ coeffAbsSum P d * powR (R.abs x) (d + 1) :=
      R.mul_le_mul_of_nonneg_left hpow_le (coeffAbsSum_nonneg P d)
    unfold coeffAbsSum
    rw [R.right_distrib]
    exact R.le_trans htri (R.add_le_add (R.le_trans ih ht1) (R.le_refl _))

/-- Negative-infinity sign lemma: a polynomial of degree `d + 1` with positive leading
    coefficient attains the sign of `(-1)^(d+1)` at some `L < B`. -/
theorem exists_lt_sign_at_neg_inf {P : Poly} {d : Nat} (hdeg : DegLe P (d + 1))
    (hlead : 0 < coeff P (d + 1)) (B : R) :
    ∃ L : R, L < B ∧
      (if (d + 1) % 2 = 0 then 0 < eval P L else eval P L < 0) := by
  let c := coeff P (d + 1)
  have hcne : c ≠ 0 := fun h => R.lt_irrefl 0 (h ▸ hlead)
  let Rlow := sub P (scale c (monomial (d + 1)))
  have hRdeg : DegLe Rlow d := by
    intro k hk
    unfold Rlow; rw [coeff_sub, coeff_scale, coeff_monomial]
    by_cases hkd : k = d + 1
    · subst hkd; simp [c, R.mul_one, R.sub_self]
    · have hgt : d + 1 < k := by omega
      simp [hkd, hdeg k hgt, R.mul_zero, R.sub_self]
  let C := coeffAbsSum Rlow d
  let U0 := (1 + R.abs B) + (C + 1) * R.inv c
  obtain ⟨k, hk⟩ := R.exists_twoPow_gt U0
  let u := R.ofQ (Q.twoPow k)
  have h1_le_U0 : (1 : R) < U0 := by
    have hB0 : (0 : R) ≤ R.abs B := R.abs_nonneg B
    have hC1 : (0 : R) < (C + 1) * R.inv c := by
      have hpC : (0 : R) < C + 1 := by
        have := R.add_le_add (coeffAbsSum_nonneg Rlow d) (R.le_refl 1)
        rw [R.zero_add] at this; exact R.lt_of_lt_of_le r_one_pos this
      exact R.mul_pos hpC (r_inv_pos hlead)
    have h1B : (1 : R) ≤ 1 + R.abs B := by
      have := R.add_le_add (R.le_refl 1) hB0; rw [R.add_zero] at this; exact this
    have hlt : 1 + R.abs B < U0 := by
      have := R.add_lt_add_left hC1 (1 + R.abs B); rw [R.add_zero] at this; exact this
    exact R.lt_of_le_of_lt h1B hlt
  have hu_gt_1 : (1 : R) < u := R.lt_trans h1_le_U0 hk
  have hu_pos : (0 : R) < u := R.lt_trans r_one_pos hu_gt_1
  let L := -u
  have hLB : L < B := by
    have hBmB : -B ≤ R.abs B := R.neg_le_abs_self B
    have h1 : R.abs B < 1 + R.abs B := by
      have := R.add_lt_add_right r_one_pos (R.abs B); rw [R.zero_add] at this; exact this
    have hC1 : (0 : R) < (C + 1) * R.inv c := by
      have hpC : (0 : R) < C + 1 := by
        have := R.add_le_add (coeffAbsSum_nonneg Rlow d) (R.le_refl 1)
        rw [R.zero_add] at this; exact R.lt_of_lt_of_le r_one_pos this
      exact R.mul_pos hpC (r_inv_pos hlead)
    have h2 : 1 + R.abs B < U0 := by
      have := R.add_lt_add_left hC1 (1 + R.abs B); rw [R.add_zero] at this; exact this
    have hmB_lt_u : -B < u := R.lt_of_le_of_lt hBmB (R.lt_trans h1 (R.lt_trans h2 hk))
    have := R.add_lt_add_right hmB_lt_u (B + -u)
    have hl : -B + (B + -u) = -u := R.neg_add_cancel_left B (-u)
    have hr : u + (B + -u) = B := by rw [R.add_comm B (-u), R.add_neg_cancel_left]
    rw [hl, hr] at this; exact this
  refine ⟨L, hLB, ?_⟩
  have habsL : R.abs L = u := by
    dsimp only [L]; rw [R.abs_neg, R.abs_of_nonneg (R.le_of_lt hu_pos)]
  have hRbound : R.abs (eval Rlow L) ≤ C * powR u d := by
    have hb := abs_eval_le_coeffAbsSum_pow d Rlow hRdeg (by rw [habsL]; exact R.le_of_lt hu_gt_1)
    rw [habsL] at hb; exact hb
  have hcu_gt_C : C < c * u := by
    have hgt : (C + 1) * R.inv c < u := by
      have hpos1B : (0 : R) < 1 + R.abs B := by
        have := R.add_le_add (R.le_refl 1) (R.abs_nonneg B); rw [R.add_zero] at this
        exact R.lt_of_lt_of_le r_one_pos this
      have hlt : (C + 1) * R.inv c < U0 := by
        have := R.add_lt_add_right hpos1B ((C + 1) * R.inv c); rw [R.zero_add] at this; exact this
      exact R.lt_trans hlt hk
    have hm := R.mul_lt_mul_of_pos_left hgt hlead
    have hc_cancel : c * ((C + 1) * R.inv c) = C + 1 := by
      calc
        c * ((C + 1) * R.inv c) = (C + 1) * (c * R.inv c) := by
          simp only [R.mul_assoc, R.mul_left_comm, R.mul_comm]
        _ = C + 1 := by rw [R.mul_inv_cancel hcne, R.mul_one]
    rw [hc_cancel] at hm
    have hCC1 : C < C + 1 := by
      have := R.add_lt_add_left r_one_pos C; rw [R.add_zero] at this; exact this
    exact R.lt_trans hCC1 hm
  have hdom : C * powR u d < c * powR u (d + 1) := by
    change C * powR u d < c * (u * powR u d)
    have hpd : 0 < powR u d := powR_pos hu_pos d
    have hm := R.mul_lt_mul_of_pos_left hcu_gt_C hpd
    rw [R.mul_comm (powR u d) C, R.mul_comm (powR u d) (c * u), R.mul_assoc c u] at hm
    exact hm
  have habs_lt : R.abs (eval Rlow L) < c * powR u (d + 1) := R.lt_of_le_of_lt hRbound hdom
  have hevQ : eval P L = eval Rlow L + c * powR L (d + 1) := by
    have : eval Rlow L = eval P L - c * powR L (d + 1) := by
      unfold Rlow; rw [eval_sub, eval_scale, eval_monomial]
    rw [this, R.sub_eq_add_neg, R.add_assoc, R.neg_add_cancel, R.add_zero]
  rw [hevQ]
  have hsignL : powR L (d + 1) = if (d + 1) % 2 = 0 then powR u (d + 1) else -powR u (d + 1) :=
    powR_neg_sign u (d + 1)
  rw [hsignL]
  by_cases hpar : (d + 1) % 2 = 0
  · simp only [hpar, ↓reduceIte]
    have hnegR : -eval Rlow L ≤ R.abs (eval Rlow L) := R.neg_le_abs_self (eval Rlow L)
    have hlt : -eval Rlow L < c * powR u (d + 1) := R.lt_of_le_of_lt hnegR habs_lt
    have hsum := R.add_lt_add_left hlt (eval Rlow L)
    rw [R.add_neg_cancel] at hsum; exact hsum
  · simp only [hpar, ↓reduceIte, R.mul_neg]
    have hleR : eval Rlow L ≤ R.abs (eval Rlow L) := R.le_abs_self (eval Rlow L)
    have hlt : eval Rlow L < c * powR u (d + 1) := R.lt_of_le_of_lt hleR habs_lt
    have hsum := R.add_lt_add_right hlt (-(c * powR u (d + 1)))
    rw [R.add_neg_cancel] at hsum; exact hsum

theorem altSigns_append_last (Q : Poly) :
    ∀ (pos : Bool) (x₀ : R) (rest : List R) (L : R),
      AltSigns pos Q (x₀ :: rest) →
      L < (match rest.getLast? with | none => x₀ | some z => z) →
      (if (if rest.length % 2 = 0 then !pos else pos) then 0 < eval Q L else eval Q L < 0) →
      AltSigns pos Q ((x₀ :: rest) ++ [L])
  | pos, x₀, [], L, hx₀, hLlt, hLsign => by
    dsimp only [List.getLast?, List.length] at hLlt hLsign ⊢
    exact ⟨hLlt, hx₀, hLsign⟩
  | pos, x₀, [x₁], L, ⟨hx₁₀, hx₀s, hx₁s⟩, hLlt, hLsign => by
    dsimp only [List.getLast?, List.length] at hLlt hLsign ⊢
    have hbn : (!(!pos)) = pos := Bool.not_not pos
    refine ⟨hx₁₀, hx₀s, hLlt, hx₁s, ?_⟩
    unfold AltSigns
    rw [hbn]; exact hLsign
  | pos, x₀, x₁ :: x₂ :: ys, L, ⟨hx₁₀, hx₀s, hrest⟩, hLlt, hLsign => by
    have hlast : (x₁ :: x₂ :: ys).getLast? = (x₂ :: ys).getLast? := rfl
    rw [hlast] at hLlt
    have hpar : (if (x₁ :: x₂ :: ys).length % 2 = 0 then !pos else pos) =
                (if (x₂ :: ys).length % 2 = 0 then !(!pos) else !pos) := by
      have hlen : (x₁ :: x₂ :: ys).length = (x₂ :: ys).length + 1 := rfl
      rw [hlen]
      by_cases he : (x₂ :: ys).length % 2 = 0
      · have ho : ((x₂ :: ys).length + 1) % 2 = 1 := by omega
        rw [if_pos he, if_neg (by omega : ((x₂ :: ys).length + 1) % 2 ≠ 0), Bool.not_not]
      · have ho : ((x₂ :: ys).length + 1) % 2 = 0 := by omega
        rw [if_neg he, if_pos ho]
    rw [hpar] at hLsign
    exact ⟨hx₁₀, hx₀s, altSigns_append_last Q (!pos) x₁ (x₂ :: ys) L hrest hLlt hLsign⟩

/-- **Master Interlacing Theorem**:
    If `SplitsNegSimple P d`, `0 < r`, and `s = natR d` (case 1) or `natR d < s` (case 2),
    then `interlaceOp r s P` satisfies `SplitsNegSimple` of degree `d` or `d + 1` respectively. -/
theorem interlaceOp_preserves_negSimpleRoots {P : Poly} {d : Nat}
    (hP : SplitsNegSimple P d) {r s : R} (hr : 0 < r) :
    (s = natR d → SplitsNegSimple (interlaceOp r s P) d) ∧
    (natR d < s → SplitsNegSimple (interlaceOp r s P) (d + 1)) := by
  rcases hP with ⟨c, rs, hc, hlen, hdec, hpeq⟩
  let P₀ := prodLinear c rs
  have hP₀_deg := prodLinear_degLe_and_lead c rs
  rw [hlen] at hP₀_deg
  have hQeq : PolyEq (interlaceOp r s P) (interlaceOp r s P₀) := interlaceOp_polyEq r s hpeq
  let Q₀ := interlaceOp r s P₀
  have hQ₀_deg := interlaceOp_degLe_and_lead r s hP₀_deg.1
  rw [hP₀_deg.2] at hQ₀_deg
  have halt0 : AltSigns true Q₀ (0 :: rs) := interlaceOp_altSigns_zero_cons hr s hc hdec
  constructor
  · intro hsd
    have hlead0 : coeff Q₀ (d + 1) = 0 := by
      rw [hQ₀_deg.2, hsd, R.sub_self, R.zero_mul]
    have hQ₀_deg_d : DegLe Q₀ d := by
      intro k hk
      by_cases hkd1 : k = d + 1
      · subst hkd1; exact hlead0
      · exact hQ₀_deg.1 k (by omega)
    obtain ⟨etas, hetas_len, hetas_dec, hetas_roots, _⟩ :=
      roots_of_altSigns_cons Q₀ true 0 rs (R.le_refl 0) halt0
    rw [hlen] at hetas_len
    have hfac := factor_of_nodup_roots etas Q₀ (strictlyDecNeg_nodup hetas_dec)
                   (hetas_len ▸ hQ₀_deg_d) hetas_roots
    rw [hetas_len] at hfac
    let c' := coeff Q₀ d
    have hq0_pos : 0 < eval Q₀ 0 := by
      cases rs with
      | nil => exact halt0
      | cons _ _ => exact halt0.2.1
    have hprod_pos : 0 < eval (prodLinear 1 etas) 0 :=
      eval_prodLinear_pos_of_gt r_one_pos (strictlyDecNeg_neg hetas_dec)
    have hscale_prod : ∀ (a : R) (us : List R) (x : R),
        eval (prodLinear a us) x = a * eval (prodLinear 1 us) x := by
      intro a us x; induction us with
      | nil =>
        change a + x * 0 = a * (1 + x * 0)
        rw [R.mul_zero, R.add_zero, R.add_zero, R.mul_one]
      | cons u us ih =>
        unfold prodLinear; rw [eval_mulLinear, eval_mulLinear, ih]
        simp only [R.mul_assoc, R.mul_left_comm, R.mul_comm]
    have hc'_pos : 0 < c' := by
      rw [eval_eq_of_polyEq hfac 0, hscale_prod c' etas 0] at hq0_pos
      rcases R.lt_trichotomy c' 0 with hn | hz | hp
      · exfalso
        have hm := R.mul_pos (r_neg_pos hn) hprod_pos
        rw [R.neg_mul] at hm
        have := R.add_lt_add_right hm (c' * eval (prodLinear 1 etas) 0)
        rw [R.zero_add, R.neg_add_cancel] at this
        exact R.lt_irrefl 0 (R.lt_trans hq0_pos this)
      · exfalso; rw [hz, R.zero_mul] at hq0_pos; exact R.lt_irrefl 0 hq0_pos
      · exact hp
    exact ⟨c', etas, hc'_pos, hetas_len, hetas_dec, polyEq_trans hQeq hfac⟩
  · intro hsgt
    have hc'_pos : 0 < coeff Q₀ (d + 1) := by
      rw [hQ₀_deg.2]
      exact R.mul_pos (R.sub_pos.mpr hsgt) hc
    let B : R := match rs.getLast? with | none => 0 | some z => z
    obtain ⟨L, hLB, hLsign⟩ := exists_lt_sign_at_neg_inf hQ₀_deg.1 hc'_pos B
    have hpar_eq : (if rs.length % 2 = 0 then (!true) else true) = decide ((d + 1) % 2 = 0) := by
      rw [hlen]
      by_cases he : d % 2 = 0
      · have ho : (d + 1) % 2 = 1 := by omega
        simp [he, ho]
      · have ho : d % 2 = 1 := by omega
        have he2 : (d + 1) % 2 = 0 := by omega
        simp [ho, he2]
    have hLsign' : (if (if rs.length % 2 = 0 then (!true) else true) then 0 < eval Q₀ L else eval Q₀ L < 0) := by
      rw [hpar_eq]
      by_cases h : (d + 1) % 2 = 0 <;> simp [h] at hLsign ⊢ <;> exact hLsign
    have halt_ext : AltSigns true Q₀ (0 :: (rs ++ [L])) :=
      altSigns_append_last Q₀ true 0 rs L halt0 hLB hLsign'
    obtain ⟨etas, hetas_len, hetas_dec, hetas_roots, _⟩ :=
      roots_of_altSigns_cons Q₀ true 0 (rs ++ [L]) (R.le_refl 0) halt_ext
    have hetas_len' : etas.length = d + 1 := by
      rw [hetas_len, List.length_append, hlen]; rfl
    have hfac := factor_of_nodup_roots etas Q₀ (strictlyDecNeg_nodup hetas_dec)
                   (hetas_len' ▸ hQ₀_deg.1) hetas_roots
    rw [hetas_len'] at hfac
    exact ⟨coeff Q₀ (d + 1), etas, hc'_pos, hetas_len', hetas_dec, polyEq_trans hQeq hfac⟩

/-! ### Linearity of `interlaceOp` and Scaling of `SplitsNegSimple` -/

theorem natR_add : ∀ a b : Nat, natR (a + b) = natR a + natR b
  | a, 0 => by rw [Nat.add_zero]; change natR a = natR a + 0; rw [R.add_zero]
  | a, b + 1 => by
    rw [Nat.add_succ]
    change natR (a + b) + 1 = natR a + (natR b + 1)
    rw [natR_add a b, R.add_assoc]

theorem natR_sub {a b : Nat} (h : b ≤ a) : natR (a - b) = natR a - natR b := by
  obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le h
  have hsub : a - b = d := by omega
  rw [hsub, hd, natR_add b d]
  rw [R.add_comm (natR b) (natR d), R.sub_eq_add_neg, R.add_assoc, R.add_neg_cancel, R.add_zero]

theorem natR_lt_of_lt {a b : Nat} (h : a < b) : natR a < natR b := by
  have hb : b = a + ((b - a - 1) + 1) := by omega
  rw [hb, natR_add]
  have hp := natR_pos (b - a - 1)
  have hlt := R.add_lt_add_left hp (natR a)
  rw [R.add_zero] at hlt
  exact hlt

theorem interlaceOp_monomial (r s : R) (k : Nat) :
    PolyEq (interlaceOp r s (monomial k))
           (add (scale (r + natR k) (monomial k)) (scale (s - natR k) (monomial (k + 1)))) := by
  have hz0 : -(0 : R) = 0 := by have := R.add_neg_cancel 0; rw [R.zero_add] at this; exact this
  intro j
  unfold interlaceOp
  rw [coeff_add, coeff_sub, coeff_add, coeff_scale, coeff_scale,
      coeff_add, coeff_scale, coeff_scale]
  cases j with
  | zero =>
    rw [(coeff_mulX _).1, (coeff_mulX _).1, (coeff_mulX _).1,
        R.sub_self, R.zero_add, R.mul_zero, R.add_zero]
    have hm1 : coeff (monomial (k + 1)) 0 = 0 := rfl
    rw [hm1, R.mul_zero, R.add_zero, coeff_monomial]
    cases k with
    | zero =>
      simp only [↓reduceIte]
      change r * 1 = (r + 0) * 1
      rw [R.add_zero]
    | succ k' =>
      have hne : 0 ≠ k' + 1 := by omega
      simp only [hne, ↓reduceIte, R.mul_zero]
  | succ j' =>
    cases j' with
    | zero =>
      rw [(coeff_mulX _).2, (coeff_mulX _).2, (coeff_mulX _).1, (coeff_mulX _).2,
          coeff_deriv, R.sub_eq_add_neg, hz0, R.add_zero]
      cases k with
      | zero =>
        have h00 : coeff (monomial 0) 0 = 1 := rfl
        have h01 : coeff (monomial 0) 1 = 0 := rfl
        have h11 : coeff (monomial 1) 1 = 1 := rfl
        have hn0 : natR 0 = 0 := rfl
        simp only [h01, h00, h11, hn0, R.mul_zero, R.mul_one, R.zero_add, R.add_zero,
                   R.sub_eq_add_neg, hz0]
      | succ k' =>
        cases k' with
        | zero =>
          have h10 : coeff (monomial 1) 0 = 0 := rfl
          have h11 : coeff (monomial 1) 1 = 1 := rfl
          have h21 : coeff (monomial 2) 1 = 0 := rfl
          simp only [h11, h10, h21, R.mul_one, R.mul_zero, R.add_zero, R.zero_add, R.add_comm]
        | succ k'' =>
          have ha : coeff (monomial (k'' + 2)) 1 = 0 := by
            rw [coeff_monomial, if_neg (by omega)]
          have hb : coeff (monomial (k'' + 2)) 0 = 0 := rfl
          have hc : coeff (monomial (k'' + 3)) 1 = 0 := by
            rw [coeff_monomial, if_neg (by omega)]
          simp only [ha, hb, hc, R.mul_zero, R.add_zero]
    | succ i =>
      rw [(coeff_mulX _).2, (coeff_mulX _).2, (coeff_mulX _).2, (coeff_mulX _).2,
          coeff_deriv, coeff_deriv]
      rw [coeff_monomial k (i + 1 + 1), coeff_monomial k (i + 1), coeff_monomial (k + 1) (i + 1 + 1)]
      by_cases h1 : i + 1 + 1 = k
      · subst h1
        have h2 : i + 1 ≠ i + 1 + 1 := by omega
        have h3 : i + 1 + 1 ≠ (i + 1 + 1) + 1 := by omega
        simp only [↓reduceIte, h2, h3, R.mul_zero, R.mul_one, R.add_zero, R.zero_add,
                   R.sub_eq_add_neg, hz0, R.add_comm]
      · by_cases h2 : i + 1 = k
        · subst h2
          simp only [h1, ↓reduceIte, R.mul_zero, R.mul_one, R.zero_add]
          rw [R.sub_eq_add_neg, R.zero_add, R.add_comm (-natR (i + 1)) s]; rfl
        · have h3 : i + 1 + 1 ≠ k + 1 := by omega
          simp only [h1, h2, h3, ↓reduceIte, R.mul_zero, R.add_zero, R.sub_self]

theorem interlaceOp_nil (r s : R) : PolyEq (interlaceOp r s []) [] := by
  have hz0 : -(0 : R) = 0 := by have := R.add_neg_cancel 0; rw [R.zero_add] at this; exact this
  intro j
  unfold interlaceOp
  rw [coeff_add, coeff_sub, coeff_add, coeff_scale, coeff_scale]
  cases j with
  | zero =>
    rw [(coeff_mulX _).1, (coeff_mulX _).1, (coeff_mulX _).1, R.sub_self, R.zero_add]
    change r * 0 + s * 0 = 0
    rw [R.mul_zero, R.mul_zero, R.add_zero]
  | succ j' =>
    cases j' with
    | zero =>
      rw [(coeff_mulX _).2, (coeff_mulX _).2, (coeff_mulX _).1, (coeff_mulX _).2]
      change (0 : R) - 0 + (r * 0 + s * 0) = 0
      rw [R.sub_self, R.zero_add, R.mul_zero, R.mul_zero, R.add_zero]
    | succ i =>
      rw [(coeff_mulX _).2, (coeff_mulX _).2, (coeff_mulX _).2, (coeff_mulX _).2]
      change coeff [] (i + 1) - coeff [] i + (r * coeff [] (i + 2) + s * coeff [] (i + 1)) = 0
      change (0 : R) - 0 + (r * 0 + s * 0) = 0
      rw [R.sub_eq_add_neg, hz0, R.add_zero, R.mul_zero, R.mul_zero, R.add_zero, R.add_zero]

theorem interlaceOp_add (r s : R) (P₁ P₂ : Poly) :
    PolyEq (interlaceOp r s (add P₁ P₂)) (add (interlaceOp r s P₁) (interlaceOp r s P₂)) := by
  have hz0 : -(0 : R) = 0 := by have := R.add_neg_cancel 0; rw [R.zero_add] at this; exact this
  intro j
  unfold interlaceOp
  simp only [coeff_add, coeff_sub, coeff_scale, R.left_distrib]
  cases j with
  | zero =>
    simp only [(coeff_mulX _).1, R.sub_self, R.mul_zero, R.add_zero, R.zero_add,
               R.add_assoc, R.add_left_comm, R.add_comm]
  | succ j' =>
    simp only [(coeff_mulX _).2, coeff_add P₁ P₂ j', R.left_distrib, (deriv_add P₁ P₂) j', coeff_add]
    cases j' with
    | zero =>
      simp only [(coeff_mulX _).1, R.sub_eq_add_neg, R.neg_add, hz0, R.add_zero, R.zero_add,
                 R.add_assoc, R.add_left_comm, R.add_comm]
    | succ i =>
      simp only [(coeff_mulX _).2, (deriv_add P₁ P₂) i, coeff_add,
                 R.sub_eq_add_neg, R.neg_add, R.add_assoc, R.add_left_comm, R.add_comm]

theorem scale_prodLinear (s c : R) : ∀ (rs : List R),
    PolyEq (scale s (prodLinear c rs)) (prodLinear (s * c) rs)
  | [] => polyEq_refl _
  | u :: rs => by
    have ih := scale_prodLinear s c rs
    intro k
    unfold prodLinear mulLinear
    have ihk : s * coeff (prodLinear c rs) k = coeff (prodLinear (s * c) rs) k := by
      rw [← coeff_scale, ih k]
    rw [coeff_scale, coeff_sub, coeff_sub, coeff_scale, coeff_scale, R.mul_sub,
        ← R.mul_assoc s u, R.mul_comm s u, R.mul_assoc u s, ihk]
    cases k with
    | zero =>
      rw [(coeff_mulX _).1, (coeff_mulX _).1, R.mul_zero]
    | succ j =>
      have ihj : s * coeff (prodLinear c rs) j = coeff (prodLinear (s * c) rs) j := by
        rw [← coeff_scale, ih j]
      rw [(coeff_mulX _).2, (coeff_mulX _).2, ihj]

theorem splitsNegSimple_of_polyEq {P₁ P₂ : Poly} {d : Nat}
    (heq : PolyEq P₁ P₂) (h : SplitsNegSimple P₂ d) : SplitsNegSimple P₁ d := by
  rcases h with ⟨c, rs, hc, hlen, hdec, hfac⟩
  exact ⟨c, rs, hc, hlen, hdec, polyEq_trans heq hfac⟩

theorem splitsNegSimple_of_scale {r : R} (hr : 0 < r) {P₁ P₂ : Poly} {d : Nat}
    (heq : PolyEq (scale r P₁) P₂) (h : SplitsNegSimple P₂ d) : SplitsNegSimple P₁ d := by
  have hrne : r ≠ 0 := fun hz => R.lt_irrefl 0 (hz ▸ hr)
  have hrinv : 0 < R.inv r := r_inv_pos hr
  rcases h with ⟨c, rs, hc, hlen, hdec, hfac⟩
  refine ⟨R.inv r * c, rs, R.mul_pos hrinv hc, hlen, hdec, fun k => ?_⟩
  have hcancel : R.inv r * (r * coeff P₁ k) = coeff P₁ k := by
    rw [← R.mul_assoc, R.mul_comm (R.inv r) r, R.mul_inv_cancel hrne, R.one_mul]
  rw [← hcancel, ← coeff_scale r P₁ k, heq k, hfac k, ← coeff_scale (R.inv r),
      (scale_prodLinear (R.inv r) c rs) k]

end Poly

/-! ## 5. Combinatorial Multiset Permutations and Universal Real-Simplicity of `A_α^{ms}(t)` -/

def countNat (v : Nat) : List Nat → Nat
  | [] => 0
  | x :: xs => (if x = v then 1 else 0) + countNat v xs

theorem countNat_pos_of_mem {v : Nat} : ∀ {w : List Nat}, v ∈ w → 0 < countNat v w
  | [], h => nomatch h
  | _ :: _, h => by
    unfold countNat
    cases h with
    | head => simp only [↓reduceIte]; omega
    | tail _ hm => have := countNat_pos_of_mem hm; omega

def des : List Nat → Nat
  | [] => 0
  | [_] => 0
  | x :: y :: ys => (if y < x then 1 else 0) + des (y :: ys)

theorem des_le_length : ∀ (w : List Nat), des w ≤ w.length
  | [] => Nat.le_refl 0
  | [_] => Nat.zero_le 1
  | x :: y :: ys => by
    unfold des
    have ih := des_le_length (y :: ys)
    have hl : (x :: y :: ys).length = (y :: ys).length + 1 := rfl
    rw [hl]
    by_cases h : y < x <;> simp only [h, ↓reduceIte] <;> omega

def insertAllWays (m : Nat) : List Nat → List (List Nat)
  | [] => [[m]]
  | x :: xs => (m :: x :: xs) :: (insertAllWays m xs).map (x :: ·)

def deleteEachMax (m : Nat) : List Nat → List (List Nat)
  | [] => []
  | x :: xs => (if x = m then [xs] else []) ++ (deleteEachMax m xs).map (x :: ·)

def countWord (w : List Nat) : List (List Nat) → Nat
  | [] => 0
  | u :: us => (if u = w then 1 else 0) + countWord w us

theorem countWord_append (w : List Nat) : ∀ (L₁ L₂ : List (List Nat)),
    countWord w (L₁ ++ L₂) = countWord w L₁ + countWord w L₂
  | [], _ => by simp [countWord]
  | _ :: us, L₂ => by
    simp only [List.cons_append, countWord, countWord_append w us L₂, Nat.add_assoc]

theorem countWord_nil_map_cons (a : Nat) : ∀ (L : List (List Nat)),
    countWord [] (L.map (a :: ·)) = 0
  | [] => rfl
  | _ :: us => by simp [countWord, countWord_nil_map_cons a us]

theorem countWord_cons_map_cons (a b : Nat) (bs : List Nat) : ∀ (L : List (List Nat)),
    countWord (b :: bs) (L.map (a :: ·)) = if a = b then countWord bs L else 0
  | [] => by simp [countWord]
  | u :: us => by
    simp only [List.map_cons, countWord, countWord_cons_map_cons a b bs us]
    by_cases hab : a = b
    · subst hab
      by_cases hub : u = bs
      · subst hub; simp
      · have hne : (a :: u) ≠ (a :: bs) := fun h => hub (List.cons.inj h).2
        simp [hub, hne]
    · have hne : (a :: u) ≠ (b :: bs) := fun h => hab (List.cons.inj h).1
      simp [hab, hne]

/-- Exact Insertion–Deletion Reciprocity Law. -/
theorem countWord_insert_eq_delete (m : Nat) : ∀ (w w' : List Nat),
    countWord w' (insertAllWays m w) = countWord w (deleteEachMax m w')
  | [], [] => rfl
  | [], y :: ys => by
    unfold insertAllWays deleteEachMax
    rw [countWord_append, countWord_nil_map_cons, Nat.add_zero]
    by_cases hym : y = m
    · subst hym
      by_cases hys : ys = [] <;> simp [hys, countWord]
    · have hne : [m] ≠ y :: ys := fun h => hym (List.cons.inj h).1.symm
      simp [hym, hne, countWord]
  | _ :: _, [] => by
    unfold insertAllWays deleteEachMax
    simp only [countWord]
    rw [countWord_nil_map_cons]; rfl
  | x :: xs, y :: ys => by
    unfold insertAllWays deleteEachMax
    rw [countWord_append, countWord_cons_map_cons]
    simp only [countWord]
    rw [countWord_cons_map_cons, countWord_insert_eq_delete m xs ys]
    by_cases hym : y = m
    · subst hym
      simp only [↓reduceIte, countWord, Nat.add_zero]
      have hhead : (if (y :: x :: xs) = (y :: ys) then 1 else 0) =
                   (if ys = x :: xs then 1 else 0) := by
        by_cases h1 : x :: xs = ys
        · subst h1; simp
        · have ha : (y :: x :: xs) ≠ (y :: ys) := fun h => h1 (List.cons.inj h).2
          have hb : ys ≠ x :: xs := fun h => h1 h.symm
          simp [ha, hb]
      have htail : (if x = y then countWord xs (deleteEachMax y ys) else 0) =
                   (if y = x then countWord xs (deleteEachMax y ys) else 0) := by
        by_cases hxy : x = y
        · subst hxy; simp
        · have hyx : y ≠ x := fun h => hxy h.symm
          simp [hxy, hyx]
      rw [hhead, htail]
    · have hmy : m ≠ y := fun h => hym h.symm
      have hne1 : (m :: x :: xs) ≠ (y :: ys) := fun h => hmy (List.cons.inj h).1
      by_cases hxy : x = y
      · subst hxy; simp [hym, hne1, countWord]
      · have hyx : y ≠ x := fun h => hxy h.symm
        simp [hym, hxy, hyx, hne1, countWord]

theorem length_deleteEachMax (m : Nat) : ∀ (w' : List Nat),
    (deleteEachMax m w').length = countNat m w'
  | [] => rfl
  | x :: xs => by
    unfold deleteEachMax countNat
    rw [List.length_append, List.length_map, length_deleteEachMax m xs]
    by_cases h : x = m <;> simp [h]

theorem mem_iff_countWord_pos {w : List Nat} : ∀ {L : List (List Nat)},
    w ∈ L ↔ 0 < countWord w L
  | [] => ⟨(fun h => nomatch h), (fun h => by simp [countWord] at h)⟩
  | u :: us => by
    simp only [countWord]
    constructor
    · intro h; cases h with
      | head => simp only [↓reduceIte]; omega
      | tail _ hm => have := mem_iff_countWord_pos.mp hm; omega
    · intro h
      by_cases huw : u = w
      · subst huw; exact List.Mem.head us
      · simp [huw] at h
        exact List.Mem.tail u (mem_iff_countWord_pos.mpr h)

theorem insertAllWays_props (m : Nat) : ∀ (w w' : List Nat),
    w' ∈ insertAllWays m w →
      w'.length = w.length + 1 ∧
      countNat m w' = countNat m w + 1 ∧
      (∀ v : Nat, v ≠ m → countNat v w' = countNat v w)
  | [], w', hw' => by
    unfold insertAllWays at hw'
    cases hw' with
    | head =>
      refine ⟨rfl, ?_, ?_⟩
      · simp [countNat]
      · intro v hvm; simp [countNat, Ne.symm hvm]
    | tail _ h => nomatch h
  | x :: xs, w', hw' => by
    unfold insertAllWays at hw'
    cases hw' with
    | head =>
      refine ⟨rfl, ?_, ?_⟩
      · simp [countNat]; omega
      · intro v hvm; simp [countNat, Ne.symm hvm]
    | tail _ hm =>
      change w' ∈ List.map (x :: ·) (insertAllWays m xs) at hm
      rw [List.mem_map] at hm
      rcases hm with ⟨u, hu, rfl⟩
      obtain ⟨hlen, hcm, hcv⟩ := insertAllWays_props m xs u hu
      refine ⟨by simp [hlen], ?_, ?_⟩
      · simp only [countNat, hcm]; omega
      · intro v hvm; simp only [countNat, hcv v hvm]

theorem deleteEachMax_props (m : Nat) : ∀ (w' u : List Nat),
    u ∈ deleteEachMax m w' →
      countNat m w' = countNat m u + 1 ∧
      (∀ v : Nat, v ≠ m → countNat v u = countNat v w')
  | [], _, hu => nomatch hu
  | x :: xs, u, hu => by
    unfold deleteEachMax at hu
    rw [List.mem_append] at hu
    rcases hu with hhead | htail
    · by_cases hxm : x = m
      · subst hxm
        simp only [↓reduceIte] at hhead
        cases hhead with
        | head =>
          refine ⟨by simp [countNat]; omega, ?_⟩
          intro v hvm; simp [countNat, Ne.symm hvm]
        | tail _ hm => nomatch hm
      · simp [hxm] at hhead
    · rw [List.mem_map] at htail
      rcases htail with ⟨w₀, hw₀, rfl⟩
      obtain ⟨hcm, hcv⟩ := deleteEachMax_props m xs w₀ hw₀
      refine ⟨by simp only [countNat, hcm]; omega, ?_⟩
      intro v hvm; simp only [countNat, hcv v hvm]

theorem countNat_des_bound (m : Nat) : ∀ (x : Nat) (xs : List Nat),
    (∀ z ∈ x :: xs, z ≤ m) →
    countNat m (x :: xs) + des (x :: xs) + (if x < m then 1 else 0) ≤ (x :: xs).length
  | x, [], hall => by
    have hxm : x ≤ m := hall x (List.Mem.head [])
    simp only [countNat, des, List.length]
    by_cases h1 : x = m <;> by_cases h2 : x < m <;> simp [h1, h2] <;> omega
  | x, y :: ys, hall => by
    have hxm : x ≤ m := hall x (List.Mem.head _)
    have hym : y ≤ m := hall y (List.Mem.tail x (List.Mem.head ys))
    have ih := countNat_des_bound m y ys (fun z hz => hall z (List.Mem.tail x hz))
    have hc : countNat m (x :: y :: ys) = (if x = m then 1 else 0) + countNat m (y :: ys) := rfl
    have hd : des (x :: y :: ys) = (if y < x then 1 else 0) + des (y :: ys) := rfl
    have hl : (x :: y :: ys).length = (y :: ys).length + 1 := rfl
    rw [hc, hd, hl]
    by_cases h1 : x = m <;> by_cases h2 : y < x <;> by_cases h3 : x < m <;> by_cases h4 : y < m
    all_goals
      try rw [if_pos h1]
      try rw [if_neg h1]
      try rw [if_pos h2]
      try rw [if_neg h2]
      try rw [if_pos h3]
      try rw [if_neg h3]
      try rw [if_pos h4] at ih
      try rw [if_neg h4] at ih
      omega

theorem countNat_add_des_le_length (m : Nat) (w : List Nat) (hall : ∀ z ∈ w, z ≤ m) :
    countNat m w + des w ≤ w.length := by
  cases w with
  | nil => simp [countNat, des]
  | cons x xs =>
    have h := countNat_des_bound m x xs hall
    omega

def polySum : List Poly → Poly
  | [] => []
  | P :: Ps => Poly.add P (polySum Ps)

theorem polySum_append : ∀ (L₁ L₂ : List Poly),
    Poly.PolyEq (polySum (L₁ ++ L₂)) (Poly.add (polySum L₁) (polySum L₂))
  | [], L₂ => fun k => by
    change Poly.coeff (polySum L₂) k = Poly.coeff (Poly.add [] (polySum L₂)) k
    rw [Poly.coeff_add]; change _ = 0 + _; rw [R.zero_add]
  | P :: Ps, L₂ => fun k => by
    simp only [List.cons_append, polySum]
    simp only [Poly.coeff_add, (polySum_append Ps L₂) k, R.add_assoc]

theorem polySum_map_mulX : ∀ (Ps : List Poly),
    Poly.PolyEq (polySum (Ps.map Poly.mulX)) (Poly.mulX (polySum Ps))
  | [] => fun k => by cases k <;> rfl
  | P :: Ps => fun k => by
    simp only [List.map_cons, polySum]
    rw [Poly.coeff_add]
    cases k with
    | zero =>
      rw [(Poly.coeff_mulX _).1, (polySum_map_mulX Ps) 0, (Poly.coeff_mulX _).1,
          (Poly.coeff_mulX _).1, R.add_zero]
    | succ j =>
      rw [(Poly.coeff_mulX _).2, (polySum_map_mulX Ps) (j + 1), (Poly.coeff_mulX _).2,
          (Poly.coeff_mulX _).2, Poly.coeff_add]

theorem interlaceOp_polySum (r s : R) : ∀ (Ps : List Poly),
    Poly.PolyEq (Poly.interlaceOp r s (polySum Ps)) (polySum (Ps.map (Poly.interlaceOp r s)))
  | [] => Poly.interlaceOp_nil r s
  | P :: Ps => fun k => by
    simp only [List.map_cons, polySum]
    rw [(Poly.interlaceOp_add r s P (polySum Ps)) k, Poly.coeff_add,
        (interlaceOp_polySum r s Ps) k, Poly.coeff_add]

theorem des_cons_of_le {x y m : Nat} (hxm : x ≤ m) (hxy : ¬ (y < x)) (ys : List Nat) :
    ∀ u ∈ insertAllWays m (y :: ys), des (x :: u) = des u := by
  intro u hu
  unfold insertAllWays at hu
  cases hu with
  | head =>
    have hmx : ¬ (m < x) := by omega
    change (if m < x then 1 else 0) + des (m :: y :: ys) = des (m :: y :: ys)
    simp [hmx]
  | tail _ hm =>
    change u ∈ List.map (y :: ·) (insertAllWays m ys) at hm
    rw [List.mem_map] at hm
    rcases hm with ⟨v, _, rfl⟩
    change (if y < x then 1 else 0) + des (y :: v) = des (y :: v)
    simp [hxy]

theorem des_tail_of_gt {x y m : Nat} (hxm : x ≤ m) (hyx : y < x) (ys : List Nat) :
    Poly.PolyEq
      (Poly.add
        (polySum (((insertAllWays m (y :: ys)).map (x :: ·)).map (fun u => Poly.monomial (des u))))
        (Poly.monomial (des (x :: y :: ys) + 1)))
      (Poly.add
        (Poly.monomial (des (x :: y :: ys)))
        (Poly.mulX (polySum ((insertAllWays m (y :: ys)).map (fun u => Poly.monomial (des u)))))) := by
  have hym : y < m := Nat.lt_of_lt_of_le hyx hxm
  have hmx : ¬ (m < x) := by omega
  have hk : des (x :: y :: ys) = 1 + des (y :: ys) := by
    change (if y < x then 1 else 0) + des (y :: ys) = 1 + des (y :: ys)
    simp [hyx]
  have hd_u0 : des (m :: y :: ys) = des (x :: y :: ys) := by
    rw [hk]; change (if y < m then 1 else 0) + des (y :: ys) = 1 + des (y :: ys)
    simp [hym]
  have hd_xu0 : des (x :: m :: y :: ys) = des (x :: y :: ys) := by
    change (if m < x then 1 else 0) + des (m :: y :: ys) = des (x :: y :: ys)
    simp [hmx, hd_u0]
  have hrest_eq :
      (((insertAllWays m ys).map (y :: ·)).map (x :: ·)).map (fun u => Poly.monomial (des u)) =
      (((insertAllWays m ys).map (y :: ·)).map (fun u => Poly.monomial (des u))).map Poly.mulX := by
    induction (insertAllWays m ys) with
    | nil => rfl
    | cons v vs ih =>
      simp only [List.map_cons, ih]
      congr 1
      have hdv : des (x :: y :: v) = des (y :: v) + 1 := by
        change (if y < x then 1 else 0) + des (y :: v) = des (y :: v) + 1
        simp [hyx, Nat.add_comm]
      rw [hdv]; rfl
  intro j
  simp only [insertAllWays, List.map_cons, polySum]
  rw [hd_xu0, hd_u0, hrest_eq]
  let S := ((insertAllWays m ys).map (y :: ·)).map (fun u => Poly.monomial (des u))
  have hmulX := polySum_map_mulX S j
  have hm_succ : Poly.coeff (Poly.monomial (des (x :: y :: ys) + 1)) j =
                 Poly.coeff (Poly.mulX (Poly.monomial (des (x :: y :: ys)))) j := rfl
  have hdist : Poly.coeff (Poly.mulX (Poly.add (Poly.monomial (des (x :: y :: ys))) (polySum S))) j =
               Poly.coeff (Poly.mulX (Poly.monomial (des (x :: y :: ys)))) j +
               Poly.coeff (Poly.mulX (polySum S)) j := by
    cases j with
    | zero => rw [(Poly.coeff_mulX _).1, (Poly.coeff_mulX _).1, (Poly.coeff_mulX _).1, R.add_zero]
    | succ i => rw [(Poly.coeff_mulX _).2, (Poly.coeff_mulX _).2, (Poly.coeff_mulX _).2, Poly.coeff_add]
  rw [Poly.coeff_add, Poly.coeff_add, Poly.coeff_add, hmulX, hm_succ, hdist]
  simp only [R.add_assoc, R.add_left_comm, R.add_comm]

/-- Combinatorial descent transition sum over all insertion positions of `m` into `w`. -/
theorem sum_insertAllWays_des (m : Nat) : ∀ (w : List Nat),
    (∀ z ∈ w, z ≤ m) →
    Poly.PolyEq
      (polySum ((insertAllWays m w).map (fun u => Poly.monomial (des u))))
      (Poly.add
        (Poly.scale (Poly.natR (countNat m w + 1 + des w)) (Poly.monomial (des w)))
        (Poly.scale (Poly.natR (w.length - countNat m w - des w)) (Poly.monomial (des w + 1))))
  | [], _ => by
    intro j
    simp only [insertAllWays, List.map, polySum, countNat, des, List.length]
    rw [Poly.coeff_add, Poly.coeff_add, Poly.coeff_scale, Poly.coeff_scale]
    change Poly.coeff (Poly.monomial 0) j + 0 =
           ((0 : R) + 1) * Poly.coeff (Poly.monomial 0) j + (0 : R) * Poly.coeff (Poly.monomial 1) j
    rw [R.zero_add, R.one_mul, R.zero_mul, R.add_zero]
  | [x], hall => by
    have hxm : x ≤ m := hall x (List.Mem.head [])
    have hmx : ¬ (m < x) := by omega
    intro j
    simp only [insertAllWays, List.map, polySum, countNat, List.length]
    have hd0 : des [x] = 0 := rfl
    have hd2 : des [x, m] = 0 := by
      change (if m < x then 1 else 0) + 0 = 0; simp [hmx]
    rw [hd0, hd2]
    by_cases h1 : x = m
    · subst h1
      have hd1 : des [x, x] = 0 := by change (if x < x then 1 else 0) + 0 = 0; simp
      rw [hd1]
      simp only [↓reduceIte, Nat.add_zero]
      rw [Poly.coeff_add, Poly.coeff_add, Poly.coeff_add, Poly.coeff_scale, Poly.coeff_scale]
      change Poly.coeff (Poly.monomial 0) j + (Poly.coeff (Poly.monomial 0) j + 0) =
             (((0 : R) + 1) + 1) * Poly.coeff (Poly.monomial 0) j + (0 : R) * Poly.coeff (Poly.monomial 1) j
      rw [R.add_zero, R.zero_add, R.right_distrib, R.one_mul, R.zero_mul, R.add_zero]
    · have hlt : x < m := by omega
      have hd1 : des [m, x] = 1 := by change (if x < m then 1 else 0) + 0 = 1; simp [hlt]
      rw [hd1]
      simp only [h1, ↓reduceIte, Nat.zero_add, Nat.add_zero, Nat.sub_zero]
      rw [Poly.coeff_add, Poly.coeff_add, Poly.coeff_add, Poly.coeff_scale, Poly.coeff_scale]
      change Poly.coeff (Poly.monomial 1) j + (Poly.coeff (Poly.monomial 0) j + 0) =
             ((0 : R) + 1) * Poly.coeff (Poly.monomial 0) j + ((0 : R) + 1) * Poly.coeff (Poly.monomial 1) j
      rw [R.add_zero, R.zero_add, R.one_mul, R.one_mul, R.add_comm]
  | x :: y :: ys, hall => by
    have hxm : x ≤ m := hall x (List.Mem.head _)
    have hall' : ∀ z ∈ y :: ys, z ≤ m := fun z hz => hall z (List.Mem.tail x hz)
    have ih := sum_insertAllWays_des m (y :: ys) hall'
    let c' := countNat m (y :: ys)
    let N' := (y :: ys).length
    let k' := des (y :: ys)
    by_cases hyx : y < x
    · have hym : y < m := Nat.lt_of_lt_of_le hyx hxm
      have hbound' := countNat_des_bound m y ys hall'
      have hck_le : c' + (k' + 1) ≤ N' := by
        simp only [hym, ↓reduceIte] at hbound'
        change countNat m (y :: ys) + (des (y :: ys) + 1) ≤ (y :: ys).length
        omega
      have hk_eq : des (x :: y :: ys) = k' + 1 := by
        change (if y < x then 1 else 0) + k' = k' + 1; simp [hyx, Nat.add_comm]
      have htail_rel := des_tail_of_gt hxm hyx ys
      intro j
      have hhead_step :
          Poly.coeff (polySum ((insertAllWays m (x :: y :: ys)).map (fun u => Poly.monomial (des u)))) j =
          Poly.coeff (Poly.monomial (des (m :: x :: y :: ys))) j +
          Poly.coeff (polySum (((insertAllWays m (y :: ys)).map (x :: ·)).map (fun u => Poly.monomial (des u)))) j := by
        simp only [insertAllWays, List.map_cons, polySum]
        rw [Poly.coeff_add]
      rw [hhead_step]
      have htr := htail_rel j
      rw [Poly.coeff_add, Poly.coeff_add] at htr
      have hmulX_ih :
          Poly.coeff (Poly.mulX (polySum ((insertAllWays m (y :: ys)).map (fun u => Poly.monomial (des u))))) j =
          Poly.natR (c' + 1 + k') * Poly.coeff (Poly.monomial (k' + 1)) j +
          Poly.natR (N' - c' - k') * Poly.coeff (Poly.monomial (k' + 2)) j := by
        cases j with
        | zero =>
          rw [(Poly.coeff_mulX _).1]
          have hm1 : Poly.coeff (Poly.monomial (k' + 1)) 0 = 0 := rfl
          have hm2 : Poly.coeff (Poly.monomial (k' + 2)) 0 = 0 := rfl
          rw [hm1, hm2, R.mul_zero, R.mul_zero, R.add_zero]
        | succ i =>
          rw [(Poly.coeff_mulX _).2, ih i, Poly.coeff_add, Poly.coeff_scale, Poly.coeff_scale]
          rfl
      rw [hk_eq, hmulX_ih] at htr
      have hNsub : N' - c' - k' = (N' - c' - (k' + 1)) + 1 := by omega
      rw [hNsub, Poly.natR_add (N' - c' - (k' + 1)) 1] at htr
      have h1r : Poly.natR 1 = 1 := R.zero_add 1
      rw [h1r, R.right_distrib, R.one_mul] at htr
      have htail_val :
          Poly.coeff (polySum (((insertAllWays m (y :: ys)).map (x :: ·)).map (fun u => Poly.monomial (des u)))) j =
          Poly.natR (c' + 1 + (k' + 1)) * Poly.coeff (Poly.monomial (k' + 1)) j +
          Poly.natR (N' - c' - (k' + 1)) * Poly.coeff (Poly.monomial (k' + 2)) j := by
        have hcancel := congrArg (· + -(Poly.coeff (Poly.monomial (k' + 2)) j)) htr
        dsimp only at hcancel
        have hL : (Poly.coeff (polySum (((insertAllWays m (y :: ys)).map (x :: ·)).map (fun u => Poly.monomial (des u)))) j +
                   Poly.coeff (Poly.monomial (k' + 2)) j) +
                  -(Poly.coeff (Poly.monomial (k' + 2)) j) =
                  Poly.coeff (polySum (((insertAllWays m (y :: ys)).map (x :: ·)).map (fun u => Poly.monomial (des u)))) j := by
          rw [R.add_assoc, R.add_neg_cancel, R.add_zero]
        have hc1 : c' + 1 + (k' + 1) = (c' + 1 + k') + 1 := by omega
        rw [hc1, Poly.natR_add (c' + 1 + k') 1, h1r, R.right_distrib, R.one_mul]
        rw [hL] at hcancel
        rw [hcancel]
        simp only [R.add_assoc, R.add_left_comm, R.add_comm,
                   R.add_neg_cancel, R.neg_add_cancel, R.add_neg_cancel_left, R.neg_add_cancel_left,
                   R.add_zero, R.zero_add]
      rw [htail_val, Poly.coeff_add, Poly.coeff_scale, Poly.coeff_scale, hk_eq]
      have hlen_w : (x :: y :: ys).length = N' + 1 := rfl
      rw [hlen_w]
      by_cases hxm_eq : x = m
      · subst hxm_eq
        have hd0 : des (x :: x :: y :: ys) = k' + 1 := by
          change (if x < x then 1 else 0) + des (x :: y :: ys) = k' + 1
          simp [hk_eq]
        have hc_eq : countNat x (x :: y :: ys) = c' + 1 := by
          change (if x = x then 1 else 0) + c' = c' + 1; simp [Nat.add_comm]
        rw [hd0, hc_eq]
        have hn1 : (N' + 1) - (c' + 1) - (k' + 1) = N' - c' - (k' + 1) := by omega
        have hn2 : (c' + 1) + 1 + (k' + 1) = (c' + 1 + (k' + 1)) + 1 := by omega
        rw [hn1, hn2, Poly.natR_add _ 1, h1r, R.right_distrib, R.one_mul]
        simp only [R.add_assoc, R.add_left_comm, R.add_comm]
      · have hxlt : x < m := by omega
        have hd0 : des (m :: x :: y :: ys) = k' + 2 := by
          change (if x < m then 1 else 0) + des (x :: y :: ys) = k' + 2
          simp only [hxlt, ↓reduceIte, hk_eq]; omega
        have hc_eq : countNat m (x :: y :: ys) = c' := by
          change (if x = m then 1 else 0) + c' = c'; simp [hxm_eq]
        rw [hd0, hc_eq]
        have hn1 : (N' + 1) - c' - (k' + 1) = (N' - c' - (k' + 1)) + 1 := by omega
        rw [hn1, Poly.natR_add _ 1, h1r, R.right_distrib, R.one_mul]
        simp only [R.add_assoc, R.add_left_comm, R.add_comm]
    · have hck_le : c' + k' ≤ N' := countNat_add_des_le_length m (y :: ys) hall'
      have hk_eq : des (x :: y :: ys) = k' := by
        change (if y < x then 1 else 0) + k' = k'; simp [hyx]
      have hmap_eq :
          ((insertAllWays m (y :: ys)).map (x :: ·)).map (fun u => Poly.monomial (des u)) =
          (insertAllWays m (y :: ys)).map (fun u => Poly.monomial (des u)) := by
        have hrec : ∀ (L : List (List Nat)), (∀ u ∈ L, des (x :: u) = des u) →
            (L.map (x :: ·)).map (fun u => Poly.monomial (des u)) =
            L.map (fun u => Poly.monomial (des u)) := by
          intro L; induction L with
          | nil => intro _; rfl
          | cons u us ihu =>
            intro hL
            simp only [List.map_cons]
            rw [hL u (List.Mem.head us), ihu (fun v hv => hL v (List.Mem.tail u hv))]
        exact hrec (insertAllWays m (y :: ys)) (des_cons_of_le hxm hyx ys)
      intro j
      simp only [insertAllWays, List.map_cons, polySum]
      rw [Poly.coeff_add]
      change Poly.coeff (Poly.monomial (des (m :: x :: y :: ys))) j +
             Poly.coeff (polySum (((insertAllWays m (y :: ys)).map (x :: ·)).map (fun u => Poly.monomial (des u)))) j = _
      rw [hmap_eq, ih j, Poly.coeff_add, Poly.coeff_scale, Poly.coeff_scale,
          Poly.coeff_add, Poly.coeff_scale, Poly.coeff_scale, hk_eq]
      have hlen_w : (x :: y :: ys).length = N' + 1 := rfl
      have h1r : Poly.natR 1 = 1 := R.zero_add 1
      rw [hlen_w]
      by_cases hxm_eq : x = m
      · subst hxm_eq
        have hd0 : des (x :: x :: y :: ys) = k' := by
          change (if x < x then 1 else 0) + des (x :: y :: ys) = k'
          simp [hk_eq]
        have hc_eq : countNat x (x :: y :: ys) = c' + 1 := by
          change (if x = x then 1 else 0) + c' = c' + 1; simp [Nat.add_comm]
        rw [hd0, hc_eq]
        have hn1 : (N' + 1) - (c' + 1) - k' = N' - c' - k' := by omega
        have hn2 : (c' + 1) + 1 + k' = (c' + 1 + k') + 1 := by omega
        rw [hn1, hn2, Poly.natR_add _ 1, h1r, R.right_distrib, R.one_mul]
        simp only [c', N', k', R.add_assoc, R.add_left_comm, R.add_comm]
      · have hxlt : x < m := by omega
        have hd0 : des (m :: x :: y :: ys) = k' + 1 := by
          change (if x < m then 1 else 0) + des (x :: y :: ys) = k' + 1
          simp only [hxlt, ↓reduceIte, hk_eq]; omega
        have hc_eq : countNat m (x :: y :: ys) = c' := by
          change (if x = m then 1 else 0) + c' = c'; simp [hxm_eq]
        rw [hd0, hc_eq]
        have hn1 : (N' + 1) - c' - k' = (N' - c' - k') + 1 := by omega
        rw [hn1, Poly.natR_add _ 1, h1r, R.right_distrib, R.one_mul]
        simp only [c', N', k', R.add_assoc, R.add_left_comm, R.add_comm]

/-! ### Duplicate-Free Multiset Permutation Generation and Double-Counting Identity -/

def beqNatList : List Nat → List Nat → Bool
  | [], [] => true
  | x :: xs, y :: ys => Nat.beq x y && beqNatList xs ys
  | _, _ => false

theorem beqNatList_iff : ∀ (u v : List Nat), beqNatList u v = true ↔ u = v
  | [], [] => ⟨fun _ => rfl, fun _ => rfl⟩
  | [], _ :: _ => ⟨(fun h => nomatch h), (fun h => nomatch h)⟩
  | _ :: _, [] => ⟨(fun h => nomatch h), (fun h => nomatch h)⟩
  | x :: xs, y :: ys => by
    unfold beqNatList
    rw [Bool.and_eq_true, Nat.beq_eq, beqNatList_iff xs ys]
    exact ⟨fun ⟨h1, h2⟩ => by subst h1; subst h2; rfl,
           fun h => ⟨(List.cons.inj h).1, (List.cons.inj h).2⟩⟩

def memBool (w : List Nat) : List (List Nat) → Bool
  | [] => false
  | u :: us => beqNatList w u || memBool w us

theorem memBool_iff (w : List Nat) : ∀ (L : List (List Nat)), memBool w L = true ↔ w ∈ L
  | [] => ⟨(fun h => nomatch h), (fun h => nomatch h)⟩
  | u :: us => by
    unfold memBool
    rw [Bool.or_eq_true, beqNatList_iff w u, memBool_iff w us]
    exact ⟨fun h => match h with | Or.inl heq => heq ▸ List.Mem.head us | Or.inr hm => List.Mem.tail u hm,
           fun h => match h with | List.Mem.head _ => Or.inl rfl | List.Mem.tail _ hm => Or.inr hm⟩

def dedupWords : List (List Nat) → List (List Nat)
  | [] => []
  | w :: ws => if memBool w ws then dedupWords ws else w :: dedupWords ws

theorem mem_dedupWords (w : List Nat) : ∀ (L : List (List Nat)), w ∈ dedupWords L ↔ w ∈ L
  | [] => Iff.rfl
  | u :: us => by
    unfold dedupWords
    by_cases hm : memBool u us = true
    · rw [if_pos hm, mem_dedupWords w us]
      have hu : u ∈ us := (memBool_iff u us).mp hm
      exact ⟨fun h => List.Mem.tail u h,
             fun h => match h with | List.Mem.head _ => hu | List.Mem.tail _ h' => h'⟩
    · rw [if_neg hm]
      constructor
      · intro h; cases h with
        | head => exact List.Mem.head us
        | tail _ h' => exact List.Mem.tail u ((mem_dedupWords w us).mp h')
      · intro h; cases h with
        | head => exact List.Mem.head _
        | tail _ h' => exact List.Mem.tail u ((mem_dedupWords w us).mpr h')

theorem dedupWords_nodup : ∀ (L : List (List Nat)), ListNodup (dedupWords L)
  | [] => ListNodup.nil
  | u :: us => by
    unfold dedupWords
    by_cases hm : memBool u us = true
    · rw [if_pos hm]; exact dedupWords_nodup us
    · rw [if_neg hm]
      refine ListNodup.cons (fun y hy heq => ?_) (dedupWords_nodup us)
      subst heq
      exact hm ((memBool_iff u us).mpr ((mem_dedupWords u us).mp hy))

def flatMapWords (f : List Nat → List (List Nat)) : List (List Nat) → List (List Nat)
  | [] => []
  | w :: ws => f w ++ flatMapWords f ws

theorem mem_flatMapWords {f : List Nat → List (List Nat)} {u : List Nat} :
    ∀ {B : List (List Nat)}, u ∈ flatMapWords f B ↔ ∃ w ∈ B, u ∈ f w
  | [] => ⟨(fun h => nomatch h), (fun ⟨_, hm, _⟩ => nomatch hm)⟩
  | w :: ws => by
    unfold flatMapWords
    rw [List.mem_append, mem_flatMapWords]
    constructor
    · rintro (h1 | ⟨w', hw', h2⟩)
      · exact ⟨w, List.Mem.head ws, h1⟩
      · exact ⟨w', List.Mem.tail w hw', h2⟩
    · rintro ⟨w', hw', h2⟩
      cases hw' with
      | head => exact Or.inl h2
      | tail _ hm => exact Or.inr ⟨w', hm, h2⟩

theorem polySum_flatMapWords (g : List Nat → List (List Nat)) (f : List Nat → Poly) :
    ∀ (B : List (List Nat)),
      Poly.PolyEq (polySum ((flatMapWords g B).map f))
                  (polySum (B.map (fun w => polySum ((g w).map f))))
  | [] => Poly.polyEq_refl []
  | w :: ws => fun k => by
    unfold flatMapWords
    rw [List.map_append, (polySum_append ((g w).map f) ((flatMapWords g ws).map f)) k]
    simp only [List.map_cons, polySum]
    rw [Poly.coeff_add, Poly.coeff_add, (polySum_flatMapWords g f ws) k]

theorem countWord_eq_zero_of_not_mem {u : List Nat} :
    ∀ {B : List (List Nat)}, (∀ y ∈ B, u ≠ y) → countWord u B = 0
  | [], _ => rfl
  | y :: ys, hne => by
    unfold countWord
    have hyu : y ≠ u := fun h => hne y (List.Mem.head ys) h.symm
    simp only [hyu, ↓reduceIte, Nat.zero_add]
    exact countWord_eq_zero_of_not_mem (fun z hz => hne z (List.Mem.tail y hz))

theorem countWord_eq_one_of_nodup {u : List Nat} :
    ∀ {B : List (List Nat)}, ListNodup B → u ∈ B → countWord u B = 1
  | [], _, hu => nomatch hu
  | y :: ys, ListNodup.cons hnotmem hnd, hu => by
    unfold countWord
    cases hu with
    | head =>
      simp only [↓reduceIte]
      rw [countWord_eq_zero_of_not_mem hnotmem]
    | tail _ hm =>
      have hyu : y ≠ u := fun h => hnotmem u hm h
      simp only [hyu, ↓reduceIte, Nat.zero_add]
      exact countWord_eq_one_of_nodup hnd hm

def sumCountWords (D : List (List Nat)) : List (List Nat) → Nat
  | [] => 0
  | w :: ws => countWord w D + sumCountWords D ws

theorem countWord_flatMap_insert_eq_sum (m : Nat) (w' : List Nat) :
    ∀ (B : List (List Nat)),
      countWord w' (flatMapWords (insertAllWays m) B) = sumCountWords (deleteEachMax m w') B
  | [] => rfl
  | w :: ws => by
    unfold flatMapWords sumCountWords
    rw [countWord_append, countWord_insert_eq_delete m w w',
        countWord_flatMap_insert_eq_sum m w' ws]

theorem sumCountWords_cons (u : List Nat) (us : List (List Nat)) :
    ∀ (B : List (List Nat)),
      sumCountWords (u :: us) B = countWord u B + sumCountWords us B
  | [] => rfl
  | w :: ws => by
    unfold sumCountWords
    rw [show countWord w (u :: us) = (if u = w then 1 else 0) + countWord w us from rfl,
        show countWord u (w :: ws) = (if w = u then 1 else 0) + countWord u ws from rfl,
        sumCountWords_cons u us ws]
    by_cases h : u = w
    · subst h; simp only [↓reduceIte]; omega
    · have h' : w ≠ u := fun he => h he.symm
      simp only [h, h', ↓reduceIte]; omega

theorem sumCountWords_nil : ∀ (B : List (List Nat)), sumCountWords [] B = 0
  | [] => rfl
  | _ :: ws => by unfold sumCountWords countWord; simp [sumCountWords_nil ws]

theorem sumCountWords_eq_length {B : List (List Nat)} (hnd : ListNodup B) :
    ∀ (D : List (List Nat)), (∀ u ∈ D, u ∈ B) → sumCountWords D B = D.length
  | [], _ => sumCountWords_nil B
  | u :: us, hsub => by
    rw [sumCountWords_cons u us B,
        countWord_eq_one_of_nodup hnd (hsub u (List.Mem.head us)),
        sumCountWords_eq_length hnd us (fun z hz => hsub z (List.Mem.tail u hz))]
    simp [Nat.add_comm]

theorem polySum_cons_countWord (f : List Nat → Poly) (u : List Nat) (us : List (List Nat)) :
    ∀ {B' : List (List Nat)}, ListNodup B' → u ∈ B' →
      Poly.PolyEq
        (polySum (B'.map (fun w' => Poly.scale (Poly.natR (countWord w' (u :: us))) (f w'))))
        (Poly.add (f u) (polySum (B'.map (fun w' => Poly.scale (Poly.natR (countWord w' us)) (f w')))))
  | [], _, hu => nomatch hu
  | y :: ys, ListNodup.cons hnotmem hnd, hu => fun j => by
    simp only [List.map_cons, polySum]
    rw [show countWord y (u :: us) = (if u = y then 1 else 0) + countWord y us from rfl]
    cases hu with
    | head =>
      simp only [↓reduceIte]
      have h1r : Poly.natR 1 = 1 := R.zero_add 1
      have htail_eq :
          ys.map (fun w' => Poly.scale (Poly.natR (countWord w' (u :: us))) (f w')) =
          ys.map (fun w' => Poly.scale (Poly.natR (countWord w' us)) (f w')) := by
        have hrec : ∀ (zs : List (List Nat)), (∀ z ∈ zs, u ≠ z) →
            zs.map (fun w' => Poly.scale (Poly.natR (countWord w' (u :: us))) (f w')) =
            zs.map (fun w' => Poly.scale (Poly.natR (countWord w' us)) (f w')) := by
          intro zs; induction zs with
          | nil => intro _; rfl
          | cons z zs ihz =>
            intro hz
            have huz : u ≠ z := hz z (List.Mem.head zs)
            simp only [List.map_cons]
            rw [show countWord z (u :: us) = (if u = z then 1 else 0) + countWord z us from rfl]
            simp only [huz, ↓reduceIte, Nat.zero_add]
            rw [ihz (fun v hv => hz v (List.Mem.tail z hv))]
        exact hrec ys hnotmem
      rw [htail_eq, Poly.coeff_add, Poly.coeff_add, Poly.coeff_add,
          Poly.coeff_scale, Poly.coeff_scale, Poly.natR_add 1 _, h1r, R.right_distrib, R.one_mul, R.add_assoc]
    | tail _ hm =>
      have hyu : u ≠ y := fun h => hnotmem u hm h.symm
      simp only [hyu, ↓reduceIte, Nat.zero_add]
      have ih := polySum_cons_countWord f u us hnd hm j
      rw [Poly.coeff_add, ih, Poly.coeff_add, Poly.coeff_add, Poly.coeff_add]
      simp only [R.add_assoc, R.add_left_comm, R.add_comm]

theorem polySum_eq_countWord_weighted (f : List Nat → Poly) {B' : List (List Nat)} (hnd : ListNodup B') :
    ∀ (L : List (List Nat)), (∀ u ∈ L, u ∈ B') →
      Poly.PolyEq (polySum (L.map f))
                  (polySum (B'.map (fun w' => Poly.scale (Poly.natR (countWord w' L)) (f w'))))
  | [], _ => fun j => by
    have hzero : ∀ (zs : List (List Nat)),
        Poly.coeff (polySum (zs.map (fun w' => Poly.scale (Poly.natR 0) (f w')))) j = 0 := by
      intro zs; induction zs with
      | nil => rfl
      | cons z zs ihz =>
        simp only [List.map_cons, polySum]
        rw [Poly.coeff_add, Poly.coeff_scale, ihz]
        change (0 : R) * _ + 0 = 0
        rw [R.zero_mul, R.add_zero]
    change (0 : R) = _; exact (hzero B').symm
  | u :: us, hsub => fun j => by
    simp only [List.map_cons, polySum]
    rw [Poly.coeff_add,
        (polySum_eq_countWord_weighted f hnd us (fun z hz => hsub z (List.Mem.tail u hz))) j,
        ← Poly.coeff_add,
        ← (polySum_cons_countWord f u us hnd (hsub u (List.Mem.head us))) j]

theorem polySum_map_scale (s : R) (f : List Nat → Poly) :
    ∀ (B' : List (List Nat)),
      Poly.PolyEq (polySum (B'.map (fun w' => Poly.scale s (f w'))))
                  (Poly.scale s (polySum (B'.map f)))
  | [] => fun j => by rw [Poly.coeff_scale]; change (0 : R) = s * 0; rw [R.mul_zero]
  | w :: ws => fun j => by
    simp only [List.map_cons, polySum]
    rw [Poly.coeff_add, Poly.coeff_scale, (polySum_map_scale s f ws) j,
        Poly.coeff_scale, Poly.coeff_scale, Poly.coeff_add, R.left_distrib]

/-! ### Multiset Permutations `multisetPerms` and Simion's Recurrence -/

def HasHist (H : Nat → Nat) (w : List Nat) : Prop :=
  ∀ v : Nat, countNat v w = H v

def updHist (H : Nat → Nat) (m c v : Nat) : Nat :=
  if v = m then c else H v

def stepInsert (m : Nat) (B : List (List Nat)) : List (List Nat) :=
  dedupWords (flatMapWords (insertAllWays m) B)

def iterInsert (m : Nat) : Nat → List (List Nat) → List (List Nat)
  | 0, B => B
  | c + 1, B => stepInsert m (iterInsert m c B)

def buildPermsAux : Nat → List Nat → List (List Nat) → List (List Nat)
  | _, [], B => B
  | i, a :: as, B => buildPermsAux (i + 1) as (iterInsert i a B)

/-- Constructive duplicate-free list of all distinct multiset permutations of `{1^{α₁}, …, m^{αₘ}}`. -/
def multisetPerms (α : List Nat) : List (List Nat) :=
  buildPermsAux 1 α [[]]

def histAt : Nat → List Nat → Nat → Nat
  | _, [], _ => 0
  | i, a :: as, v => if v = i then a else histAt (i + 1) as v

def targetCount (α : List Nat) (v : Nat) : Nat :=
  histAt 1 α v

def totalWeight : List Nat → Nat
  | [] => 0
  | a :: as => a + totalWeight as

def maxEntry : List Nat → Nat
  | [] => 0
  | a :: as => Nat.max a (maxEntry as)

def desPoly (B : List (List Nat)) : Poly :=
  polySum (B.map (fun w => Poly.monomial (des w)))

/-- Combinatorial multiset Eulerian polynomial `A_α^{ms}(t) = ∑_{w ∈ S(M(α))} t^{des(w)}`. -/
def eulerianPoly (α : List Nat) : Poly :=
  desPoly (multisetPerms α)

theorem stepInsert_spec (H : Nat → Nat) (m N₀ c : Nat) (B : List (List Nat))
    (hHgt : ∀ v : Nat, m < v → H v = 0)
    (hnd : ListNodup B)
    (hmem : ∀ w : List Nat, w ∈ B ↔ HasHist (updHist H m c) w)
    (hlen : ∀ w ∈ B, w.length = N₀ + c) :
    let B' := stepInsert m B
    ListNodup B' ∧
    (∀ w' : List Nat, w' ∈ B' ↔ HasHist (updHist H m (c + 1)) w') ∧
    (∀ w' ∈ B', w'.length = N₀ + (c + 1)) ∧
    Poly.PolyEq (Poly.scale (Poly.natR (c + 1)) (desPoly B'))
                (Poly.interlaceOp (Poly.natR (c + 1)) (Poly.natR N₀) (desPoly B)) := by
  let B' := stepInsert m B
  let L := flatMapWords (insertAllWays m) B
  have hB'_nd : ListNodup B' := dedupWords_nodup L
  have hB'_mem : ∀ w' : List Nat, w' ∈ B' ↔ HasHist (updHist H m (c + 1)) w' := by
    intro w'
    dsimp only [B']; unfold stepInsert
    rw [mem_dedupWords, mem_flatMapWords]
    constructor
    · rintro ⟨w, hwB, hw'ins⟩
      have hwH := (hmem w).mp hwB
      obtain ⟨_, hcm, hcv⟩ := insertAllWays_props m w w' hw'ins
      intro v
      unfold updHist
      by_cases hvm : v = m
      · subst hvm; rw [hcm, hwH v]; simp [updHist]
      · rw [hcv v hvm, hwH v]; simp [updHist, hvm]
    · intro hw'H
      have hcm' : countNat m w' = c + 1 := by have := hw'H m; simp [updHist] at this; exact this
      have hdlen : (deleteEachMax m w').length = c + 1 := by rw [length_deleteEachMax, hcm']
      cases hd : deleteEachMax m w' with
      | nil => rw [hd] at hdlen; simp at hdlen
      | cons w ws =>
        have hwdel : w ∈ deleteEachMax m w' := by rw [hd]; exact List.Mem.head ws
        obtain ⟨hcm_rel, hcv_rel⟩ := deleteEachMax_props m w' w hwdel
        have hwH : HasHist (updHist H m c) w := by
          intro v; unfold updHist
          by_cases hvm : v = m
          · subst hvm; simp only [↓reduceIte]; omega
          · rw [hcv_rel v hvm, hw'H v]; simp [updHist, hvm]
        have hwB : w ∈ B := (hmem w).mpr hwH
        have hpos : 0 < countWord w (deleteEachMax m w') := mem_iff_countWord_pos.mp hwdel
        rw [← countWord_insert_eq_delete m w w'] at hpos
        exact ⟨w, hwB, mem_iff_countWord_pos.mpr hpos⟩
  have hB'_len : ∀ w' ∈ B', w'.length = N₀ + (c + 1) := by
    intro w' hw'
    dsimp only [B'] at hw'; unfold stepInsert at hw'
    rw [mem_dedupWords, mem_flatMapWords] at hw'
    rcases hw' with ⟨w, hwB, hwins⟩
    rw [(insertAllWays_props m w w' hwins).1, hlen w hwB, Nat.add_assoc]
  -- Count each w' ∈ B' inside L: exactly c + 1 times
  have hcount_L : ∀ w' ∈ B', countWord w' L = c + 1 := by
    intro w' hw'B'
    have hw'H := (hB'_mem w').mp hw'B'
    rw [countWord_flatMap_insert_eq_sum m w' B]
    have hsub : ∀ u ∈ deleteEachMax m w', u ∈ B := by
      intro u hu
      obtain ⟨hcm_rel, hcv_rel⟩ := deleteEachMax_props m w' u hu
      have hcm' : countNat m w' = c + 1 := by have := hw'H m; simp [updHist] at this; exact this
      apply (hmem u).mpr
      intro v; unfold updHist
      by_cases hvm : v = m
      · subst hvm; simp only [↓reduceIte]; omega
      · rw [hcv_rel v hvm, hw'H v]; simp [updHist, hvm]
    rw [sumCountWords_eq_length hnd (deleteEachMax m w') hsub, length_deleteEachMax, hw'H m]
    simp [updHist]
  -- Left identity: polySum (L.map ...) ≡ scale (c + 1) (desPoly B')
  have hLHS : Poly.PolyEq (polySum (L.map (fun u => Poly.monomial (des u))))
                          (Poly.scale (Poly.natR (c + 1)) (desPoly B')) := by
    have h1 := polySum_eq_countWord_weighted (fun u => Poly.monomial (des u)) hB'_nd L
                 (fun u hu => (mem_dedupWords u L).mpr hu)
    have hmap_eq :
        B'.map (fun w' => Poly.scale (Poly.natR (countWord w' L)) (Poly.monomial (des w'))) =
        B'.map (fun w' => Poly.scale (Poly.natR (c + 1)) (Poly.monomial (des w'))) := by
      have hrec : ∀ (zs : List (List Nat)), (∀ z ∈ zs, countWord z L = c + 1) →
          zs.map (fun w' => Poly.scale (Poly.natR (countWord w' L)) (Poly.monomial (des w'))) =
          zs.map (fun w' => Poly.scale (Poly.natR (c + 1)) (Poly.monomial (des w'))) := by
        intro zs; induction zs with
        | nil => intro _; rfl
        | cons z zs ihz =>
          intro hz
          simp only [List.map_cons, hz z (List.Mem.head zs)]
          rw [ihz (fun v hv => hz v (List.Mem.tail z hv))]
      exact hrec B' hcount_L
    rw [hmap_eq] at h1
    exact Poly.polyEq_trans h1 (polySum_map_scale (Poly.natR (c + 1)) (fun u => Poly.monomial (des u)) B')
  -- Right identity: polySum (L.map ...) ≡ interlaceOp (c + 1) N₀ (desPoly B)
  have hRHS : Poly.PolyEq (polySum (L.map (fun u => Poly.monomial (des u))))
                          (Poly.interlaceOp (Poly.natR (c + 1)) (Poly.natR N₀) (desPoly B)) := by
    have hflat := polySum_flatMapWords (insertAllWays m) (fun u => Poly.monomial (des u)) B
    have hlin := Poly.polyEq_symm (interlaceOp_polySum (Poly.natR (c + 1)) (Poly.natR N₀)
                   (B.map (fun w => Poly.monomial (des w))))
    have hterm : ∀ w ∈ B,
        Poly.PolyEq (polySum ((insertAllWays m w).map (fun u => Poly.monomial (des u))))
                    (Poly.interlaceOp (Poly.natR (c + 1)) (Poly.natR N₀) (Poly.monomial (des w))) := by
      intro w hwB
      have hwH := (hmem w).mp hwB
      have hwlen := hlen w hwB
      have hall_le : ∀ z ∈ w, z ≤ m := by
        intro z hzw
        have hp := countNat_pos_of_mem (v := z) hzw
        rw [hwH z] at hp
        by_cases hgt : m < z
        · have hne : z ≠ m := by omega
          simp [updHist, hne, hHgt z hgt] at hp
        · omega
      have hcm : countNat m w = c := by have := hwH m; simp [updHist] at this; exact this
      have hdes_le : des w ≤ N₀ := by
        have hb := countNat_add_des_le_length m w hall_le
        omega
      have hs1 := sum_insertAllWays_des m w hall_le
      have hs2 := Poly.interlaceOp_monomial (Poly.natR (c + 1)) (Poly.natR N₀) (des w)
      intro j
      rw [hs1 j, hs2 j, hcm, hwlen]
      have hn_sub : (N₀ + c) - c - des w = N₀ - des w := by omega
      rw [hn_sub, Poly.natR_add (c + 1) (des w), Poly.natR_sub hdes_le]
    have hsum_eq :
        Poly.PolyEq (polySum (B.map (fun w => polySum ((insertAllWays m w).map (fun u => Poly.monomial (des u))))))
                    (polySum ((B.map (fun w => Poly.monomial (des w))).map
                      (Poly.interlaceOp (Poly.natR (c + 1)) (Poly.natR N₀)))) := by
      have hrec : ∀ (zs : List (List Nat)), (∀ w ∈ zs,
            Poly.PolyEq (polySum ((insertAllWays m w).map (fun u => Poly.monomial (des u))))
                        (Poly.interlaceOp (Poly.natR (c + 1)) (Poly.natR N₀) (Poly.monomial (des w)))) →
          Poly.PolyEq (polySum (zs.map (fun w => polySum ((insertAllWays m w).map (fun u => Poly.monomial (des u))))))
                      (polySum ((zs.map (fun w => Poly.monomial (des w))).map
                        (Poly.interlaceOp (Poly.natR (c + 1)) (Poly.natR N₀)))) := by
        intro zs; induction zs with
        | nil => intro _; exact Poly.polyEq_refl []
        | cons z zs ihz =>
          intro hz j
          simp only [List.map_cons, polySum]
          rw [Poly.coeff_add, Poly.coeff_add, hz z (List.Mem.head zs) j,
              ihz (fun v hv => hz v (List.Mem.tail z hv)) j]
      exact hrec B hterm
    exact Poly.polyEq_trans hflat (Poly.polyEq_trans hsum_eq hlin)
  exact ⟨hB'_nd, hB'_mem, hB'_len, Poly.polyEq_trans (Poly.polyEq_symm hLHS) hRHS⟩

theorem iterInsert_spec (H : Nat → Nat) (m N₀ d : Nat)
    (hHm0 : H m = 0) (hHgt : ∀ v : Nat, m < v → H v = 0) (hd_le : d ≤ N₀) :
    ∀ (a : Nat) {B : List (List Nat)},
      ListNodup B →
      (∀ w : List Nat, w ∈ B ↔ HasHist H w) →
      (∀ w ∈ B, w.length = N₀) →
      Poly.SplitsNegSimple (desPoly B) d →
      let B_a := iterInsert m a B
      ListNodup B_a ∧
      (∀ w : List Nat, w ∈ B_a ↔ HasHist (updHist H m a) w) ∧
      (∀ w ∈ B_a, w.length = N₀ + a) ∧
      Poly.SplitsNegSimple (desPoly B_a) (Nat.min (d + a) N₀)
  | 0, B, hnd, hmem, hlen, hsplit => by
    have hmem0 : ∀ w : List Nat, w ∈ B ↔ HasHist (updHist H m 0) w := by
      intro w; rw [hmem w]
      constructor
      · intro hh v; unfold updHist; by_cases hvm : v = m
        · subst hvm; simp [hh v, hHm0]
        · simp [hvm, hh v]
      · intro hh v; have hv := hh v; unfold updHist at hv; by_cases hvm : v = m
        · subst hvm; simp at hv; rw [hv, hHm0]
        · simp [hvm] at hv; exact hv
    have hd_min : Nat.min (d + 0) N₀ = d := by
      simp only [Nat.min_def]; split <;> omega
    rw [hd_min]
    exact ⟨hnd, hmem0, hlen, hsplit⟩
  | c + 1, B, hnd, hmem, hlen, hsplit => by
    obtain ⟨hnd_c, hmem_c, hlen_c, hsplit_c⟩ :=
      iterInsert_spec H m N₀ d hHm0 hHgt hd_le c hnd hmem hlen hsplit
    obtain ⟨hnd_next, hmem_next, hlen_next, hrec_poly⟩ :=
      stepInsert_spec H m N₀ c (iterInsert m c B) hHgt hnd_c hmem_c hlen_c
    have hr_pos : (0 : R) < Poly.natR (c + 1) := Poly.natR_pos c
    have hpres := Poly.interlaceOp_preserves_negSimpleRoots hsplit_c (s := Poly.natR N₀) hr_pos
    let d_c := Nat.min (d + c) N₀
    have hsplit_next : Poly.SplitsNegSimple (desPoly (stepInsert m (iterInsert m c B)))
                         (Nat.min (d + (c + 1)) N₀) := by
      by_cases hlt : d + c < N₀
      · have hdc : d_c = d + c := by
          dsimp only [d_c]; simp only [Nat.min_def]; split <;> omega
        have hdnext : Nat.min (d + (c + 1)) N₀ = d_c + 1 := by
          rw [hdc]; simp only [Nat.min_def]; split <;> omega
        have hslt : Poly.natR d_c < Poly.natR N₀ := Poly.natR_lt_of_lt (by omega)
        rw [hdnext]
        exact Poly.splitsNegSimple_of_scale hr_pos hrec_poly (hpres.2 hslt)
      · have hdc : d_c = N₀ := by
          dsimp only [d_c]; simp only [Nat.min_def]; split <;> omega
        have hdnext : Nat.min (d + (c + 1)) N₀ = d_c := by
          rw [hdc]; simp only [Nat.min_def]; split <;> omega
        have hseq : Poly.natR N₀ = Poly.natR d_c := by rw [hdc]
        rw [hdnext]
        exact Poly.splitsNegSimple_of_scale hr_pos hrec_poly (hpres.1 hseq)
    exact ⟨hnd_next, hmem_next, hlen_next, hsplit_next⟩

theorem buildPermsAux_spec :
    ∀ (as : List Nat) (i N₀ M : Nat) (H : Nat → Nat) (B : List (List Nat)),
      1 ≤ i → M ≤ N₀ →
      (∀ v : Nat, i ≤ v → H v = 0) →
      ListNodup B →
      (∀ w : List Nat, w ∈ B ↔ HasHist H w) →
      (∀ w ∈ B, w.length = N₀) →
      Poly.SplitsNegSimple (desPoly B) (N₀ - M) →
      let B_end := buildPermsAux i as B
      ListNodup B_end ∧
      (∀ w : List Nat, w ∈ B_end ↔ HasHist (fun v => if v < i then H v else histAt i as v) w) ∧
      (∀ w ∈ B_end, w.length = N₀ + totalWeight as) ∧
      Poly.SplitsNegSimple (desPoly B_end) ((N₀ + totalWeight as) - Nat.max M (maxEntry as))
  | [], i, N₀, M, H, B, _, _, hHge, hnd, hmem, hlen, hsplit => by
    have hmem_eq : ∀ w : List Nat, w ∈ B ↔ HasHist (fun v => if v < i then H v else 0) w := by
      intro w; rw [hmem w]
      constructor <;> intro hh v
      · by_cases hvi : v < i
        · simp [hvi, hh v]
        · simp [hvi, hh v, hHge v (by omega)]
      · have hv := hh v
        by_cases hvi : v < i
        · simp [hvi] at hv; exact hv
        · simp [hvi] at hv; rw [hv, hHge v (by omega)]
    have hmax0 : Nat.max M 0 = M := by simp only [Nat.max_def]; split <;> omega
    simp only [buildPermsAux, histAt, totalWeight, maxEntry, Nat.add_zero, hmax0]
    exact ⟨hnd, hmem_eq, hlen, hsplit⟩
  | a :: as, i, N₀, M, H, B, hi, hMle, hHge, hnd, hmem, hlen, hsplit => by
    have hHi0 : H i = 0 := hHge i (Nat.le_refl i)
    have hHgt : ∀ v : Nat, i < v → H v = 0 := fun v hv => hHge v (by omega)
    obtain ⟨hnd1, hmem1, hlen1, hsplit1⟩ :=
      iterInsert_spec H i N₀ (N₀ - M) hHi0 hHgt (by omega) a hnd hmem hlen hsplit
    have hmin_eq : Nat.min ((N₀ - M) + a) N₀ = (N₀ + a) - Nat.max M a := by
      simp only [Nat.min_def, Nat.max_def]
      by_cases h1 : (N₀ - M) + a ≤ N₀ <;> by_cases h2 : M ≤ a <;> simp only [h1, h2, ↓reduceIte] <;> omega
    rw [hmin_eq] at hsplit1
    have hMle' : Nat.max M a ≤ N₀ + a := by
      simp only [Nat.max_def]; split <;> omega
    have hH1_ge : ∀ v : Nat, i + 1 ≤ v → updHist H i a v = 0 := by
      intro v hv; unfold updHist
      have hne : v ≠ i := by omega
      simp [hne, hHge v (by omega)]
    obtain ⟨hnd2, hmem2, hlen2, hsplit2⟩ :=
      buildPermsAux_spec as (i + 1) (N₀ + a) (Nat.max M a) (updHist H i a) (iterInsert i a B)
        (by omega) hMle' hH1_ge hnd1 hmem1 hlen1 hsplit1
    have hhist_eq : ∀ w : List Nat,
        HasHist (fun v => if v < i + 1 then updHist H i a v else histAt (i + 1) as v) w ↔
        HasHist (fun v => if v < i then H v else histAt i (a :: as) v) w := by
      intro w
      have hpt : ∀ v : Nat,
          (if v < i + 1 then updHist H i a v else histAt (i + 1) as v) =
          (if v < i then H v else histAt i (a :: as) v) := by
        intro v
        change (if v < i + 1 then (if v = i then a else H v) else histAt (i + 1) as v) =
               (if v < i then H v else (if v = i then a else histAt (i + 1) as v))
        by_cases hvi : v < i
        · have h1 : v < i + 1 := by omega
          have h2 : v ≠ i := by omega
          simp [hvi, h1, h2]
        · by_cases heq : v = i
          · subst heq; simp [hvi]
          · have h1 : ¬ (v < i + 1) := by omega
            simp [hvi, heq, h1]
      constructor <;> intro hh v <;> rw [hh v] <;> simp [hpt v]
    have hw_assoc : (N₀ + a) + totalWeight as = N₀ + totalWeight (a :: as) := by
      change (N₀ + a) + totalWeight as = N₀ + (a + totalWeight as); omega
    have hm_assoc : Nat.max (Nat.max M a) (maxEntry as) = Nat.max M (maxEntry (a :: as)) := by
      let E := maxEntry as
      change Nat.max (Nat.max M a) E = Nat.max M (Nat.max a E)
      simp only [Nat.max_def]
      by_cases h1 : M ≤ a <;> by_cases h2 : a ≤ E <;> by_cases h3 : M ≤ E <;>
        simp only [h1, h2, h3, ↓reduceIte] <;> omega
    rw [hw_assoc, hm_assoc] at hsplit2
    exact ⟨hnd2, fun w => (hmem2 w).trans (hhist_eq w),
           fun w hw => (hlen2 w hw).trans hw_assoc, hsplit2⟩

theorem base_perms_spec :
    ListNodup ([[]] : List (List Nat)) ∧
    (∀ w : List Nat, w ∈ ([[]] : List (List Nat)) ↔ HasHist (fun _ => 0) w) ∧
    (∀ w ∈ ([[]] : List (List Nat)), w.length = 0) ∧
    Poly.SplitsNegSimple (desPoly [[]]) 0 := by
  refine ⟨ListNodup.cons (fun _ hy => nomatch hy) ListNodup.nil, ?_, ?_, ?_⟩
  · intro w
    constructor
    · intro hw; cases hw with
      | head => intro _; rfl
      | tail _ hm => nomatch hm
    · intro hh
      cases w with
      | nil => exact List.Mem.head []
      | cons x xs =>
        have hp := countNat_pos_of_mem (v := x) (List.Mem.head xs)
        have hx0 : countNat x (x :: xs) = 0 := hh x
        omega
  · intro w hw; cases hw with | head => rfl | tail _ hm => nomatch hm
  · refine ⟨1, [], Poly.r_one_pos, rfl, Poly.StrictlyDecNeg.nil, fun k => ?_⟩
    unfold desPoly List.map polySum des Poly.monomial Poly.prodLinear
    cases k with
    | zero => change (1 : R) + 0 = 1; rw [R.add_zero]
    | succ j =>
      change Poly.coeff [1] (j + 1) + 0 = Poly.coeff [1] (j + 1)
      rw [R.add_zero]

/-- Semantic exactness and universal negative-root factorization of `multisetPerms α` and `eulerianPoly α`. -/
theorem multisetPerms_and_eulerianPoly_master (α : List Nat) :
    ListNodup (multisetPerms α) ∧
    (∀ w : List Nat, w ∈ multisetPerms α ↔ ∀ v : Nat, countNat v w = targetCount α v) ∧
    (∀ w ∈ multisetPerms α, w.length = totalWeight α) ∧
    Poly.SplitsNegSimple (eulerianPoly α) (totalWeight α - maxEntry α) := by
  obtain ⟨h0_nd, h0_mem, h0_len, h0_split⟩ := base_perms_spec
  obtain ⟨hnd, hmem, hlen, hsplit⟩ :=
    buildPermsAux_spec α 1 0 0 (fun _ => 0) [[]] (Nat.le_refl 1) (Nat.le_refl 0)
      (fun _ _ => rfl) h0_nd h0_mem h0_len h0_split
  have hhist0 : ∀ v : Nat, (if v < 1 then 0 else histAt 1 α v) = targetCount α v := by
    intro v; unfold targetCount
    by_cases hv : v < 1
    · have hv0 : v = 0 := by omega
      subst hv0
      have hz : histAt 1 α 0 = 0 := by
        have hrec : ∀ (bs : List Nat) (j : Nat), 1 ≤ j → histAt j bs 0 = 0 := by
          intro bs; induction bs with
          | nil => intro _ _; rfl
          | cons b bs ihb =>
            intro j hj
            unfold histAt
            have hne : 0 ≠ j := by omega
            simp [hne, ihb (j + 1) (by omega)]
        exact hrec α 1 (Nat.le_refl 1)
      simp [hz]
    · simp [hv]
  have hmem' : ∀ w : List Nat, w ∈ multisetPerms α ↔ ∀ v : Nat, countNat v w = targetCount α v := by
    intro w; unfold multisetPerms
    rw [hmem w]
    constructor
    · intro hh v; have hv := hh v; dsimp only at hv; rw [hhist0 v] at hv; exact hv
    · intro hh v; dsimp only; rw [hhist0 v]; exact hh v
  have hzmax : Nat.max 0 (maxEntry α) = maxEntry α := by simp only [Nat.max_def]; split <;> omega
  simp only [Nat.zero_add, hzmax] at hlen hsplit
  exact ⟨hnd, hmem', hlen, hsplit⟩

/-- Valid nonempty positive integer multi-index `α = (α₁, …, αₘ) ∈ Z_{≥ 1}^m`. -/
def ValidMultiIndex (α : List Nat) : Prop :=
  α ≠ [] ∧ ∀ a ∈ α, 1 ≤ a

/-- **Simion's Differential Recurrence** proved directly from combinatorial multiset permutations:
    incrementing the `(m+1)`-st multiplicity from `c` to `c + 1` satisfies
    `(c + 1) A_{α ++ [c + 1]}^{ms}(t) = T_{c + 1, |α|}(A_{α ++ [c]}^{ms})(t)`. -/
theorem simion_recurrence (α : List Nat) (c : Nat) :
    Poly.PolyEq
      (Poly.scale (Poly.natR (c + 1)) (eulerianPoly (α ++ [c + 1])))
      (Poly.interlaceOp (Poly.natR (c + 1)) (Poly.natR (totalWeight α)) (eulerianPoly (α ++ [c]))) := by
  have hbuild_append : ∀ (as : List Nat) (i : Nat) (B : List (List Nat)) (r : Nat),
      buildPermsAux i (as ++ [r]) B = iterInsert (i + as.length) r (buildPermsAux i as B) := by
    intro as; induction as with
    | nil => intro i B r; simp [buildPermsAux]
    | cons a as ihas =>
      intro i B r
      simp only [List.cons_append, buildPermsAux, List.length_cons]
      rw [ihas (i + 1) (iterInsert i a B) r]
      have hij : i + 1 + as.length = i + (as.length + 1) := by omega
      rw [hij]
  unfold eulerianPoly multisetPerms
  rw [hbuild_append α 1 [[]] (c + 1), hbuild_append α 1 [[]] c]
  let m := 1 + α.length
  let B₀ := buildPermsAux 1 α [[]]
  obtain ⟨hB₀_nd, hB₀_mem, hB₀_len, hB₀_split⟩ := multisetPerms_and_eulerianPoly_master α
  let H : Nat → Nat := targetCount α
  have hHm0 : H m = 0 := by
    unfold H targetCount
    have hrec : ∀ (bs : List Nat) (j : Nat), histAt j bs (j + bs.length) = 0 := by
      intro bs; induction bs with
      | nil => intro _; rfl
      | cons b bs ihb =>
        intro j
        change (if j + (bs.length + 1) = j then b else histAt (j + 1) bs (j + (bs.length + 1))) = 0
        have hne : j + (bs.length + 1) ≠ j := by omega
        have heq : j + (bs.length + 1) = (j + 1) + bs.length := by omega
        rw [if_neg hne, heq]
        exact ihb (j + 1)
    exact hrec α 1
  have hHgt : ∀ v : Nat, m < v → H v = 0 := by
    intro v hv; unfold H targetCount
    have hrec : ∀ (bs : List Nat) (j : Nat), j + bs.length < v → histAt j bs v = 0 := by
      intro bs; induction bs with
      | nil => intro _ _; rfl
      | cons b bs ihb =>
        intro j hlt
        change (if v = j then b else histAt (j + 1) bs v) = 0
        have hne : v ≠ j := by simp at hlt; omega
        simp only [hne, ↓reduceIte]
        exact ihb (j + 1) (by simp at hlt; omega)
    exact hrec α 1 hv
  have hd_le : totalWeight α - maxEntry α ≤ totalWeight α := by omega
  obtain ⟨hnd_c, hmem_c, hlen_c, _⟩ :=
    iterInsert_spec H m (totalWeight α) (totalWeight α - maxEntry α) hHm0 hHgt hd_le c
      hB₀_nd hB₀_mem hB₀_len hB₀_split
  exact (stepInsert_spec H m (totalWeight α) c (iterInsert m c B₀) hHgt hnd_c hmem_c hlen_c).2.2.2

/-- **Universal Theorem 1 (Multiset Eulerian Polynomials)**:
    For *every* valid multi-index `α ∈ Z_{≥ 1}^m`, `eulerianPoly α` splits into `|α| - max(α)`
    distinct negative real roots, so BOTH `eulerianPoly α` and the `t`-shifted `t · eulerianPoly α`
    have all real simple complex roots. -/
theorem multiset_allRealSimple {α : List Nat} (_ : ValidMultiIndex α) :
    Poly.SplitsNegSimple (eulerianPoly α) (totalWeight α - maxEntry α) ∧
    Poly.HasAllRealSimpleRoots (eulerianPoly α) ∧
    Poly.HasAllRealSimpleRoots (Poly.mulX (eulerianPoly α)) := by
  have hs := (multisetPerms_and_eulerianPoly_master α).2.2.2
  exact ⟨hs, Poly.allRealSimple_of_splitsNegSimple hs, (Poly.splits_mulX_of_splitsNegSimple hs).2⟩

/-! ## 6. Multiple Polylogarithm Eulerian Polynomials `A_α^{mpl}(t)` and `A_α^{mpl,⋆}(t)` -/

def iterInterlace (r : R) : Nat → Nat → Poly → Poly
  | 0, _, P => P
  | k + 1, s, P => iterInterlace r k (s + 1) (Poly.interlaceOp r (Poly.natR s) P)

theorem iterInterlace_preserves_negSimpleRoots {r : R} (hr : 0 < r) :
    ∀ (k s d : Nat) {P : Poly},
      d < s → Poly.SplitsNegSimple P d →
      Poly.SplitsNegSimple (iterInterlace r k s P) (d + k)
  | 0, _, d, _, _, hP => by rw [Nat.add_zero]; exact hP
  | k + 1, s, d, P, hds, hP => by
    unfold iterInterlace
    have hstep := (Poly.interlaceOp_preserves_negSimpleRoots hP (s := Poly.natR s) hr).2
                    (Poly.natR_lt_of_lt hds)
    have ih := iterInterlace_preserves_negSimpleRoots hr k (s + 1) (d + 1) (by omega) hstep
    have heq : (d + 1) + k = d + (k + 1) := by omega
    rw [heq] at ih
    exact ih

/-- Strict Multiple Polylogarithm Eulerian polynomial `A_α^{mpl}(t)` (`Li_{-α₁,…,-αₘ}(t)` numerator core). -/
def mplEulerianPoly : List Nat → Poly
  | [] => [1]
  | [a] => iterInterlace 1 (a - 1) 1 [1]
  | a :: b :: bs =>
      iterInterlace (Poly.natR ((b :: bs).length + 1)) a (totalWeight (b :: bs))
        (mplEulerianPoly (b :: bs))

/-- Non-strict Multiple Polylogarithm Eulerian polynomial `A_α^{mpl,⋆}(t)` (`Li^⋆_{-α₁,…,-αₘ}(t)` numerator core). -/
def mplStarEulerianPoly : List Nat → Poly
  | [] => [1]
  | [a] => iterInterlace 1 (a - 1) 1 [1]
  | a :: b :: bs =>
      iterInterlace 1 a (totalWeight (b :: bs) + (b :: bs).length)
        (mplStarEulerianPoly (b :: bs))

theorem totalWeight_pos_of_valid : ∀ {α : List Nat}, ValidMultiIndex α → 1 ≤ totalWeight α
  | [], ⟨hne, _⟩ => False.elim (hne rfl)
  | a :: as, ⟨_, hall⟩ => by
    unfold totalWeight
    have ha : 1 ≤ a := hall a (List.Mem.head as)
    omega

theorem splitsNegSimple_one : Poly.SplitsNegSimple [1] 0 :=
  ⟨1, [], Poly.r_one_pos, rfl, Poly.StrictlyDecNeg.nil, Poly.polyEq_refl [1]⟩

/-- **Universal Theorem 2a (Strict Multiple Polylogarithm Eulerian Polynomials)**:
    For *every* valid multi-index `α ∈ Z_{≥ 1}^m`, `mplEulerianPoly α` has degree `|α| - 1`
    and all real simple roots. -/
theorem mpl_allRealSimple : ∀ {α : List Nat}, ValidMultiIndex α →
    Poly.SplitsNegSimple (mplEulerianPoly α) (totalWeight α - 1) ∧
    Poly.HasAllRealSimpleRoots (mplEulerianPoly α)
  | [], ⟨hne, _⟩ => False.elim (hne rfl)
  | [a], ⟨_, hall⟩ => by
    have ha : 1 ≤ a := hall a (List.Mem.head [])
    unfold mplEulerianPoly totalWeight
    have hs := iterInterlace_preserves_negSimpleRoots Poly.r_one_pos (a - 1) 1 0 (by omega) splitsNegSimple_one
    have hdeg : 0 + (a - 1) = (a + 0) - 1 := by omega
    rw [hdeg] at hs
    exact ⟨hs, Poly.allRealSimple_of_splitsNegSimple hs⟩
  | a :: b :: bs, ⟨_, hall⟩ => by
    have ha : 1 ≤ a := hall a (List.Mem.head _)
    have hvalid_tail : ValidMultiIndex (b :: bs) :=
      ⟨(fun h => nomatch h), fun x hx => hall x (List.Mem.tail a hx)⟩
    have hw_pos : 1 ≤ totalWeight (b :: bs) := totalWeight_pos_of_valid hvalid_tail
    obtain ⟨hs_tail, _⟩ := mpl_allRealSimple hvalid_tail
    unfold mplEulerianPoly
    have hr_pos : (0 : R) < Poly.natR ((b :: bs).length + 1) := Poly.natR_pos (b :: bs).length
    have hs := iterInterlace_preserves_negSimpleRoots hr_pos a (totalWeight (b :: bs))
                 (totalWeight (b :: bs) - 1) (by omega) hs_tail
    have hdeg : (totalWeight (b :: bs) - 1) + a = totalWeight (a :: b :: bs) - 1 := by
      change (totalWeight (b :: bs) - 1) + a = (a + totalWeight (b :: bs)) - 1; omega
    rw [hdeg] at hs
    exact ⟨hs, Poly.allRealSimple_of_splitsNegSimple hs⟩

/-- **Universal Theorem 2b (Star Multiple Polylogarithm Eulerian Polynomials)**:
    For *every* valid multi-index `α ∈ Z_{≥ 1}^m`, `mplStarEulerianPoly α` has degree `|α| - 1`
    and all real simple roots. -/
theorem mplStar_allRealSimple : ∀ {α : List Nat}, ValidMultiIndex α →
    Poly.SplitsNegSimple (mplStarEulerianPoly α) (totalWeight α - 1) ∧
    Poly.HasAllRealSimpleRoots (mplStarEulerianPoly α)
  | [], ⟨hne, _⟩ => False.elim (hne rfl)
  | [a], ⟨_, hall⟩ => by
    have ha : 1 ≤ a := hall a (List.Mem.head [])
    unfold mplStarEulerianPoly totalWeight
    have hs := iterInterlace_preserves_negSimpleRoots Poly.r_one_pos (a - 1) 1 0 (by omega) splitsNegSimple_one
    have hdeg : 0 + (a - 1) = (a + 0) - 1 := by omega
    rw [hdeg] at hs
    exact ⟨hs, Poly.allRealSimple_of_splitsNegSimple hs⟩
  | a :: b :: bs, ⟨_, hall⟩ => by
    have ha : 1 ≤ a := hall a (List.Mem.head _)
    have hvalid_tail : ValidMultiIndex (b :: bs) :=
      ⟨(fun h => nomatch h), fun x hx => hall x (List.Mem.tail a hx)⟩
    have hw_pos : 1 ≤ totalWeight (b :: bs) := totalWeight_pos_of_valid hvalid_tail
    obtain ⟨hs_tail, _⟩ := mplStar_allRealSimple hvalid_tail
    unfold mplStarEulerianPoly
    have hs := iterInterlace_preserves_negSimpleRoots Poly.r_one_pos a
                 (totalWeight (b :: bs) + (b :: bs).length)
                 (totalWeight (b :: bs) - 1) (by simp; omega) hs_tail
    have hdeg : (totalWeight (b :: bs) - 1) + a = totalWeight (a :: b :: bs) - 1 := by
      change (totalWeight (b :: bs) - 1) + a = (a + totalWeight (b :: bs)) - 1; omega
    rw [hdeg] at hs
    exact ⟨hs, Poly.allRealSimple_of_splitsNegSimple hs⟩

/-! ## 7. Piecewise-Constant Criteria, Explicit Certificates, Alternative Conventions, and Disproof -/

/-- Criterion 1: Constant multi-index (`α₁ = α₂ = … = αₘ`). -/
def IsConstantIndex : List Nat → Prop
  | [] => True
  | [_] => True
  | x :: y :: ys => x = y ∧ IsConstantIndex (y :: ys)

/-- Criterion 2: Block-constant multi-index with all contiguous constant runs of length `≥ 2`. -/
inductive IsBlockConstantGe2 : List Nat → Prop where
  | two (x : Nat) : IsBlockConstantGe2 [x, x]
  | extend (x : Nat) {xs : List Nat} :
      IsBlockConstantGe2 (x :: xs) → IsBlockConstantGe2 (x :: x :: xs)
  | appendBlock (x : Nat) {xs : List Nat} :
      IsBlockConstantGe2 xs → IsBlockConstantGe2 (x :: x :: xs)

theorem not_blockConstantGe2_of_head_ne {x y : Nat} {ys : List Nat} (hne : x ≠ y) :
    ¬ IsBlockConstantGe2 (x :: y :: ys) := by
  intro h
  cases h with
  | two _ => exact hne rfl
  | extend _ _ => exact hne rfl
  | appendBlock _ _ => exact hne rfl

/-- Criterion 3: Multi-index having at least one equal adjacent pair (`∃ i, αᵢ = αᵢ₊₁`). -/
def HasAdjacentEqual : List Nat → Prop
  | [] => False
  | [_] => False
  | x :: y :: ys => x = y ∨ HasAdjacentEqual (y :: ys)

/-- Criterion 4: Arbitrary proper (non-trivial) criterion excluding at least one valid multi-index. -/
def IsProperCriterion (C : List Nat → Prop) : Prop :=
  ∃ α : List Nat, ValidMultiIndex α ∧ ¬ C α

/-! ### Pure `Nat` Histogram Evaluator and `RawQ` Rational Polynomial Evaluator -/

def statPoly (f : List Nat → Nat) (L : List (List Nat)) : Poly :=
  polySum (L.map (fun w => Poly.monomial (f w)))

def statCoeffNat (f : List Nat → Nat) (L : List (List Nat)) (k : Nat) : Nat :=
  countNat k (L.map f)

theorem coeff_statPoly (f : List Nat → Nat) : ∀ (L : List (List Nat)) (k : Nat),
    Poly.coeff (statPoly f L) k = R.ofNat (statCoeffNat f L k)
  | [], _ => rfl
  | w :: ws, k => by
    change Poly.coeff (Poly.add (Poly.monomial (f w)) (statPoly f ws)) k =
           R.ofNat ((if f w = k then 1 else 0) + statCoeffNat f ws k)
    rw [Poly.coeff_add, coeff_statPoly f ws k, Poly.coeff_monomial,
        ← Poly.natR_eq_ofNat, ← Poly.natR_eq_ofNat, Poly.natR_add]
    by_cases h : k = f w
    · subst h; simp only [↓reduceIte]
      have h1 : Poly.natR 1 = 1 := R.zero_add 1
      rw [h1]
    · have h' : f w ≠ k := fun he => h he.symm
      simp only [h, h', ↓reduceIte]
      change (0 : R) + _ = (0 : R) + _; rfl

theorem statCoeffNat_eq_zero_of_gt (f : List Nat → Nat) :
    ∀ (L : List (List Nat)) {D k : Nat}, (∀ w ∈ L, f w ≤ D) → D < k → statCoeffNat f L k = 0
  | [], _, _, _, _ => rfl
  | w :: ws, D, k, hle, hgt => by
    unfold statCoeffNat List.map countNat
    have hw : f w ≠ k := by have := hle w (List.Mem.head ws); omega
    simp only [hw, ↓reduceIte, Nat.zero_add]
    exact statCoeffNat_eq_zero_of_gt f ws (fun u hu => hle u (List.Mem.tail w hu)) hgt

instance instDecidableRawQEquiv (a b : RawQ) : Decidable (RawQ.equiv a b) :=
  inferInstanceAs (Decidable (a.num * b.den = b.num * a.den))

instance instDecidableRawQLt (a b : RawQ) : Decidable (RawQ.lt a b) :=
  inferInstanceAs (Decidable (a.num * b.den < b.num * a.den))

instance instDecidableQMkLt (a b : RawQ) : Decidable (Q.mk a < Q.mk b) :=
  inferInstanceAs (Decidable (a.num * b.den < b.num * a.den))

def evalRawQ : List RawQ → RawQ → RawQ
  | [], _ => RawQ.ofInt 0
  | c :: cs, x => RawQ.add c (RawQ.mul x (evalRawQ cs x))

theorem eval_map_ofQ_mk : ∀ (cs : List RawQ) (x : RawQ),
    Poly.eval (cs.map (fun r => R.ofQ (Q.mk r))) (R.ofQ (Q.mk x)) =
    R.ofQ (Q.mk (evalRawQ cs x))
  | [], _ => rfl
  | c :: cs, x => by
    simp only [List.map, Poly.eval, evalRawQ]
    rw [eval_map_ofQ_mk cs x, ← R.ofQ_mul, ← R.ofQ_add]; rfl

/-! ### Explicit Counterexamples `α = [1, 2]`, `α = [1, 2, 3]`, and Infinite Family `(1, 2, …, m+2)` -/

theorem valid_12 : ValidMultiIndex [1, 2] := by
  refine ⟨(fun h => nomatch h), fun a ha => ?_⟩
  cases ha with
  | head => omega
  | tail _ h1 => cases h1 with | head => omega | tail _ h2 => nomatch h2

theorem valid_123 : ValidMultiIndex [1, 2, 3] := by
  refine ⟨(fun h => nomatch h), fun a ha => ?_⟩
  cases ha with
  | head => omega
  | tail _ h1 => cases h1 with
    | head => omega
    | tail _ h2 => cases h2 with | head => omega | tail _ h3 => nomatch h3

theorem nonPiecewise_12 :
    ¬ IsConstantIndex [1, 2] ∧ ¬ IsBlockConstantGe2 [1, 2] ∧ ¬ HasAdjacentEqual [1, 2] :=
  ⟨by simp [IsConstantIndex],
   not_blockConstantGe2_of_head_ne (by decide),
   by simp [HasAdjacentEqual]⟩

theorem nonPiecewise_123 :
    ¬ IsConstantIndex [1, 2, 3] ∧ ¬ IsBlockConstantGe2 [1, 2, 3] ∧ ¬ HasAdjacentEqual [1, 2, 3] :=
  ⟨by simp [IsConstantIndex],
   not_blockConstantGe2_of_head_ne (by decide),
   by simp [HasAdjacentEqual]⟩

theorem multisetPerms_12_length : (multisetPerms [1, 2]).length = 3 := rfl
theorem multisetPerms_123_length : (multisetPerms [1, 2, 3]).length = 60 := rfl

theorem eulerianPoly_12_eq : Poly.PolyEq (eulerianPoly [1, 2]) [1, 2] := by
  intro k
  change Poly.coeff (statPoly des (multisetPerms [1, 2])) k = Poly.coeff [1, 2] k
  rw [coeff_statPoly]
  cases k with
  | zero =>
    have h0 : statCoeffNat des (multisetPerms [1, 2]) 0 = 1 := rfl
    rw [h0]; rfl
  | succ k1 =>
    cases k1 with
    | zero =>
      have h1 : statCoeffNat des (multisetPerms [1, 2]) 1 = 2 := rfl
      rw [h1]; rfl
    | succ k2 =>
      cases k2 with
      | zero =>
        have h2 : statCoeffNat des (multisetPerms [1, 2]) 2 = 0 := rfl
        rw [h2]; rfl
      | succ k3 =>
        cases k3 with
        | zero =>
          have h3 : statCoeffNat des (multisetPerms [1, 2]) 3 = 0 := rfl
          rw [h3]; rfl
        | succ k4 =>
          have hbound : ∀ w ∈ multisetPerms [1, 2], des w ≤ 3 := fun w hw =>
            Nat.le_trans (des_le_length w)
              (by rw [(multisetPerms_and_eulerianPoly_master [1, 2]).2.2.1 w hw]; decide)
          rw [statCoeffNat_eq_zero_of_gt des (multisetPerms [1, 2]) hbound (by omega)]
          rfl

theorem eulerianPoly_123_eq : Poly.PolyEq (eulerianPoly [1, 2, 3]) [1, 17, 33, 9] := by
  intro k
  change Poly.coeff (statPoly des (multisetPerms [1, 2, 3])) k = Poly.coeff [1, 17, 33, 9] k
  rw [coeff_statPoly]
  cases k with
  | zero =>
    have h : statCoeffNat des (multisetPerms [1, 2, 3]) 0 = 1 := rfl
    rw [h]; rfl
  | succ k1 =>
    cases k1 with
    | zero =>
      have h : statCoeffNat des (multisetPerms [1, 2, 3]) 1 = 17 := rfl
      rw [h]; rfl
    | succ k2 =>
      cases k2 with
      | zero =>
        have h : statCoeffNat des (multisetPerms [1, 2, 3]) 2 = 33 := rfl
        rw [h]; rfl
      | succ k3 =>
        cases k3 with
        | zero =>
          have h : statCoeffNat des (multisetPerms [1, 2, 3]) 3 = 9 := rfl
          rw [h]; rfl
        | succ k4 =>
          cases k4 with
          | zero =>
            have h : statCoeffNat des (multisetPerms [1, 2, 3]) 4 = 0 := rfl
            rw [h]; rfl
          | succ k5 =>
            cases k5 with
            | zero =>
              have h : statCoeffNat des (multisetPerms [1, 2, 3]) 5 = 0 := rfl
              rw [h]; rfl
            | succ k6 =>
              cases k6 with
              | zero =>
                have h : statCoeffNat des (multisetPerms [1, 2, 3]) 6 = 0 := rfl
                rw [h]; rfl
              | succ k7 =>
                have hbound : ∀ w ∈ multisetPerms [1, 2, 3], des w ≤ 6 := fun w hw =>
                  Nat.le_trans (des_le_length w)
                    (by rw [(multisetPerms_and_eulerianPoly_master [1, 2, 3]).2.2.1 w hw]; decide)
                rw [statCoeffNat_eq_zero_of_gt des (multisetPerms [1, 2, 3]) hbound (by omega)]
                rfl

/-- Cubic discriminant `Δ(a₀ + a₁ t + a₂ t² + a₃ t³) = a₁² a₂² - 4 a₀ a₂³ - 4 a₁³ a₃ - 27 a₀² a₃² + 18 a₀ a₁ a₂ a₃`. -/
def cubicDiscriminantInt (a₀ a₁ a₂ a₃ : Int) : Int :=
  a₁ * a₁ * (a₂ * a₂) - 4 * a₀ * (a₂ * a₂ * a₂) - 4 * (a₁ * a₁ * a₁) * a₃ -
  27 * (a₀ * a₀) * (a₃ * a₃) + 18 * a₀ * a₁ * a₂ * a₃

/-- Complete certificate for the strictly non-piecewise-constant index `α = [1, 2, 3]`:
    exact rational sign-alternation at `-10 < -1 < -1/3 < 0`, positive cubic discriminant `82800 > 0`,
    and `HasAllRealSimpleRoots`. -/
theorem counterexample_123_allRealSimple :
    let qNeg10 : RawQ := ⟨-10, 1, by decide⟩
    let qNeg1 : RawQ := ⟨-1, 1, by decide⟩
    let qNegThird : RawQ := ⟨-1, 3, by decide⟩
    let qZero : RawQ := ⟨0, 1, by decide⟩
    ValidMultiIndex [1, 2, 3] ∧
    ¬ IsConstantIndex [1, 2, 3] ∧
    ¬ IsBlockConstantGe2 [1, 2, 3] ∧
    ¬ HasAdjacentEqual [1, 2, 3] ∧
    Poly.eval (eulerianPoly [1, 2, 3]) (R.ofQ (Q.mk qNeg10)) < 0 ∧
    0 < Poly.eval (eulerianPoly [1, 2, 3]) (R.ofQ (Q.mk qNeg1)) ∧
    Poly.eval (eulerianPoly [1, 2, 3]) (R.ofQ (Q.mk qNegThird)) < 0 ∧
    0 < Poly.eval (eulerianPoly [1, 2, 3]) (R.ofQ (Q.mk qZero)) ∧
    cubicDiscriminantInt 1 17 33 9 = 82800 ∧
    0 < cubicDiscriminantInt 1 17 33 9 ∧
    Poly.HasAllRealSimpleRoots (eulerianPoly [1, 2, 3]) := by
  intro qNeg10 qNeg1 qNegThird qZero
  let rawC : List RawQ := [⟨1, 1, by decide⟩, ⟨17, 1, by decide⟩, ⟨33, 1, by decide⟩, ⟨9, 1, by decide⟩]
  have hmap : rawC.map (fun r => R.ofQ (Q.mk r)) = ([1, 17, 33, 9] : Poly) := rfl
  refine ⟨valid_123, nonPiecewise_123.1, nonPiecewise_123.2.1, nonPiecewise_123.2.2,
          ?_, ?_, ?_, ?_, by decide, by decide, (multiset_allRealSimple valid_123).2.1⟩
  · rw [Poly.eval_eq_of_polyEq eulerianPoly_123_eq, ← hmap, eval_map_ofQ_mk]
    exact R.ofQ_lt_iff.mpr (by change RawQ.lt (evalRawQ rawC qNeg10) (RawQ.ofInt 0); decide)
  · rw [Poly.eval_eq_of_polyEq eulerianPoly_123_eq, ← hmap, eval_map_ofQ_mk]
    exact R.ofQ_lt_iff.mpr (by change RawQ.lt (RawQ.ofInt 0) (evalRawQ rawC qNeg1); decide)
  · rw [Poly.eval_eq_of_polyEq eulerianPoly_123_eq, ← hmap, eval_map_ofQ_mk]
    exact R.ofQ_lt_iff.mpr (by change RawQ.lt (evalRawQ rawC qNegThird) (RawQ.ofInt 0); decide)
  · rw [Poly.eval_eq_of_polyEq eulerianPoly_123_eq, ← hmap, eval_map_ofQ_mk]
    exact R.ofQ_lt_iff.mpr (by change RawQ.lt (RawQ.ofInt 0) (evalRawQ rawC qZero); decide)

/-- Infinite family of strictly increasing indices `strictIncIndex m = (1, 2, …, m + 2)`. -/
def rangeFrom : Nat → Nat → List Nat
  | _, 0 => []
  | s, k + 1 => s :: rangeFrom (s + 1) k

def strictIncIndex (m : Nat) : List Nat :=
  rangeFrom 1 (m + 2)

theorem rangeFrom_valid : ∀ (s k : Nat), 1 ≤ s → ∀ a ∈ rangeFrom s k, 1 ≤ a
  | _, 0, _, _, ha => nomatch ha
  | s, k + 1, hs, a, ha => by
    unfold rangeFrom at ha
    cases ha with
    | head => exact hs
    | tail _ hm => exact rangeFrom_valid (s + 1) k (by omega) a hm

theorem rangeFrom_no_adjEq : ∀ (s k : Nat), ¬ HasAdjacentEqual (rangeFrom s (k + 2))
  | s, 0 => by
    change ¬ (s = s + 1 ∨ False)
    rintro (h | h)
    · omega
    · exact False.elim h
  | s, k + 1 => by
    change ¬ (s = s + 1 ∨ HasAdjacentEqual (rangeFrom (s + 1) (k + 2)))
    rintro (heq | htail)
    · omega
    · exact rangeFrom_no_adjEq (s + 1) k htail

theorem strictIncFamily_counterexamples (m : Nat) :
    ValidMultiIndex (strictIncIndex m) ∧
    ¬ IsConstantIndex (strictIncIndex m) ∧
    ¬ IsBlockConstantGe2 (strictIncIndex m) ∧
    ¬ HasAdjacentEqual (strictIncIndex m) ∧
    Poly.HasAllRealSimpleRoots (eulerianPoly (strictIncIndex m)) ∧
    Poly.HasAllRealSimpleRoots (mplEulerianPoly (strictIncIndex m)) := by
  have hval : ValidMultiIndex (strictIncIndex m) :=
    ⟨(by unfold strictIncIndex rangeFrom; intro h; nomatch h),
     rangeFrom_valid 1 (m + 2) (Nat.le_refl 1)⟩
  have hnc : ¬ IsConstantIndex (strictIncIndex m) := by
    unfold strictIncIndex rangeFrom IsConstantIndex
    intro ⟨heq, _⟩; omega
  have hnb : ¬ IsBlockConstantGe2 (strictIncIndex m) := by
    unfold strictIncIndex rangeFrom
    exact not_blockConstantGe2_of_head_ne (by decide)
  exact ⟨hval, hnc, hnb, rangeFrom_no_adjEq 1 m,
         (multiset_allRealSimple hval).2.1, (mpl_allRealSimple hval).2⟩

/-! ### Direct Formal Refutations of Conjecture 00000000472 -/

theorem disproof_conjecture472_multiset_constant :
    ¬ (∀ α : List Nat, ValidMultiIndex α →
        (Poly.HasAllRealSimpleRoots (eulerianPoly α) ↔ IsConstantIndex α)) := by
  intro hall
  exact nonPiecewise_123.1 ((hall [1, 2, 3] valid_123).mp (multiset_allRealSimple valid_123).2.1)

theorem disproof_conjecture472_multiset_blockGe2 :
    ¬ (∀ α : List Nat, ValidMultiIndex α →
        (Poly.HasAllRealSimpleRoots (eulerianPoly α) ↔ IsBlockConstantGe2 α)) := by
  intro hall
  exact nonPiecewise_123.2.1 ((hall [1, 2, 3] valid_123).mp (multiset_allRealSimple valid_123).2.1)

theorem disproof_conjecture472_multiset_adjEq :
    ¬ (∀ α : List Nat, ValidMultiIndex α →
        (Poly.HasAllRealSimpleRoots (eulerianPoly α) ↔ HasAdjacentEqual α)) := by
  intro hall
  exact nonPiecewise_123.2.2 ((hall [1, 2, 3] valid_123).mp (multiset_allRealSimple valid_123).2.1)

theorem disproof_conjecture472_multiset_anyProper {C : List Nat → Prop} (hC : IsProperCriterion C) :
    ¬ (∀ α : List Nat, ValidMultiIndex α →
        (Poly.HasAllRealSimpleRoots (eulerianPoly α) ↔ C α)) := by
  rcases hC with ⟨α, hval, hnC⟩
  intro hall
  exact hnC ((hall α hval).mp (multiset_allRealSimple hval).2.1)

theorem disproof_conjecture472_shifted_anyProper {C : List Nat → Prop} (hC : IsProperCriterion C) :
    ¬ (∀ α : List Nat, ValidMultiIndex α →
        (Poly.HasAllRealSimpleRoots (Poly.mulX (eulerianPoly α)) ↔ C α)) := by
  rcases hC with ⟨α, hval, hnC⟩
  intro hall
  exact hnC ((hall α hval).mp (multiset_allRealSimple hval).2.2)

theorem disproof_conjecture472_mpl_anyProper {C : List Nat → Prop} (hC : IsProperCriterion C) :
    ¬ (∀ α : List Nat, ValidMultiIndex α →
        (Poly.HasAllRealSimpleRoots (mplEulerianPoly α) ↔ C α)) := by
  rcases hC with ⟨α, hval, hnC⟩
  intro hall
  exact hnC ((hall α hval).mp (mpl_allRealSimple hval).2)

theorem disproof_conjecture472_mplStar_anyProper {C : List Nat → Prop} (hC : IsProperCriterion C) :
    ¬ (∀ α : List Nat, ValidMultiIndex α →
        (Poly.HasAllRealSimpleRoots (mplStarEulerianPoly α) ↔ C α)) := by
  rcases hC with ⟨α, hval, hnC⟩
  intro hall
  exact hnC ((hall α hval).mp (mplStar_allRealSimple hval).2)

/-! ### Alternative Conventions: Bidirectional Failures -/

def wdes : List Nat → Nat
  | [] => 0
  | [_] => 0
  | x :: y :: ys => (if y ≤ x then 1 else 0) + wdes (y :: ys)

theorem wdes_le_length : ∀ (w : List Nat), wdes w ≤ w.length
  | [] => Nat.le_refl 0
  | [_] => Nat.zero_le 1
  | x :: y :: ys => by
    unfold wdes
    have ih := wdes_le_length (y :: ys)
    have hl : (x :: y :: ys).length = (y :: ys).length + 1 := rfl
    rw [hl]
    by_cases h : y ≤ x <;> simp only [h, ↓reduceIte] <;> omega

/-- Unstripped weak-descent multiset Eulerian polynomial `W_α(t) = ∑_{w ∈ S(M(α))} t^{wdes(w)}`. -/
def weakDescentPoly (α : List Nat) : Poly :=
  statPoly wdes (multisetPerms α)

theorem weakDescentPoly_12_eq : Poly.PolyEq (weakDescentPoly [1, 2]) [0, 2, 1] := by
  intro k
  unfold weakDescentPoly
  rw [coeff_statPoly]
  cases k with
  | zero =>
    have h : statCoeffNat wdes (multisetPerms [1, 2]) 0 = 0 := rfl
    rw [h]; rfl
  | succ k1 =>
    cases k1 with
    | zero =>
      have h : statCoeffNat wdes (multisetPerms [1, 2]) 1 = 2 := rfl
      rw [h]; rfl
    | succ k2 =>
      cases k2 with
      | zero =>
        have h : statCoeffNat wdes (multisetPerms [1, 2]) 2 = 1 := rfl
        rw [h]; rfl
      | succ k3 =>
        cases k3 with
        | zero =>
          have h : statCoeffNat wdes (multisetPerms [1, 2]) 3 = 0 := rfl
          rw [h]; rfl
        | succ k4 =>
          have hbound : ∀ w ∈ multisetPerms [1, 2], wdes w ≤ 3 := fun w hw =>
            Nat.le_trans (wdes_le_length w)
              (by rw [(multisetPerms_and_eulerianPoly_master [1, 2]).2.2.1 w hw]; decide)
          rw [statCoeffNat_eq_zero_of_gt wdes (multisetPerms [1, 2]) hbound (by omega)]
          rfl

/-- Bidirectional failure for unstripped weak-descent `W_α(t)`:
    non-piecewise-constant `α = [1, 2]` has simple real roots (`0` and `-2`),
    whereas constant `α = [3, 3]` has a double root at `t = 0` (`W_{[3,3]}(0) = W'_{[3,3]}(0) = 0`). -/
theorem weakDescent_bidirectional_failure :
    (ValidMultiIndex [1, 2] ∧ ¬ HasAdjacentEqual [1, 2] ∧
     Poly.HasAllRealSimpleRoots (weakDescentPoly [1, 2])) ∧
    (ValidMultiIndex [3, 3] ∧ IsConstantIndex [3, 3] ∧ IsBlockConstantGe2 [3, 3] ∧
     ¬ Poly.HasAllRealSimpleRoots (weakDescentPoly [3, 3])) := by
  refine ⟨⟨valid_12, nonPiecewise_12.2.2, ?_⟩, ⟨?_, ⟨rfl, trivial⟩, IsBlockConstantGe2.two 3, ?_⟩⟩
  · -- W_{[1,2]}(t) = 2t + t^2 = 1 * (t - 0) * (t - (-2))
    let r2 : R := R.ofQ (Q.mk ⟨-2, 1, by decide⟩)
    have hnd : ListNodup ([0, r2] : List R) := by
      refine ListNodup.cons (fun y hy heq => ?_) (ListNodup.cons (fun _ h => nomatch h) ListNodup.nil)
      cases hy with
      | head =>
        have hlt : r2 < 0 := R.ofQ_lt_iff.mpr (by change RawQ.lt ⟨-2, 1, _⟩ (RawQ.ofInt 0); decide)
        exact R.lt_irrefl 0 (heq ▸ hlt)
      | tail _ hm => nomatch hm
    have hdeg : Poly.DegLe [0, 2, 1] 2 := by
      intro k hk
      cases k with
      | zero => omega
      | succ k1 => cases k1 with
        | zero => omega
        | succ k2 => cases k2 with
          | zero => omega
          | succ k3 => cases k3 <;> rfl
    let rawW : List RawQ := [⟨0, 1, by decide⟩, ⟨2, 1, by decide⟩, ⟨1, 1, by decide⟩]
    have hmap : rawW.map (fun r => R.ofQ (Q.mk r)) = ([0, 2, 1] : Poly) := rfl
    have hroots : ∀ u ∈ ([0, r2] : List R), Poly.eval [0, 2, 1] u = 0 := by
      intro u hu
      cases hu with
      | head =>
        rw [← hmap]
        change Poly.eval (rawW.map _) (R.ofQ (Q.mk ⟨0, 1, by decide⟩)) = R.ofQ (Q.mk (RawQ.ofInt 0))
        rw [eval_map_ofQ_mk]; apply congrArg R.ofQ; apply Q.sound; decide
      | tail _ hm =>
        cases hm with
        | head =>
          rw [← hmap]
          change Poly.eval (rawW.map _) (R.ofQ (Q.mk ⟨-2, 1, by decide⟩)) = R.ofQ (Q.mk (RawQ.ofInt 0))
          rw [eval_map_ofQ_mk]; apply congrArg R.ofQ; apply Q.sound; decide
        | tail _ h2 => nomatch h2
    have hfac := Poly.factor_of_nodup_roots [0, r2] [0, 2, 1] hnd hdeg hroots
    have hc1 : Poly.coeff [0, 2, 1] ([0, r2] : List R).length = 1 := rfl
    rw [hc1] at hfac
    exact Poly.allRealSimple_of_splits ⟨1, [0, r2], R.one_ne_zero, hnd,
      Poly.polyEq_trans weakDescentPoly_12_eq hfac⟩
  · refine ⟨(fun h => nomatch h), fun a ha => ?_⟩
    cases ha with | head => omega | tail _ h1 => cases h1 with | head => omega | tail _ h2 => nomatch h2
  · -- W_{[3,3]}(t) has coeff 0 = 0 and coeff 1 = 0, hence a double root at t = 0
    have hc0 : Poly.coeff (weakDescentPoly [3, 3]) 0 = 0 := by
      unfold weakDescentPoly; rw [coeff_statPoly]
      have h : statCoeffNat wdes (multisetPerms [3, 3]) 0 = 0 := rfl
      rw [h]; rfl
    have hc1 : Poly.coeff (weakDescentPoly [3, 3]) 1 = 0 := by
      unfold weakDescentPoly; rw [coeff_statPoly]
      have h : statCoeffNat wdes (multisetPerms [3, 3]) 1 = 0 := rfl
      rw [h]; rfl
    have heval0 : ∀ (P : Poly), Poly.eval P 0 = Poly.coeff P 0
      | [] => rfl
      | c :: cs => by unfold Poly.eval Poly.coeff; rw [R.zero_mul, R.add_zero]
    have hp0 : Poly.eval (weakDescentPoly [3, 3]) 0 = 0 := by rw [heval0, hc0]
    have hdp0 : Poly.eval (Poly.deriv (weakDescentPoly [3, 3])) 0 = 0 := by
      rw [heval0, Poly.coeff_deriv, hc1, R.mul_zero]
    exact (Poly.not_allRealSimple_of_double_root hp0 hdp0).1

def invSeqs : List Nat → List (List Nat)
  | [] => [[]]
  | s :: ss => flatMapWords (fun x => match x with | [] => [] | e :: _ => (invSeqs ss).map (e :: ·))
                 ((rangeFrom 0 s).map (fun e => [e]))

def ascInvAux : Nat → Nat → List Nat → List Nat → Nat
  | _, _, _, [] => 0
  | _, _, [], _ :: _ => 0
  | ep, sp, s :: ss, e :: es =>
      (if ep * s < e * sp then 1 else 0) + ascInvAux e s ss es

def ascInv (α e : List Nat) : Nat :=
  ascInvAux 0 1 α e

theorem ascInvAux_le_length : ∀ (ep sp : Nat) (α e : List Nat), ascInvAux ep sp α e ≤ e.length
  | _, _, α, [] => by cases α <;> exact Nat.le_refl 0
  | _, _, [], _ :: es => by unfold ascInvAux; exact Nat.zero_le (es.length + 1)
  | ep, sp, s :: ss, e :: es => by
    unfold ascInvAux
    have ih := ascInvAux_le_length e s ss es
    have hl : (e :: es).length = es.length + 1 := rfl
    rw [hl]
    by_cases h : ep * s < e * sp <;> simp only [h, ↓reduceIte] <;> omega

/-- Savage–Schuster `α`-Eulerian polynomial `E_α(t)` over inversion sequences `∏_{i=1}^m {0,…,αᵢ-1}`. -/
def savageSchusterPoly (α : List Nat) : Poly :=
  statPoly (ascInv α) (invSeqs α)

theorem invSeqs_length_elem : ∀ (α e : List Nat), e ∈ invSeqs α → e.length = α.length
  | [], e, he => by
    unfold invSeqs at he
    cases he with | head => rfl | tail _ hm => nomatch hm
  | s :: ss, e, he => by
    unfold invSeqs at he
    rw [mem_flatMapWords] at he
    rcases he with ⟨w, hw, hew⟩
    rw [List.mem_map] at hw
    rcases hw with ⟨x, _, rfl⟩
    dsimp only at hew
    rw [List.mem_map] at hew
    rcases hew with ⟨es, hes, rfl⟩
    simp [invSeqs_length_elem ss es hes]

theorem savageSchuster_123_eq : Poly.PolyEq (savageSchusterPoly [1, 2, 3]) [1, 4, 1] := by
  intro k
  unfold savageSchusterPoly
  rw [coeff_statPoly]
  cases k with
  | zero =>
    have h : statCoeffNat (ascInv [1, 2, 3]) (invSeqs [1, 2, 3]) 0 = 1 := rfl
    rw [h]; rfl
  | succ k1 =>
    cases k1 with
    | zero =>
      have h : statCoeffNat (ascInv [1, 2, 3]) (invSeqs [1, 2, 3]) 1 = 4 := rfl
      rw [h]; rfl
    | succ k2 =>
      cases k2 with
      | zero =>
        have h : statCoeffNat (ascInv [1, 2, 3]) (invSeqs [1, 2, 3]) 2 = 1 := rfl
        rw [h]; rfl
      | succ k3 =>
        cases k3 with
        | zero =>
          have h : statCoeffNat (ascInv [1, 2, 3]) (invSeqs [1, 2, 3]) 3 = 0 := rfl
          rw [h]; rfl
        | succ k4 =>
          have hbound : ∀ e ∈ invSeqs [1, 2, 3], ascInv [1, 2, 3] e ≤ 3 := fun e he =>
            Nat.le_trans (ascInvAux_le_length 0 1 [1, 2, 3] e)
              (by rw [invSeqs_length_elem [1, 2, 3] e he]; decide)
          rw [statCoeffNat_eq_zero_of_gt (ascInv [1, 2, 3]) (invSeqs [1, 2, 3]) hbound (by omega)]
          rfl

theorem savageSchuster_221122_eq : Poly.PolyEq (savageSchusterPoly [2, 2, 1, 1, 2, 2]) [1, 6, 9] := by
  intro k
  unfold savageSchusterPoly
  rw [coeff_statPoly]
  cases k with
  | zero =>
    have h : statCoeffNat (ascInv [2, 2, 1, 1, 2, 2]) (invSeqs [2, 2, 1, 1, 2, 2]) 0 = 1 := rfl
    rw [h]; rfl
  | succ k1 =>
    cases k1 with
    | zero =>
      have h : statCoeffNat (ascInv [2, 2, 1, 1, 2, 2]) (invSeqs [2, 2, 1, 1, 2, 2]) 1 = 6 := rfl
      rw [h]; rfl
    | succ k2 =>
      cases k2 with
      | zero =>
        have h : statCoeffNat (ascInv [2, 2, 1, 1, 2, 2]) (invSeqs [2, 2, 1, 1, 2, 2]) 2 = 9 := rfl
        rw [h]; rfl
      | succ k3 =>
        cases k3 with
        | zero =>
          have h : statCoeffNat (ascInv [2, 2, 1, 1, 2, 2]) (invSeqs [2, 2, 1, 1, 2, 2]) 3 = 0 := rfl
          rw [h]; rfl
        | succ k4 =>
          cases k4 with
          | zero =>
            have h : statCoeffNat (ascInv [2, 2, 1, 1, 2, 2]) (invSeqs [2, 2, 1, 1, 2, 2]) 4 = 0 := rfl
            rw [h]; rfl
          | succ k5 =>
            cases k5 with
            | zero =>
              have h : statCoeffNat (ascInv [2, 2, 1, 1, 2, 2]) (invSeqs [2, 2, 1, 1, 2, 2]) 5 = 0 := rfl
              rw [h]; rfl
            | succ k6 =>
              cases k6 with
              | zero =>
                have h : statCoeffNat (ascInv [2, 2, 1, 1, 2, 2]) (invSeqs [2, 2, 1, 1, 2, 2]) 6 = 0 := rfl
                rw [h]; rfl
              | succ k7 =>
                have hbound : ∀ e ∈ invSeqs [2, 2, 1, 1, 2, 2], ascInv [2, 2, 1, 1, 2, 2] e ≤ 6 := fun e he =>
                  Nat.le_trans (ascInvAux_le_length 0 1 [2, 2, 1, 1, 2, 2] e)
                    (by rw [invSeqs_length_elem [2, 2, 1, 1, 2, 2] e he]; decide)
                rw [statCoeffNat_eq_zero_of_gt (ascInv [2, 2, 1, 1, 2, 2]) (invSeqs [2, 2, 1, 1, 2, 2]) hbound (by omega)]
                rfl

/-- Bidirectional failure for Savage–Schuster `E_α(t)`:
    strictly non-piecewise-constant `α = [1, 2, 3]` gives `E_{[1,2,3]}(t) = 1 + 4t + t²` (simple real roots),
    whereas block-constant `α = [2, 2, 1, 1, 2, 2]` gives `E_{[2,2,1,1,2,2]}(t) = (1 + 3t)²` (double root at `-1/3`). -/
theorem savageSchuster_bidirectional_failure :
    (ValidMultiIndex [1, 2, 3] ∧ ¬ HasAdjacentEqual [1, 2, 3] ∧
     Poly.HasAllRealSimpleRoots (savageSchusterPoly [1, 2, 3])) ∧
    (ValidMultiIndex [2, 2, 1, 1, 2, 2] ∧ IsBlockConstantGe2 [2, 2, 1, 1, 2, 2] ∧
     ¬ Poly.HasAllRealSimpleRoots (savageSchusterPoly [2, 2, 1, 1, 2, 2])) := by
  refine ⟨⟨valid_123, nonPiecewise_123.2.2, ?_⟩,
          ⟨?_, IsBlockConstantGe2.appendBlock 2 (IsBlockConstantGe2.appendBlock 1 (IsBlockConstantGe2.two 2)), ?_⟩⟩
  · -- E_{[1,2,3]}(t) = 1 + 4t + t^2 alternates signs at 0 > -1 > -4, giving 2 distinct real roots
    let rawE : List RawQ := [⟨1, 1, by decide⟩, ⟨4, 1, by decide⟩, ⟨1, 1, by decide⟩]
    have hmap : rawE.map (fun r => R.ofQ (Q.mk r)) = ([1, 4, 1] : Poly) := rfl
    let x0 : R := R.ofQ (Q.mk ⟨0, 1, by decide⟩)
    let x1 : R := R.ofQ (Q.mk ⟨-1, 1, by decide⟩)
    let x2 : R := R.ofQ (Q.mk ⟨-4, 1, by decide⟩)
    have halt : Poly.AltSigns true [1, 4, 1] [x0, x1, x2] := by
      unfold Poly.AltSigns
      refine ⟨R.ofQ_lt_iff.mpr (by decide), ?_, R.ofQ_lt_iff.mpr (by decide), ?_, ?_⟩
      · change 0 < Poly.eval [1, 4, 1] x0
        rw [← hmap, eval_map_ofQ_mk]
        exact R.ofQ_lt_iff.mpr (by change RawQ.lt (RawQ.ofInt 0) (evalRawQ rawE ⟨0, 1, _⟩); decide)
      · change Poly.eval [1, 4, 1] x1 < 0
        rw [← hmap, eval_map_ofQ_mk]
        exact R.ofQ_lt_iff.mpr (by change RawQ.lt (evalRawQ rawE ⟨-1, 1, _⟩) (RawQ.ofInt 0); decide)
      · change 0 < Poly.eval [1, 4, 1] x2
        rw [← hmap, eval_map_ofQ_mk]
        exact R.ofQ_lt_iff.mpr (by change RawQ.lt (RawQ.ofInt 0) (evalRawQ rawE ⟨-4, 1, _⟩); decide)
    obtain ⟨etas, hetas_len, hetas_dec, hetas_roots, _⟩ :=
      Poly.roots_of_altSigns_cons [1, 4, 1] true x0 [x1, x2] (R.le_refl 0) halt
    have hdeg : Poly.DegLe [1, 4, 1] 2 := by
      intro k hk
      cases k with
      | zero => omega
      | succ k1 => cases k1 with
        | zero => omega
        | succ k2 => cases k2 with
          | zero => omega
          | succ k3 => cases k3 <;> rfl
    have hfac := Poly.factor_of_nodup_roots etas [1, 4, 1] (Poly.strictlyDecNeg_nodup hetas_dec)
                   (hetas_len ▸ hdeg) hetas_roots
    have hc1 : Poly.coeff [1, 4, 1] etas.length = 1 := by rw [hetas_len]; rfl
    rw [hc1] at hfac
    exact Poly.allRealSimple_of_splits ⟨1, etas, R.one_ne_zero,
      Poly.strictlyDecNeg_nodup hetas_dec, Poly.polyEq_trans savageSchuster_123_eq hfac⟩
  · refine ⟨(fun h => nomatch h), fun a ha => ?_⟩
    rcases ha with (_ | ⟨_, _ | ⟨_, _ | ⟨_, _ | ⟨_, _ | ⟨_, _ | ⟨_, h6⟩⟩⟩⟩⟩⟩) <;> try omega
    nomatch h6
  · -- E_{[2,2,1,1,2,2]}(t) = 1 + 6t + 9t^2 has double root at x = -1/3
    let x : R := R.ofQ (Q.mk ⟨-1, 3, by decide⟩)
    let rawP : List RawQ := [⟨1, 1, by decide⟩, ⟨6, 1, by decide⟩, ⟨9, 1, by decide⟩]
    let rawD : List RawQ := [⟨6, 1, by decide⟩, ⟨18, 1, by decide⟩]
    have hmapP : rawP.map (fun r => R.ofQ (Q.mk r)) = ([1, 6, 9] : Poly) := rfl
    have hmapD : rawD.map (fun r => R.ofQ (Q.mk r)) = ([6, 18] : Poly) := rfl
    have hderiv_eq : Poly.PolyEq (Poly.deriv [1, 6, 9]) [6, 18] := by
      intro k
      rw [Poly.coeff_deriv, Poly.natR_eq_ofNat]
      cases k with
      | zero =>
        change R.ofQ (Q.mk (RawQ.ofInt 1)) * R.ofQ (Q.mk (RawQ.ofInt 6)) = R.ofQ (Q.mk (RawQ.ofInt 6))
        rw [← R.ofQ_mul]; apply congrArg R.ofQ; apply Q.sound; decide
      | succ k1 =>
        cases k1 with
        | zero =>
          change R.ofQ (Q.mk (RawQ.ofInt 2)) * R.ofQ (Q.mk (RawQ.ofInt 9)) = R.ofQ (Q.mk (RawQ.ofInt 18))
          rw [← R.ofQ_mul]; apply congrArg R.ofQ; apply Q.sound; decide
        | succ k2 =>
          have hz : Poly.coeff [1, 6, 9] (k2 + 3) = 0 := by cases k2 <;> rfl
          rw [hz, R.mul_zero]
          cases k2 <;> rfl
    have hp : Poly.eval (savageSchusterPoly [2, 2, 1, 1, 2, 2]) x = 0 := by
      rw [Poly.eval_eq_of_polyEq savageSchuster_221122_eq, ← hmapP, eval_map_ofQ_mk]
      apply congrArg R.ofQ; apply Q.sound; decide
    have hdp : Poly.eval (Poly.deriv (savageSchusterPoly [2, 2, 1, 1, 2, 2])) x = 0 := by
      rw [Poly.eval_eq_of_polyEq (Poly.polyEq_trans (Poly.deriv_polyEq savageSchuster_221122_eq) hderiv_eq),
          ← hmapD, eval_map_ofQ_mk]
      apply congrArg R.ofQ; apply Q.sound; decide
    exact (Poly.not_allRealSimple_of_double_root hp hdp).1

/-! ### Non-Vacuity & Non-Tautology Positive Witnesses -/

/-- Positive witness 1: `α = [1, 1]` simultaneously inhabits `ValidMultiIndex`, `IsConstantIndex`,
    `IsBlockConstantGe2`, `HasAdjacentEqual`, and `HasAllRealSimpleRoots` for both `eulerianPoly` and `mplEulerianPoly`. -/
theorem positive_witness_constant_11 :
    ValidMultiIndex [1, 1] ∧
    IsConstantIndex [1, 1] ∧
    IsBlockConstantGe2 [1, 1] ∧
    HasAdjacentEqual [1, 1] ∧
    Poly.HasAllRealSimpleRoots (eulerianPoly [1, 1]) ∧
    Poly.HasAllRealSimpleRoots (mplEulerianPoly [1, 1]) := by
  have hval : ValidMultiIndex [1, 1] := by
    refine ⟨(fun h => nomatch h), fun a ha => ?_⟩
    cases ha with | head => omega | tail _ h1 => cases h1 with | head => omega | tail _ h2 => nomatch h2
  exact ⟨hval, ⟨rfl, trivial⟩, IsBlockConstantGe2.two 1, Or.inl rfl,
         (multiset_allRealSimple hval).2.1, (mpl_allRealSimple hval).2⟩

/-- Positive witness 2 (non-tautology of `HasAllRealSimpleRoots` against non-real complex roots):
    `P(t) = 1 + t²` (`[1, 0, 1]`) vanishes at `z = i ∈ C` with `Im(i) = 1 ≠ 0`. -/
theorem positive_witness_nonreal_roots : ¬ Poly.HasAllRealSimpleRoots [1, 0, 1] := by
  intro ⟨_, hall⟩
  let I : Complex := ⟨0, 1⟩
  have hz : Poly.evalC [1, 0, 1] I = 0 := by
    unfold Poly.evalC
    apply Complex.ext
    · change (1 : R) + ((0 : R) * ((0 : R) + ((0 : R) * ((1 : R) + (0 * 0 - 1 * 0)) -
             (1 : R) * ((0 : R) + (0 * 0 + 1 * 0)))) -
             (1 : R) * ((0 : R) + ((0 : R) * ((0 : R) + (0 * 0 + 1 * 0)) +
             (1 : R) * ((1 : R) + (0 * 0 - 1 * 0))))) = 0
      have hz0 : -(0 : R) = 0 := by have := R.add_neg_cancel 0; rw [R.zero_add] at this; exact this
      simp only [R.zero_mul, R.mul_zero, R.one_mul, R.sub_eq_add_neg, hz0, R.add_zero, R.zero_add, R.add_neg_cancel]
    · change (0 : R) + ((0 : R) * ((0 : R) + ((0 : R) * ((0 : R) + (0 * 0 + 1 * 0)) +
             (1 : R) * ((1 : R) + (0 * 0 - 1 * 0)))) +
             (1 : R) * ((0 : R) + ((0 : R) * ((1 : R) + (0 * 0 - 1 * 0)) -
             (1 : R) * ((0 : R) + (0 * 0 + 1 * 0))))) = 0
      have hz0 : -(0 : R) = 0 := by have := R.add_neg_cancel 0; rw [R.zero_add] at this; exact this
      simp only [R.zero_mul, R.mul_zero, R.one_mul, R.sub_eq_add_neg, hz0, R.add_zero, R.zero_add]
  exact R.one_ne_zero (hall I hz).1

/-- Positive witness 3 (non-tautology of `HasAllRealSimpleRoots` against repeated real roots):
    `P(t) = 1 + 2t + t² = (1 + t)²` (`[1, 2, 1]`) has a double real root at `t = -1`. -/
theorem positive_witness_multiple_real_root : ¬ Poly.HasAllRealSimpleRoots [1, 2, 1] := by
  let x : R := R.ofQ (Q.mk ⟨-1, 1, by decide⟩)
  let rawP : List RawQ := [⟨1, 1, by decide⟩, ⟨2, 1, by decide⟩, ⟨1, 1, by decide⟩]
  let rawD : List RawQ := [⟨2, 1, by decide⟩, ⟨2, 1, by decide⟩]
  have hmapP : rawP.map (fun r => R.ofQ (Q.mk r)) = ([1, 2, 1] : Poly) := rfl
  have hmapD : rawD.map (fun r => R.ofQ (Q.mk r)) = ([2, 2] : Poly) := rfl
  have hderiv_eq : Poly.PolyEq (Poly.deriv [1, 2, 1]) [2, 2] := by
    intro k; rw [Poly.coeff_deriv, Poly.natR_eq_ofNat]
    cases k with
    | zero =>
      change R.ofQ (Q.mk (RawQ.ofInt 1)) * R.ofQ (Q.mk (RawQ.ofInt 2)) = R.ofQ (Q.mk (RawQ.ofInt 2))
      rw [← R.ofQ_mul]; apply congrArg R.ofQ; apply Q.sound; decide
    | succ k1 =>
      cases k1 with
      | zero =>
        change R.ofQ (Q.mk (RawQ.ofInt 2)) * R.ofQ (Q.mk (RawQ.ofInt 1)) = R.ofQ (Q.mk (RawQ.ofInt 2))
        rw [← R.ofQ_mul]; apply congrArg R.ofQ; apply Q.sound; decide
      | succ k2 =>
        have hz : Poly.coeff [1, 2, 1] (k2 + 3) = 0 := by cases k2 <;> rfl
        rw [hz, R.mul_zero]; cases k2 <;> rfl
  have hp : Poly.eval [1, 2, 1] x = 0 := by
    rw [← hmapP, eval_map_ofQ_mk]; apply congrArg R.ofQ; apply Q.sound; decide
  have hdp : Poly.eval (Poly.deriv [1, 2, 1]) x = 0 := by
    rw [Poly.eval_eq_of_polyEq hderiv_eq, ← hmapD, eval_map_ofQ_mk]
    apply congrArg R.ofQ; apply Q.sound; decide
  exact (Poly.not_allRealSimple_of_double_root hp hdp).1

end Conjecture00000000472

/-! ## Axiom Verification Audit -/

#print axioms Conjecture00000000472.Poly.poly_ivt
#print axioms Conjecture00000000472.Poly.interlaceOp_preserves_negSimpleRoots
#print axioms Conjecture00000000472.simion_recurrence
#print axioms Conjecture00000000472.multiset_allRealSimple
#print axioms Conjecture00000000472.mpl_allRealSimple
#print axioms Conjecture00000000472.mplStar_allRealSimple
#print axioms Conjecture00000000472.counterexample_123_allRealSimple
#print axioms Conjecture00000000472.strictIncFamily_counterexamples
#print axioms Conjecture00000000472.disproof_conjecture472_multiset_constant
#print axioms Conjecture00000000472.disproof_conjecture472_multiset_blockGe2
#print axioms Conjecture00000000472.disproof_conjecture472_multiset_adjEq
#print axioms Conjecture00000000472.disproof_conjecture472_multiset_anyProper
#print axioms Conjecture00000000472.disproof_conjecture472_shifted_anyProper
#print axioms Conjecture00000000472.disproof_conjecture472_mpl_anyProper
#print axioms Conjecture00000000472.disproof_conjecture472_mplStar_anyProper
#print axioms Conjecture00000000472.weakDescent_bidirectional_failure
#print axioms Conjecture00000000472.savageSchuster_bidirectional_failure
#print axioms Conjecture00000000472.positive_witness_constant_11
#print axioms Conjecture00000000472.positive_witness_nonreal_roots
#print axioms Conjecture00000000472.positive_witness_multiple_real_root


