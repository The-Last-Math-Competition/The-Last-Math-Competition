/-
  LidskiiProduct/Algebra.lean
  Core Lean 4 integer algebra and order lemmas (zero external dependencies).
-/

namespace LidskiiProduct

theorem sq_eq_mul_self (x : Int) : x ^ 2 = x * x := by
  simp [Int.pow_succ, Int.pow_zero]

theorem mul_self_nonneg' (x : Int) : 0 ≤ x * x := by
  rcases Int.le_total 0 x with h | h
  · exact Int.mul_nonneg h h
  · have hpos : 0 ≤ -x := by omega
    have hm : 0 ≤ (-x) * (-x) := Int.mul_nonneg hpos hpos
    rw [Int.neg_mul_neg] at hm
    exact hm

theorem sq_nonneg (x : Int) : 0 ≤ x ^ 2 := by
  rw [sq_eq_mul_self]
  exact mul_self_nonneg' x

theorem sq_pos_of_ne_zero {x : Int} (hx : x ≠ 0) : 0 < x ^ 2 := by
  rw [sq_eq_mul_self]
  rcases Int.lt_trichotomy x 0 with hlt | heq | hgt
  · have hpos : 0 < -x := by omega
    have hmul : 0 < (-x) * (-x) := Int.mul_pos hpos hpos
    rw [Int.neg_mul_neg] at hmul
    exact hmul
  · exact absurd heq hx
  · exact Int.mul_pos hgt hgt

theorem diff_sq (a b : Int) : (a - b) * (a + b) = a * a - b * b := by
  rw [Int.mul_add, Int.sub_mul, Int.sub_mul, Int.mul_comm b a]
  omega

theorem eq_of_sq_eq_of_nonneg {x y : Int} (hx : 0 ≤ x) (hy : 0 ≤ y)
    (h : x ^ 2 = y ^ 2) : x = y := by
  rw [sq_eq_mul_self, sq_eq_mul_self] at h
  have hdiff : (x - y) * (x + y) = 0 := by
    rw [diff_sq]
    omega
  rcases Int.mul_eq_zero.mp hdiff with h1 | h2
  · omega
  · omega

theorem le_of_sq_le_of_nonneg {x y : Int} (hy : 0 ≤ y)
    (h : x ^ 2 ≤ y ^ 2) : x ≤ y := by
  rw [sq_eq_mul_self, sq_eq_mul_self] at h
  rcases Int.le_total x y with hle | hge
  · exact hle
  · have h1 : 0 ≤ x - y := by omega
    have h2 : 0 ≤ x + y := by omega
    have hprod : 0 ≤ (x - y) * (x + y) := Int.mul_nonneg h1 h2
    rw [diff_sq] at hprod
    have hsq_eq : x ^ 2 = y ^ 2 := by
      rw [sq_eq_mul_self, sq_eq_mul_self]
      omega
    have hx : 0 ≤ x := by omega
    have heq := eq_of_sq_eq_of_nonneg hx hy hsq_eq
    omega

theorem add_sq (a b : Int) : (a + b) ^ 2 = a ^ 2 + b ^ 2 + 2 * (a * b) := by
  rw [sq_eq_mul_self, sq_eq_mul_self, sq_eq_mul_self]
  rw [Int.add_mul, Int.mul_add, Int.mul_add, Int.mul_comm b a]
  omega

theorem sub_sq (a b : Int) : (a - b) ^ 2 = a ^ 2 + b ^ 2 - 2 * (a * b) := by
  rw [sq_eq_mul_self, sq_eq_mul_self, sq_eq_mul_self]
  rw [Int.sub_mul, Int.mul_sub, Int.mul_sub, Int.mul_comm b a]
  omega

theorem mul_pow_two (a b : Int) : (a * b) ^ 2 = a ^ 2 * b ^ 2 := by
  rw [sq_eq_mul_self, sq_eq_mul_self, sq_eq_mul_self]
  rw [Int.mul_assoc, Int.mul_left_comm b a b, ← Int.mul_assoc]

/-- The Brahmagupta-Fibonacci (two-square Cauchy-Schwarz) identity. -/
theorem brahmagupta_fibonacci (a b c d : Int) :
    (a * c + b * d) ^ 2 + (a * d - b * c) ^ 2 = (a ^ 2 + b ^ 2) * (c ^ 2 + d ^ 2) := by
  rw [add_sq, sub_sq, mul_pow_two, mul_pow_two, mul_pow_two, mul_pow_two]
  have hmid : (a * c) * (b * d) = (a * d) * (b * c) := calc
    (a * c) * (b * d) = a * (c * (b * d)) := Int.mul_assoc a c (b * d)
    _ = a * (c * (d * b)) := by rw [Int.mul_comm b d]
    _ = a * ((c * d) * b) := by rw [← Int.mul_assoc c d b]
    _ = a * ((d * c) * b) := by rw [Int.mul_comm c d]
    _ = a * (d * (c * b)) := by rw [Int.mul_assoc d c b]
    _ = a * (d * (b * c)) := by rw [Int.mul_comm c b]
    _ = (a * d) * (b * c) := by rw [← Int.mul_assoc a d (b * c)]
  rw [hmid]
  rw [Int.add_mul, Int.mul_add, Int.mul_add]
  omega

/-- Key polynomial identity connecting two pairs `(X, Y)` and `(P, Q)` with equal products:
    `(X - P) * (X - Q) = X * ((X + Y) - (P + Q))`. -/
theorem factor_of_prod_eq {X Y P Q : Int} (hprod : X * Y = P * Q) :
    (X - P) * (X - Q) = X * ((X + Y) - (P + Q)) := by
  rw [Int.sub_mul, Int.mul_sub, Int.mul_sub, Int.mul_comm P X]
  have _h1 : P * Q = X * Y := hprod.symm
  have _h2 : X * ((X + Y) - (P + Q)) = X * X + X * Y - X * P - X * Q := by
    rw [Int.mul_sub, Int.mul_add, Int.mul_add]
    omega
  omega

/-- If `0 ≤ Y ≤ X`, `0 ≤ Q ≤ P`, `X * Y = P * Q`, and `X + Y ≤ P + Q`, then `X ≤ P`. -/
theorem pair_domination_of_sum_le_of_prod_eq
    {X Y P Q : Int}
    (_hXY : Y ≤ X) (hPQ : Q ≤ P) (_hY0 : 0 ≤ Y) (_hQ0 : 0 ≤ Q)
    (hprod : X * Y = P * Q) (hsum : X + Y ≤ P + Q) :
    X ≤ P := by
  rcases Int.lt_trichotomy X P with hlt | heq | hgt
  · omega
  · omega
  · have hXP : 0 < X - P := by omega
    have hXQ : 0 < X - Q := by omega
    have hXpos : 0 < X := by omega
    have hlhs : 0 < (X - P) * (X - Q) := Int.mul_pos hXP hXQ
    have hrhs_nonpos : X * ((X + Y) - (P + Q)) ≤ 0 := by
      have hdiff_nonneg : 0 ≤ (P + Q) - (X + Y) := by omega
      have hmul_nonneg : 0 ≤ X * ((P + Q) - (X + Y)) :=
        Int.mul_nonneg (Int.le_of_lt hXpos) hdiff_nonneg
      have heq_neg : X * ((P + Q) - (X + Y)) + X * ((X + Y) - (P + Q)) = 0 := by
        rw [← Int.mul_add]
        have hzero : ((P + Q) - (X + Y)) + ((X + Y) - (P + Q)) = 0 := by omega
        rw [hzero, Int.mul_zero]
      omega
    have hid := factor_of_prod_eq hprod
    omega

/-- Conversely, log-majorization `(X ≤ P, X * Y = P * Q)` on sorted non-negative pairs
    implies additive weak majorization `(X ≤ P, X + Y ≤ P + Q)`. -/
theorem sum_le_of_le_of_prod_eq
    {X Y P Q : Int}
    (hXY : Y ≤ X) (_hPQ : Q ≤ P) (hY0 : 0 ≤ Y) (_hQ0 : 0 ≤ Q)
    (hle : X ≤ P) (hprod : X * Y = P * Q) :
    X + Y ≤ P + Q := by
  have hid : (P - X) * (P - Y) = P * ((P + Q) - (X + Y)) := by
    have _hsym := factor_of_prod_eq hprod.symm
    omega
  have hPX : 0 ≤ P - X := by omega
  have hPY : 0 ≤ P - Y := by omega
  have hlhs : 0 ≤ (P - X) * (P - Y) := Int.mul_nonneg hPX hPY
  rcases Int.lt_trichotomy P 0 with hPneg | hP0 | hPpos
  · omega
  · omega
  · rw [hid] at hlhs
    rcases Int.lt_trichotomy (X + Y) (P + Q) with _hok1 | _hok2 | hlt
    · omega
    · omega
    · have hneg : 0 < (X + Y) - (P + Q) := by omega
      have _hpos_prod : 0 < P * ((X + Y) - (P + Q)) := Int.mul_pos hPpos hneg
      have _hsum_zero : P * ((P + Q) - (X + Y)) + P * ((X + Y) - (P + Q)) = 0 := by
        rw [← Int.mul_add]
        have hz : ((P + Q) - (X + Y)) + ((X + Y) - (P + Q)) = 0 := by omega
        rw [hz, Int.mul_zero]
      omega

/-- Sorted pairs with identical sum and product are identical. -/
theorem pair_eq_of_sum_eq_of_prod_eq
    {X Y P Q : Int}
    (hXY : Y ≤ X) (hPQ : Q ≤ P)
    (hprod : X * Y = P * Q) (hsum : X + Y = P + Q) :
    X = P ∧ Y = Q := by
  have hid := factor_of_prod_eq hprod
  have hz : (X + Y) - (P + Q) = 0 := by omega
  rw [hz, Int.mul_zero] at hid
  rcases Int.mul_eq_zero.mp hid with _hXP | _hXQ
  · omega
  · omega

/-- Integer absolute value `|x|` with zero external dependencies. -/
def absInt (x : Int) : Int := if 0 ≤ x then x else -x

theorem absInt_nonneg (x : Int) : 0 ≤ absInt x := by
  dsimp [absInt]
  split <;> omega

theorem absInt_sq (x : Int) : (absInt x) ^ 2 = x ^ 2 := by
  dsimp [absInt]
  split
  · rfl
  · rw [sq_eq_mul_self, sq_eq_mul_self, Int.neg_mul_neg]

end LidskiiProduct
