/-
  Conjecture 00000001284 — Nim-Multiplication and Square Density in the Nim-Square Sequence
  Self-contained formalization in Core Lean 4 (v4.19.0, zero external dependencies).
-/

namespace Conjecture00000001284

/-! ## Section 1: Nim-Addition (`nimAdd`) and Base-`M k` Arithmetic -/

/-- Nim-addition on `Nat` is bitwise exclusive-or (XOR). -/
def nimAdd (x y : Nat) : Nat := x ^^^ y

theorem nimAdd_comm (x y : Nat) : nimAdd x y = nimAdd y x :=
  Nat.xor_comm x y

theorem nimAdd_assoc (x y z : Nat) : nimAdd (nimAdd x y) z = nimAdd x (nimAdd y z) :=
  Nat.xor_assoc x y z

theorem nimAdd_self (x : Nat) : nimAdd x x = 0 :=
  Nat.xor_self x

theorem nimAdd_zero (x : Nat) : nimAdd x 0 = x :=
  Nat.xor_zero x

theorem zero_nimAdd (x : Nat) : nimAdd 0 x = x :=
  Nat.zero_xor x

theorem nimAdd_cancel_left (x y : Nat) : nimAdd x (nimAdd x y) = y := by
  rw [← nimAdd_assoc, nimAdd_self, zero_nimAdd]

theorem nimAdd_cancel_right (x y : Nat) : nimAdd (nimAdd x y) y = x := by
  rw [nimAdd_assoc, nimAdd_self, nimAdd_zero]

theorem nimAdd_eq_zero_iff (x y : Nat) : nimAdd x y = 0 ↔ x = y := by
  constructor
  · intro h
    have h1 : nimAdd x (nimAdd x y) = nimAdd x 0 := congrArg (nimAdd x) h
    rw [nimAdd_cancel_left, nimAdd_zero] at h1
    exact h1.symm
  · intro h
    subst h
    exact nimAdd_self x

theorem nimAdd_lt_two_pow {x y n : Nat} (hx : x < 2 ^ n) (hy : y < 2 ^ n) :
    nimAdd x y < 2 ^ n :=
  Nat.xor_lt_two_pow hx hy

theorem nimAdd_four_swap (a b c d : Nat) :
    nimAdd (nimAdd a b) (nimAdd c d) = nimAdd (nimAdd a c) (nimAdd b d) := by
  rw [nimAdd_assoc, nimAdd_assoc, ← nimAdd_assoc b c d, nimAdd_comm b c, nimAdd_assoc c b d]

/-- Fermat 2-powers `M k = 2^(2^k)` (`M 0 = 2, M 1 = 4, M 2 = 16, ...`). -/
def M (k : Nat) : Nat := 2 ^ (2 ^ k)

/-- Half Fermat 2-powers `P k = 2^(2^k - 1)` (`P 0 = 1, P 1 = 2, P 2 = 8, ...`). -/
def P (k : Nat) : Nat := 2 ^ (2 ^ k - 1)

theorem two_pow_pos (n : Nat) : 0 < 2 ^ n := by
  induction n with
  | zero => decide
  | succ n ih => omega

theorem M_pos (k : Nat) : 0 < M k :=
  two_pow_pos (2 ^ k)

theorem one_lt_M (k : Nat) : 1 < M k := by
  unfold M
  have h1 : 1 ≤ 2 ^ k := two_pow_pos k
  obtain ⟨t, ht⟩ : ∃ t, 2 ^ k = t + 1 := ⟨2 ^ k - 1, by omega⟩
  rw [ht, Nat.pow_succ]
  have h2 : 0 < 2 ^ t := two_pow_pos t
  omega

theorem pow_add_eq (a b : Nat) : 2 ^ (a + b) = 2 ^ a * 2 ^ b :=
  Nat.pow_add 2 a b

theorem M_succ (k : Nat) : M (k + 1) = M k * M k := by
  unfold M
  have h : 2 ^ (k + 1) = 2 ^ k + 2 ^ k := by
    rw [Nat.pow_succ]
    omega
  rw [h, pow_add_eq]

theorem M_mono {k l : Nat} (hkl : k ≤ l) : M k ≤ M l := by
  induction hkl with
  | refl => exact Nat.le_refl _
  | @step m _ ih =>
    rw [M_succ m]
    have hp : 1 ≤ M m := M_pos m
    have hm : M m * 1 ≤ M m * M m := Nat.mul_le_mul_left (M m) hp
    omega

theorem two_mul_P (k : Nat) : 2 * P k = M k := by
  unfold P M
  have hk : 1 ≤ 2 ^ k := two_pow_pos k
  have h : (2 ^ k - 1) + 1 = 2 ^ k := by omega
  calc
    2 * 2 ^ (2 ^ k - 1) = 2 ^ (2 ^ k - 1) * 2 := Nat.mul_comm _ _
    _ = 2 ^ ((2 ^ k - 1) + 1) := (Nat.pow_succ 2 (2 ^ k - 1)).symm
    _ = 2 ^ (2 ^ k) := by rw [h]

theorem P_lt_M (k : Nat) : P k < M k := by
  have h1 : 2 * P k = M k := two_mul_P k
  have h2 : 0 < P k := two_pow_pos (2 ^ k - 1)
  omega

theorem P_succ (k : Nat) : P (k + 1) = M k * P k := by
  unfold P M
  have hk : 1 ≤ 2 ^ k := two_pow_pos k
  have h : 2 ^ (k + 1) - 1 = 2 ^ k + (2 ^ k - 1) := by
    rw [Nat.pow_succ]
    omega
  rw [h, pow_add_eq]

/-- High and low digits of `x` in base `M k`, and reconstruction `join k a b = M k * a + b`. -/
def hi (k x : Nat) : Nat := x / M k
def lo (k x : Nat) : Nat := x % M k
def join (k a b : Nat) : Nat := M k * a + b

theorem lo_lt (k x : Nat) : lo k x < M k :=
  Nat.mod_lt x (M_pos k)

theorem join_hi_lo (k x : Nat) : join k (hi k x) (lo k x) = x :=
  Nat.div_add_mod x (M k)

theorem div_mod_unique {m a b q r : Nat} (hb : b < m) (hr : r < m)
    (heq : m * a + b = m * q + r) : a = q ∧ b = r := by
  have hlt_or : a < q ∨ q < a ∨ a = q := by omega
  rcases hlt_or with hlt | hgt | rfl
  · have hle : a + 1 ≤ q := hlt
    have hm : m * (a + 1) ≤ m * q := Nat.mul_le_mul_left m hle
    rw [Nat.mul_add, Nat.mul_one] at hm
    omega
  · have hle : q + 1 ≤ a := hgt
    have hm : m * (q + 1) ≤ m * a := Nat.mul_le_mul_left m hle
    rw [Nat.mul_add, Nat.mul_one] at hm
    omega
  · exact ⟨rfl, by omega⟩

theorem hi_join (k a b : Nat) (hb : b < M k) : hi k (join k a b) = a := by
  have h := div_mod_unique hb (lo_lt k (join k a b)) (join_hi_lo k (join k a b)).symm
  exact h.1.symm

theorem lo_join (k a b : Nat) (hb : b < M k) : lo k (join k a b) = b := by
  have h := div_mod_unique hb (lo_lt k (join k a b)) (join_hi_lo k (join k a b)).symm
  exact h.2.symm

theorem join_lt (k a b : Nat) (ha : a < M k) (hb : b < M k) : join k a b < M (k + 1) := by
  unfold join
  rw [M_succ]
  have hle : a + 1 ≤ M k := ha
  have hm : M k * (a + 1) ≤ M k * M k := Nat.mul_le_mul_left (M k) hle
  rw [Nat.mul_add, Nat.mul_one] at hm
  omega

theorem hi_lt_of_lt (k x : Nat) (hx : x < M (k + 1)) : hi k x < M k := by
  rw [M_succ] at hx
  have hdiv := join_hi_lo k x
  unfold join at hdiv
  cases Nat.lt_or_ge (hi k x) (M k) with
  | inl hlt => exact hlt
  | inr hge =>
    have hm : M k * M k ≤ M k * hi k x := Nat.mul_le_mul_left (M k) hge
    omega

theorem join_lt_mul_iff (k a b c : Nat) (hb : b < M k) :
    join k a b < M k * c ↔ a < c := by
  unfold join
  constructor
  · intro h
    cases Nat.lt_or_ge a c with
    | inl hlt => exact hlt
    | inr hge =>
      have hm : M k * c ≤ M k * a := Nat.mul_le_mul_left (M k) hge
      omega
  · intro h
    have hle : a + 1 ≤ c := h
    have hm : M k * (a + 1) ≤ M k * c := Nat.mul_le_mul_left (M k) hle
    rw [Nat.mul_add, Nat.mul_one] at hm
    omega

theorem nimAdd_join (k a1 b1 a2 b2 : Nat) (hb1 : b1 < M k) (hb2 : b2 < M k) :
    nimAdd (join k a1 b1) (join k a2 b2) = join k (nimAdd a1 a2) (nimAdd b1 b2) := by
  unfold nimAdd join M
  apply Nat.eq_of_testBit_eq
  intro j
  have hb12 : (b1 ^^^ b2) < 2 ^ (2 ^ k) := Nat.xor_lt_two_pow hb1 hb2
  rw [Nat.testBit_xor,
      Nat.testBit_two_pow_mul_add a1 hb1 j,
      Nat.testBit_two_pow_mul_add a2 hb2 j,
      Nat.testBit_two_pow_mul_add (a1 ^^^ a2) hb12 j]
  split
  · exact (Nat.testBit_xor b1 b2 j).symm
  · exact (Nat.testBit_xor a1 a2 (j - 2 ^ k)).symm

theorem join_eq_nimAdd (k a b : Nat) (hb : b < M k) :
    join k a b = nimAdd (M k * a) b := by
  have h := nimAdd_join k a 0 0 b (M_pos k) hb
  simpa [join, nimAdd_zero, zero_nimAdd] using h.symm

theorem hi_nimAdd (k x y : Nat) : hi k (nimAdd x y) = nimAdd (hi k x) (hi k y) := by
  have hx := join_hi_lo k x
  have hy := join_hi_lo k y
  conv => lhs; rw [← hx, ← hy]
  rw [nimAdd_join k _ _ _ _ (lo_lt k x) (lo_lt k y)]
  exact hi_join k _ _ (nimAdd_lt_two_pow (lo_lt k x) (lo_lt k y))

theorem lo_nimAdd (k x y : Nat) : lo k (nimAdd x y) = nimAdd (lo k x) (lo k y) := by
  have hx := join_hi_lo k x
  have hy := join_hi_lo k y
  conv => lhs; rw [← hx, ← hy]
  rw [nimAdd_join k _ _ _ _ (lo_lt k x) (lo_lt k y)]
  exact lo_join k _ _ (nimAdd_lt_two_pow (lo_lt k x) (lo_lt k y))

/-! ## Section 2: Quadratic Field Tower `nimMulK` and Global Field `(Nat, nimAdd, nimMul)` -/

/--
  Inductive finite-field multiplication on `F_k = [0, M k)` (`|F_k| = 2^(2^k)`),
  realizing `F_{k+1} = F_k[α_k] / (α_k^2 + α_k + P k)` where `α_k = M k` and `P k = M k / 2`.
-/
def nimMulK : Nat → Nat → Nat → Nat
  | 0, x, y => (x % 2) * (y % 2)
  | k + 1, x, y =>
    let x1 := hi k x
    let x0 := lo k x
    let y1 := hi k y
    let y0 := lo k y
    let p11 := nimMulK k x1 y1
    let p10 := nimMulK k x1 y0
    let p01 := nimMulK k x0 y1
    let p00 := nimMulK k x0 y0
    join k (nimAdd (nimAdd p11 p10) p01) (nimAdd p00 (nimMulK k (P k) p11))

theorem nimMulK_zero_eq (x y : Nat) : nimMulK 0 x y = (x % 2) * (y % 2) := rfl

theorem nimMulK_succ_eq (k x y : Nat) :
    nimMulK (k + 1) x y =
      join k
        (nimAdd (nimAdd (nimMulK k (hi k x) (hi k y)) (nimMulK k (hi k x) (lo k y)))
                (nimMulK k (lo k x) (hi k y)))
        (nimAdd (nimMulK k (lo k x) (lo k y))
                (nimMulK k (P k) (nimMulK k (hi k x) (hi k y)))) := rfl

theorem nimMulK_lt (k x y : Nat) : nimMulK k x y < M k := by
  induction k generalizing x y with
  | zero =>
    rw [nimMulK_zero_eq]
    unfold M
    have hx : x % 2 ≤ 1 := by omega
    have hy : y % 2 ≤ 1 := by omega
    have hxy : (x % 2) * (y % 2) ≤ 1 * 1 := Nat.mul_le_mul hx hy
    omega
  | succ k ih =>
    rw [nimMulK_succ_eq]
    apply join_lt
    · exact nimAdd_lt_two_pow (nimAdd_lt_two_pow (ih _ _) (ih _ _)) (ih _ _)
    · exact nimAdd_lt_two_pow (ih _ _) (ih _ _)

theorem nimMulK_comm (k x y : Nat) : nimMulK k x y = nimMulK k y x := by
  induction k generalizing x y with
  | zero =>
    rw [nimMulK_zero_eq, nimMulK_zero_eq]
    exact Nat.mul_comm _ _
  | succ k ih =>
    rw [nimMulK_succ_eq, nimMulK_succ_eq]
    rw [ih (hi k x) (hi k y), ih (hi k x) (lo k y), ih (lo k x) (hi k y), ih (lo k x) (lo k y)]
    congr 1
    rw [nimAdd_assoc, nimAdd_comm (nimMulK k (lo k y) (hi k x)) (nimMulK k (hi k y) (lo k x)),
        ← nimAdd_assoc]

theorem nimMulK_zero_left (k y : Nat) : nimMulK k 0 y = 0 := by
  induction k generalizing y with
  | zero => simp [nimMulK_zero_eq]
  | succ k ih =>
    rw [nimMulK_succ_eq]
    have h0hi : hi k 0 = 0 := Nat.zero_div (M k)
    have h0lo : lo k 0 = 0 := Nat.zero_mod (M k)
    rw [h0hi, h0lo, ih, ih, nimMulK_comm k (P k) 0, ih]
    simp [nimAdd_zero, join]

theorem nimMulK_zero_right (k x : Nat) : nimMulK k x 0 = 0 := by
  rw [nimMulK_comm, nimMulK_zero_left]

theorem hi_of_lt (k x : Nat) (hx : x < M k) : hi k x = 0 :=
  Nat.div_eq_of_lt hx

theorem lo_of_lt (k x : Nat) (hx : x < M k) : lo k x = x :=
  Nat.mod_eq_of_lt hx

theorem nimMulK_succ_of_lt (k x y : Nat) (hx : x < M k) (hy : y < M k) :
    nimMulK (k + 1) x y = nimMulK k x y := by
  rw [nimMulK_succ_eq, hi_of_lt k x hx, lo_of_lt k x hx, hi_of_lt k y hy, lo_of_lt k y hy]
  simp [nimMulK_zero_left, nimMulK_zero_right, nimAdd_zero, zero_nimAdd, join]

theorem nimMulK_le_of_lt {k l : Nat} (hkl : k ≤ l) {x y : Nat} (hx : x < M k) (hy : y < M k) :
    nimMulK l x y = nimMulK k x y := by
  induction l with
  | zero =>
    have hk0 : k = 0 := by omega
    subst hk0
    rfl
  | succ l ih =>
    by_cases hlt : k ≤ l
    · have hMl : M k ≤ M l := M_mono hlt
      rw [nimMulK_succ_of_lt l x y (Nat.lt_of_lt_of_le hx hMl) (Nat.lt_of_lt_of_le hy hMl)]
      exact ih hlt
    · have hkeq : k = l + 1 := by omega
      subst hkeq
      rfl

theorem nimMulK_one_left (k x : Nat) (hx : x < M k) : nimMulK k 1 x = x := by
  induction k generalizing x with
  | zero =>
    rw [nimMulK_zero_eq]
    unfold M at hx
    omega
  | succ k ih =>
    have h1 : 1 < M k := one_lt_M k
    rw [nimMulK_succ_eq, hi_of_lt k 1 h1, lo_of_lt k 1 h1]
    simp [nimMulK_zero_left, nimMulK_zero_right, nimAdd_zero, zero_nimAdd,
          ih (hi k x) (hi_lt_of_lt k x hx), ih (lo k x) (lo_lt k x), join_hi_lo]

theorem nimMulK_one_right (k x : Nat) (hx : x < M k) : nimMulK k x 1 = x := by
  rw [nimMulK_comm, nimMulK_one_left k x hx]

private theorem bit_mul_xor (a b c : Nat) (ha : a < 2) :
    a * (b ^^^ c) = (a * b) ^^^ (a * c) := by
  have ha2 : a = 0 ∨ a = 1 := by omega
  rcases ha2 with rfl | rfl
  · simp
  · simp

private theorem mod2_xor (y z : Nat) : (y ^^^ z) % 2 = (y % 2) ^^^ (z % 2) :=
  lo_nimAdd 0 y z

theorem nimMulK_distrib_left (k x y z : Nat) :
    nimMulK k x (nimAdd y z) = nimAdd (nimMulK k x y) (nimMulK k x z) := by
  induction k generalizing x y z with
  | zero =>
    rw [nimMulK_zero_eq, nimMulK_zero_eq, nimMulK_zero_eq]
    unfold nimAdd
    rw [mod2_xor]
    exact bit_mul_xor (x % 2) (y % 2) (z % 2) (Nat.mod_lt x (by decide))
  | succ k ih =>
    rw [nimMulK_succ_eq, nimMulK_succ_eq, nimMulK_succ_eq]
    rw [hi_nimAdd, lo_nimAdd]
    rw [ih (hi k x) (hi k y) (hi k z),
        ih (hi k x) (lo k y) (lo k z),
        ih (lo k x) (hi k y) (hi k z),
        ih (lo k x) (lo k y) (lo k z),
        ih (P k) (nimMulK k (hi k x) (hi k y)) (nimMulK k (hi k x) (hi k z))]
    have hlo1 : nimAdd (nimMulK k (lo k x) (lo k y))
        (nimMulK k (P k) (nimMulK k (hi k x) (hi k y))) < M k :=
      nimAdd_lt_two_pow (nimMulK_lt _ _ _) (nimMulK_lt _ _ _)
    have hlo2 : nimAdd (nimMulK k (lo k x) (lo k z))
        (nimMulK k (P k) (nimMulK k (hi k x) (hi k z))) < M k :=
      nimAdd_lt_two_pow (nimMulK_lt _ _ _) (nimMulK_lt _ _ _)
    rw [nimAdd_join k _ _ _ _ hlo1 hlo2]
    congr 1
    · apply Nat.eq_of_testBit_eq
      intro i
      unfold nimAdd
      simp only [Nat.testBit_xor]
      cases (nimMulK k (hi k x) (hi k y)).testBit i <;>
      cases (nimMulK k (hi k x) (hi k z)).testBit i <;>
      cases (nimMulK k (hi k x) (lo k y)).testBit i <;>
      cases (nimMulK k (hi k x) (lo k z)).testBit i <;>
      cases (nimMulK k (lo k x) (hi k y)).testBit i <;>
      cases (nimMulK k (lo k x) (hi k z)).testBit i <;> rfl
    · exact nimAdd_four_swap _ _ _ _

theorem nimMulK_distrib_right (k x y z : Nat) :
    nimMulK k (nimAdd x y) z = nimAdd (nimMulK k x z) (nimMulK k y z) := by
  rw [nimMulK_comm k (nimAdd x y) z, nimMulK_distrib_left, nimMulK_comm k z x, nimMulK_comm k z y]

theorem nimMulK_assoc (k x y z : Nat) :
    nimMulK k (nimMulK k x y) z = nimMulK k x (nimMulK k y z) := by
  induction k generalizing x y z with
  | zero =>
    rw [nimMulK_zero_eq, nimMulK_zero_eq, nimMulK_zero_eq, nimMulK_zero_eq]
    have hxy : (x % 2) * (y % 2) < 2 := by
      have hx : x % 2 ≤ 1 := by omega
      have hy : y % 2 ≤ 1 := by omega
      have := Nat.mul_le_mul hx hy
      omega
    have hyz : (y % 2) * (z % 2) < 2 := by
      have hy : y % 2 ≤ 1 := by omega
      have hz : z % 2 ≤ 1 := by omega
      have := Nat.mul_le_mul hy hz
      omega
    rw [Nat.mod_eq_of_lt hxy, Nat.mod_eq_of_lt hyz, Nat.mul_assoc]
  | succ k ih =>
    have hhi_xy : hi k (nimMulK (k + 1) x y) =
        nimAdd (nimAdd (nimMulK k (hi k x) (hi k y)) (nimMulK k (hi k x) (lo k y)))
               (nimMulK k (lo k x) (hi k y)) := by
      rw [nimMulK_succ_eq]
      exact hi_join k _ _ (nimAdd_lt_two_pow (nimMulK_lt _ _ _) (nimMulK_lt _ _ _))
    have hlo_xy : lo k (nimMulK (k + 1) x y) =
        nimAdd (nimMulK k (lo k x) (lo k y))
               (nimMulK k (P k) (nimMulK k (hi k x) (hi k y))) := by
      rw [nimMulK_succ_eq]
      exact lo_join k _ _ (nimAdd_lt_two_pow (nimMulK_lt _ _ _) (nimMulK_lt _ _ _))
    have hhi_yz : hi k (nimMulK (k + 1) y z) =
        nimAdd (nimAdd (nimMulK k (hi k y) (hi k z)) (nimMulK k (hi k y) (lo k z)))
               (nimMulK k (lo k y) (hi k z)) := by
      rw [nimMulK_succ_eq]
      exact hi_join k _ _ (nimAdd_lt_two_pow (nimMulK_lt _ _ _) (nimMulK_lt _ _ _))
    have hlo_yz : lo k (nimMulK (k + 1) y z) =
        nimAdd (nimMulK k (lo k y) (lo k z))
               (nimMulK k (P k) (nimMulK k (hi k y) (hi k z))) := by
      rw [nimMulK_succ_eq]
      exact lo_join k _ _ (nimAdd_lt_two_pow (nimMulK_lt _ _ _) (nimMulK_lt _ _ _))
    conv => lhs; rw [nimMulK_succ_eq]
    conv => rhs; rw [nimMulK_succ_eq]
    rw [hhi_xy, hlo_xy, hhi_yz, hlo_yz]
    simp only [nimMulK_distrib_left, nimMulK_distrib_right]
    have hP1 : nimMulK k (nimMulK k (P k) (nimMulK k (hi k x) (hi k y))) (hi k z) =
        nimMulK k (P k) (nimMulK k (hi k x) (nimMulK k (hi k y) (hi k z))) := by
      rw [ih, ih]
    have hP2 : nimMulK k (nimMulK k (P k) (nimMulK k (hi k x) (hi k y))) (lo k z) =
        nimMulK k (P k) (nimMulK k (hi k x) (nimMulK k (hi k y) (lo k z))) := by
      rw [ih, ih]
    have hP3 : nimMulK k (hi k x) (nimMulK k (P k) (nimMulK k (hi k y) (hi k z))) =
        nimMulK k (P k) (nimMulK k (hi k x) (nimMulK k (hi k y) (hi k z))) := by
      rw [← ih, nimMulK_comm k (hi k x) (P k), ih]
    have hP4 : nimMulK k (lo k x) (nimMulK k (P k) (nimMulK k (hi k y) (hi k z))) =
        nimMulK k (P k) (nimMulK k (lo k x) (nimMulK k (hi k y) (hi k z))) := by
      rw [← ih, nimMulK_comm k (lo k x) (P k), ih]
    rw [hP1, hP2, hP3, hP4]
    simp only [ih]
    congr 1
    · apply Nat.eq_of_testBit_eq
      intro i
      unfold nimAdd
      simp only [Nat.testBit_xor]
      cases (nimMulK k (hi k x) (nimMulK k (hi k y) (hi k z))).testBit i <;>
      cases (nimMulK k (hi k x) (nimMulK k (hi k y) (lo k z))).testBit i <;>
      cases (nimMulK k (hi k x) (nimMulK k (lo k y) (hi k z))).testBit i <;>
      cases (nimMulK k (lo k x) (nimMulK k (hi k y) (hi k z))).testBit i <;>
      cases (nimMulK k (hi k x) (nimMulK k (lo k y) (lo k z))).testBit i <;>
      cases (nimMulK k (lo k x) (nimMulK k (hi k y) (lo k z))).testBit i <;>
      cases (nimMulK k (lo k x) (nimMulK k (lo k y) (hi k z))).testBit i <;>
      cases (nimMulK k (P k) (nimMulK k (hi k x) (nimMulK k (hi k y) (hi k z)))).testBit i <;> rfl
    · apply Nat.eq_of_testBit_eq
      intro i
      unfold nimAdd
      simp only [Nat.testBit_xor]
      cases (nimMulK k (lo k x) (nimMulK k (lo k y) (lo k z))).testBit i <;>
      cases (nimMulK k (P k) (nimMulK k (hi k x) (nimMulK k (hi k y) (hi k z)))).testBit i <;>
      cases (nimMulK k (P k) (nimMulK k (hi k x) (nimMulK k (hi k y) (lo k z)))).testBit i <;>
      cases (nimMulK k (P k) (nimMulK k (hi k x) (nimMulK k (lo k y) (hi k z)))).testBit i <;>
      cases (nimMulK k (P k) (nimMulK k (lo k x) (nimMulK k (hi k y) (hi k z)))).testBit i <;> rfl

/-- Squaring formula in `F_{k+1}`: cross terms cancel in characteristic 2. -/
theorem nimMulK_sq_succ (k x : Nat) :
    nimMulK (k + 1) x x =
      join k (nimMulK k (hi k x) (hi k x))
             (nimAdd (nimMulK k (lo k x) (lo k x))
                     (nimMulK k (P k) (nimMulK k (hi k x) (hi k x)))) := by
  rw [nimMulK_succ_eq, nimMulK_comm k (lo k x) (hi k x), nimAdd_assoc, nimAdd_self, nimAdd_zero]

/--
  Artin-Schreier bound: for every `x < M k`, `(x ⊗ x) ⊕ x < P k`.
  In particular `(x ⊗ x) ⊕ x ≠ P k`, so `T^2 + T + P k` is irreducible over `F_k`.
-/
theorem artin_schreier_lt (k x : Nat) (hx : x < M k) :
    nimAdd (nimMulK k x x) x < P k := by
  induction k generalizing x with
  | zero =>
    rw [nimMulK_zero_eq]
    unfold M P nimAdd at *
    have hcases : x = 0 ∨ x = 1 := by omega
    rcases hcases with rfl | rfl <;> decide
  | succ k ih =>
    rw [nimMulK_sq_succ]
    conv => lhs; rhs; rw [← join_hi_lo k x]
    have hlo1 : nimAdd (nimMulK k (lo k x) (lo k x))
        (nimMulK k (P k) (nimMulK k (hi k x) (hi k x))) < M k :=
      nimAdd_lt_two_pow (nimMulK_lt _ _ _) (nimMulK_lt _ _ _)
    rw [nimAdd_join k _ _ _ _ hlo1 (lo_lt k x)]
    rw [P_succ]
    have hlo2 : nimAdd (nimAdd (nimMulK k (lo k x) (lo k x))
        (nimMulK k (P k) (nimMulK k (hi k x) (hi k x)))) (lo k x) < M k :=
      nimAdd_lt_two_pow hlo1 (lo_lt k x)
    rw [join_lt_mul_iff k _ _ (P k) hlo2]
    exact ih (hi k x) (hi_lt_of_lt k x hx)

/-- Explicit multiplicative inverse in `F_k = [0, M k)` via quadratic field norm. -/
def nimInvK : Nat → Nat → Nat
  | 0, x => x % 2
  | k + 1, x =>
    let x1 := hi k x
    let x0 := lo k x
    let norm := nimAdd (nimAdd (nimMulK k x0 x0) (nimMulK k x0 x1))
                       (nimMulK k (P k) (nimMulK k x1 x1))
    let invN := nimInvK k norm
    join k (nimMulK k invN x1) (nimMulK k invN (nimAdd x0 x1))

theorem nimInvK_zero_eq (x : Nat) : nimInvK 0 x = x % 2 := rfl

theorem nimInvK_succ_eq (k x : Nat) :
    nimInvK (k + 1) x =
      let x1 := hi k x
      let x0 := lo k x
      let norm := nimAdd (nimAdd (nimMulK k x0 x0) (nimMulK k x0 x1))
                         (nimMulK k (P k) (nimMulK k x1 x1))
      let invN := nimInvK k norm
      join k (nimMulK k invN x1) (nimMulK k invN (nimAdd x0 x1)) := rfl

theorem nimInvK_lt (k x : Nat) : nimInvK k x < M k := by
  induction k generalizing x with
  | zero =>
    rw [nimInvK_zero_eq]
    unfold M
    exact Nat.mod_lt x (by decide)
  | succ k ih =>
    rw [nimInvK_succ_eq]
    exact join_lt k _ _ (nimMulK_lt _ _ _) (nimMulK_lt _ _ _)

private theorem nimMulK_mul_self_comm (k a b : Nat) :
    nimMulK k (nimMulK k a a) (nimMulK k b b) =
      nimMulK k (nimMulK k a b) (nimMulK k a b) := by
  rw [nimMulK_assoc k a a (nimMulK k b b),
      ← nimMulK_assoc k a b b,
      nimMulK_comm k a b,
      nimMulK_assoc k b a b,
      ← nimMulK_assoc k a b (nimMulK k a b),
      nimMulK_comm k a b]

private theorem norm_factor_lemma (k u x1 : Nat) :
    nimAdd (nimAdd (nimMulK k (nimMulK k u x1) (nimMulK k u x1))
                   (nimMulK k (nimMulK k u x1) x1))
           (nimMulK k (P k) (nimMulK k x1 x1)) =
      nimMulK k (nimAdd (nimAdd (nimMulK k u u) u) (P k)) (nimMulK k x1 x1) := by
  rw [nimMulK_distrib_right, nimMulK_distrib_right,
      ← nimMulK_mul_self_comm k u x1, nimMulK_assoc k u x1 x1]

theorem nimMulK_nimInvK (k x : Nat) (hpos : 0 < x) (hx : x < M k) :
    nimMulK k x (nimInvK k x) = 1 := by
  induction k generalizing x with
  | zero =>
    rw [nimInvK_zero_eq, nimMulK_zero_eq]
    unfold M at hx
    have : x = 1 := by omega
    subst this
    rfl
  | succ k ih =>
    rw [nimInvK_succ_eq]
    let x1 := hi k x
    let x0 := lo k x
    let norm := nimAdd (nimAdd (nimMulK k x0 x0) (nimMulK k x0 x1))
                       (nimMulK k (P k) (nimMulK k x1 x1))
    let invN := nimInvK k norm
    change nimMulK (k + 1) x (join k (nimMulK k invN x1) (nimMulK k invN (nimAdd x0 x1))) = 1
    have hx1_lt : x1 < M k := hi_lt_of_lt k x hx
    have hx0_lt : x0 < M k := lo_lt k x
    have hnorm_lt : norm < M k :=
      nimAdd_lt_two_pow (nimAdd_lt_two_pow (nimMulK_lt _ _ _) (nimMulK_lt _ _ _)) (nimMulK_lt _ _ _)
    have hnorm_pos : 0 < norm := by
      by_cases hx1 : x1 = 0
      · have hx0_pos : 0 < x0 := by
          have hj : M k * x1 + x0 = x := join_hi_lo k x
          rw [hx1, Nat.mul_zero, Nat.zero_add] at hj
          omega
        have hnorm_eq : norm = nimMulK k x0 x0 := by
          dsimp only [norm]
          rw [hx1, nimMulK_zero_right, nimMulK_zero_left, nimMulK_zero_right,
              nimAdd_zero, nimAdd_zero]
        rw [hnorm_eq]
        cases Nat.eq_zero_or_pos (nimMulK k x0 x0) with
        | inr hp => exact hp
        | inl hz =>
          have hinv0 := ih x0 hx0_pos hx0_lt
          have hcalc : nimMulK k (nimMulK k x0 x0) (nimMulK k (nimInvK k x0) (nimInvK k x0)) = 1 := by
            rw [nimMulK_mul_self_comm, hinv0, nimMulK_one_left k 1 (one_lt_M k)]
          rw [hz, nimMulK_zero_left] at hcalc
          cases hcalc
      · have hx1_pos : 0 < x1 := by omega
        have hinv1 := ih x1 hx1_pos hx1_lt
        let y1 := nimInvK k x1
        let u := nimMulK k x0 y1
        have hu_lt : u < M k := nimMulK_lt k x0 y1
        have hx0_eq : x0 = nimMulK k u x1 := by
          calc
            x0 = nimMulK k x0 1 := (nimMulK_one_right k x0 hx0_lt).symm
            _ = nimMulK k x0 (nimMulK k x1 y1) := by rw [hinv1]
            _ = nimMulK k u x1 := by
                dsimp only [u]
                rw [← nimMulK_assoc, nimMulK_assoc k x0 x1 y1, nimMulK_comm k x1 y1, ← nimMulK_assoc]
        have hsq_x1 : nimMulK k (nimMulK k x1 x1) (nimMulK k y1 y1) = 1 := by
          rw [nimMulK_mul_self_comm, hinv1, nimMulK_one_left k 1 (one_lt_M k)]
        have hnorm_fac : norm = nimMulK k (nimAdd (nimAdd (nimMulK k u u) u) (P k))
            (nimMulK k x1 x1) := by
          calc
            norm = nimAdd (nimAdd (nimMulK k (nimMulK k u x1) (nimMulK k u x1))
                                  (nimMulK k (nimMulK k u x1) x1))
                          (nimMulK k (P k) (nimMulK k x1 x1)) := by
              dsimp only [norm]
              rw [← hx0_eq]
            _ = nimMulK k (nimAdd (nimAdd (nimMulK k u u) u) (P k)) (nimMulK k x1 x1) :=
              norm_factor_lemma k u x1
        cases Nat.eq_zero_or_pos norm with
        | inr hp => exact hp
        | inl hz =>
          have hkill : nimAdd (nimAdd (nimMulK k u u) u) (P k) = 0 := by
            calc
              nimAdd (nimAdd (nimMulK k u u) u) (P k)
                = nimMulK k (nimAdd (nimAdd (nimMulK k u u) u) (P k)) 1 :=
                  (nimMulK_one_right k _ (nimAdd_lt_two_pow
                    (nimAdd_lt_two_pow (nimMulK_lt _ _ _) hu_lt) (P_lt_M k))).symm
              _ = nimMulK k (nimAdd (nimAdd (nimMulK k u u) u) (P k))
                    (nimMulK k (nimMulK k x1 x1) (nimMulK k y1 y1)) := by rw [hsq_x1]
              _ = nimMulK k norm (nimMulK k y1 y1) := by rw [← nimMulK_assoc, ← hnorm_fac]
              _ = 0 := by rw [hz, nimMulK_zero_left]
          have heqP : nimAdd (nimMulK k u u) u = P k := (nimAdd_eq_zero_iff _ _).mp hkill
          have has := artin_schreier_lt k u hu_lt
          omega
    have hinvN : nimMulK k invN norm = 1 := by
      rw [nimMulK_comm]
      exact ih norm hnorm_pos hnorm_lt
    rw [nimMulK_succ_eq]
    rw [hi_join k _ _ (nimMulK_lt _ _ _), lo_join k _ _ (nimMulK_lt _ _ _)]
    change join k
      (nimAdd (nimAdd (nimMulK k x1 (nimMulK k invN x1))
                      (nimMulK k x1 (nimMulK k invN (nimAdd x0 x1))))
              (nimMulK k x0 (nimMulK k invN x1)))
      (nimAdd (nimMulK k x0 (nimMulK k invN (nimAdd x0 x1)))
              (nimMulK k (P k) (nimMulK k x1 (nimMulK k invN x1)))) = 1
    have hp11 : nimMulK k x1 (nimMulK k invN x1) = nimMulK k invN (nimMulK k x1 x1) := by
      rw [← nimMulK_assoc, nimMulK_comm k x1 invN, nimMulK_assoc]
    have hp10 : nimMulK k x1 (nimMulK k invN (nimAdd x0 x1)) =
        nimAdd (nimMulK k invN (nimMulK k x0 x1)) (nimMulK k invN (nimMulK k x1 x1)) := by
      rw [← nimMulK_assoc, nimMulK_comm k x1 invN, nimMulK_assoc,
          nimMulK_distrib_left, nimMulK_distrib_left, nimMulK_comm k x1 x0]
    have hp01 : nimMulK k x0 (nimMulK k invN x1) = nimMulK k invN (nimMulK k x0 x1) := by
      rw [← nimMulK_assoc, nimMulK_comm k x0 invN, nimMulK_assoc]
    have hp00 : nimMulK k x0 (nimMulK k invN (nimAdd x0 x1)) =
        nimMulK k invN (nimAdd (nimMulK k x0 x0) (nimMulK k x0 x1)) := by
      rw [← nimMulK_assoc, nimMulK_comm k x0 invN, nimMulK_assoc, nimMulK_distrib_left]
    rw [hp11, hp10, hp01, hp00]
    have hpP : nimMulK k (P k) (nimMulK k invN (nimMulK k x1 x1)) =
        nimMulK k invN (nimMulK k (P k) (nimMulK k x1 x1)) := by
      rw [← nimMulK_assoc, nimMulK_comm k (P k) invN, nimMulK_assoc]
    rw [hpP]
    have hhi_zero : nimAdd (nimAdd (nimMulK k invN (nimMulK k x1 x1))
        (nimAdd (nimMulK k invN (nimMulK k x0 x1)) (nimMulK k invN (nimMulK k x1 x1))))
        (nimMulK k invN (nimMulK k x0 x1)) = 0 := by
      rw [nimAdd_comm (nimMulK k invN (nimMulK k x0 x1)) (nimMulK k invN (nimMulK k x1 x1)),
          nimAdd_cancel_left, nimAdd_self]
    rw [hhi_zero, ← nimMulK_distrib_left]
    change join k 0 (nimMulK k invN norm) = 1
    rw [hinvN]
    simp [join]

/-- Fast tier finder: returns a small `k` such that `n < M k`. -/
def tierLoop (n : Nat) : Nat → Nat → Nat
  | 0, k => k + 1
  | fuel + 1, k => if n < M k then k else tierLoop n fuel (k + 1)

def tier (n : Nat) : Nat := tierLoop n n 0

theorem lt_two_pow_self (n : Nat) : n < 2 ^ n := by
  induction n with
  | zero => decide
  | succ n ih =>
    rw [Nat.pow_succ]
    have : 1 ≤ 2 ^ n := two_pow_pos n
    omega

theorem le_M (k : Nat) : k < M k := by
  unfold M
  have h1 : k < 2 ^ k := lt_two_pow_self k
  have h2 : 2 ^ k < 2 ^ (2 ^ k) := lt_two_pow_self (2 ^ k)
  omega

theorem lt_M_tierLoop (n fuel k : Nat) (h : n ≤ fuel + k) :
    n < M (tierLoop n fuel k) := by
  induction fuel generalizing k with
  | zero =>
    unfold tierLoop
    have hk : k + 1 < M (k + 1) := le_M (k + 1)
    omega
  | succ fuel ih =>
    unfold tierLoop
    split
    · assumption
    · exact ih (k + 1) (by omega)

theorem lt_M_tier (n : Nat) : n < M (tier n) :=
  lt_M_tierLoop n n 0 (by omega)

/-- Global Nim-multiplication on `Nat` (`x ⊗ y`). -/
def nimMul (x y : Nat) : Nat :=
  nimMulK (Nat.max (tier x) (tier y)) x y

/-- Global Nim-multiplicative inverse on `Nat` (`0 ↦ 0`). -/
def nimInv (x : Nat) : Nat :=
  if x = 0 then 0 else nimInvK (tier x) x

theorem nimMul_eq_nimMulK (k x y : Nat) (hx : x < M k) (hy : y < M k) :
    nimMul x y = nimMulK k x y := by
  unfold nimMul
  let t := Nat.max (tier x) (tier y)
  have hxt : x < M t := Nat.lt_of_lt_of_le (lt_M_tier x) (M_mono (Nat.le_max_left _ _))
  have hyt : y < M t := Nat.lt_of_lt_of_le (lt_M_tier y) (M_mono (Nat.le_max_right _ _))
  rw [← nimMulK_le_of_lt (Nat.le_max_right k t) hxt hyt]
  exact nimMulK_le_of_lt (Nat.le_max_left k t) hx hy

theorem nimMul_comm (x y : Nat) : nimMul x y = nimMul y x := by
  let k := Nat.max (tier x) (tier y)
  have hx : x < M k := Nat.lt_of_lt_of_le (lt_M_tier x) (M_mono (Nat.le_max_left _ _))
  have hy : y < M k := Nat.lt_of_lt_of_le (lt_M_tier y) (M_mono (Nat.le_max_right _ _))
  rw [nimMul_eq_nimMulK k x y hx hy, nimMul_eq_nimMulK k y x hy hx, nimMulK_comm]

theorem nimMul_zero (x : Nat) : nimMul x 0 = 0 := by
  rw [nimMul_eq_nimMulK (tier x) x 0 (lt_M_tier x) (M_pos _), nimMulK_zero_right]

theorem zero_nimMul (x : Nat) : nimMul 0 x = 0 := by
  rw [nimMul_comm, nimMul_zero]

theorem nimMul_one (x : Nat) : nimMul x 1 = x := by
  rw [nimMul_eq_nimMulK (tier x) x 1 (lt_M_tier x) (one_lt_M _),
      nimMulK_one_right _ x (lt_M_tier x)]

theorem one_nimMul (x : Nat) : nimMul 1 x = x := by
  rw [nimMul_comm, nimMul_one]

theorem nimMul_distrib_left (x y z : Nat) :
    nimMul x (nimAdd y z) = nimAdd (nimMul x y) (nimMul x z) := by
  let k := Nat.max (tier x) (Nat.max (tier y) (tier z))
  have hx : x < M k := Nat.lt_of_lt_of_le (lt_M_tier x) (M_mono (Nat.le_max_left _ _))
  have hy : y < M k := Nat.lt_of_lt_of_le (lt_M_tier y)
    (M_mono (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _)))
  have hz : z < M k := Nat.lt_of_lt_of_le (lt_M_tier z)
    (M_mono (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _)))
  have hyz : nimAdd y z < M k := nimAdd_lt_two_pow hy hz
  rw [nimMul_eq_nimMulK k x (nimAdd y z) hx hyz,
      nimMul_eq_nimMulK k x y hx hy,
      nimMul_eq_nimMulK k x z hx hz,
      nimMulK_distrib_left]

theorem nimMul_distrib_right (x y z : Nat) :
    nimMul (nimAdd x y) z = nimAdd (nimMul x z) (nimMul y z) := by
  rw [nimMul_comm, nimMul_distrib_left, nimMul_comm z x, nimMul_comm z y]

theorem nimMul_assoc (x y z : Nat) :
    nimMul (nimMul x y) z = nimMul x (nimMul y z) := by
  let k := Nat.max (tier x) (Nat.max (tier y) (tier z))
  have hx : x < M k := Nat.lt_of_lt_of_le (lt_M_tier x) (M_mono (Nat.le_max_left _ _))
  have hy : y < M k := Nat.lt_of_lt_of_le (lt_M_tier y)
    (M_mono (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _)))
  have hz : z < M k := Nat.lt_of_lt_of_le (lt_M_tier z)
    (M_mono (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _)))
  rw [nimMul_eq_nimMulK k x y hx hy,
      nimMul_eq_nimMulK k (nimMulK k x y) z (nimMulK_lt k x y) hz,
      nimMul_eq_nimMulK k y z hy hz,
      nimMul_eq_nimMulK k x (nimMulK k y z) hx (nimMulK_lt k y z),
      nimMulK_assoc]

theorem nimMul_nimInv {x : Nat} (hx : x ≠ 0) : nimMul x (nimInv x) = 1 := by
  unfold nimInv
  rw [if_neg hx]
  rw [nimMul_eq_nimMulK (tier x) x (nimInvK (tier x) x) (lt_M_tier x) (nimInvK_lt _ _)]
  exact nimMulK_nimInvK (tier x) x (Nat.pos_of_ne_zero hx) (lt_M_tier x)

theorem nimMul_eq_zero_iff (x y : Nat) : nimMul x y = 0 ↔ x = 0 ∨ y = 0 := by
  constructor
  · intro h
    by_cases hx : x = 0
    · exact Or.inl hx
    · right
      calc
        y = nimMul 1 y := (one_nimMul y).symm
        _ = nimMul (nimMul (nimInv x) x) y := by rw [nimMul_comm (nimInv x) x, nimMul_nimInv hx]
        _ = nimMul (nimInv x) (nimMul x y) := nimMul_assoc _ _ _
        _ = 0 := by rw [h, nimMul_zero]
  · rintro (rfl | rfl)
    · exact zero_nimMul y
    · exact nimMul_zero x

/-- Subfield closure of `F_k = [0, 2^(2^k))` under Nim field operations. -/
theorem subfield_closed (k : Nat) :
    (∀ x y, x < M k → y < M k → nimAdd x y < M k) ∧
    (∀ x y, x < M k → y < M k → nimMul x y < M k) := by
  refine ⟨fun x y hx hy => nimAdd_lt_two_pow hx hy, fun x y hx hy => ?_⟩
  rw [nimMul_eq_nimMulK k x y hx hy]
  exact nimMulK_lt k x y

/-- Conway's first Fermat 2-power rule: `M k ⊗ x = M k * x` for `x < M k`. -/
theorem nimMul_fermat_lt (k x : Nat) (hx : x < M k) :
    nimMul (M k) x = M k * x := by
  have hMk_lt : M k < M (k + 1) := by
    rw [M_succ]
    have h1 := one_lt_M k
    have hp := M_pos k
    have : M k * 1 < M k * M k := Nat.mul_lt_mul_of_pos_left h1 hp
    omega
  have hx_lt : x < M (k + 1) := Nat.lt_trans hx hMk_lt
  rw [nimMul_eq_nimMulK (k + 1) (M k) x hMk_lt hx_lt, nimMulK_succ_eq]
  have hhiM : hi k (M k) = 1 := by
    have := hi_join k 1 0 (M_pos k)
    simpa [join] using this
  have hloM : lo k (M k) = 0 := by
    have := lo_join k 1 0 (M_pos k)
    simpa [join] using this
  rw [hhiM, hloM, hi_of_lt k x hx, lo_of_lt k x hx]
  simp [nimMulK_zero_left, nimMulK_zero_right, nimMulK_one_left k x hx,
        nimAdd_zero, zero_nimAdd, join]

/-- Conway's second Fermat 2-power rule: `M k ⊗ M k = M k + P k = (3/2) * M k`. -/
theorem nimMul_fermat_self (k : Nat) :
    nimMul (M k) (M k) = M k + P k := by
  have hMk_lt : M k < M (k + 1) := by
    rw [M_succ]
    have h1 := one_lt_M k
    have hp := M_pos k
    have : M k * 1 < M k * M k := Nat.mul_lt_mul_of_pos_left h1 hp
    omega
  rw [nimMul_eq_nimMulK (k + 1) (M k) (M k) hMk_lt hMk_lt, nimMulK_succ_eq]
  have hhiM : hi k (M k) = 1 := by
    have := hi_join k 1 0 (M_pos k)
    simpa [join] using this
  have hloM : lo k (M k) = 0 := by
    have := lo_join k 1 0 (M_pos k)
    simpa [join] using this
  rw [hhiM, hloM]
  simp [nimMulK_zero_left, nimMulK_zero_right, nimMulK_one_left k 1 (one_lt_M k),
        nimMulK_one_right k (P k) (P_lt_M k), nimAdd_zero, zero_nimAdd, join]

/-- Uniqueness of Nim-multiplication: any commutative ring on `(Nat, nimAdd)` satisfying
    Conway's Fermat 2-power rules coincides identically with `nimMul`. -/
theorem nimMul_unique (mul' : Nat → Nat → Nat)
    (hcomm : ∀ x y, mul' x y = mul' y x)
    (hassoc : ∀ x y z, mul' (mul' x y) z = mul' x (mul' y z))
    (hdist : ∀ x y z, mul' x (nimAdd y z) = nimAdd (mul' x y) (mul' x z))
    (hone : ∀ x, mul' 1 x = x)
    (hzero : ∀ x, mul' 0 x = 0)
    (hfermat_lt : ∀ k x, x < M k → mul' (M k) x = M k * x)
    (hfermat_self : ∀ k, mul' (M k) (M k) = M k + P k) :
    ∀ x y : Nat, mul' x y = nimMul x y := by
  have hdist_r : ∀ x y z, mul' (nimAdd x y) z = nimAdd (mul' x z) (mul' y z) := by
    intro x y z; rw [hcomm, hdist, hcomm z x, hcomm z y]
  have htier : ∀ k x y, x < M k → y < M k → mul' x y = nimMulK k x y := by
    intro k
    induction k with
    | zero =>
      intro x y hx hy
      rw [nimMulK_zero_eq]
      unfold M at hx hy
      have hx2 : x = 0 ∨ x = 1 := by omega
      have hy2 : y = 0 ∨ y = 1 := by omega
      rcases hx2 with rfl | rfl
      · simp [hzero]
      · rcases hy2 with rfl | rfl <;> simp [hone]
    | succ k ih =>
      intro x y hx hy
      have hx1 : hi k x < M k := hi_lt_of_lt k x hx
      have hx0 : lo k x < M k := lo_lt k x
      have hy1 : hi k y < M k := hi_lt_of_lt k y hy
      have hy0 : lo k y < M k := lo_lt k y
      have hx_rep : x = nimAdd (mul' (M k) (hi k x)) (lo k x) := by
        rw [hfermat_lt k (hi k x) hx1, ← join_eq_nimAdd k (hi k x) (lo k x) hx0, join_hi_lo]
      have hy_rep : y = nimAdd (mul' (M k) (hi k y)) (lo k y) := by
        rw [hfermat_lt k (hi k y) hy1, ← join_eq_nimAdd k (hi k y) (lo k y) hy0, join_hi_lo]
      conv => lhs; rw [hx_rep, hy_rep]
      rw [hdist_r, hdist, hdist]
      have hMM : mul' (mul' (M k) (hi k x)) (mul' (M k) (hi k y)) =
          nimAdd (M k * nimMulK k (hi k x) (hi k y))
                 (nimMulK k (P k) (nimMulK k (hi k x) (hi k y))) := by
        calc
          mul' (mul' (M k) (hi k x)) (mul' (M k) (hi k y))
            = mul' (mul' (M k) (M k)) (mul' (hi k x) (hi k y)) := by
              rw [hassoc, ← hassoc (hi k x) (M k) (hi k y), hcomm (hi k x) (M k), hassoc, ← hassoc]
          _ = mul' (nimAdd (M k) (P k)) (nimMulK k (hi k x) (hi k y)) := by
              rw [hfermat_self k, ih _ _ hx1 hy1]
              have hMP : M k + P k = nimAdd (M k) (P k) := by
                have := join_eq_nimAdd k 1 (P k) (P_lt_M k)
                simpa [join] using this
              rw [hMP]
          _ = nimAdd (mul' (M k) (nimMulK k (hi k x) (hi k y)))
                     (mul' (P k) (nimMulK k (hi k x) (hi k y))) := hdist_r _ _ _
          _ = nimAdd (M k * nimMulK k (hi k x) (hi k y))
                     (nimMulK k (P k) (nimMulK k (hi k x) (hi k y))) := by
              rw [hfermat_lt k _ (nimMulK_lt _ _ _), ih _ _ (P_lt_M k) (nimMulK_lt _ _ _)]
      have hM10 : mul' (mul' (M k) (hi k x)) (lo k y) = M k * nimMulK k (hi k x) (lo k y) := by
        rw [hassoc, ih _ _ hx1 hy0, hfermat_lt k _ (nimMulK_lt _ _ _)]
      have hM01 : mul' (lo k x) (mul' (M k) (hi k y)) = M k * nimMulK k (lo k x) (hi k y) := by
        rw [← hassoc, hcomm (lo k x) (M k), hassoc, ih _ _ hx0 hy1, hfermat_lt k _ (nimMulK_lt _ _ _)]
      have h00 : mul' (lo k x) (lo k y) = nimMulK k (lo k x) (lo k y) := ih _ _ hx0 hy0
      rw [hMM, hM10, hM01, h00, nimMulK_succ_eq]
      have h10_eq : M k * nimMulK k (hi k x) (lo k y) =
          join k (nimMulK k (hi k x) (lo k y)) 0 := by simp [join]
      have h01_eq : M k * nimMulK k (lo k x) (hi k y) =
          join k (nimMulK k (lo k x) (hi k y)) 0 := by simp [join]
      have h11_eq : nimAdd (M k * nimMulK k (hi k x) (hi k y))
          (nimMulK k (P k) (nimMulK k (hi k x) (hi k y))) =
          join k (nimMulK k (hi k x) (hi k y))
                 (nimMulK k (P k) (nimMulK k (hi k x) (hi k y))) :=
        (join_eq_nimAdd k _ _ (nimMulK_lt _ _ _)).symm
      have h00_eq : nimMulK k (lo k x) (lo k y) =
          join k 0 (nimMulK k (lo k x) (lo k y)) := by simp [join]
      rw [h11_eq, h10_eq, h01_eq, h00_eq]
      rw [nimAdd_join k _ _ _ _ (nimMulK_lt _ _ _) (M_pos k),
          nimAdd_join k _ _ _ _ (M_pos k) (nimMulK_lt _ _ _),
          nimAdd_join k _ _ _ _
            (nimAdd_lt_two_pow (nimMulK_lt _ _ _) (M_pos k))
            (nimAdd_lt_two_pow (M_pos k) (nimMulK_lt _ _ _))]
      simp only [nimAdd_zero, zero_nimAdd]
      congr 1
      rw [nimAdd_comm (nimMulK k (P k) (nimMulK k (hi k x) (hi k y)))]
      simp [join]
  intro x y
  let k := Nat.max (tier x) (tier y)
  have hx : x < M k := Nat.lt_of_lt_of_le (lt_M_tier x) (M_mono (Nat.le_max_left _ _))
  have hy : y < M k := Nat.lt_of_lt_of_le (lt_M_tier y) (M_mono (Nat.le_max_right _ _))
  rw [htier k x y hx hy, nimMul_eq_nimMulK k x y hx hy]

/-- Conway's `mex` exclusion property for all `x' < x` and `y' < y`. -/
theorem nimMul_mex_ne {x y x' y' : Nat} (hx : x' < x) (hy : y' < y) :
    nimAdd (nimAdd (nimMul x' y) (nimMul x y')) (nimMul x' y') ≠ nimMul x y := by
  intro heq
  have hprod : nimMul (nimAdd x x') (nimAdd y y') = 0 := by
    rw [nimMul_distrib_right, nimMul_distrib_left, nimMul_distrib_left]
    rw [← heq]
    apply Nat.eq_of_testBit_eq
    intro i
    unfold nimAdd
    simp only [Nat.testBit_xor, Nat.zero_testBit]
    cases (nimMul x y).testBit i <;> cases (nimMul x' y).testBit i <;>
    cases (nimMul x y').testBit i <;> cases (nimMul x' y').testBit i <;> rfl
  rcases (nimMul_eq_zero_iff _ _).mp hprod with hxz | hyz
  · have := (nimAdd_eq_zero_iff x x').mp hxz
    omega
  · have := (nimAdd_eq_zero_iff y y').mp hyz
    omega

/-! ## Section 3: Frobenius Automorphism `nimSq`, Explicit `nimSqrt`, and Dyadic Bijection -/

/-- The nim-square sequence `s(x) = x ⊗ x`. -/
def nimSq (x : Nat) : Nat := nimMul x x

theorem nimSq_eq_nimMulK (k x : Nat) (hx : x < M k) :
    nimSq x = nimMulK k x x :=
  nimMul_eq_nimMulK k x x hx hx

theorem nimSq_zero : nimSq 0 = 0 := nimMul_zero 0
theorem nimSq_one : nimSq 1 = 1 := nimMul_one 1

/-- Frobenius additivity in characteristic 2: `(x ⊕ y) ⊗ (x ⊕ y) = (x ⊗ x) ⊕ (y ⊗ y)`. -/
theorem nimSq_nimAdd (x y : Nat) : nimSq (nimAdd x y) = nimAdd (nimSq x) (nimSq y) := by
  unfold nimSq
  rw [nimMul_distrib_right, nimMul_distrib_left, nimMul_distrib_left, nimMul_comm y x]
  apply Nat.eq_of_testBit_eq
  intro i
  unfold nimAdd
  simp only [Nat.testBit_xor]
  cases (nimMul x x).testBit i <;> cases (nimMul x y).testBit i <;>
  cases (nimMul y y).testBit i <;> rfl

/-- Frobenius multiplicativity: `(x ⊗ y) ⊗ (x ⊗ y) = (x ⊗ x) ⊗ (y ⊗ y)`. -/
theorem nimSq_nimMul (x y : Nat) : nimSq (nimMul x y) = nimMul (nimSq x) (nimSq y) := by
  unfold nimSq
  rw [nimMul_assoc, ← nimMul_assoc y x y, nimMul_comm y x, nimMul_assoc, ← nimMul_assoc]

/-- Frobenius injectivity on `Nat`: `x ⊗ x = y ⊗ y → x = y`. -/
theorem nimSq_injective {x y : Nat} (h : nimSq x = nimSq y) : x = y := by
  have hdiff : nimSq (nimAdd x y) = 0 := by
    rw [nimSq_nimAdd, h, nimAdd_self]
  have hz : nimAdd x y = 0 := by
    rcases (nimMul_eq_zero_iff _ _).mp hdiff with h0 | h0 <;> exact h0
  exact (nimAdd_eq_zero_iff x y).mp hz

/-- Constructive inverse Frobenius map `nimSqrtK` on `F_k = [0, M k)`. -/
def nimSqrtK : Nat → Nat → Nat
  | 0, y => y % 2
  | k + 1, y =>
    let y1 := hi k y
    let y0 := lo k y
    join k (nimSqrtK k y1) (nimSqrtK k (nimAdd y0 (nimMulK k (P k) y1)))

theorem nimSqrtK_zero_eq (y : Nat) : nimSqrtK 0 y = y % 2 := rfl

theorem nimSqrtK_succ_eq (k y : Nat) :
    nimSqrtK (k + 1) y =
      join k (nimSqrtK k (hi k y))
             (nimSqrtK k (nimAdd (lo k y) (nimMulK k (P k) (hi k y)))) := rfl

theorem nimSqrtK_lt (k y : Nat) : nimSqrtK k y < M k := by
  induction k generalizing y with
  | zero =>
    rw [nimSqrtK_zero_eq]
    unfold M
    exact Nat.mod_lt y (by decide)
  | succ k ih =>
    rw [nimSqrtK_succ_eq]
    exact join_lt k _ _ (ih _) (ih _)

theorem nimSqK_nimSqrtK (k y : Nat) (hy : y < M k) :
    nimMulK k (nimSqrtK k y) (nimSqrtK k y) = y := by
  induction k generalizing y with
  | zero =>
    rw [nimSqrtK_zero_eq, nimMulK_zero_eq]
    unfold M at hy
    have hcases : y = 0 ∨ y = 1 := by omega
    rcases hcases with rfl | rfl <;> rfl
  | succ k ih =>
    rw [nimSqrtK_succ_eq, nimMulK_sq_succ]
    rw [hi_join k _ _ (nimSqrtK_lt _ _), lo_join k _ _ (nimSqrtK_lt _ _)]
    have hy1 : hi k y < M k := hi_lt_of_lt k y hy
    have hy0P : nimAdd (lo k y) (nimMulK k (P k) (hi k y)) < M k :=
      nimAdd_lt_two_pow (lo_lt k y) (nimMulK_lt _ _ _)
    rw [ih (hi k y) hy1, ih _ hy0P, nimAdd_cancel_right, join_hi_lo]

theorem nimSqrtK_nimSqK (k x : Nat) (hx : x < M k) :
    nimSqrtK k (nimMulK k x x) = x := by
  have hsq := nimSqK_nimSqrtK k (nimMulK k x x) (nimMulK_lt k x x)
  have heq : nimSq (nimSqrtK k (nimMulK k x x)) = nimSq x := by
    rw [nimSq_eq_nimMulK k _ (nimSqrtK_lt _ _), nimSq_eq_nimMulK k x hx, hsq]
  exact nimSq_injective heq

/-- Global constructive Nim square root on `Nat`. -/
def nimSqrt (y : Nat) : Nat := nimSqrtK (tier y) y

theorem nimSq_nimSqrt (y : Nat) : nimSq (nimSqrt y) = y := by
  unfold nimSqrt
  rw [nimSq_eq_nimMulK (tier y) _ (nimSqrtK_lt _ _)]
  exact nimSqK_nimSqrtK (tier y) y (lt_M_tier y)

theorem nimSqrt_nimSq (x : Nat) : nimSqrt (nimSq x) = x := by
  apply nimSq_injective
  exact nimSq_nimSqrt (nimSq x)

/-- Every natural number is the Nim-square of a unique natural number. -/
theorem existsUnique_nimSq (n : Nat) :
    ∃ x : Nat, nimSq x = n ∧ ∀ z : Nat, nimSq z = n → z = x :=
  ⟨nimSqrt n, nimSq_nimSqrt n, fun _ hz => by rw [← hz, nimSqrt_nimSq]⟩

/-- Helper for base-`M k` small bound `B ≤ M k`. -/
private theorem join_lt_small_iff (k a b B : Nat) (hB : B ≤ M k) :
    join k a b < B ↔ a = 0 ∧ b < B := by
  unfold join
  constructor
  · intro h
    cases Nat.eq_zero_or_pos a with
    | inl ha0 =>
      subst ha0
      exact ⟨rfl, by omega⟩
    | inr hapos =>
      have hm : M k * 1 ≤ M k * a := Nat.mul_le_mul_left (M k) hapos
      omega
  · rintro ⟨rfl, hb⟩
    omega

/--
  Key Structural Lemma: Nim-squaring preserves EVERY dyadic threshold `2 ^ d`,
  not merely Fermat 2-power thresholds `2^(2^k)`.
-/
theorem nimMulK_sq_lt_two_pow_iff (k d x : Nat) (hd : d ≤ 2 ^ k) (hx : x < M k) :
    nimMulK k x x < 2 ^ d ↔ x < 2 ^ d := by
  induction k generalizing d x with
  | zero =>
    rw [nimMulK_zero_eq]
    unfold M at hx
    have hx2 : x = 0 ∨ x = 1 := by omega
    have hd2 : d = 0 ∨ d = 1 := by omega
    rcases hx2 with rfl | rfl
    · rcases hd2 with rfl | rfl <;> decide
    · rcases hd2 with rfl | rfl <;> decide
  | succ k ih =>
    by_cases hd_le : d ≤ 2 ^ k
    · have h2d_le : 2 ^ d ≤ M k := by
        unfold M
        exact Nat.pow_le_pow_right (by decide) hd_le
      have hx_split : x < 2 ^ d ↔ hi k x = 0 ∧ lo k x < 2 ^ d := by
        conv => lhs; rw [← join_hi_lo k x]
        exact join_lt_small_iff k (hi k x) (lo k x) (2 ^ d) h2d_le
      rw [nimMulK_sq_succ, hx_split,
          join_lt_small_iff k (nimMulK k (hi k x) (hi k x)) _ (2 ^ d) h2d_le]
      have hs1_zero_iff : nimMulK k (hi k x) (hi k x) = 0 ↔ hi k x = 0 := by
        rw [← nimSq_eq_nimMulK k (hi k x) (hi_lt_of_lt k x hx)]
        constructor
        · intro hz
          exact nimSq_injective (by rw [hz, nimSq_zero])
        · intro h0
          rw [h0, nimSq_zero]
      constructor
      · rintro ⟨hs0, hlow⟩
        have hhi0 : hi k x = 0 := hs1_zero_iff.mp hs0
        rw [hs0, nimMulK_zero_right, nimAdd_zero, ih d (lo k x) hd_le (lo_lt k x)] at hlow
        exact ⟨hhi0, hlow⟩
      · rintro ⟨hhi0, hlo⟩
        have hs0 : nimMulK k (hi k x) (hi k x) = 0 := hs1_zero_iff.mpr hhi0
        refine ⟨hs0, ?_⟩
        rw [hs0, nimMulK_zero_right, nimAdd_zero]
        exact (ih d (lo k x) hd_le (lo_lt k x)).mpr hlo
    · have hd_decomp : ∃ e, e ≤ 2 ^ k ∧ d = 2 ^ k + e := by
        refine ⟨d - 2 ^ k, ?_, by omega⟩
        have hsucc : 2 ^ (k + 1) = 2 ^ k + 2 ^ k := by
          rw [Nat.pow_succ]
          omega
        omega
      rcases hd_decomp with ⟨e, he_le, rfl⟩
      have hpow : 2 ^ (2 ^ k + e) = M k * 2 ^ e := by
        rw [pow_add_eq]
        rfl
      rw [hpow, nimMulK_sq_succ]
      have hlow_lt : nimAdd (nimMulK k (lo k x) (lo k x))
          (nimMulK k (P k) (nimMulK k (hi k x) (hi k x))) < M k :=
        nimAdd_lt_two_pow (nimMulK_lt _ _ _) (nimMulK_lt _ _ _)
      rw [join_lt_mul_iff k _ _ (2 ^ e) hlow_lt]
      conv => rhs; lhs; rw [← join_hi_lo k x]
      rw [join_lt_mul_iff k (hi k x) (lo k x) (2 ^ e) (lo_lt k x)]
      exact ih e (hi k x) he_le (hi_lt_of_lt k x hx)

theorem nimSq_lt_two_pow_iff (d x : Nat) :
    nimSq x < 2 ^ d ↔ x < 2 ^ d := by
  let k := Nat.max (tier x) d
  have hx : x < M k := Nat.lt_of_lt_of_le (lt_M_tier x) (M_mono (Nat.le_max_left _ _))
  have hd : d ≤ 2 ^ k := by
    have h1 : d ≤ k := Nat.le_max_right _ _
    have h2 : k ≤ 2 ^ k := Nat.le_of_lt (lt_two_pow_self k)
    omega
  rw [nimSq_eq_nimMulK k x hx]
  exact nimMulK_sq_lt_two_pow_iff k d x hd hx

theorem nimSqrt_lt_two_pow_iff (d y : Nat) :
    nimSqrt y < 2 ^ d ↔ y < 2 ^ d := by
  conv => rhs; rw [← nimSq_nimSqrt y]
  exact (nimSq_lt_two_pow_iff d (nimSqrt y)).symm

/-! ## Section 4: Bijection Counting, Interpretation A, and Interpretation B -/

/-- Self-contained duplicate-free list predicate on `Nat`. -/
inductive NoDup : List Nat → Prop where
  | nil : NoDup []
  | cons {a : Nat} {l : List Nat} : a ∉ l → NoDup l → NoDup (a :: l)

theorem noDup_append {l1 l2 : List Nat} (h1 : NoDup l1) (h2 : NoDup l2)
    (hdisj : ∀ x, x ∈ l1 → x ∉ l2) : NoDup (l1 ++ l2) := by
  induction h1 with
  | nil => exact h2
  | @cons a as hnot _ ih =>
    simp only [List.cons_append]
    apply NoDup.cons
    · intro hmem
      rcases List.mem_append.mp hmem with hmas | hml2
      · exact hnot hmas
      · exact hdisj a List.mem_cons_self hml2
    · exact ih (fun x hx => hdisj x (List.mem_cons_of_mem a hx))

theorem noDup_range (n : Nat) : NoDup (List.range n) := by
  induction n with
  | zero => exact NoDup.nil
  | succ n ih =>
    rw [List.range_succ]
    apply noDup_append ih (NoDup.cons (by simp) NoDup.nil)
    intro x hx hmem
    rw [List.mem_range] at hx
    simp at hmem
    omega

theorem noDup_filter (p : Nat → Bool) {l : List Nat} (h : NoDup l) :
    NoDup (l.filter p) := by
  induction h with
  | nil => exact NoDup.nil
  | @cons a as hnot _ ih =>
    unfold List.filter
    split
    · apply NoDup.cons
      · intro hmem
        rw [List.mem_filter] at hmem
        exact hnot hmem.1
      · exact ih
    · exact ih

theorem noDup_map_on (f : Nat → Nat) {l : List Nat} (h : NoDup l)
    (hinj : ∀ x y, x ∈ l → y ∈ l → f x = f y → x = y) :
    NoDup (l.map f) := by
  induction h with
  | nil => exact NoDup.nil
  | @cons a as hnot _ ih =>
    simp only [List.map]
    apply NoDup.cons
    · intro hmem
      rw [List.mem_map] at hmem
      rcases hmem with ⟨b, hb_mem, hfb⟩
      have hab : a = b := hinj a b List.mem_cons_self (List.mem_cons_of_mem a hb_mem) hfb.symm
      subst hab
      exact hnot hb_mem
    · exact ih (fun x y hx hy hf =>
        hinj x y (List.mem_cons_of_mem a hx) (List.mem_cons_of_mem a hy) hf)

theorem mem_erase_of_ne {a b : Nat} {l : List Nat} (hne : a ≠ b) :
    a ∈ l.erase b ↔ a ∈ l := by
  induction l with
  | nil => simp [List.erase]
  | cons c cs ih =>
    unfold List.erase
    by_cases hcb : (c == b) = true
    · simp only [hcb]
      have hceq : c = b := beq_iff_eq.mp hcb
      subst hceq
      constructor
      · intro h; exact List.mem_cons_of_mem c h
      · intro h
        rcases List.mem_cons.mp h with rfl | hcs
        · exact absurd rfl hne
        · exact hcs
    · have hcbf : (c == b) = false := Bool.eq_false_iff.mpr hcb
      simp only [hcbf, List.mem_cons, ih]

theorem not_mem_erase_of_noDup {a : Nat} {l : List Nat} (h : NoDup l) :
    a ∉ l.erase a := by
  induction h with
  | nil => simp [List.erase]
  | @cons c cs hnot _ ih =>
    unfold List.erase
    by_cases hca : (c == a) = true
    · simp only [hca]
      have hceq : c = a := beq_iff_eq.mp hca
      subst hceq
      exact hnot
    · have hcaf : (c == a) = false := Bool.eq_false_iff.mpr hca
      simp only [hcaf, List.mem_cons]
      rintro (rfl | hmem)
      · simp at hcaf
      · exact ih hmem

theorem noDup_erase (a : Nat) {l : List Nat} (h : NoDup l) :
    NoDup (l.erase a) := by
  induction h with
  | nil => exact NoDup.nil
  | @cons c cs hnot hnodup ih =>
    unfold List.erase
    by_cases hca : (c == a) = true
    · simp only [hca]
      exact hnodup
    · have hcaf : (c == a) = false := Bool.eq_false_iff.mpr hca
      simp only [hcaf]
      apply NoDup.cons
      · intro hx
        have hca_ne : c ≠ a := fun heq => by subst heq; simp at hcaf
        exact hnot ((mem_erase_of_ne hca_ne).mp hx)
      · exact ih

theorem length_erase_of_mem {a : Nat} {l : List Nat} (h : a ∈ l) :
    (l.erase a).length + 1 = l.length := by
  induction l with
  | nil => cases h
  | cons c cs ih =>
    unfold List.erase
    by_cases hca : (c == a) = true
    · simp [hca]
    · have hcaf : (c == a) = false := Bool.eq_false_iff.mpr hca
      simp only [hcaf, List.length_cons]
      rcases List.mem_cons.mp h with rfl | hcs
      · simp at hcaf
      · have := ih hcs
        omega

theorem noDup_length_eq_of_mem_iff {l1 l2 : List Nat}
    (h1 : NoDup l1) (h2 : NoDup l2) (hiff : ∀ x, x ∈ l1 ↔ x ∈ l2) :
    l1.length = l2.length := by
  induction h1 generalizing l2 with
  | nil =>
    cases l2 with
    | nil => rfl
    | cons b bs =>
      have := (hiff b).mpr List.mem_cons_self
      cases this
  | @cons a as hnot _ ih =>
    have ha2 : a ∈ l2 := (hiff a).mp List.mem_cons_self
    have hlen2 := length_erase_of_mem ha2
    have heq_as : as.length = (l2.erase a).length := by
      apply ih (noDup_erase a h2)
      intro x
      by_cases hxa : x = a
      · subst hxa
        constructor
        · intro hx; exact absurd hx hnot
        · intro hx; exact absurd hx (not_mem_erase_of_noDup h2)
      · rw [mem_erase_of_ne hxa]
        constructor
        · intro hx; exact (hiff x).mp (List.mem_cons_of_mem a hx)
        · intro hx
          rcases List.mem_cons.mp ((hiff x).mpr hx) with rfl | hmem
          · exact absurd rfl hxa
          · exact hmem
    simp only [List.length_cons]
    omega

/-- Cardinality invariance under a bijection `(f, g)` on `[0, B)`. -/
theorem filter_range_bij_length (B : Nat) (f g : Nat → Nat) (p : Nat → Bool)
    (hf : ∀ x, x < B → f x < B)
    (hg : ∀ y, y < B → g y < B)
    (hgf : ∀ x, x < B → g (f x) = x)
    (hfg : ∀ y, y < B → f (g y) = y) :
    ((List.range B).filter (fun x => p (f x))).length =
      ((List.range B).filter p).length := by
  let L1 := (List.range B).filter (fun x => p (f x))
  let L2 := (List.range B).filter p
  have hmap_len : (L1.map f).length = L1.length := List.length_map f
  change L1.length = L2.length
  rw [← hmap_len]
  apply noDup_length_eq_of_mem_iff
  · apply noDup_map_on f (noDup_filter _ (noDup_range B))
    intro x y hx hy heq
    rw [List.mem_filter, List.mem_range] at hx hy
    calc
      x = g (f x) := (hgf x hx.1).symm
      _ = g (f y) := by rw [heq]
      _ = y := hgf y hy.1
  · exact noDup_filter _ (noDup_range B)
  · intro y
    rw [List.mem_map, List.mem_filter, List.mem_range]
    constructor
    · rintro ⟨x, hx, rfl⟩
      rw [List.mem_filter, List.mem_range] at hx
      exact ⟨hf x hx.1, hx.2⟩
    · rintro ⟨hyB, hpy⟩
      refine ⟨g y, ?_, hfg y hyB⟩
      rw [List.mem_filter, List.mem_range, hfg y hyB]
      exact ⟨hg y hyB, hpy⟩

theorem filter_range_mono (p : Nat → Bool) {A B : Nat} (hAB : A ≤ B) :
    ((List.range A).filter p).length ≤ ((List.range B).filter p).length := by
  obtain ⟨k, rfl⟩ : ∃ k, B = A + k := ⟨B - A, by omega⟩
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Nat.add_succ, List.range_succ, List.filter_append, List.length_append]
    omega

/-! ### Interpretation A: Nim-Squares `{x ⊗ x : x ∈ Nat}` in `Nat` -/

/-- Predicate that `n` is a nim-square (`n = x ⊗ x` for some `x : Nat`). -/
def IsNimSquare (n : Nat) : Prop := ∃ x : Nat, nimSq x = n

/-- Computable boolean test for `IsNimSquare`. -/
def isNimSquareBool (n : Nat) : Bool := nimSq (nimSqrt n) == n

theorem isNimSquareBool_eq_true (n : Nat) : isNimSquareBool n = true := by
  unfold isNimSquareBool
  exact beq_iff_eq.mpr (nimSq_nimSqrt n)

theorem isNimSquareBool_iff (n : Nat) : isNimSquareBool n = true ↔ IsNimSquare n := by
  constructor
  · intro _
    exact ⟨nimSqrt n, nimSq_nimSqrt n⟩
  · intro _
    exact isNimSquareBool_eq_true n

/-- Every natural number is a nim-square. -/
theorem every_nat_is_nimSquare (n : Nat) : IsNimSquare n :=
  ⟨nimSqrt n, nimSq_nimSqrt n⟩

/-- Counting function of nim-square values in `[0, N)`. -/
def nimSquareCount (N : Nat) : Nat :=
  ((List.range N).filter isNimSquareBool).length

/--
  **Interpretation A (Main Theorem 1):**
  For every `N`, 100% of integers in `[0, N)` are nim-squares: `nimSquareCount N = N`.
  Thus the asymptotic density of nim-squares in `Nat` is identically `1` (not `0`).
-/
theorem interpretationA_nimSquare_density_one (N : Nat) :
    nimSquareCount N = N := by
  unfold nimSquareCount
  have h : (List.range N).filter isNimSquareBool = List.range N := by
    induction N with
    | zero => rfl
    | succ n ih =>
      rw [List.range_succ, List.filter_append, ih]
      simp [List.filter, isNimSquareBool_eq_true]
  rw [h, List.length_range]

/-- Restricted-witness nim-square count: `|{y < N : ∃ x < N, x ⊗ x = y}|`. -/
def restrictedNimSquareCount (N : Nat) : Nat :=
  ((List.range N).filter (fun y => decide (nimSqrt y < N))).length

theorem exists_lt_nimSq_iff (N y : Nat) :
    (∃ x, x < N ∧ nimSq x = y) ↔ nimSqrt y < N := by
  constructor
  · rintro ⟨x, hxN, rfl⟩
    rw [nimSqrt_nimSq]
    exact hxN
  · intro h
    exact ⟨nimSqrt y, h, nimSq_nimSqrt y⟩

/-- Binary logarithm `ilog2 N = ⌊log_2 N⌋` for `N ≥ 1`. -/
def ilog2Aux : Nat → Nat → Nat
  | 0, _ => 0
  | fuel + 1, n => if n < 2 then 0 else ilog2Aux fuel (n / 2) + 1

def ilog2 (n : Nat) : Nat := ilog2Aux n n

theorem ilog2Aux_spec (fuel n : Nat) (hpos : 0 < n) (hfuel : n ≤ fuel) :
    2 ^ (ilog2Aux fuel n) ≤ n ∧ n < 2 ^ (ilog2Aux fuel n + 1) := by
  induction fuel generalizing n with
  | zero => omega
  | succ fuel ih =>
    unfold ilog2Aux
    by_cases hlt2 : n < 2
    · rw [if_pos hlt2]
      have : n = 1 := by omega
      subst this
      decide
    · rw [if_neg hlt2]
      have hn2_pos : 0 < n / 2 := by omega
      have hn2_le : n / 2 ≤ fuel := by omega
      rcases ih (n / 2) hn2_pos hn2_le with ⟨hlo, hhi⟩
      rw [Nat.pow_succ, Nat.pow_succ]
      omega

theorem ilog2_spec {n : Nat} (hpos : 0 < n) :
    2 ^ (ilog2 n) ≤ n ∧ n < 2 ^ (ilog2 n + 1) :=
  ilog2Aux_spec n n hpos (Nat.le_refl n)

/--
  **Interpretation A (Main Theorem 2 — Restricted Witnesses `x < N`):**
  At every dyadic horizon `N = 2^d`, 100% of `y < N` have `x < N` with `x ⊗ x = y`;
  and for EVERY `N ≥ 1`, strictly more than half of `y < N` satisfy `∃ x < N, x ⊗ x = y`.
-/
theorem interpretationA_restricted_nimSquare_bounds :
    (∀ d : Nat, restrictedNimSquareCount (2 ^ d) = 2 ^ d) ∧
    (∀ N : Nat, 1 ≤ N → N < 2 * restrictedNimSquareCount N) := by
  have hpow : ∀ d : Nat, restrictedNimSquareCount (2 ^ d) = 2 ^ d := by
    intro d
    unfold restrictedNimSquareCount
    have h : ∀ y ∈ List.range (2 ^ d), decide (nimSqrt y < 2 ^ d) = true := by
      intro y hy
      rw [List.mem_range] at hy
      simp [nimSqrt_lt_two_pow_iff, hy]
    have hfilt : ∀ l : List Nat, (∀ y ∈ l, decide (nimSqrt y < 2 ^ d) = true) →
        (l.filter (fun y => decide (nimSqrt y < 2 ^ d))) = l := by
      intro l hl
      induction l with
      | nil => rfl
      | cons a as ihl =>
        have ha := hl a List.mem_cons_self
        simp [List.filter, ha, ihl (fun y hy => hl y (List.mem_cons_of_mem a hy))]
    rw [hfilt _ h, List.length_range]
  refine ⟨hpow, fun N hN => ?_⟩
  rcases ilog2_spec hN with ⟨hlo, hhi⟩
  let d := ilog2 N
  have hsub : 2 ^ d ≤ restrictedNimSquareCount N := by
    calc
      2 ^ d = restrictedNimSquareCount (2 ^ d) := (hpow d).symm
      _ = ((List.range (2 ^ d)).filter (fun y => decide (nimSqrt y < 2 ^ d))).length := rfl
      _ ≤ ((List.range (2 ^ d)).filter (fun y => decide (nimSqrt y < N))).length := by
        have h_imp : ∀ l : List Nat,
            (l.filter (fun y => decide (nimSqrt y < 2 ^ d))).length ≤
            (l.filter (fun y => decide (nimSqrt y < N))).length := by
          intro l
          induction l with
          | nil => simp
          | cons a as ihl =>
            unfold List.filter
            by_cases ha : nimSqrt a < 2 ^ d
            · have haN : nimSqrt a < N := Nat.lt_of_lt_of_le ha hlo
              simp [ha, haN, List.length_cons]
              omega
            · simp [ha]
              by_cases ha2 : nimSqrt a < N
              · simp [ha2, List.length_cons]; omega
              · simp [ha2]; omega
        exact h_imp (List.range (2 ^ d))
      _ ≤ restrictedNimSquareCount N := filter_range_mono _ hlo
  change N < 2 * restrictedNimSquareCount N
  have hhi' : N < 2 ^ d * 2 := by
    rw [← Nat.pow_succ]
    exact hhi
  omega

/-! ### Interpretation B: Ordinary Perfect Squares `m^2` in the Nim-Square Sequence `s(x) = x ⊗ x` -/

/-- Verified logarithmic-time integer square root `isqrt n = ⌊√n⌋`. -/
def isqrtAux : Nat → Nat → Nat
  | 0, _ => 0
  | fuel + 1, n =>
    if n == 0 then 0
    else
      let r := isqrtAux fuel (n / 4)
      let cand := 2 * r + 1
      if cand * cand ≤ n then cand else 2 * r

def isqrt (n : Nat) : Nat := isqrtAux n n

theorem isqrtAux_spec (fuel n : Nat) (hfuel : n ≤ fuel) :
    isqrtAux fuel n * isqrtAux fuel n ≤ n ∧
      n < (isqrtAux fuel n + 1) * (isqrtAux fuel n + 1) := by
  induction fuel generalizing n with
  | zero =>
    have : n = 0 := by omega
    subst this
    decide
  | succ fuel ih =>
    cases n with
    | zero =>
      simp [isqrtAux]
    | succ m =>
      have hdiv_le : (m + 1) / 4 ≤ fuel := by omega
      rcases ih ((m + 1) / 4) hdiv_le with ⟨hlo, hhi⟩
      let r := isqrtAux fuel ((m + 1) / 4)
      have hr_lo : r * r ≤ (m + 1) / 4 := hlo
      have hr_hi : (m + 1) / 4 < (r + 1) * (r + 1) := hhi
      have h2r_sq : (2 * r) * (2 * r) = 4 * (r * r) := by
        calc
          (2 * r) * (2 * r) = 2 * 2 * (r * r) := by
            rw [Nat.mul_assoc, Nat.mul_left_comm r 2 r, ← Nat.mul_assoc]
          _ = 4 * (r * r) := rfl
      have h2r2_sq : (2 * r + 1 + 1) * (2 * r + 1 + 1) = 4 * ((r + 1) * (r + 1)) := by
        have h1 : 2 * r + 1 + 1 = 2 * (r + 1) := by omega
        rw [h1]
        calc
          (2 * (r + 1)) * (2 * (r + 1)) = 2 * 2 * ((r + 1) * (r + 1)) := by
            rw [Nat.mul_assoc, Nat.mul_left_comm (r + 1) 2 (r + 1), ← Nat.mul_assoc]
          _ = 4 * ((r + 1) * (r + 1)) := rfl
      have hexp : isqrtAux (fuel + 1) (m + 1) =
          if (2 * r + 1) * (2 * r + 1) ≤ m + 1 then 2 * r + 1 else 2 * r := rfl
      rw [hexp]
      by_cases hcand : (2 * r + 1) * (2 * r + 1) ≤ m + 1
      · rw [if_pos hcand]
        exact ⟨hcand, by omega⟩
      · rw [if_neg hcand]
        exact ⟨by omega, by omega⟩

theorem isqrt_spec (n : Nat) :
    isqrt n * isqrt n ≤ n ∧ n < (isqrt n + 1) * (isqrt n + 1) :=
  isqrtAux_spec n n (Nat.le_refl n)

/-- Ordinary perfect square predicate `∃ m : Nat, m * m = n`. -/
def IsOrdSquare (n : Nat) : Prop := ∃ m : Nat, m * m = n

/-- Computable boolean test for ordinary integer squares. -/
def isOrdSquareBool (n : Nat) : Bool := isqrt n * isqrt n == n

theorem mul_self_strict_mono {a b : Nat} (h : a < b) : a * a < b * b := by
  have h1 : a * a ≤ a * b := Nat.mul_le_mul_left a (Nat.le_of_lt h)
  have h2 : a * b < b * b := Nat.mul_lt_mul_of_pos_right h (by omega)
  omega

theorem mul_self_mono {a b : Nat} (h : a ≤ b) : a * a ≤ b * b := by
  rcases Nat.eq_or_lt_of_le h with rfl | hlt
  · exact Nat.le_refl _
  · exact Nat.le_of_lt (mul_self_strict_mono hlt)

theorem isOrdSquareBool_iff (n : Nat) : isOrdSquareBool n = true ↔ IsOrdSquare n := by
  unfold isOrdSquareBool IsOrdSquare
  rw [beq_iff_eq]
  constructor
  · intro h
    exact ⟨isqrt n, h⟩
  · rintro ⟨m, rfl⟩
    rcases isqrt_spec (m * m) with ⟨hlo, hhi⟩
    have htrich : isqrt (m * m) < m ∨ m < isqrt (m * m) ∨ isqrt (m * m) = m := by omega
    rcases htrich with hlt | hgt | heq
    · have hle1 : isqrt (m * m) + 1 ≤ m := by omega
      have hsq := mul_self_mono hle1
      omega
    · have hsq := mul_self_strict_mono hgt
      omega
    · rw [heq]

/-- Count of ordinary perfect squares in `[0, N)`. -/
def ordSquareCount (N : Nat) : Nat :=
  ((List.range N).filter isOrdSquareBool).length

/--
  Count of indices `0 ≤ x < N` for which the nim-square `s(x) = x ⊗ x`
  is an ordinary perfect square `m^2`.
-/
def nimSeqOrdSquareCount (N : Nat) : Nat :=
  ((List.range N).filter (fun x => isOrdSquareBool (nimSq x))).length

/-- Ceiling square root `⌈√N⌉` (`0` at `0`, `⌊√(N-1)⌋ + 1` for `N ≥ 1`). -/
def ceilSqrt (N : Nat) : Nat :=
  if N = 0 then 0 else isqrt (N - 1) + 1

theorem ordSquareCount_eq_ceilSqrt (N : Nat) :
    ordSquareCount N = ceilSqrt N := by
  unfold ordSquareCount ceilSqrt
  by_cases hN0 : N = 0
  · subst hN0
    rfl
  · rw [if_neg hN0]
    let R := isqrt (N - 1) + 1
    have hmap_len : ((List.range R).map (fun m => m * m)).length = R := by
      rw [List.length_map, List.length_range]
    change ((List.range N).filter isOrdSquareBool).length = R
    rw [← hmap_len]
    apply noDup_length_eq_of_mem_iff
    · exact noDup_filter _ (noDup_range N)
    · apply noDup_map_on (fun m => m * m) (noDup_range R)
      intro x y _ _ heq
      have htrich : x < y ∨ y < x ∨ x = y := by omega
      rcases htrich with hlt | hgt | h
      · have := mul_self_strict_mono hlt; omega
      · have := mul_self_strict_mono hgt; omega
      · exact h
    · intro y
      rw [List.mem_filter, List.mem_range, List.mem_map]
      rcases isqrt_spec (N - 1) with ⟨hlo, hhi⟩
      constructor
      · rintro ⟨hyN, hsq⟩
        rcases (isOrdSquareBool_iff y).mp hsq with ⟨m, rfl⟩
        refine ⟨m, ?_, rfl⟩
        rw [List.mem_range]
        cases Nat.lt_or_ge m R with
        | inl hlt => exact hlt
        | inr hge =>
          have hsq_le : R * R ≤ m * m := mul_self_mono hge
          dsimp only [R] at hsq_le
          omega
      · rintro ⟨m, hmR, rfl⟩
        rw [List.mem_range] at hmR
        dsimp only [R] at hmR
        have hm_le : m ≤ isqrt (N - 1) := by omega
        have hsq_le : m * m ≤ isqrt (N - 1) * isqrt (N - 1) := mul_self_mono hm_le
        exact ⟨by omega, (isOrdSquareBool_iff (m * m)).mpr ⟨m, rfl⟩⟩

theorem ceilSqrt_bounds {N : Nat} (hN : 1 ≤ N) :
    (ceilSqrt N - 1) * (ceilSqrt N - 1) < N ∧ N ≤ ceilSqrt N * ceilSqrt N := by
  unfold ceilSqrt
  have hN0 : N ≠ 0 := by omega
  rw [if_neg hN0]
  have hsub : isqrt (N - 1) + 1 - 1 = isqrt (N - 1) := by omega
  rw [hsub]
  rcases isqrt_spec (N - 1) with ⟨hlo, hhi⟩
  omega

theorem ordSquareCount_exact_sq (m : Nat) (hm : 1 ≤ m) :
    ordSquareCount (m * m) = m := by
  rw [ordSquareCount_eq_ceilSqrt]
  have hpos : 1 ≤ m * m := Nat.mul_le_mul hm hm
  rcases ceilSqrt_bounds hpos with ⟨hlo, hhi⟩
  let c := ceilSqrt (m * m)
  have hc_lo : (c - 1) * (c - 1) < m * m := hlo
  have hc_hi : m * m ≤ c * c := hhi
  change c = m
  have htrich : c < m ∨ m < c ∨ c = m := by omega
  rcases htrich with hlt | hgt | heq
  · have := mul_self_strict_mono hlt
    omega
  · have hle : m ≤ c - 1 := by omega
    have hsq : m * m ≤ (c - 1) * (c - 1) := mul_self_mono hle
    omega
  · exact heq

/--
  **Interpretation B (Main Theorem 1 — Exact Dyadic & Fermat-Tower Evaluation):**
  Because `x ↦ x ⊗ x` is a bijection on `[0, 2^d)` for every `d ≥ 0`:
  1. `nimSeqOrdSquareCount (2 ^ d) = ordSquareCount (2 ^ d)` for all `d`;
  2. `nimSeqOrdSquareCount (2 ^ (2 * m)) = 2 ^ m` for all `m` (`N = 4^m`, count `= √N`);
  3. `nimSeqOrdSquareCount (M (k + 1)) = M k` for all `k` (`N = 2^(2^(k+1))`, count `= √N`).
-/
theorem nimSeqOrdSquareCount_two_pow (d : Nat) :
    nimSeqOrdSquareCount (2 ^ d) = ordSquareCount (2 ^ d) := by
  unfold nimSeqOrdSquareCount ordSquareCount
  exact filter_range_bij_length (2 ^ d) nimSq nimSqrt isOrdSquareBool
    (fun x hx => (nimSq_lt_two_pow_iff d x).mpr hx)
    (fun y hy => (nimSqrt_lt_two_pow_iff d y).mpr hy)
    (fun x _ => nimSqrt_nimSq x)
    (fun y _ => nimSq_nimSqrt y)

theorem nimSeqOrdSquareCount_even_two_pow (m : Nat) :
    nimSeqOrdSquareCount (2 ^ (2 * m)) = 2 ^ m := by
  rw [nimSeqOrdSquareCount_two_pow]
  have hpow : 2 ^ (2 * m) = 2 ^ m * 2 ^ m := by
    have h2m : 2 * m = m + m := by omega
    rw [h2m, pow_add_eq]
  rw [hpow]
  exact ordSquareCount_exact_sq (2 ^ m) (two_pow_pos m)

theorem nimSeqOrdSquareCount_fermat (k : Nat) :
    nimSeqOrdSquareCount (M (k + 1)) = M k := by
  have hexp : M (k + 1) = 2 ^ (2 * 2 ^ k) := by
    unfold M
    congr 1
    rw [Nat.pow_succ]
    omega
  rw [hexp, nimSeqOrdSquareCount_even_two_pow]
  rfl

/--
  **Interpretation B (Main Theorem 2 — Uniform All-`N` Polynomial `Θ(N^{-1/2})` Bounds):**
  For EVERY positive integer `N ≥ 1` (including all intermediate `N` between Fermat 2-powers):
    `N < 2 * C(N)^2` and `C(N)^2 < 8 * N`,
  where `C(N) = nimSeqOrdSquareCount N`. Dividing by `N^2` gives
    `(1 / √2) * N^{-1/2} < C(N) / N < 2√2 * N^{-1/2}` for all `N ≥ 1`.
-/
theorem interpretationB_polynomial_bounds_all_N {N : Nat} (hN : 1 ≤ N) :
    N < 2 * (nimSeqOrdSquareCount N * nimSeqOrdSquareCount N) ∧
      nimSeqOrdSquareCount N * nimSeqOrdSquareCount N < 8 * N := by
  rcases ilog2_spec hN with ⟨hlo, hhi⟩
  let d := ilog2 N
  have hd_lo : 2 ^ d ≤ N := hlo
  have hd_hi : N < 2 ^ (d + 1) := hhi
  have hmono_lo : ordSquareCount (2 ^ d) ≤ nimSeqOrdSquareCount N := by
    rw [← nimSeqOrdSquareCount_two_pow d]
    exact filter_range_mono _ hd_lo
  have hmono_hi : nimSeqOrdSquareCount N ≤ ordSquareCount (2 ^ (d + 1)) := by
    rw [← nimSeqOrdSquareCount_two_pow (d + 1)]
    exact filter_range_mono _ (Nat.le_of_lt hd_hi)
  rw [ordSquareCount_eq_ceilSqrt] at hmono_lo hmono_hi
  rcases ceilSqrt_bounds (two_pow_pos d) with ⟨_, hsq_lo⟩
  rcases ceilSqrt_bounds (two_pow_pos (d + 1)) with ⟨hsq_hi, _⟩
  let C := nimSeqOrdSquareCount N
  change N < 2 * (C * C) ∧ C * C < 8 * N
  constructor
  · have hc_sq : ceilSqrt (2 ^ d) * ceilSqrt (2 ^ d) ≤ C * C := mul_self_mono hmono_lo
    have hd_hi' : N < 2 ^ d * 2 := by rw [← Nat.pow_succ]; exact hd_hi
    omega
  · have hp : C - 1 ≤ ceilSqrt (2 ^ (d + 1)) - 1 := by
      have : C ≤ ceilSqrt (2 ^ (d + 1)) := hmono_hi
      omega
    have hpred_sq : (C - 1) * (C - 1) ≤
        (ceilSqrt (2 ^ (d + 1)) - 1) * (ceilSqrt (2 ^ (d + 1)) - 1) := mul_self_mono hp
    have h2d1 : 2 ^ (d + 1) ≤ 2 * N := by
      rw [Nat.pow_succ]
      omega
    have hpred_lt : (C - 1) * (C - 1) < 2 * N := by omega
    by_cases hC1 : C ≤ 1
    · have : C * C ≤ 1 := by
        have h01 : C = 0 ∨ C = 1 := by omega
        rcases h01 with h0 | h1
        · simp [h0]
        · simp [h1]
      omega
    · have hle2 : C ≤ 2 * (C - 1) := by omega
      have hC_sq : C * C ≤ (2 * (C - 1)) * (2 * (C - 1)) := mul_self_mono hle2
      have h4 : (2 * (C - 1)) * (2 * (C - 1)) = 4 * ((C - 1) * (C - 1)) := by
        calc
          (2 * (C - 1)) * (2 * (C - 1)) = 2 * 2 * ((C - 1) * (C - 1)) := by
            rw [Nat.mul_assoc, Nat.mul_left_comm (C - 1) 2 (C - 1), ← Nat.mul_assoc]
          _ = 4 * ((C - 1) * (C - 1)) := rfl
      omega

/--
  **Interpretation B (Main Theorem 3 — Zero Asymptotic Density Confirmed):**
  For every integer `K ≥ 1`, there exists `N₀ ≥ 1` such that for all `N ≥ N₀`,
  `K * C(N) < N` (i.e. `C(N) / N < 1 / K`, so `lim_{N → ∞} C(N) / N = 0`).
-/
theorem interpretationB_zero_density (K : Nat) (hK : 1 ≤ K) :
    ∃ N₀ : Nat, 1 ≤ N₀ ∧ ∀ N : Nat, N₀ ≤ N → K * nimSeqOrdSquareCount N < N := by
  refine ⟨8 * (K * K), by
    have : 1 ≤ K * K := Nat.mul_le_mul hK hK
    omega, fun N hN => ?_⟩
  have hN1 : 1 ≤ N := by
    have : 1 ≤ K * K := Nat.mul_le_mul hK hK
    omega
  have hup := (interpretationB_polynomial_bounds_all_N hN1).2
  let C := nimSeqOrdSquareCount N
  have hKC_sq : (K * C) * (K * C) < N * N := by
    have h1 : (K * C) * (K * C) = (K * K) * (C * C) := by
      rw [Nat.mul_assoc, Nat.mul_left_comm C K C, ← Nat.mul_assoc]
    have h2 : (K * K) * (C * C) < (K * K) * (8 * N) :=
      Nat.mul_lt_mul_of_pos_left hup (Nat.mul_pos hK hK)
    have h3 : (K * K) * (8 * N) = (8 * (K * K)) * N := by
      rw [← Nat.mul_assoc, Nat.mul_comm (K * K) 8]
    have h4 : (8 * (K * K)) * N ≤ N * N := Nat.mul_le_mul_right N hN
    omega
  cases Nat.lt_or_ge (K * C) N with
  | inl hlt => exact hlt
  | inr hge =>
    have hsq : N * N ≤ (K * C) * (K * C) := mul_self_mono hge
    omega

/-- Elementary exponential-beats-quadratic inequality `d * d ≤ 2 ^ d` for all `d ≥ 4`. -/
theorem sq_le_two_pow {d : Nat} (hd : 4 ≤ d) : d * d ≤ 2 ^ d := by
  obtain ⟨t, rfl⟩ : ∃ t, d = t + 4 := ⟨d - 4, by omega⟩
  induction t with
  | zero => decide
  | succ t ih =>
    have hlin : 2 * (t + 4) + 1 ≤ (t + 4) * (t + 4) := by
      have : 4 * (t + 4) ≤ (t + 4) * (t + 4) := Nat.mul_le_mul_right (t + 4) (by omega)
      omega
    have hstep : (t + 1 + 4) * (t + 1 + 4) = (t + 4) * (t + 4) + (2 * (t + 4) + 1) := by
      have h1 : t + 1 + 4 = (t + 4) + 1 := by omega
      rw [h1, Nat.add_mul, Nat.mul_add, Nat.mul_one, Nat.one_mul]
      omega
    have hpow : 2 ^ (t + 1 + 4) = 2 ^ (t + 4) + 2 ^ (t + 4) := by
      have h1 : t + 1 + 4 = (t + 4) + 1 := by omega
      rw [h1, Nat.pow_succ]
      omega
    omega

theorem ilog2_mono {a b : Nat} (ha : 1 ≤ a) (hab : a ≤ b) : ilog2 a ≤ ilog2 b := by
  rcases ilog2_spec ha with ⟨hlo_a, _⟩
  rcases ilog2_spec (Nat.le_trans ha hab) with ⟨_, hhi_b⟩
  cases Nat.lt_or_ge (ilog2 b) (ilog2 a) with
  | inr hle => exact hle
  | inl hgt =>
    have hle1 : ilog2 b + 1 ≤ ilog2 a := hgt
    have hpow : 2 ^ (ilog2 b + 1) ≤ 2 ^ (ilog2 a) := Nat.pow_le_pow_right (by decide) hle1
    omega

theorem ilog2_two_pow (d : Nat) : ilog2 (2 ^ d) = d := by
  rcases ilog2_spec (two_pow_pos d) with ⟨hlo, hhi⟩
  have htrich : ilog2 (2 ^ d) < d ∨ d < ilog2 (2 ^ d) ∨ ilog2 (2 ^ d) = d := by omega
  rcases htrich with hlt | hgt | heq
  · have hpow : 2 ^ (ilog2 (2 ^ d) + 1) ≤ 2 ^ d := Nat.pow_le_pow_right (by decide) hlt
    omega
  · have hle : d + 1 ≤ ilog2 (2 ^ d) := hgt
    have hp : 2 ^ (d + 1) ≤ 2 ^ (ilog2 (2 ^ d)) := Nat.pow_le_pow_right (by decide) hle
    rw [Nat.pow_succ] at hp
    have := two_pow_pos d
    omega
  · exact heq

/--
  **Interpretation B (Main Theorem 4 — Refutation of `(log N)^{-1/2}` Decay):**
  For EVERY `K ≥ 1`, there exists `N₀ ≥ 2` such that for all `N ≥ N₀`,
    `K * C(N)^2 * ilog2 N < N^2`,
  i.e. `(C(N) / N) / (ilog2 N)^{-1/2} < 1 / √K → 0` as `N → ∞`.
  Consequently, `C(N) / N` decays strictly faster than ANY constant multiple of `(log N)^{-1/2}`,
  even along arbitrary infinite subsequences.
-/
theorem interpretationB_ratio_to_inv_sqrt_log_tends_to_zero (K : Nat) (hK : 1 ≤ K) :
    ∃ N₀ : Nat, 2 ≤ N₀ ∧ ∀ N : Nat, N₀ ≤ N →
      K * (nimSeqOrdSquareCount N * nimSeqOrdSquareCount N) * ilog2 N < N * N := by
  let d₀ := Nat.max 4 (8 * K)
  refine ⟨2 ^ d₀, ?_, fun N hN => ?_⟩
  · have hd0 : 1 ≤ d₀ := Nat.le_trans (by decide : 1 ≤ 4) (Nat.le_max_left 4 (8 * K))
    exact show 2 ^ 1 ≤ 2 ^ d₀ from Nat.pow_le_pow_right (by decide : 0 < 2) hd0
  · have hd0_ge4 : 4 ≤ d₀ := Nat.le_max_left 4 (8 * K)
    have hd0_ge8K : 8 * K ≤ d₀ := Nat.le_max_right 4 (8 * K)
    have h2d0_pos : 1 ≤ 2 ^ d₀ := two_pow_pos d₀
    have hN1 : 1 ≤ N := Nat.le_trans h2d0_pos hN
    let d := ilog2 N
    have hd_ge_d0 : d₀ ≤ d := by
      have hm := ilog2_mono h2d0_pos hN
      rw [ilog2_two_pow] at hm
      exact hm
    have hd_ge4 : 4 ≤ d := Nat.le_trans hd0_ge4 hd_ge_d0
    have hd_ge8K : 8 * K ≤ d := Nat.le_trans hd0_ge8K hd_ge_d0
    rcases ilog2_spec hN1 with ⟨h2d_le_N, _⟩
    have h8Kd_le_N : 8 * K * d ≤ N := by
      calc
        8 * K * d ≤ d * d := Nat.mul_le_mul_right d hd_ge8K
        _ ≤ 2 ^ d := sq_le_two_pow hd_ge4
        _ ≤ N := h2d_le_N
    have hup := (interpretationB_polynomial_bounds_all_N hN1).2
    let C := nimSeqOrdSquareCount N
    have hK_pos : 0 < K := by omega
    have hstep1 : K * (C * C) < K * (8 * N) := Nat.mul_lt_mul_of_pos_left hup hK_pos
    have hd_pos : 0 < d := by omega
    have hstep2 : K * (C * C) * d < K * (8 * N) * d := Nat.mul_lt_mul_of_pos_right hstep1 hd_pos
    have hrew : K * (8 * N) * d = (8 * K * d) * N := by
      calc
        K * (8 * N) * d = (K * 8) * N * d := by rw [Nat.mul_assoc K 8 N]
        _ = (8 * K) * (N * d) := by rw [Nat.mul_comm K 8, Nat.mul_assoc]
        _ = (8 * K) * (d * N) := by rw [Nat.mul_comm N d]
        _ = (8 * K * d) * N := (Nat.mul_assoc (8 * K) d N).symm
    have hstep3 : (8 * K * d) * N ≤ N * N := Nat.mul_le_mul_right N h8Kd_le_N
    change K * (C * C) * d < N * N
    omega

theorem interpretationB_refute_inv_sqrt_log_decay :
    ¬ (∃ K : Nat, 1 ≤ K ∧ ∀ N₁ : Nat, ∃ N : Nat, N₁ ≤ N ∧
        N * N ≤ K * (nimSeqOrdSquareCount N * nimSeqOrdSquareCount N) * ilog2 N) := by
  rintro ⟨K, hK, hinf⟩
  rcases interpretationB_ratio_to_inv_sqrt_log_tends_to_zero K hK with ⟨N₀, _, hlt⟩
  rcases hinf N₀ with ⟨N, hNN₀, hge⟩
  have := hlt N hNN₀
  omega

/-! ## Section 5: Explicit Non-Vacuity Computations on `[0, 16)` and `[0, 256]` -/

theorem nonvacuity_nimMul_samples :
    nimMul 2 2 = 3 ∧
    nimMul 3 3 = 2 ∧
    nimMul 2 3 = 1 ∧
    nimMul 4 4 = 6 ∧
    nimMul 4 15 = 1 ∧
    nimMul 8 8 = 13 ∧
    nimMul 15 15 = 9 := by
  decide

theorem nonvacuity_nimSq_first_16 :
    (List.range 16).map nimSq =
      [0, 1, 3, 2, 6, 7, 5, 4, 13, 12, 14, 15, 11, 10, 8, 9] := by
  rfl

theorem nonvacuity_ordSquareCount_samples :
    nimSeqOrdSquareCount 1 = 1 ∧
    nimSeqOrdSquareCount 2 = 2 ∧
    nimSeqOrdSquareCount 4 = 2 ∧
    nimSeqOrdSquareCount 8 = 3 ∧
    nimSeqOrdSquareCount 16 = 4 ∧
    nimSeqOrdSquareCount 64 = 8 ∧
    nimSeqOrdSquareCount 256 = 16 := by
  decide

end Conjecture00000001284

/-! ## Axiom Audit -/

#print axioms Conjecture00000001284.nimMul_comm
#print axioms Conjecture00000001284.nimMul_assoc
#print axioms Conjecture00000001284.nimMul_distrib_left
#print axioms Conjecture00000001284.nimMul_nimInv
#print axioms Conjecture00000001284.nimMul_eq_zero_iff
#print axioms Conjecture00000001284.nimMul_fermat_lt
#print axioms Conjecture00000001284.nimMul_fermat_self
#print axioms Conjecture00000001284.nimMul_unique
#print axioms Conjecture00000001284.nimMul_mex_ne
#print axioms Conjecture00000001284.existsUnique_nimSq
#print axioms Conjecture00000001284.nimSq_lt_two_pow_iff
#print axioms Conjecture00000001284.interpretationA_nimSquare_density_one
#print axioms Conjecture00000001284.interpretationA_restricted_nimSquare_bounds
#print axioms Conjecture00000001284.nimSeqOrdSquareCount_two_pow
#print axioms Conjecture00000001284.nimSeqOrdSquareCount_fermat
#print axioms Conjecture00000001284.interpretationB_polynomial_bounds_all_N
#print axioms Conjecture00000001284.interpretationB_zero_density
#print axioms Conjecture00000001284.interpretationB_ratio_to_inv_sqrt_log_tends_to_zero
#print axioms Conjecture00000001284.interpretationB_refute_inv_sqrt_log_decay
#print axioms Conjecture00000001284.nonvacuity_nimMul_samples
#print axioms Conjecture00000001284.nonvacuity_nimSq_first_16
#print axioms Conjecture00000001284.nonvacuity_ordSquareCount_samples
