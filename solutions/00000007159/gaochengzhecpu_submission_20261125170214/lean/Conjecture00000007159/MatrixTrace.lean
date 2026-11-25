/-
  Conjecture 00000007159 — First-Principles Matrix & Trace Algebra
  Core Lean 4.19.0 (zero external dependencies)
-/

namespace Conjecture00000007159

/-- Finite sum over `Fin n` valued in `Int`. -/
def finSum : {n : Nat} → (Fin n → Int) → Int
  | 0, _ => 0
  | n + 1, f => finSum (fun i : Fin n => f ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩) + f ⟨n, Nat.lt_succ_self n⟩

theorem finSum_congr {n : Nat} {f g : Fin n → Int} (h : ∀ i, f i = g i) :
    finSum f = finSum g := by
  induction n with
  | zero => rfl
  | succ m ih =>
    simp only [finSum]
    rw [ih (fun i => h _), h _]

theorem finSum_zero (n : Nat) : finSum (fun _ : Fin n => (0 : Int)) = 0 := by
  induction n with
  | zero => rfl
  | succ m ih =>
    simp only [finSum, ih, Int.add_zero]

theorem finSum_add {n : Nat} (f g : Fin n → Int) :
    finSum (fun i => f i + g i) = finSum f + finSum g := by
  induction n with
  | zero => simp [finSum]
  | succ m ih =>
    simp only [finSum, ih]
    omega

theorem finSum_sub {n : Nat} (f g : Fin n → Int) :
    finSum (fun i => f i - g i) = finSum f - finSum g := by
  induction n with
  | zero => simp [finSum]
  | succ m ih =>
    simp only [finSum, ih]
    omega

theorem finSum_mul_left {n : Nat} (c : Int) (f : Fin n → Int) :
    finSum (fun i => c * f i) = c * finSum f := by
  induction n with
  | zero => simp [finSum]
  | succ m ih =>
    simp only [finSum, ih, Int.mul_add]

theorem finSum_mul_right {n : Nat} (f : Fin n → Int) (c : Int) :
    finSum (fun i => f i * c) = finSum f * c := by
  induction n with
  | zero => simp [finSum]
  | succ m ih =>
    simp only [finSum, ih, Int.add_mul]

theorem finSum_nonneg {n : Nat} {f : Fin n → Int} (h : ∀ i, 0 ≤ f i) :
    0 ≤ finSum f := by
  induction n with
  | zero => simp [finSum]
  | succ m ih =>
    simp only [finSum]
    have h1 : 0 ≤ finSum (fun i : Fin m => f ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩) :=
      ih (fun i => h _)
    have h2 : 0 ≤ f ⟨m, Nat.lt_succ_self m⟩ := h _
    omega

theorem finSum_le {n : Nat} {f g : Fin n → Int} (h : ∀ i, f i ≤ g i) :
    finSum f ≤ finSum g := by
  induction n with
  | zero => simp [finSum]
  | succ m ih =>
    simp only [finSum]
    have h1 : finSum (fun i : Fin m => f ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩) ≤
        finSum (fun i : Fin m => g ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩) :=
      ih (fun i => h _)
    have h2 : f ⟨m, Nat.lt_succ_self m⟩ ≤ g ⟨m, Nat.lt_succ_self m⟩ := h _
    omega

theorem finSum_swap {m n : Nat} (f : Fin m → Fin n → Int) :
    finSum (fun i => finSum (fun j => f i j)) = finSum (fun j => finSum (fun i => f i j)) := by
  induction m with
  | zero =>
    simp only [finSum]
    rw [finSum_zero]
  | succ m' ih =>
    simp only [finSum]
    rw [ih, ← finSum_add]

theorem sq_nonneg_int (x : Int) : 0 ≤ x * x := by
  by_cases h : 0 ≤ x
  · exact Int.mul_nonneg h h
  · have h' : 0 ≤ -x := by omega
    have hmul : 0 ≤ (-x) * (-x) := Int.mul_nonneg h' h'
    have heq : (-x) * (-x) = x * x := by
      rw [Int.neg_mul, Int.mul_neg, Int.neg_neg]
    rw [← heq]
    exact hmul

/-- Helper linear combination rule for `finSum`. -/
theorem finSum_lin3 {n : Nat} (a b c : Int) (f g h : Fin n → Int) :
    finSum (fun i => a * f i - b * g i + c * h i) =
      a * finSum f - b * finSum g + c * finSum h := by
  induction n with
  | zero => simp [finSum]
  | succ m ih =>
    simp only [finSum, ih, Int.mul_add]
    omega

/-- Discrete Cauchy-Schwarz inequality over `Int` via Lagrange's identity. -/
theorem finSum_cauchy_schwarz {n : Nat} (u v : Fin n → Int) :
    finSum (fun i => u i * v i) * finSum (fun i => u i * v i) ≤
      finSum (fun i => u i * u i) * finSum (fun i => v i * v i) := by
  let S := finSum (fun i => finSum (fun j => (u i * v j - u j * v i) * (u i * v j - u j * v i)))
  have hS_nonneg : 0 ≤ S :=
    finSum_nonneg (fun i => finSum_nonneg (fun j => sq_nonneg_int _))
  have hexp : ∀ a b c d : Int,
      (a * d - c * b) * (a * d - c * b) =
        (a * a) * (d * d) - (2 * (a * b)) * (c * d) + 1 * ((c * c) * (b * b)) := by
    intro a b c d
    have h1 : (a * d - c * b) * (a * d - c * b) =
        (a * d) * (a * d) - (a * d) * (c * b) - (c * b) * (a * d) + (c * b) * (c * b) := by
      rw [Int.sub_mul, Int.mul_sub, Int.mul_sub]
      omega
    have t1 : (a * d) * (a * d) = (a * a) * (d * d) := by
      simp [Int.mul_assoc, Int.mul_left_comm, Int.mul_comm]
    have t2 : (a * d) * (c * b) = (a * b) * (c * d) := by
      simp [Int.mul_assoc, Int.mul_left_comm, Int.mul_comm]
    have t3 : (c * b) * (a * d) = (a * b) * (c * d) := by
      simp [Int.mul_assoc, Int.mul_left_comm, Int.mul_comm]
    have t4 : (c * b) * (c * b) = (c * c) * (b * b) := by
      simp [Int.mul_assoc, Int.mul_left_comm, Int.mul_comm]
    rw [h1, t1, t2, t3, t4, Int.mul_assoc 2 (a * b) (c * d), Int.one_mul]
    omega
  let SU := finSum (fun i => u i * u i)
  let SV := finSum (fun j => v j * v j)
  let SP := finSum (fun j => u j * v j)
  have hj : ∀ i,
      finSum (fun j => (u i * v j - u j * v i) * (u i * v j - u j * v i)) =
        SV * (u i * u i) - (2 * SP) * (u i * v i) + SU * (v i * v i) := by
    intro i
    have hc : finSum (fun j => (u i * v j - u j * v i) * (u i * v j - u j * v i)) =
        finSum (fun j => (u i * u i) * (v j * v j) - (2 * (u i * v i)) * (u j * v j) +
          (v i * v i) * (u j * u j)) := by
      apply finSum_congr
      intro j
      rw [hexp (u i) (v i) (u j) (v j), Int.one_mul, Int.mul_comm (u j * u j) (v i * v i)]
    rw [hc, finSum_lin3]
    dsimp [SU, SV, SP]
    have m1 : (u i * u i) * finSum (fun j => v j * v j) = finSum (fun j => v j * v j) * (u i * u i) :=
      Int.mul_comm _ _
    have m2 : (2 * (u i * v i)) * finSum (fun j => u j * v j) =
        (2 * finSum (fun j => u j * v j)) * (u i * v i) := by
      simp [Int.mul_assoc, Int.mul_left_comm, Int.mul_comm]
    have m3 : (v i * v i) * finSum (fun j => u j * u j) = finSum (fun j => u j * u j) * (v i * v i) :=
      Int.mul_comm _ _
    rw [m1, m2, m3]
  have hS_eq : S = SV * SU - (2 * SP) * SP + SU * SV := by
    dsimp [S]
    rw [finSum_congr hj, finSum_lin3]
  have hcomm : SV * SU = SU * SV := Int.mul_comm SV SU
  have h2 : (2 * SP) * SP = 2 * (SP * SP) := Int.mul_assoc 2 SP SP
  dsimp [SU, SV, SP] at hS_eq hcomm h2
  omega

/-- `n × n` integer matrices. -/
abbrev Mat (n : Nat) := Fin n → Fin n → Int

namespace Mat

def zero (n : Nat) : Mat n := fun _ _ => 0

def one (n : Nat) : Mat n := fun i j => if i = j then 1 else 0

def add {n : Nat} (A B : Mat n) : Mat n := fun i j => A i j + B i j

def sub {n : Nat} (A B : Mat n) : Mat n := fun i j => A i j - B i j

def mul {n : Nat} (A B : Mat n) : Mat n :=
  fun i j => finSum (fun k => A i k * B k j)

def transpose {n : Nat} (A : Mat n) : Mat n := fun i j => A j i

def diag {n : Nat} (d : Fin n → Int) : Mat n := fun i j => if i = j then d i else 0

def commutator {n : Nat} (A B : Mat n) : Mat n := sub (mul A B) (mul B A)

def pow {n : Nat} (A : Mat n) : Nat → Mat n
  | 0 => one n
  | k + 1 => mul (pow A k) A

def tr {n : Nat} (A : Mat n) : Int := finSum (fun i => A i i)

def frobInner {n : Nat} (X Y : Mat n) : Int := tr (mul (transpose X) Y)

def frobNormSq {n : Nat} (X : Mat n) : Int := frobInner X X

@[ext]
theorem ext {n : Nat} {A B : Mat n} (h : ∀ i j, A i j = B i j) : A = B := by
  funext i j
  exact h i j

theorem finSum_ite_eq {n : Nat} (i : Fin n) (g : Fin n → Int) :
    finSum (fun k => if k = i then g k else 0) = g i := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ m ih =>
    simp only [finSum]
    by_cases hi : i.val = m
    · have hik : i = ⟨m, Nat.lt_succ_self m⟩ := Fin.ext hi
      subst hik
      have hpoint : ∀ k : Fin m,
          (if (⟨k.val, Nat.lt_succ_of_lt k.isLt⟩ : Fin (m + 1)) = ⟨m, Nat.lt_succ_self m⟩
           then g ⟨k.val, Nat.lt_succ_of_lt k.isLt⟩ else 0) = 0 := by
        intro k
        have hne : (⟨k.val, Nat.lt_succ_of_lt k.isLt⟩ : Fin (m + 1)) ≠ ⟨m, Nat.lt_succ_self m⟩ := by
          intro heq
          exact Nat.ne_of_lt k.isLt (congrArg Fin.val heq)
        simp [hne]
      rw [finSum_congr hpoint, finSum_zero]
      simp
    · have hlt : i.val < m := Nat.lt_of_le_of_ne (Nat.le_of_lt_succ i.isLt) hi
      let i' : Fin m := ⟨i.val, hlt⟩
      have hlast : (⟨m, Nat.lt_succ_self m⟩ : Fin (m + 1)) ≠ i := by
        intro heq
        exact hi (congrArg Fin.val heq).symm
      simp only [hlast, ↓reduceIte, Int.add_zero]
      have hcong : finSum (fun k : Fin m =>
          if (⟨k.val, Nat.lt_succ_of_lt k.isLt⟩ : Fin (m + 1)) = i
          then g ⟨k.val, Nat.lt_succ_of_lt k.isLt⟩ else 0) =
          finSum (fun k : Fin m => if k = i' then g ⟨k.val, Nat.lt_succ_of_lt k.isLt⟩ else 0) := by
        apply finSum_congr
        intro k
        by_cases hk : k = i'
        · have heq : (⟨k.val, Nat.lt_succ_of_lt k.isLt⟩ : Fin (m + 1)) = i :=
            Fin.ext (show k.val = i.val from congrArg Fin.val hk)
          rw [if_pos heq, if_pos hk]
        · have hne : (⟨k.val, Nat.lt_succ_of_lt k.isLt⟩ : Fin (m + 1)) ≠ i := by
            intro heq
            exact hk (Fin.ext (show k.val = i.val from congrArg Fin.val heq))
          rw [if_neg hne, if_neg hk]
      rw [hcong, ih i']

theorem one_mul {n : Nat} (A : Mat n) : mul (one n) A = A := by
  ext i j
  dsimp [mul, one]
  have hcong : finSum (fun k => (if i = k then (1 : Int) else 0) * A k j) =
      finSum (fun k => if k = i then A k j else 0) := by
    apply finSum_congr
    intro k
    by_cases hik : i = k
    · subst hik; simp
    · have hki : k ≠ i := fun h => hik h.symm
      simp [hik, hki]
  rw [hcong, finSum_ite_eq]

theorem mul_one {n : Nat} (A : Mat n) : mul A (one n) = A := by
  ext i j
  dsimp [mul, one]
  have hcong : finSum (fun k => A i k * (if k = j then (1 : Int) else 0)) =
      finSum (fun k => if k = j then A i k else 0) := by
    apply finSum_congr
    intro k
    by_cases hkj : k = j <;> simp [hkj]
  rw [hcong, finSum_ite_eq]

theorem mul_assoc {n : Nat} (A B C : Mat n) : mul (mul A B) C = mul A (mul B C) := by
  ext i j
  dsimp [mul]
  have h1 : finSum (fun l => finSum (fun k => A i k * B k l) * C l j) =
      finSum (fun l => finSum (fun k => (A i k * B k l) * C l j)) :=
    finSum_congr (fun l => (finSum_mul_right (fun k => A i k * B k l) (C l j)).symm)
  rw [h1, finSum_swap]
  apply finSum_congr
  intro k
  rw [← finSum_mul_left]
  exact finSum_congr (fun l => Int.mul_assoc (A i k) (B k l) (C l j))

theorem mul_add {n : Nat} (A B C : Mat n) : mul A (add B C) = add (mul A B) (mul A C) := by
  ext i j
  dsimp [mul, add]
  rw [← finSum_add]
  exact finSum_congr (fun k => Int.mul_add (A i k) (B k j) (C k j))

theorem add_mul {n : Nat} (A B C : Mat n) : mul (add A B) C = add (mul A C) (mul B C) := by
  ext i j
  dsimp [mul, add]
  rw [← finSum_add]
  exact finSum_congr (fun k => Int.add_mul (A i k) (B i k) (C k j))

theorem mul_sub {n : Nat} (A B C : Mat n) : mul A (sub B C) = sub (mul A B) (mul A C) := by
  ext i j
  dsimp [mul, sub]
  rw [← finSum_sub]
  exact finSum_congr (fun k => Int.mul_sub (A i k) (B k j) (C k j))

theorem sub_mul {n : Nat} (A B C : Mat n) : mul (sub A B) C = sub (mul A C) (mul B C) := by
  ext i j
  dsimp [mul, sub]
  rw [← finSum_sub]
  exact finSum_congr (fun k => Int.sub_mul (A i k) (B i k) (C k j))

theorem transpose_transpose {n : Nat} (A : Mat n) : transpose (transpose A) = A := rfl

theorem transpose_one (n : Nat) : transpose (one n) = one n := by
  ext i j
  dsimp [transpose, one]
  by_cases h : i = j
  · subst h; simp
  · have h' : j ≠ i := fun e => h e.symm
    simp [h, h']

theorem transpose_sub {n : Nat} (A B : Mat n) :
    transpose (sub A B) = sub (transpose A) (transpose B) := rfl

theorem transpose_mul {n : Nat} (A B : Mat n) :
    transpose (mul A B) = mul (transpose B) (transpose A) := by
  ext i j
  dsimp [transpose, mul]
  exact finSum_congr (fun k => Int.mul_comm (A j k) (B k i))

theorem pow_add {n : Nat} (A : Mat n) (p q : Nat) :
    pow A (p + q) = mul (pow A p) (pow A q) := by
  induction q with
  | zero =>
    simp [pow, mul_one]
  | succ q' ih =>
    rw [Nat.add_succ, pow, pow, ih, mul_assoc]

theorem pow_one {n : Nat} (A : Mat n) : pow A 1 = A := by
  simp [pow, one_mul]

theorem pow_two {n : Nat} (A : Mat n) : pow A 2 = mul A A := by
  simp [pow, one_mul]

theorem transpose_pow {n : Nat} (A : Mat n) (p : Nat) :
    transpose (pow A p) = pow (transpose A) p := by
  induction p with
  | zero => exact transpose_one n
  | succ k ih =>
    simp only [pow, transpose_mul, ih]
    have hcomm : ∀ (M : Mat n) (m : Nat), mul M (pow M m) = mul (pow M m) M := by
      intro M m
      induction m with
      | zero => simp [pow, one_mul, mul_one]
      | succ m' ihm =>
        simp only [pow]
        rw [← mul_assoc, ihm]
    exact hcomm (transpose A) k

theorem tr_add {n : Nat} (A B : Mat n) : tr (add A B) = tr A + tr B :=
  finSum_add _ _

theorem tr_sub {n : Nat} (A B : Mat n) : tr (sub A B) = tr A - tr B :=
  finSum_sub _ _

theorem tr_transpose {n : Nat} (A : Mat n) : tr (transpose A) = tr A := rfl

/-- Cyclic invariance of the trace: `tr(A B) = tr(B A)`. -/
theorem tr_mul_comm {n : Nat} (A B : Mat n) : tr (mul A B) = tr (mul B A) := by
  dsimp [tr, mul]
  rw [finSum_swap]
  exact finSum_congr (fun j => finSum_congr (fun i => Int.mul_comm (A i j) (B j i)))

theorem frobInner_eq_double_sum {n : Nat} (X Y : Mat n) :
    frobInner X Y = finSum (fun i => finSum (fun j => X j i * Y j i)) := rfl

theorem frobNormSq_nonneg {n : Nat} (X : Mat n) : 0 ≤ frobNormSq X := by
  rw [frobNormSq, frobInner_eq_double_sum]
  exact finSum_nonneg (fun i => finSum_nonneg (fun j => sq_nonneg_int _))

/-- Matrix Frobenius Cauchy-Schwarz inequality over `Int`:
    `⟨X, Y⟩_F^2 ≤ ‖X‖_F^2 ‖Y‖_F^2`. -/
theorem frob_cauchy_schwarz {n : Nat} (X Y : Mat n) :
    frobInner X Y * frobInner X Y ≤ frobNormSq X * frobNormSq Y := by
  let S := finSum (fun i => finSum (fun j => finSum (fun k => finSum (fun l =>
    (X j i * Y l k - X l k * Y j i) * (X j i * Y l k - X l k * Y j i)))))
  have hS_nonneg : 0 ≤ S :=
    finSum_nonneg (fun _ => finSum_nonneg (fun _ => finSum_nonneg (fun _ =>
      finSum_nonneg (fun _ => sq_nonneg_int _))))
  have hexp : ∀ a b c d : Int,
      (a * d - c * b) * (a * d - c * b) =
        (a * a) * (d * d) - (2 * (a * b)) * (c * d) + (b * b) * (c * c) := by
    intro a b c d
    have h1 : (a * d - c * b) * (a * d - c * b) =
        (a * d) * (a * d) - (a * d) * (c * b) - (c * b) * (a * d) + (c * b) * (c * b) := by
      rw [Int.sub_mul, Int.mul_sub, Int.mul_sub]
      omega
    have t1 : (a * d) * (a * d) = (a * a) * (d * d) := by
      simp [Int.mul_assoc, Int.mul_left_comm, Int.mul_comm]
    have t2 : (a * d) * (c * b) = (a * b) * (c * d) := by
      simp [Int.mul_assoc, Int.mul_left_comm, Int.mul_comm]
    have t3 : (c * b) * (a * d) = (a * b) * (c * d) := by
      simp [Int.mul_assoc, Int.mul_left_comm, Int.mul_comm]
    have t4 : (c * b) * (c * b) = (b * b) * (c * c) := by
      simp [Int.mul_assoc, Int.mul_left_comm, Int.mul_comm]
    rw [h1, t1, t2, t3, t4, Int.mul_assoc 2 (a * b) (c * d)]
    omega
  let NX := frobNormSq X
  let NY := frobNormSq Y
  let IP := frobInner X Y
  have h_l : ∀ i j k,
      finSum (fun l => (X j i * Y l k - X l k * Y j i) * (X j i * Y l k - X l k * Y j i)) =
        (X j i * X j i) * finSum (fun l => Y l k * Y l k) -
        (2 * (X j i * Y j i)) * finSum (fun l => X l k * Y l k) +
        (Y j i * Y j i) * finSum (fun l => X l k * X l k) := by
    intro i j k
    rw [finSum_congr (fun l => hexp (X j i) (Y j i) (X l k) (Y l k)), finSum_lin3]
  have h_kl : ∀ i j,
      finSum (fun k => finSum (fun l =>
        (X j i * Y l k - X l k * Y j i) * (X j i * Y l k - X l k * Y j i))) =
      NY * (X j i * X j i) - (2 * IP) * (X j i * Y j i) + NX * (Y j i * Y j i) := by
    intro i j
    rw [finSum_congr (fun k => h_l i j k), finSum_lin3]
    dsimp [NX, NY, IP, frobNormSq, frobInner, tr, mul, transpose]
    have m1 : (X j i * X j i) * finSum (fun k => finSum (fun l => Y l k * Y l k)) =
        finSum (fun k => finSum (fun l => Y l k * Y l k)) * (X j i * X j i) := Int.mul_comm _ _
    have m2 : (2 * (X j i * Y j i)) * finSum (fun k => finSum (fun l => X l k * Y l k)) =
        (2 * finSum (fun k => finSum (fun l => X l k * Y l k))) * (X j i * Y j i) := by
      simp [Int.mul_assoc, Int.mul_left_comm, Int.mul_comm]
    have m3 : (Y j i * Y j i) * finSum (fun k => finSum (fun l => X l k * X l k)) =
        finSum (fun k => finSum (fun l => X l k * X l k)) * (Y j i * Y j i) := Int.mul_comm _ _
    rw [m1, m2, m3]
  have h_j : ∀ i,
      finSum (fun j => finSum (fun k => finSum (fun l =>
        (X j i * Y l k - X l k * Y j i) * (X j i * Y l k - X l k * Y j i)))) =
      NY * finSum (fun j => X j i * X j i) - (2 * IP) * finSum (fun j => X j i * Y j i) +
      NX * finSum (fun j => Y j i * Y j i) := by
    intro i
    rw [finSum_congr (fun j => h_kl i j), finSum_lin3]
  have hS_eq : S = NY * NX - (2 * IP) * IP + NX * NY := by
    dsimp [S]
    rw [finSum_congr h_j, finSum_lin3]
    rfl
  have hcomm : NY * NX = NX * NY := Int.mul_comm NY NX
  have h2 : (2 * IP) * IP = 2 * (IP * IP) := Int.mul_assoc 2 IP IP
  dsimp [NX, NY, IP] at hS_eq hcomm h2
  omega

/-- Submultiplicativity of the squared Frobenius norm: `‖P Q‖_F^2 ≤ ‖P‖_F^2 ‖Q‖_F^2`. -/
theorem frobNormSq_mul_le {n : Nat} (P Q : Mat n) :
    frobNormSq (mul P Q) ≤ frobNormSq P * frobNormSq Q := by
  rw [frobNormSq, frobInner_eq_double_sum]
  have hpoint : ∀ i j : Fin n,
      mul P Q j i * mul P Q j i ≤
        finSum (fun k => P j k * P j k) * finSum (fun k => Q k i * Q k i) := by
    intro i j
    dsimp [mul]
    exact finSum_cauchy_schwarz (fun k => P j k) (fun k => Q k i)
  have hsum_j : ∀ i : Fin n,
      finSum (fun j => mul P Q j i * mul P Q j i) ≤
        finSum (fun j => finSum (fun k => P j k * P j k)) * finSum (fun k => Q k i * Q k i) := by
    intro i
    rw [← finSum_mul_right]
    exact finSum_le (fun j => hpoint i j)
  have hsum_i :
      finSum (fun i => finSum (fun j => mul P Q j i * mul P Q j i)) ≤
        finSum (fun j => finSum (fun k => P j k * P j k)) *
          finSum (fun i => finSum (fun k => Q k i * Q k i)) := by
    rw [← finSum_mul_left]
    exact finSum_le hsum_j
  have hP : finSum (fun j => finSum (fun k => P j k * P j k)) = frobNormSq P := by
    rw [finSum_swap]
    rfl
  have hQ : finSum (fun i => finSum (fun k => Q k i * Q k i)) = frobNormSq Q := rfl
  rw [hP, hQ] at hsum_i
  exact hsum_i

/-- Symmetry and Gram positive semidefinite / 2×2 positive definite predicates. -/
def IsSymm {n : Nat} (A : Mat n) : Prop := transpose A = A

def IsGramPSD {n : Nat} (A : Mat n) : Prop := ∃ X : Mat n, A = mul (transpose X) X

theorem isGramPSD_isSymm {n : Nat} {A : Mat n} (h : IsGramPSD A) : IsSymm A := by
  rcases h with ⟨X, rfl⟩
  simp [IsSymm, transpose_mul, transpose_transpose]

theorem symm_pow {n : Nat} {A : Mat n} (hA : IsSymm A) (p : Nat) : IsSymm (pow A p) := by
  rw [IsSymm, transpose_pow, hA]

/-- Determinant of a `2 × 2` matrix. -/
def det2 (A : Mat 2) : Int := A 0 0 * A 1 1 - A 0 1 * A 1 0

/-- Constructive `2 × 2` integer matrix from entries `a, b, c, d`. -/
def mat2 (a b c d : Int) : Mat 2 :=
  fun i j =>
    match i.val, j.val with
    | 0, 0 => a
    | 0, 1 => b
    | 1, 0 => c
    | _, _ => d

/-- Strictly positive definite `2 × 2` Gram matrix `A = L^T L` with `det L ≠ 0`. -/
def IsStrictGramSPD2 (A : Mat 2) : Prop :=
  ∃ L : Mat 2, det2 L ≠ 0 ∧ A = mul (transpose L) L

theorem strictGramSPD2_to_gramPSD {A : Mat 2} (h : IsStrictGramSPD2 A) : IsGramPSD A := by
  rcases h with ⟨L, _, hA⟩
  exact ⟨L, hA⟩

theorem finSum2 (f : Fin 2 → Int) : finSum f = f 0 + f 1 := by
  simp [finSum]

theorem det2_transpose_mul_self (L : Mat 2) :
    det2 (mul (transpose L) L) = det2 L * det2 L := by
  dsimp [det2, mul, transpose]
  simp only [finSum2]
  have p1 : (L 0 0 * L 0 0 + L 1 0 * L 1 0) * (L 0 1 * L 0 1 + L 1 1 * L 1 1) =
      (L 0 0 * L 0 1) * (L 0 0 * L 0 1) + (L 0 0 * L 1 1) * (L 0 0 * L 1 1) +
      (L 1 0 * L 0 1) * (L 1 0 * L 0 1) + (L 1 0 * L 1 1) * (L 1 0 * L 1 1) := by
    rw [Int.add_mul, Int.mul_add, Int.mul_add]
    have a1 : (L 0 0 * L 0 0) * (L 0 1 * L 0 1) = (L 0 0 * L 0 1) * (L 0 0 * L 0 1) := by
      simp [Int.mul_assoc, Int.mul_left_comm, Int.mul_comm]
    have a2 : (L 0 0 * L 0 0) * (L 1 1 * L 1 1) = (L 0 0 * L 1 1) * (L 0 0 * L 1 1) := by
      simp [Int.mul_assoc, Int.mul_left_comm, Int.mul_comm]
    have a3 : (L 1 0 * L 1 0) * (L 0 1 * L 0 1) = (L 1 0 * L 0 1) * (L 1 0 * L 0 1) := by
      simp [Int.mul_assoc, Int.mul_left_comm, Int.mul_comm]
    have a4 : (L 1 0 * L 1 0) * (L 1 1 * L 1 1) = (L 1 0 * L 1 1) * (L 1 0 * L 1 1) := by
      simp [Int.mul_assoc, Int.mul_left_comm, Int.mul_comm]
    rw [a1, a2, a3, a4]
    omega
  have p2 : (L 0 0 * L 0 1 + L 1 0 * L 1 1) * (L 0 1 * L 0 0 + L 1 1 * L 1 0) =
      (L 0 0 * L 0 1) * (L 0 0 * L 0 1) + 2 * ((L 0 0 * L 1 1) * (L 0 1 * L 1 0)) +
      (L 1 0 * L 1 1) * (L 1 0 * L 1 1) := by
    rw [Int.add_mul, Int.mul_add, Int.mul_add]
    have b1 : (L 0 0 * L 0 1) * (L 0 1 * L 0 0) = (L 0 0 * L 0 1) * (L 0 0 * L 0 1) := by
      simp [Int.mul_assoc, Int.mul_left_comm, Int.mul_comm]
    have b2 : (L 0 0 * L 0 1) * (L 1 1 * L 1 0) = (L 0 0 * L 1 1) * (L 0 1 * L 1 0) := by
      simp [Int.mul_assoc, Int.mul_left_comm, Int.mul_comm]
    have b3 : (L 1 0 * L 1 1) * (L 0 1 * L 0 0) = (L 0 0 * L 1 1) * (L 0 1 * L 1 0) := by
      simp [Int.mul_assoc, Int.mul_left_comm, Int.mul_comm]
    have b4 : (L 1 0 * L 1 1) * (L 1 1 * L 1 0) = (L 1 0 * L 1 1) * (L 1 0 * L 1 1) := by
      simp [Int.mul_assoc, Int.mul_left_comm, Int.mul_comm]
    rw [b1, b2, b3, b4]
    omega
  have p3 : (L 0 0 * L 1 1 - L 0 1 * L 1 0) * (L 0 0 * L 1 1 - L 0 1 * L 1 0) =
      (L 0 0 * L 1 1) * (L 0 0 * L 1 1) - 2 * ((L 0 0 * L 1 1) * (L 0 1 * L 1 0)) +
      (L 1 0 * L 0 1) * (L 1 0 * L 0 1) := by
    rw [Int.sub_mul, Int.mul_sub, Int.mul_sub]
    have c1 : (L 0 1 * L 1 0) * (L 0 0 * L 1 1) = (L 0 0 * L 1 1) * (L 0 1 * L 1 0) :=
      Int.mul_comm _ _
    have c2 : (L 0 1 * L 1 0) * (L 0 1 * L 1 0) = (L 1 0 * L 0 1) * (L 1 0 * L 0 1) := by
      simp [Int.mul_assoc, Int.mul_left_comm, Int.mul_comm]
    rw [c1, c2]
    omega
  rw [p1, p2, p3]
  omega

theorem strictGramSPD2_det_pos {A : Mat 2} (h : IsStrictGramSPD2 A) : 0 < det2 A := by
  rcases h with ⟨L, hdet, rfl⟩
  rw [det2_transpose_mul_self]
  by_cases hp : 0 < det2 L
  · exact Int.mul_pos hp hp
  · have hn : 0 < -det2 L := by omega
    have hmul : 0 < (-det2 L) * (-det2 L) := Int.mul_pos hn hn
    have heq : (-det2 L) * (-det2 L) = det2 L * det2 L := by
      rw [Int.neg_mul, Int.mul_neg, Int.neg_neg]
    rw [← heq]
    exact hmul

end Mat

end Conjecture00000007159
