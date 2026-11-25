/-
  Conjecture 00000004764 — Formal Power Series, Composition vs Simplified Non-Composition
  Generating-Function Equations, Boolean & Free Convolutions, and Bercovici–Pata Bijection
  Core Lean 4.19.0 (zero external dependencies)
-/
import BooleanFreeConv.Basic

namespace BooleanFreeConv

/-- Formal power series over `ℤ`: `f n` is the coefficient `[z^n] f(z)`. -/
abbrev Series := Nat → Int

/-- Finite prefix sum `rangeSum m f = ∑_{j = 0}^{m - 1} f j`. -/
def rangeSum : Nat → (Nat → Int) → Int
  | 0, _ => 0
  | m + 1, f => rangeSum m f + f m

theorem rangeSum_congr {m : Nat} {f g : Nat → Int} (h : ∀ j, j < m → f j = g j) :
    rangeSum m f = rangeSum m g := by
  induction m with
  | zero => rfl
  | succ k ih =>
    simp only [rangeSum]
    rw [ih (fun j hj => h j (Nat.lt_succ_of_lt hj)), h k (Nat.lt_succ_self k)]

theorem rangeSum_eq_zero {m : Nat} {f : Nat → Int} (h : ∀ j, j < m → f j = 0) :
    rangeSum m f = 0 := by
  induction m with
  | zero => rfl
  | succ k ih =>
    simp only [rangeSum]
    rw [ih (fun j hj => h j (Nat.lt_succ_of_lt hj)), h k (Nat.lt_succ_self k)]
    rfl

theorem rangeSum_add_distrib (m : Nat) (f g : Nat → Int) :
    rangeSum m (fun j => f j + g j) = rangeSum m f + rangeSum m g := by
  induction m with
  | zero => rfl
  | succ k ih =>
    simp only [rangeSum, ih]
    omega

theorem rangeSum_sub_distrib (m : Nat) (f g : Nat → Int) :
    rangeSum m (fun j => f j - g j) = rangeSum m f - rangeSum m g := by
  induction m with
  | zero => rfl
  | succ k ih =>
    simp only [rangeSum, ih]
    omega

theorem rangeSum_add_split (k d : Nat) (f : Nat → Int) :
    rangeSum (k + d) f = rangeSum k f + rangeSum d (fun i => f (k + i)) := by
  induction d with
  | zero => simp [rangeSum]
  | succ m ih =>
    rw [Nat.add_succ, rangeSum, ih, rangeSum, Int.add_assoc]

theorem rangeSum_succ_left (m : Nat) (f : Nat → Int) :
    rangeSum (m + 1) f = f 0 + rangeSum m (fun i => f (i + 1)) := by
  have h := rangeSum_add_split 1 m f
  rw [Nat.add_comm 1 m] at h
  rw [h]
  simp only [rangeSum, Int.zero_add]
  apply congrArg (f 0 + ·)
  apply rangeSum_congr
  intro i _
  rw [Nat.add_comm 1 i]

namespace Series

def zero : Series := fun _ => 0

def one : Series := fun n => if n = 0 then 1 else 0

/-- Multiplication by `z`: `(shift f)(z) = z * f(z)`. -/
def shift (f : Series) : Series
  | 0 => 0
  | n + 1 => f n

def add (f g : Series) : Series := fun n => f n + g n

def sub (f g : Series) : Series := fun n => f n - g n

def smul (c : Int) (f : Series) : Series := fun n => c * f n

/-- Cauchy product `(mul f g)(z) = f(z) * g(z)`. -/
def mul (f g : Series) : Series :=
  fun n => rangeSum (n + 1) (fun j => f j * g (n - j))

/-- Formal power `f(z)^k`. -/
def pow (f : Series) : Nat → Series
  | 0 => one
  | k + 1 => mul (pow f k) f

/-- Formal power series composition `C(W(z))` when `W(0) = 0`:
    `[z^n] C(W(z)) = ∑_{k = 0}^n C_k * [z^n] (W(z)^k)`. -/
def compZeroConst (C W : Series) : Series :=
  fun n => rangeSum (n + 1) (fun k => C k * (pow W k) n)

@[ext]
theorem ext {f g : Series} (h : ∀ n, f n = g n) : f = g :=
  funext h

theorem mul_zero_coeff (f g : Series) : mul f g 0 = f 0 * g 0 := by
  simp [mul, rangeSum]

theorem mul_one_left (f : Series) : mul one f = f := by
  ext n
  simp only [mul]
  rw [rangeSum_succ_left n]
  have h0 : one 0 * f (n - 0) = f n := by simp [one]
  have hrest : rangeSum n (fun i => one (i + 1) * f (n - (i + 1))) = 0 := by
    apply rangeSum_eq_zero
    intro i _
    simp [one]
  rw [h0, hrest, Int.add_zero]

theorem mul_sub_left (a b c : Series) : mul (sub a b) c = sub (mul a c) (mul b c) := by
  ext n
  simp only [mul, sub]
  have hdist : (fun j => (a j - b j) * c (n - j)) =
      (fun j => a j * c (n - j) - b j * c (n - j)) := by
    funext j
    exact Int.sub_mul (a j) (b j) (c (n - j))
  rw [hdist, rangeSum_sub_distrib]

theorem mul_shift_left (f g : Series) : mul (shift f) g = shift (mul f g) := by
  ext n
  cases n with
  | zero =>
    simp [mul, shift, rangeSum]
  | succ d =>
    simp only [mul, shift]
    rw [rangeSum_succ_left (d + 1)]
    simp only [shift, Int.zero_mul, Int.zero_add]
    apply rangeSum_congr
    intro i _
    have hsub : d + 1 - (i + 1) = d - i := by omega
    rw [hsub]

theorem mul_shift_right (f g : Series) : mul f (shift g) = shift (mul f g) := by
  ext n
  cases n with
  | zero =>
    simp [mul, shift, rangeSum]
  | succ d =>
    change rangeSum ((d + 1) + 1) (fun j => f j * shift g (d + 1 - j)) = mul f g d
    rw [rangeSum, Nat.sub_self]
    simp only [shift, Int.mul_zero, Int.add_zero]
    unfold mul
    apply rangeSum_congr
    intro j hj
    have hsub : d + 1 - j = (d - j) + 1 := by omega
    rw [hsub]

theorem mul_shift_comm (f g : Series) : mul (shift f) g = mul f (shift g) := by
  rw [mul_shift_left, mul_shift_right]

theorem pow_zero_coeff_of_unit {m : Series} (hm : m 0 = 1) (k : Nat) :
    (pow m k) 0 = 1 := by
  induction k with
  | zero => rfl
  | succ j ih =>
    simp [pow, mul_zero_coeff, ih, hm]

theorem pow_congr_le {m₁ m₂ : Series} :
    ∀ k d, (∀ r, r ≤ d → m₁ r = m₂ r) → (pow m₁ k) d = (pow m₂ k) d
  | 0, _, _ => rfl
  | k + 1, d, h => by
    simp only [pow, mul]
    apply rangeSum_congr
    intro j hj
    have hjd : j ≤ d := Nat.le_of_lt_succ hj
    have hsub : d - j ≤ d := Nat.sub_le d j
    rw [pow_congr_le k j (fun r hr => h r (Nat.le_trans hr hjd)), h (d - j) hsub]

/-- For `n < k`, `[z^n] ((z * M(z))^k) = 0`, confirming that `compZeroConst C (shift M)`
    is the exact infinite formal composition without truncation loss. -/
theorem pow_shift_lt_zero (M : Series) :
    ∀ k n, n < k → (pow (shift M) k) n = 0
  | 0, _, h => absurd h (Nat.not_lt_zero _)
  | k + 1, n, h => by
    simp only [pow, mul]
    apply rangeSum_eq_zero
    intro j hj
    by_cases hjk : j < k
    · rw [pow_shift_lt_zero M k j hjk, Int.zero_mul]
    · have hjeq : j = k ∧ n = k := by omega
      rcases hjeq with ⟨rfl, rfl⟩
      simp [shift]

/-- Exact shift-power identity: `[z^(k + d)] ((z * M(z))^k) = [z^d] (M(z)^k)`. -/
theorem pow_shift_add (M : Series) :
    ∀ k d, (pow (shift M) k) (k + d) = (pow M k) d
  | 0, d => by simp [pow]
  | k + 1, d => by
    change rangeSum (k + 1 + d + 1) (fun j => (pow (shift M) k) j * (shift M) (k + 1 + d - j)) =
      rangeSum (d + 1) (fun i => (pow M k) i * M (d - i))
    have hlen : k + 1 + d + 1 = k + ((d + 1) + 1) := by omega
    rw [hlen, rangeSum_add_split k ((d + 1) + 1)]
    have hfirst : rangeSum k (fun j => (pow (shift M) k) j * (shift M) (k + 1 + d - j)) = 0 := by
      apply rangeSum_eq_zero
      intro j hj
      rw [pow_shift_lt_zero M k j hj, Int.zero_mul]
    rw [hfirst, Int.zero_add, rangeSum]
    have hlast : k + 1 + d - (k + (d + 1)) = 0 := by omega
    rw [hlast]
    simp only [shift, Int.mul_zero, Int.add_zero]
    apply rangeSum_congr
    intro i hi
    have hsub : k + 1 + d - (k + i) = (d - i) + 1 := by omega
    rw [hsub, pow_shift_add M k i]

end Series

open Series

/-! ### Generating-Function Characterization: Simplified (No Composition) vs Free (Composition) -/

/-- Boolean generating-function relation: `(1 - B(z)) * M(z) = 1`. -/
def BoolGenEq (M B : Series) : Prop :=
  mul (sub one B) M = one

/-- Free generating-function relation with explicit composition: `M(z) = C(z * M(z))`. -/
def FreeGenEq (M C : Series) : Prop :=
  M = compZeroConst C (shift M)

/-- Exact formal-series proof of the Definition in `SOURCE.md`:
    When `B(z) = z * B̃(z)`, the Boolean equation `(1 - B(z)) * M(z) = 1` is equivalent
    to `M(z) - 1 = B̃(z) * (z * M(z))` — obtained from the free generating-function
    equation `M(z) - 1 = R(z * M(z)) * (z * M(z))` by dropping the composition
    `w = z * M(z)` inside `R`. -/
theorem boolGenEq_iff_no_comp (M bTilde : Series) :
    BoolGenEq M (shift bTilde) ↔ sub M one = mul bTilde (shift M) := by
  unfold BoolGenEq
  rw [mul_sub_left, mul_one_left, mul_shift_comm]
  constructor
  · intro h
    ext n
    have hn := congrFun h n
    simp only [sub] at hn ⊢
    omega
  · intro h
    ext n
    have hn := congrFun h n
    simp only [sub] at hn ⊢
    omega

/-! ### Constructive Bijections: Moments ↔ Boolean Cumulants and Moments ↔ Free Cumulants -/

def boolStep (b m : Series) : Series :=
  fun n => if n = 0 then 1 else rangeSum n (fun i => b (i + 1) * m (n - 1 - i))

def boolApprox (b : Series) : Nat → Series
  | 0 => one
  | s + 1 => boolStep b (boolApprox b s)

/-- Moment generating series `M(z)` constructed from Boolean cumulant series `B(z)` (`B(0) = 0`). -/
def momentsFromBool (b : Series) : Series :=
  fun n => boolApprox b n n

theorem boolStep_congr_lt (b : Series) {m₁ m₂ : Series} {n : Nat}
    (h : ∀ r, r < n → m₁ r = m₂ r) : boolStep b m₁ n = boolStep b m₂ n := by
  cases n with
  | zero => rfl
  | succ d =>
    simp only [boolStep, Nat.succ_ne_zero, ↓reduceIte, Nat.add_sub_cancel]
    apply rangeSum_congr
    intro i hi
    rw [h (d - i) (by omega)]

theorem boolApprox_succ_eq (b : Series) :
    ∀ s n, n ≤ s → boolApprox b (s + 1) n = boolApprox b s n
  | 0, n, hn => by
    have h0 : n = 0 := by omega
    subst h0
    rfl
  | s + 1, n, hn => by
    simp only [boolApprox]
    apply boolStep_congr_lt
    intro r hr
    exact boolApprox_succ_eq b s r (by omega)

theorem boolApprox_ge_eq (b : Series) {n : Nat} :
    ∀ s, n ≤ s → boolApprox b s n = momentsFromBool b n := by
  intro s hs
  induction s with
  | zero =>
    have h0 : n = 0 := by omega
    subst h0
    rfl
  | succ k ih =>
    by_cases hnk : n ≤ k
    · rw [boolApprox_succ_eq b k n hnk, ih hnk]
    · have heq : n = k + 1 := by omega
      subst heq
      rfl

theorem momentsFromBool_fixed (b : Series) :
    momentsFromBool b = boolStep b (momentsFromBool b) := by
  ext n
  cases n with
  | zero => rfl
  | succ d =>
    change boolApprox b (d + 1) (d + 1) = boolStep b (momentsFromBool b) (d + 1)
    simp only [boolApprox]
    apply boolStep_congr_lt
    intro r hr
    exact boolApprox_ge_eq b d (by omega)

theorem boolStep_unique (b m₁ m₂ : Series)
    (h₁ : m₁ = boolStep b m₁) (h₂ : m₂ = boolStep b m₂) : m₁ = m₂ := by
  ext n
  have hall : ∀ k, k ≤ n → m₁ k = m₂ k := by
    induction n with
    | zero =>
      intro k hk
      have hk0 : k = 0 := by omega
      subst hk0
      have e₁ := congrFun h₁ 0
      have e₂ := congrFun h₂ 0
      rw [e₁, e₂]
      rfl
    | succ d ih =>
      intro k hk
      by_cases hkd : k ≤ d
      · exact ih k hkd
      · have hkeq : k = d + 1 := by omega
        subst hkeq
        have e₁ := congrFun h₁ (d + 1)
        have e₂ := congrFun h₂ (d + 1)
        rw [e₁, e₂]
        apply boolStep_congr_lt
        intro r hr
        exact ih r (by omega)
  exact hall n (Nat.le_refl n)

/-- Exact generating-function identity `(1 - B(z)) * M(z) = 1` for `M = momentsFromBool B`. -/
theorem boolGenEq_momentsFromBool (b : Series) (hb : b 0 = 0) :
    BoolGenEq (momentsFromBool b) b := by
  unfold BoolGenEq
  rw [mul_sub_left, mul_one_left]
  ext n
  have hfix := congrFun (momentsFromBool_fixed b) n
  cases n with
  | zero =>
    simp [sub, mul, one, rangeSum, hb, boolStep] at hfix ⊢
    omega
  | succ d =>
    simp only [sub, mul, one, Nat.succ_ne_zero, ↓reduceIte]
    rw [rangeSum_succ_left (d + 1)]
    simp only [hb, Int.zero_mul, Int.zero_add]
    simp only [boolStep, Nat.succ_ne_zero, ↓reduceIte, Nat.add_sub_cancel] at hfix
    have hsum :
        rangeSum (d + 1) (fun i => b (i + 1) * momentsFromBool b (d + 1 - (i + 1))) =
          rangeSum (d + 1) (fun i => b (i + 1) * momentsFromBool b (d - i)) := by
      apply rangeSum_congr
      intro i _
      have hsub : d + 1 - (i + 1) = d - i := by omega
      rw [hsub]
    rw [hsum, ← hfix]
    omega

def boolCumStep (m b : Series) : Series :=
  fun n => if n = 0 then 0 else m n - rangeSum (n - 1) (fun i => b (i + 1) * m (n - 1 - i))

def boolCumApprox (m : Series) : Nat → Series
  | 0 => zero
  | s + 1 => boolCumStep m (boolCumApprox m s)

/-- Boolean cumulant series `B(z)` (`B(0) = 0`) extracted from a moment series `M(z)` (`M(0) = 1`). -/
def boolFromMoments (m : Series) : Series :=
  fun n => boolCumApprox m n n

theorem boolCumStep_congr_lt (m : Series) {b₁ b₂ : Series} {n : Nat}
    (h : ∀ r, r < n → b₁ r = b₂ r) : boolCumStep m b₁ n = boolCumStep m b₂ n := by
  cases n with
  | zero => rfl
  | succ d =>
    simp only [boolCumStep, Nat.succ_ne_zero, ↓reduceIte, Nat.add_sub_cancel]
    apply congrArg (m (d + 1) - ·)
    apply rangeSum_congr
    intro i hi
    rw [h (i + 1) (by omega)]

theorem boolCumApprox_succ_eq (m : Series) :
    ∀ s n, n ≤ s → boolCumApprox m (s + 1) n = boolCumApprox m s n
  | 0, n, hn => by
    have h0 : n = 0 := by omega
    subst h0
    rfl
  | s + 1, n, hn => by
    simp only [boolCumApprox]
    apply boolCumStep_congr_lt
    intro r hr
    exact boolCumApprox_succ_eq m s r (by omega)

theorem boolCumApprox_ge_eq (m : Series) {n : Nat} :
    ∀ s, n ≤ s → boolCumApprox m s n = boolFromMoments m n := by
  intro s hs
  induction s with
  | zero =>
    have h0 : n = 0 := by omega
    subst h0
    rfl
  | succ k ih =>
    by_cases hnk : n ≤ k
    · rw [boolCumApprox_succ_eq m k n hnk, ih hnk]
    · have heq : n = k + 1 := by omega
      subst heq
      rfl

theorem boolFromMoments_fixed (m : Series) :
    boolFromMoments m = boolCumStep m (boolFromMoments m) := by
  ext n
  cases n with
  | zero => rfl
  | succ d =>
    change boolCumApprox m (d + 1) (d + 1) = boolCumStep m (boolFromMoments m) (d + 1)
    simp only [boolCumApprox]
    apply boolCumStep_congr_lt
    intro r hr
    exact boolCumApprox_ge_eq m d (by omega)

theorem boolFromMoments_zero (m : Series) : boolFromMoments m 0 = 0 := rfl

theorem momentsFromBool_zero (b : Series) : momentsFromBool b 0 = 1 := rfl

theorem boolCumStep_iff_boolStep {m b : Series} (hm : m 0 = 1) (hb : b 0 = 0) :
    b = boolCumStep m b ↔ m = boolStep b m := by
  constructor
  · intro h
    ext n
    cases n with
    | zero => exact hm
    | succ d =>
      have hd := congrFun h (d + 1)
      simp only [boolCumStep, boolStep, Nat.succ_ne_zero, ↓reduceIte, Nat.add_sub_cancel,
        rangeSum, Nat.sub_self, hm, Int.mul_one] at hd ⊢
      omega
  · intro h
    ext n
    cases n with
    | zero => exact hb
    | succ d =>
      have hd := congrFun h (d + 1)
      simp only [boolCumStep, boolStep, Nat.succ_ne_zero, ↓reduceIte, Nat.add_sub_cancel,
        rangeSum, Nat.sub_self, hm, Int.mul_one] at hd ⊢
      omega

theorem momentsFromBool_boolFromMoments {m : Series} (hm : m 0 = 1) :
    momentsFromBool (boolFromMoments m) = m := by
  have hm' : m = boolStep (boolFromMoments m) m :=
    (boolCumStep_iff_boolStep hm (boolFromMoments_zero m)).mp (boolFromMoments_fixed m)
  exact boolStep_unique (boolFromMoments m) (momentsFromBool (boolFromMoments m)) m
    (momentsFromBool_fixed (boolFromMoments m)) hm'

theorem boolCumStep_unique (m b₁ b₂ : Series)
    (h₁ : b₁ = boolCumStep m b₁) (h₂ : b₂ = boolCumStep m b₂) : b₁ = b₂ := by
  ext n
  have hall : ∀ k, k ≤ n → b₁ k = b₂ k := by
    induction n with
    | zero =>
      intro k hk
      have hk0 : k = 0 := by omega
      subst hk0
      have e₁ := congrFun h₁ 0
      have e₂ := congrFun h₂ 0
      rw [e₁, e₂]
      rfl
    | succ d ih =>
      intro k hk
      by_cases hkd : k ≤ d
      · exact ih k hkd
      · have hkeq : k = d + 1 := by omega
        subst hkeq
        have e₁ := congrFun h₁ (d + 1)
        have e₂ := congrFun h₂ (d + 1)
        rw [e₁, e₂]
        apply boolCumStep_congr_lt
        intro r hr
        exact ih r (by omega)
  exact hall n (Nat.le_refl n)

theorem boolFromMoments_momentsFromBool {b : Series} (hb : b 0 = 0) :
    boolFromMoments (momentsFromBool b) = b := by
  have hb' : b = boolCumStep (momentsFromBool b) b :=
    (boolCumStep_iff_boolStep (momentsFromBool_zero b) hb).mpr (momentsFromBool_fixed b)
  exact boolCumStep_unique (momentsFromBool b) (boolFromMoments (momentsFromBool b)) b
    (boolFromMoments_fixed (momentsFromBool b)) hb'

/-- Exact generating-function identity `(1 - B(z)) * M(z) = 1` for `B = boolFromMoments M`. -/
theorem boolGenEq_boolFromMoments {m : Series} (hm : m 0 = 1) :
    BoolGenEq m (boolFromMoments m) := by
  have h := boolGenEq_momentsFromBool (boolFromMoments m) (boolFromMoments_zero m)
  rw [momentsFromBool_boolFromMoments hm] at h
  exact h

/-! ### Free Cumulant ↔ Moment Bijection and Exact Composition Equation `M(z) = C(z * M(z))` -/

def freeStep (k m : Series) : Series :=
  fun n => if n = 0 then 1 else rangeSum n (fun i => k (i + 1) * (pow m (i + 1)) (n - 1 - i))

def freeApprox (k : Series) : Nat → Series
  | 0 => one
  | s + 1 => freeStep k (freeApprox k s)

/-- Moment generating series `M(z)` constructed from free cumulant series `k(w)` (`k(0) = 0`),
    where `C(w) = 1 + k(w)`. -/
def momentsFromFree (k : Series) : Series :=
  fun n => freeApprox k n n

theorem freeStep_congr_lt (k : Series) {m₁ m₂ : Series} {n : Nat}
    (h : ∀ r, r < n → m₁ r = m₂ r) : freeStep k m₁ n = freeStep k m₂ n := by
  cases n with
  | zero => rfl
  | succ d =>
    simp only [freeStep, Nat.succ_ne_zero, ↓reduceIte, Nat.add_sub_cancel]
    apply rangeSum_congr
    intro i hi
    apply congrArg (k (i + 1) * ·)
    apply pow_congr_le
    intro r hr
    exact h r (by omega)

theorem freeApprox_succ_eq (k : Series) :
    ∀ s n, n ≤ s → freeApprox k (s + 1) n = freeApprox k s n
  | 0, n, hn => by
    have h0 : n = 0 := by omega
    subst h0
    rfl
  | s + 1, n, hn => by
    simp only [freeApprox]
    apply freeStep_congr_lt
    intro r hr
    exact freeApprox_succ_eq k s r (by omega)

theorem freeApprox_ge_eq (k : Series) {n : Nat} :
    ∀ s, n ≤ s → freeApprox k s n = momentsFromFree k n := by
  intro s hs
  induction s with
  | zero =>
    have h0 : n = 0 := by omega
    subst h0
    rfl
  | succ j ih =>
    by_cases hnj : n ≤ j
    · rw [freeApprox_succ_eq k j n hnj, ih hnj]
    · have heq : n = j + 1 := by omega
      subst heq
      rfl

theorem momentsFromFree_fixed (k : Series) :
    momentsFromFree k = freeStep k (momentsFromFree k) := by
  ext n
  cases n with
  | zero => rfl
  | succ d =>
    change freeApprox k (d + 1) (d + 1) = freeStep k (momentsFromFree k) (d + 1)
    simp only [freeApprox]
    apply freeStep_congr_lt
    intro r hr
    exact freeApprox_ge_eq k d (by omega)

theorem momentsFromFree_zero (k : Series) : momentsFromFree k 0 = 1 := rfl

theorem freeStep_unique (k m₁ m₂ : Series)
    (h₁ : m₁ = freeStep k m₁) (h₂ : m₂ = freeStep k m₂) : m₁ = m₂ := by
  ext n
  have hall : ∀ j, j ≤ n → m₁ j = m₂ j := by
    induction n with
    | zero =>
      intro j hj
      have hj0 : j = 0 := by omega
      subst hj0
      have e₁ := congrFun h₁ 0
      have e₂ := congrFun h₂ 0
      rw [e₁, e₂]
      rfl
    | succ d ih =>
      intro j hj
      by_cases hjd : j ≤ d
      · exact ih j hjd
      · have hjeq : j = d + 1 := by omega
        subst hjeq
        have e₁ := congrFun h₁ (d + 1)
        have e₂ := congrFun h₂ (d + 1)
        rw [e₁, e₂]
        apply freeStep_congr_lt
        intro r hr
        exact ih r (by omega)
  exact hall n (Nat.le_refl n)

/-- Exact formal-composition theorem `M(z) = C(z * M(z))` for `M = momentsFromFree k`
    and `C = 1 + k` (`k(0) = 0`). -/
theorem freeGenEq_momentsFromFree (k : Series) (hk : k 0 = 0) :
    FreeGenEq (momentsFromFree k) (add one k) := by
  unfold FreeGenEq
  ext n
  have hfix := congrFun (momentsFromFree_fixed k) n
  cases n with
  | zero =>
    simp [compZeroConst, rangeSum, add, one, hk, pow, freeStep] at hfix ⊢
    exact hfix
  | succ d =>
    simp only [compZeroConst]
    rw [rangeSum_succ_left (d + 1)]
    have hp0 : (add one k 0) * (pow (shift (momentsFromFree k)) 0) (d + 1) = 0 := by
      simp [add, one, hk, pow]
    rw [hp0, Int.zero_add]
    simp only [freeStep, Nat.succ_ne_zero, ↓reduceIte, Nat.add_sub_cancel] at hfix
    rw [hfix]
    apply rangeSum_congr
    intro i hi
    have hai : add one k (i + 1) = k (i + 1) := by simp [add, one]
    rw [hai]
    have hsplit : d + 1 = (i + 1) + (d - i) := by omega
    rw [hsplit, pow_shift_add (momentsFromFree k) (i + 1) (d - i)]

def freeCumStep (m k : Series) : Series :=
  fun n => if n = 0 then 0 else m n - rangeSum (n - 1) (fun i => k (i + 1) * (pow m (i + 1)) (n - 1 - i))

def freeCumApprox (m : Series) : Nat → Series
  | 0 => zero
  | s + 1 => freeCumStep m (freeCumApprox m s)

/-- Free cumulant series `k(w)` (`k(0) = 0`) extracted from a moment series `M(z)` (`M(0) = 1`). -/
def freeFromMoments (m : Series) : Series :=
  fun n => freeCumApprox m n n

theorem freeCumStep_congr_lt (m : Series) {k₁ k₂ : Series} {n : Nat}
    (h : ∀ r, r < n → k₁ r = k₂ r) : freeCumStep m k₁ n = freeCumStep m k₂ n := by
  cases n with
  | zero => rfl
  | succ d =>
    simp only [freeCumStep, Nat.succ_ne_zero, ↓reduceIte, Nat.add_sub_cancel]
    apply congrArg (m (d + 1) - ·)
    apply rangeSum_congr
    intro i hi
    rw [h (i + 1) (by omega)]

theorem freeCumApprox_succ_eq (m : Series) :
    ∀ s n, n ≤ s → freeCumApprox m (s + 1) n = freeCumApprox m s n
  | 0, n, hn => by
    have h0 : n = 0 := by omega
    subst h0
    rfl
  | s + 1, n, hn => by
    simp only [freeCumApprox]
    apply freeCumStep_congr_lt
    intro r hr
    exact freeCumApprox_succ_eq m s r (by omega)

theorem freeCumApprox_ge_eq (m : Series) {n : Nat} :
    ∀ s, n ≤ s → freeCumApprox m s n = freeFromMoments m n := by
  intro s hs
  induction s with
  | zero =>
    have h0 : n = 0 := by omega
    subst h0
    rfl
  | succ j ih =>
    by_cases hnj : n ≤ j
    · rw [freeCumApprox_succ_eq m j n hnj, ih hnj]
    · have heq : n = j + 1 := by omega
      subst heq
      rfl

theorem freeFromMoments_fixed (m : Series) :
    freeFromMoments m = freeCumStep m (freeFromMoments m) := by
  ext n
  cases n with
  | zero => rfl
  | succ d =>
    change freeCumApprox m (d + 1) (d + 1) = freeCumStep m (freeFromMoments m) (d + 1)
    simp only [freeCumApprox]
    apply freeCumStep_congr_lt
    intro r hr
    exact freeCumApprox_ge_eq m d (by omega)

theorem freeFromMoments_zero (m : Series) : freeFromMoments m 0 = 0 := rfl

theorem freeCumStep_iff_freeStep {m k : Series} (hm : m 0 = 1) (hk : k 0 = 0) :
    k = freeCumStep m k ↔ m = freeStep k m := by
  constructor
  · intro h
    ext n
    cases n with
    | zero => exact hm
    | succ d =>
      have hd := congrFun h (d + 1)
      simp only [freeCumStep, freeStep, Nat.succ_ne_zero, ↓reduceIte, Nat.add_sub_cancel,
        rangeSum, Nat.sub_self, pow_zero_coeff_of_unit hm, Int.mul_one] at hd ⊢
      omega
  · intro h
    ext n
    cases n with
    | zero => exact hk
    | succ d =>
      have hd := congrFun h (d + 1)
      simp only [freeCumStep, freeStep, Nat.succ_ne_zero, ↓reduceIte, Nat.add_sub_cancel,
        rangeSum, Nat.sub_self, pow_zero_coeff_of_unit hm, Int.mul_one] at hd ⊢
      omega

theorem momentsFromFree_freeFromMoments {m : Series} (hm : m 0 = 1) :
    momentsFromFree (freeFromMoments m) = m := by
  have hm' : m = freeStep (freeFromMoments m) m :=
    (freeCumStep_iff_freeStep hm (freeFromMoments_zero m)).mp (freeFromMoments_fixed m)
  exact freeStep_unique (freeFromMoments m) (momentsFromFree (freeFromMoments m)) m
    (momentsFromFree_fixed (freeFromMoments m)) hm'

theorem freeCumStep_unique (m k₁ k₂ : Series)
    (h₁ : k₁ = freeCumStep m k₁) (h₂ : k₂ = freeCumStep m k₂) : k₁ = k₂ := by
  ext n
  have hall : ∀ j, j ≤ n → k₁ j = k₂ j := by
    induction n with
    | zero =>
      intro j hj
      have hj0 : j = 0 := by omega
      subst hj0
      have e₁ := congrFun h₁ 0
      have e₂ := congrFun h₂ 0
      rw [e₁, e₂]
      rfl
    | succ d ih =>
      intro j hj
      by_cases hjd : j ≤ d
      · exact ih j hjd
      · have hjeq : j = d + 1 := by omega
        subst hjeq
        have e₁ := congrFun h₁ (d + 1)
        have e₂ := congrFun h₂ (d + 1)
        rw [e₁, e₂]
        apply freeCumStep_congr_lt
        intro r hr
        exact ih r (by omega)
  exact hall n (Nat.le_refl n)

theorem freeFromMoments_momentsFromFree {k : Series} (hk : k 0 = 0) :
    freeFromMoments (momentsFromFree k) = k := by
  have hk' : k = freeCumStep (momentsFromFree k) k :=
    (freeCumStep_iff_freeStep (momentsFromFree_zero k) hk).mpr (momentsFromFree_fixed k)
  exact freeCumStep_unique (momentsFromFree k) (freeFromMoments (momentsFromFree k)) k
    (freeFromMoments_fixed (momentsFromFree k)) hk'

/-- Exact composition generating-function equation `M(z) = C(z * M(z))` for any normalized `M`. -/
theorem freeGenEq_freeFromMoments {m : Series} (hm : m 0 = 1) :
    FreeGenEq m (add one (freeFromMoments m)) := by
  have h := freeGenEq_momentsFromFree (freeFromMoments m) (freeFromMoments_zero m)
  rw [momentsFromFree_freeFromMoments hm] at h
  exact h

/-! ### Boolean Convolution `⊎`, Free Convolution `⊞`, and Bercovici–Pata Bijection `𝔹₁` -/

/-- Speicher–Woroudi Boolean additive convolution `m₁ ⊎ m₂` on moment generating series. -/
def boolConv (m₁ m₂ : Series) : Series :=
  momentsFromBool (add (boolFromMoments m₁) (boolFromMoments m₂))

/-- Voiculescu free additive convolution `m₁ ⊞ m₂` on moment generating series. -/
def freeConv (m₁ m₂ : Series) : Series :=
  momentsFromFree (add (freeFromMoments m₁) (freeFromMoments m₂))

/-- Boolean-to-free Bercovici–Pata / Belinschi–Nica bijection `𝔹₁`:
    maps `μ` to the unique distribution `𝔹₁(μ)` whose free cumulants equal `β_n(μ)`. -/
def bercoviciPataBF (m : Series) : Series :=
  momentsFromFree (boolFromMoments m)

/-- Inverse free-to-Boolean Bercovici–Pata bijection `𝔹₁⁻¹`:
    maps `ν` to the unique distribution whose Boolean cumulants equal `κ_n(ν)`. -/
def bercoviciPataFB (m : Series) : Series :=
  momentsFromBool (freeFromMoments m)

theorem bercoviciPata_left_inv {m : Series} (hm : m 0 = 1) :
    bercoviciPataFB (bercoviciPataBF m) = m := by
  unfold bercoviciPataFB bercoviciPataBF
  rw [freeFromMoments_momentsFromFree (boolFromMoments_zero m),
      momentsFromBool_boolFromMoments hm]

theorem bercoviciPata_right_inv {m : Series} (hm : m 0 = 1) :
    bercoviciPataBF (bercoviciPataFB m) = m := by
  unfold bercoviciPataFB bercoviciPataBF
  rw [boolFromMoments_momentsFromBool (freeFromMoments_zero m),
      momentsFromFree_freeFromMoments hm]

/-- Exact convolution homomorphism property of `𝔹₁`:
    `𝔹₁(m₁ ⊎ m₂) = 𝔹₁(m₁) ⊞ 𝔹₁(m₂)` as entire formal power series. -/
theorem bercoviciPataBF_hom (m₁ m₂ : Series) :
    bercoviciPataBF (boolConv m₁ m₂) = freeConv (bercoviciPataBF m₁) (bercoviciPataBF m₂) := by
  unfold bercoviciPataBF boolConv freeConv
  have h0 : add (boolFromMoments m₁) (boolFromMoments m₂) 0 = 0 := by
    simp [add, boolFromMoments_zero]
  rw [boolFromMoments_momentsFromBool h0,
      freeFromMoments_momentsFromFree (boolFromMoments_zero m₁),
      freeFromMoments_momentsFromFree (boolFromMoments_zero m₂)]

end BooleanFreeConv
