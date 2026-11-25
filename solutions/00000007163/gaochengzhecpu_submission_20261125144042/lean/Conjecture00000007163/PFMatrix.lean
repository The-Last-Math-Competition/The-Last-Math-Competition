/-
  Conjecture 00000007163 — Core Lean 4.19.0 Formalization
  File: Conjecture00000007163/PFMatrix.lean

  First-principles development of:
  1. Gaussian integers `GaussInt` (ℤ[i]), squared modulus `normSq`, and weighted
     convex-combination norm bounds without external dependencies.
  2. Finite sums/products over `Fin n`, integer `n × n` matrices `IMat n`,
     matrix multiplication, matrix powers `matPow`, recursive Laplace cofactor
     determinants `det`, and characteristic polynomial evaluation `charPolyEval`.
  3. Perron–Frobenius structural predicates (`IsNonneg`, `IsStrictlyPositive`,
     `IsIrreducible`, `IsPrimitive`, `HasSingleEssentialClass`,
     `IsBlockSupportedPrimitive`) and positivity moduli (`posModulusMin`,
     `doeblinModulus`, `entryMax`).
-/

namespace Conjecture00000007163

/-! ## 1. Elementary Integer Arithmetic Lemmas -/

theorem int_mul_self_mul_self (x y : Int) : (x * x) * (y * y) = (x * y) * (x * y) := by
  calc
    (x * x) * (y * y) = x * (x * (y * y)) := Int.mul_assoc x x (y * y)
    _ = x * ((x * y) * y) := by rw [← Int.mul_assoc x y y]
    _ = x * ((y * x) * y) := by rw [Int.mul_comm x y]
    _ = x * (y * (x * y)) := by rw [Int.mul_assoc y x y]
    _ = (x * y) * (x * y) := by rw [← Int.mul_assoc x y (x * y)]

theorem int_sq_nonneg (a : Int) : 0 ≤ a * a := by
  by_cases h : 0 ≤ a
  · exact Int.mul_nonneg h h
  · have hn : 0 ≤ -a := by omega
    have heq : (-a) * (-a) = a * a := by rw [Int.neg_mul_neg]
    rw [← heq]
    exact Int.mul_nonneg hn hn

theorem int_sq_pos_of_ne_zero {a : Int} (h : a ≠ 0) : 0 < a * a := by
  by_cases hp : 0 < a
  · exact Int.mul_pos hp hp
  · have hn : 0 < -a := by omega
    have heq : (-a) * (-a) = a * a := by rw [Int.neg_mul_neg]
    rw [← heq]
    exact Int.mul_pos hn hn

theorem int_le_of_sq_le_sq {a b : Int} (hb : 0 ≤ b) (h : a * a ≤ b * b) : a ≤ b := by
  by_cases hab : a ≤ b
  · exact hab
  · exfalso
    have hgt : b < a := by omega
    have ha : 0 < a := by omega
    by_cases hb0 : b = 0
    · subst hb0
      have hapos : 0 < a * a := Int.mul_pos ha ha
      omega
    · have hbp : 0 < b := by omega
      have hlt1 : b * b < a * b := Int.mul_lt_mul_of_pos_right hgt hbp
      have hle2 : a * b ≤ a * a :=
        Int.mul_le_mul (Int.le_refl a) (by omega) hb (by omega)
      omega

theorem int_lt_of_sq_lt_sq {a b : Int} (hb : 0 ≤ b) (h : a * a < b * b) : a < b := by
  by_cases hab : a < b
  · exact hab
  · exfalso
    have hge : b ≤ a := by omega
    have hsq : b * b ≤ a * a := Int.mul_le_mul hge hge hb (by omega)
    omega

theorem int_sq_lt_sq {a b : Int} (ha : 0 ≤ a) (h : a < b) : a * a < b * b := by
  by_cases ha0 : a = 0
  · subst ha0
    have hb : 0 < b := by omega
    have hbb : 0 < b * b := Int.mul_pos hb hb
    omega
  · have hap : 0 < a := by omega
    have hbp : 0 < b := by omega
    have h1 : a * a < a * b := Int.mul_lt_mul_of_pos_left h hap
    have h2 : a * b < b * b := Int.mul_lt_mul_of_pos_right h hbp
    omega

theorem int_sq_le_sq {a b : Int} (ha : 0 ≤ a) (h : a ≤ b) : a * a ≤ b * b :=
  Int.mul_le_mul h h ha (by omega)

/-! ## 2. Gaussian Integers `GaussInt` (ℤ[i]) and Convex-Combination Norm Bounds -/

structure GaussInt where
  re : Int
  im : Int
  deriving DecidableEq, Repr

namespace GaussInt

def ofInt (n : Int) : GaussInt := ⟨n, 0⟩
def zero : GaussInt := ⟨0, 0⟩

def add (z w : GaussInt) : GaussInt := ⟨z.re + w.re, z.im + w.im⟩
def sub (z w : GaussInt) : GaussInt := ⟨z.re - w.re, z.im - w.im⟩
def neg (z : GaussInt) : GaussInt := ⟨-z.re, -z.im⟩
def mul (z w : GaussInt) : GaussInt :=
  ⟨z.re * w.re - z.im * w.im, z.re * w.im + z.im * w.re⟩
def scale (c : Int) (z : GaussInt) : GaussInt := ⟨c * z.re, c * z.im⟩

instance : Add GaussInt := ⟨add⟩
instance : Sub GaussInt := ⟨sub⟩
instance : Neg GaussInt := ⟨neg⟩
instance : Mul GaussInt := ⟨mul⟩

def normSq (z : GaussInt) : Int := z.re * z.re + z.im * z.im

@[ext]
theorem ext {z w : GaussInt} (hre : z.re = w.re) (him : z.im = w.im) : z = w := by
  cases z; cases w; simp_all

theorem scale_scale (a b : Int) (z : GaussInt) :
    scale a (scale b z) = scale (a * b) z := by
  apply ext
  · change a * (b * z.re) = (a * b) * z.re; rw [Int.mul_assoc]
  · change a * (b * z.im) = (a * b) * z.im; rw [Int.mul_assoc]

theorem scale_add (c : Int) (z w : GaussInt) :
    scale c (z + w) = scale c z + scale c w := by
  apply ext
  · change c * (z.re + w.re) = c * z.re + c * w.re; rw [Int.mul_add]
  · change c * (z.im + w.im) = c * z.im + c * w.im; rw [Int.mul_add]

theorem scale_sub (c : Int) (z w : GaussInt) :
    scale c (z - w) = scale c z - scale c w := by
  apply ext
  · change c * (z.re - w.re) = c * z.re - c * w.re; rw [Int.mul_sub]
  · change c * (z.im - w.im) = c * z.im - c * w.im; rw [Int.mul_sub]

theorem sub_scale (a b : Int) (z : GaussInt) :
    scale (a - b) z = scale a z - scale b z := by
  apply ext
  · change (a - b) * z.re = a * z.re - b * z.re; rw [Int.sub_mul]
  · change (a - b) * z.im = a * z.im - b * z.im; rw [Int.sub_mul]

theorem mul_scale_right (lam : GaussInt) (c : Int) (z : GaussInt) :
    lam * scale c z = scale c (lam * z) := by
  apply ext
  · change lam.re * (c * z.re) - lam.im * (c * z.im) = c * (lam.re * z.re - lam.im * z.im)
    rw [Int.mul_sub, ← Int.mul_assoc lam.re c z.re, Int.mul_comm lam.re c, Int.mul_assoc c lam.re z.re,
        ← Int.mul_assoc lam.im c z.im, Int.mul_comm lam.im c, Int.mul_assoc c lam.im z.im]
  · change lam.re * (c * z.im) + lam.im * (c * z.re) = c * (lam.re * z.im + lam.im * z.re)
    rw [Int.mul_add, ← Int.mul_assoc lam.re c z.im, Int.mul_comm lam.re c, Int.mul_assoc c lam.re z.im,
        ← Int.mul_assoc lam.im c z.re, Int.mul_comm lam.im c, Int.mul_assoc c lam.im z.re]

theorem mul_sub_right (lam z w : GaussInt) :
    lam * (z - w) = lam * z - lam * w := by
  apply ext
  · change lam.re * (z.re - w.re) - lam.im * (z.im - w.im) =
           (lam.re * z.re - lam.im * z.im) - (lam.re * w.re - lam.im * w.im)
    rw [Int.mul_sub, Int.mul_sub]
    omega
  · change lam.re * (z.im - w.im) + lam.im * (z.re - w.re) =
           (lam.re * z.im + lam.im * z.re) - (lam.re * w.im + lam.im * w.re)
    rw [Int.mul_sub, Int.mul_sub]
    omega

theorem sub_mul_left (a b z : GaussInt) :
    (a - b) * z = a * z - b * z := by
  apply ext
  · change (a.re - b.re) * z.re - (a.im - b.im) * z.im =
           (a.re * z.re - a.im * z.im) - (b.re * z.re - b.im * z.im)
    rw [Int.sub_mul, Int.sub_mul]
    omega
  · change (a.re - b.re) * z.im + (a.im - b.im) * z.re =
           (a.re * z.im + a.im * z.re) - (b.re * z.im + b.im * z.re)
    rw [Int.sub_mul, Int.sub_mul]
    omega

theorem sub_self (z : GaussInt) : z - z = zero := by
  apply ext
  · change z.re - z.re = 0; omega
  · change z.im - z.im = 0; omega

theorem ofInt_mul (c : Int) (z : GaussInt) :
    ofInt c * z = scale c z := by
  apply ext
  · change c * z.re - 0 * z.im = c * z.re; omega
  · change c * z.im + 0 * z.re = c * z.im; omega

theorem normSq_nonneg (z : GaussInt) : 0 ≤ normSq z := by
  unfold normSq
  have h1 := int_sq_nonneg z.re
  have h2 := int_sq_nonneg z.im
  omega

theorem normSq_pos_of_ne_zero {z : GaussInt} (h : z ≠ zero) : 0 < normSq z := by
  unfold normSq
  by_cases hre : z.re = 0
  · have him : z.im ≠ 0 := by
      intro him0
      exact h (ext hre him0)
    have h2 := int_sq_pos_of_ne_zero him
    have h1 : z.re * z.re = 0 := by rw [hre]; rfl
    omega
  · have h1 := int_sq_pos_of_ne_zero hre
    have h2 := int_sq_nonneg z.im
    omega

theorem sub_ne_zero_of_ne {z w : GaussInt} (h : z ≠ w) : z - w ≠ zero := by
  intro h0
  apply h
  have hre : z.re - w.re = 0 := congrArg GaussInt.re h0
  have him : z.im - w.im = 0 := congrArg GaussInt.im h0
  exact ext (by omega) (by omega)

theorem normSq_sub_symm (z w : GaussInt) : normSq (z - w) = normSq (w - z) := by
  change (z.re - w.re) * (z.re - w.re) + (z.im - w.im) * (z.im - w.im) =
         (w.re - z.re) * (w.re - z.re) + (w.im - z.im) * (w.im - z.im)
  have h1 : w.re - z.re = -(z.re - w.re) := by omega
  have h2 : w.im - z.im = -(z.im - w.im) := by omega
  rw [h1, h2, Int.neg_mul_neg, Int.neg_mul_neg]

theorem normSq_scale (c : Int) (z : GaussInt) :
    normSq (scale c z) = (c * c) * normSq z := by
  change (c * z.re) * (c * z.re) + (c * z.im) * (c * z.im) =
         (c * c) * (z.re * z.re + z.im * z.im)
  rw [Int.mul_add, ← int_mul_self_mul_self c z.re, ← int_mul_self_mul_self c z.im]

theorem normSq_mul (z w : GaussInt) : normSq (z * w) = normSq z * normSq w := by
  rcases z with ⟨a, b⟩
  rcases w with ⟨c, d⟩
  change (a * c - b * d) * (a * c - b * d) + (a * d + b * c) * (a * d + b * c) =
         (a * a + b * b) * (c * c + d * d)
  have lhs1 : (a * c - b * d) * (a * c - b * d) =
      (a * c) * (a * c) - (a * c) * (b * d) - (b * d) * (a * c) + (b * d) * (b * d) := by
    rw [Int.mul_sub, Int.sub_mul, Int.sub_mul]; omega
  have lhs2 : (a * d + b * c) * (a * d + b * c) =
      (a * d) * (a * d) + (a * d) * (b * c) + (b * c) * (a * d) + (b * c) * (b * c) := by
    rw [Int.mul_add, Int.add_mul, Int.add_mul]; omega
  have rhs : (a * a + b * b) * (c * c + d * d) =
      (a * a) * (c * c) + (a * a) * (d * d) + (b * b) * (c * c) + (b * b) * (d * d) := by
    rw [Int.add_mul, Int.mul_add, Int.mul_add]; omega
  have m1 := (int_mul_self_mul_self a c).symm
  have m2 := (int_mul_self_mul_self b d).symm
  have m3 := (int_mul_self_mul_self a d).symm
  have m4 := (int_mul_self_mul_self b c).symm
  have c1 : (a * c) * (b * d) = (a * d) * (b * c) := by
    calc
      (a * c) * (b * d) = a * (c * (b * d)) := Int.mul_assoc _ _ _
      _ = a * ((c * b) * d) := by rw [← Int.mul_assoc c b d]
      _ = a * ((b * c) * d) := by rw [Int.mul_comm c b]
      _ = a * (b * (c * d)) := by rw [Int.mul_assoc b c d]
      _ = a * (b * (d * c)) := by rw [Int.mul_comm c d]
      _ = a * ((b * d) * c) := by rw [← Int.mul_assoc b d c]
      _ = a * ((d * b) * c) := by rw [Int.mul_comm b d]
      _ = a * (d * (b * c)) := by rw [Int.mul_assoc d b c]
      _ = (a * d) * (b * c) := by rw [← Int.mul_assoc a d (b * c)]
  have c2 : (b * d) * (a * c) = (b * c) * (a * d) := by
    rw [Int.mul_comm (b * d) (a * c), Int.mul_comm (b * c) (a * d), c1]
  rw [lhs1, lhs2, rhs, m1, m2, m3, m4, c1, c2]
  omega

/-- Cauchy–Schwarz inner-product bound over `GaussInt`. -/
theorem inner_sq_le_normSq_mul (z w : GaussInt) :
    (z.re * w.re + z.im * w.im) * (z.re * w.re + z.im * w.im) ≤ normSq z * normSq w := by
  have hlag : normSq z * normSq w =
      (z.re * w.re + z.im * w.im) * (z.re * w.re + z.im * w.im) +
      (z.re * w.im - z.im * w.re) * (z.re * w.im - z.im * w.re) := by
    have hconj : normSq ⟨z.re, -z.im⟩ = normSq z := by
      change z.re * z.re + (-z.im) * (-z.im) = z.re * z.re + z.im * z.im
      rw [Int.neg_mul_neg]
    have hprod : (⟨z.re, -z.im⟩ : GaussInt) * w =
        ⟨z.re * w.re + z.im * w.im, z.re * w.im - z.im * w.re⟩ := by
      apply ext
      · change z.re * w.re - (-z.im) * w.im = z.re * w.re + z.im * w.im
        rw [Int.neg_mul]; omega
      · change z.re * w.im + (-z.im) * w.re = z.re * w.im - z.im * w.re
        rw [Int.neg_mul]; omega
    have hm2 := normSq_mul ⟨z.re, -z.im⟩ w
    rw [hconj, hprod] at hm2
    exact hm2.symm
  have hnn := int_sq_nonneg (z.re * w.im - z.im * w.re)
  omega

/-- Inductive step for weighted convex-combination norm bounds over `GaussInt`. -/
theorem normSq_add_le_of_bounds (z₁ z₂ : GaussInt) (s₁ s₂ D : Int)
    (hs₁ : 0 ≤ s₁) (hs₂ : 0 ≤ s₂) (hD : 0 ≤ D)
    (h₁ : normSq z₁ ≤ s₁ * s₁ * D) (h₂ : normSq z₂ ≤ s₂ * s₂ * D) :
    normSq (z₁ + z₂) ≤ (s₁ + s₂) * (s₁ + s₂) * D := by
  have hexp : normSq (z₁ + z₂) =
      normSq z₁ + normSq z₂ + 2 * (z₁.re * z₂.re + z₁.im * z₂.im) := by
    change (z₁.re + z₂.re) * (z₁.re + z₂.re) + (z₁.im + z₂.im) * (z₁.im + z₂.im) =
           (z₁.re * z₁.re + z₁.im * z₁.im) + (z₂.re * z₂.re + z₂.im * z₂.im) +
           2 * (z₁.re * z₂.re + z₁.im * z₂.im)
    rw [Int.mul_add, Int.add_mul, Int.add_mul,
        Int.mul_add, Int.add_mul, Int.add_mul]
    have c1 : z₂.re * z₁.re = z₁.re * z₂.re := Int.mul_comm _ _
    have c2 : z₂.im * z₁.im = z₁.im * z₂.im := Int.mul_comm _ _
    omega
  have hrhs : (s₁ + s₂) * (s₁ + s₂) * D =
      s₁ * s₁ * D + s₂ * s₂ * D + 2 * (s₁ * s₂ * D) := by
    have hss : (s₁ + s₂) * (s₁ + s₂) = s₁ * s₁ + s₂ * s₂ + 2 * (s₁ * s₂) := by
      rw [Int.mul_add, Int.add_mul, Int.add_mul, Int.mul_comm s₂ s₁]; omega
    rw [hss, Int.add_mul, Int.add_mul, Int.mul_assoc 2 (s₁ * s₂) D]
  have hinner : z₁.re * z₂.re + z₁.im * z₂.im ≤ s₁ * s₂ * D := by
    have hbnd : 0 ≤ s₁ * s₂ * D :=
      Int.mul_nonneg (Int.mul_nonneg hs₁ hs₂) hD
    by_cases hpos : z₁.re * z₂.re + z₁.im * z₂.im ≤ 0
    · omega
    · apply int_le_of_sq_le_sq hbnd
      have hcs := inner_sq_le_normSq_mul z₁ z₂
      have hmul : normSq z₁ * normSq z₂ ≤ (s₁ * s₁ * D) * (s₂ * s₂ * D) :=
        Int.mul_le_mul h₁ h₂ (normSq_nonneg z₂)
          (Int.mul_nonneg (Int.mul_nonneg hs₁ hs₁) hD)
      have hrew : (s₁ * s₁ * D) * (s₂ * s₂ * D) = (s₁ * s₂ * D) * (s₁ * s₂ * D) := by
        have p1 : (s₁ * s₁ * D) * (s₂ * s₂ * D) = ((s₁ * s₁) * (s₂ * s₂)) * (D * D) := by
          calc
            (s₁ * s₁ * D) * (s₂ * s₂ * D) = (s₁ * s₁) * (D * ((s₂ * s₂) * D)) := Int.mul_assoc _ _ _
            _ = (s₁ * s₁) * ((D * (s₂ * s₂)) * D) := by rw [← Int.mul_assoc D (s₂ * s₂) D]
            _ = (s₁ * s₁) * (((s₂ * s₂) * D) * D) := by rw [Int.mul_comm D (s₂ * s₂)]
            _ = (s₁ * s₁) * ((s₂ * s₂) * (D * D)) := by rw [Int.mul_assoc (s₂ * s₂) D D]
            _ = ((s₁ * s₁) * (s₂ * s₂)) * (D * D) := by rw [← Int.mul_assoc (s₁ * s₁) (s₂ * s₂) (D * D)]
        rw [p1, int_mul_self_mul_self s₁ s₂, int_mul_self_mul_self (s₁ * s₂) D]
      rw [hrew] at hmul
      exact Int.le_trans hcs hmul
  omega

end GaussInt

/-! ## 3. Finite Sums and Products over `Fin n` -/

def finSum : (n : Nat) → (Fin n → Int) → Int
  | 0, _ => 0
  | n + 1, f => finSum n (fun i => f ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩) + f ⟨n, Nat.lt_succ_self n⟩

def finProd : (n : Nat) → (Fin n → Int) → Int
  | 0, _ => 1
  | n + 1, f => finProd n (fun i => f ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩) * f ⟨n, Nat.lt_succ_self n⟩

def cFinSum : (n : Nat) → (Fin n → GaussInt) → GaussInt
  | 0, _ => GaussInt.zero
  | n + 1, f =>
      cFinSum n (fun i => f ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩) + f ⟨n, Nat.lt_succ_self n⟩

theorem finSum_congr {n : Nat} {f g : Fin n → Int} (h : ∀ i, f i = g i) :
    finSum n f = finSum n g := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [finSum]
    rw [ih (fun i => h _), h _]

theorem finProd_congr {n : Nat} {f g : Fin n → Int} (h : ∀ i, f i = g i) :
    finProd n f = finProd n g := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [finProd]
    rw [ih (fun i => h _), h _]

theorem cFinSum_congr {n : Nat} {f g : Fin n → GaussInt} (h : ∀ i, f i = g i) :
    cFinSum n f = cFinSum n g := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [cFinSum]
    rw [ih (fun i => h _), h _]

theorem finSum_add (n : Nat) (f g : Fin n → Int) :
    finSum n (fun i => f i + g i) = finSum n f + finSum n g := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [finSum]; rw [ih]; omega

theorem finSum_sub (n : Nat) (f g : Fin n → Int) :
    finSum n (fun i => f i - g i) = finSum n f - finSum n g := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [finSum]; rw [ih]; omega

theorem finSum_mul_left (n : Nat) (c : Int) (f : Fin n → Int) :
    finSum n (fun i => c * f i) = c * finSum n f := by
  induction n with
  | zero => simp only [finSum]; omega
  | succ n ih => simp only [finSum]; rw [ih, Int.mul_add]

theorem finSum_mul_right (n : Nat) (f : Fin n → Int) (c : Int) :
    finSum n (fun i => f i * c) = finSum n f * c := by
  induction n with
  | zero => simp only [finSum]; omega
  | succ n ih => simp only [finSum]; rw [ih, Int.add_mul]

theorem finSum_const (n : Nat) (c : Int) :
    finSum n (fun _ => c) = (n : Int) * c := by
  induction n with
  | zero => simp only [finSum]; omega
  | succ n ih =>
    simp only [finSum]
    rw [ih]
    have hn : ((n + 1 : Nat) : Int) = (n : Int) + 1 := by omega
    rw [hn, Int.add_mul]; omega

theorem finSum_nonneg {n : Nat} {f : Fin n → Int} (h : ∀ i, 0 ≤ f i) :
    0 ≤ finSum n f := by
  induction n with
  | zero => exact Int.le_refl 0
  | succ n ih =>
    simp only [finSum]
    have h1 := ih (f := fun i => f ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩)
      (fun i => h ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩)
    have h2 := h ⟨n, Nat.lt_succ_self n⟩
    omega

theorem finSum_eq_zero_of_nonneg {n : Nat} {f : Fin n → Int}
    (hf : ∀ i, 0 ≤ f i) (hsum : finSum n f = 0) :
    ∀ i, f i = 0 := by
  induction n with
  | zero => intro i; exact Fin.elim0 i
  | succ n ih =>
    simp only [finSum] at hsum
    have h1 := finSum_nonneg (n := n) (f := fun j => f ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩)
      (fun j => hf ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩)
    have h2 := hf ⟨n, Nat.lt_succ_self n⟩
    have hsum0 : finSum n (fun j => f ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩) = 0 := by omega
    have hlast0 : f ⟨n, Nat.lt_succ_self n⟩ = 0 := by omega
    intro i
    by_cases hi : i.val = n
    · have hieq : i = ⟨n, Nat.lt_succ_self n⟩ := Fin.ext hi
      rw [hieq]; exact hlast0
    · have hilt : i.val < n := by omega
      have hp := ih (f := fun j => f ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩)
        (fun j => hf ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩) hsum0 ⟨i.val, hilt⟩
      exact hp

theorem finProd_pos {n : Nat} {f : Fin n → Int} (h : ∀ i, 0 < f i) :
    0 < finProd n f := by
  induction n with
  | zero => simp [finProd]
  | succ n ih =>
    simp only [finProd]
    exact Int.mul_pos
      (ih (f := fun i => f ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩)
        (fun i => h ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩))
      (h ⟨n, Nat.lt_succ_self n⟩)

theorem finSum_le {n : Nat} {f g : Fin n → Int} (h : ∀ i, f i ≤ g i) :
    finSum n f ≤ finSum n g := by
  have hsub : 0 ≤ finSum n (fun i => g i - f i) :=
    finSum_nonneg (fun i => by have := h i; omega)
  rw [finSum_sub] at hsub
  omega

/-- Kronecker-delta sum evaluation over `Fin n`. -/
theorem finSum_ite_eq {n : Nat} (a : Fin n) (v : Int) :
    finSum n (fun j => if j = a then v else 0) = v := by
  induction n with
  | zero => exact Fin.elim0 a
  | succ m ihm =>
    simp only [finSum]
    by_cases ha : a.val = m
    · have haeq : a = ⟨m, Nat.lt_succ_self m⟩ := Fin.ext ha
      subst haeq
      have hz : finSum m (fun j : Fin m =>
          if (⟨j.val, Nat.lt_succ_of_lt j.isLt⟩ : Fin (m + 1)) = ⟨m, Nat.lt_succ_self m⟩
          then v else 0) = 0 := by
        have hc : ∀ j : Fin m,
            (if (⟨j.val, Nat.lt_succ_of_lt j.isLt⟩ : Fin (m + 1)) = ⟨m, Nat.lt_succ_self m⟩
             then v else (0 : Int)) = 0 := by
          intro j
          have hne : (⟨j.val, Nat.lt_succ_of_lt j.isLt⟩ : Fin (m + 1)) ≠ ⟨m, Nat.lt_succ_self m⟩ := by
            intro heq
            exact Nat.ne_of_lt j.isLt (Fin.mk.inj heq)
          simp [hne]
        rw [finSum_congr hc, finSum_const]
        omega
      rw [hz]
      simp
    · have halt : a.val < m := by omega
      have hlast_ne : (⟨m, Nat.lt_succ_self m⟩ : Fin (m + 1)) ≠ a := by
        intro heq
        have hval : m = a.val := congrArg Fin.val heq
        omega
      have hc : ∀ j : Fin m,
          (if (⟨j.val, Nat.lt_succ_of_lt j.isLt⟩ : Fin (m + 1)) = a then v else (0 : Int)) =
          (if j = ⟨a.val, halt⟩ then v else 0) := by
        intro j
        by_cases hj : j.val = a.val
        · have h1 : (⟨j.val, Nat.lt_succ_of_lt j.isLt⟩ : Fin (m + 1)) = a := Fin.ext hj
          have h2 : j = ⟨a.val, halt⟩ := Fin.ext hj
          simp [h1, h2]
        · have h1 : (⟨j.val, Nat.lt_succ_of_lt j.isLt⟩ : Fin (m + 1)) ≠ a :=
            fun heq => hj (congrArg Fin.val heq)
          have h2 : j ≠ ⟨a.val, halt⟩ :=
            fun heq => hj (congrArg Fin.val heq)
          simp [h1, h2]
      rw [finSum_congr hc, ihm ⟨a.val, halt⟩]
      simp [hlast_ne]

/-- Two-distinct-terms lower bound when all terms are nonnegative. -/
theorem finSum_ge_pair {n : Nat} {f : Fin n → Int} (hf : ∀ j, 0 ≤ f j)
    (i k : Fin n) (hne : i ≠ k) :
    f i + f k ≤ finSum n f := by
  let g : Fin n → Int := fun j => if j = i then 0 else if j = k then 0 else f j
  have hfg : ∀ j, f j = (if j = i then f i else 0) + (if j = k then f k else 0) + g j := by
    intro j
    by_cases hji : j = i
    · subst hji
      simp [g, hne]
    · by_cases hjk : j = k
      · subst hjk
        simp [g, hji]
      · simp [g, hji, hjk]
  have hdecomp : finSum n f =
      finSum n (fun j => if j = i then f i else 0) +
      finSum n (fun j => if j = k then f k else 0) +
      finSum n g := by
    rw [finSum_congr hfg, finSum_add, finSum_add]
  rw [hdecomp, finSum_ite_eq i (f i), finSum_ite_eq k (f k)]
  have hgnn : 0 ≤ finSum n g := by
    apply finSum_nonneg
    intro j
    dsimp [g]
    by_cases h1 : j = i
    · simp [h1]
    · by_cases h2 : j = k
      · simp [h1, h2]
      · simp [h1, h2]; exact hf j
  omega

theorem cFinSum_add (n : Nat) (f g : Fin n → GaussInt) :
    cFinSum n (fun i => f i + g i) = cFinSum n f + cFinSum n g := by
  induction n with
  | zero => apply GaussInt.ext <;> rfl
  | succ n ih =>
    simp only [cFinSum]; rw [ih]
    apply GaussInt.ext
    · change (cFinSum n _).re + (cFinSum n _).re + ((f _).re + (g _).re) =
             ((cFinSum n _).re + (f _).re) + ((cFinSum n _).re + (g _).re); omega
    · change (cFinSum n _).im + (cFinSum n _).im + ((f _).im + (g _).im) =
             ((cFinSum n _).im + (f _).im) + ((cFinSum n _).im + (g _).im); omega

theorem cFinSum_sub (n : Nat) (f g : Fin n → GaussInt) :
    cFinSum n (fun i => f i - g i) = cFinSum n f - cFinSum n g := by
  induction n with
  | zero => apply GaussInt.ext <;> rfl
  | succ n ih =>
    simp only [cFinSum]; rw [ih]
    apply GaussInt.ext
    · change (cFinSum n _).re - (cFinSum n _).re + ((f _).re - (g _).re) =
             ((cFinSum n _).re + (f _).re) - ((cFinSum n _).re + (g _).re); omega
    · change (cFinSum n _).im - (cFinSum n _).im + ((f _).im - (g _).im) =
             ((cFinSum n _).im + (f _).im) - ((cFinSum n _).im + (g _).im); omega

theorem cFinSum_scale (n : Nat) (c : Int) (f : Fin n → GaussInt) :
    cFinSum n (fun i => GaussInt.scale c (f i)) = GaussInt.scale c (cFinSum n f) := by
  induction n with
  | zero => apply GaussInt.ext <;> simp [cFinSum, GaussInt.scale, GaussInt.zero]
  | succ n ih =>
    simp only [cFinSum]; rw [ih]
    apply GaussInt.ext
    · change c * (cFinSum n _).re + c * (f _).re = c * ((cFinSum n _).re + (f _).re)
      rw [Int.mul_add]
    · change c * (cFinSum n _).im + c * (f _).im = c * ((cFinSum n _).im + (f _).im)
      rw [Int.mul_add]

theorem cFinSum_scale_vec (n : Nat) (w : Fin n → Int) (z : GaussInt) :
    cFinSum n (fun i => GaussInt.scale (w i) z) = GaussInt.scale (finSum n w) z := by
  induction n with
  | zero => apply GaussInt.ext <;> simp [cFinSum, finSum, GaussInt.scale, GaussInt.zero]
  | succ n ih =>
    simp only [cFinSum, finSum]; rw [ih]
    apply GaussInt.ext
    · change finSum n _ * z.re + w _ * z.re = (finSum n _ + w _) * z.re
      rw [Int.add_mul]
    · change finSum n _ * z.im + w _ * z.im = (finSum n _ + w _) * z.im
      rw [Int.add_mul]

/-- General `n`-term weighted convex-combination norm bound over `GaussInt`. -/
theorem normSq_cFinSum_le (n : Nat) (f : Fin n → GaussInt) (s : Fin n → Int) (D : Int)
    (hs : ∀ i, 0 ≤ s i) (hD : 0 ≤ D)
    (hb : ∀ i, GaussInt.normSq (f i) ≤ s i * s i * D) :
    GaussInt.normSq (cFinSum n f) ≤ finSum n s * finSum n s * D := by
  induction n with
  | zero => simp [cFinSum, finSum, GaussInt.normSq, GaussInt.zero]
  | succ n ih =>
    simp only [cFinSum, finSum]
    apply GaussInt.normSq_add_le_of_bounds
    · exact finSum_nonneg (fun i => hs _)
    · exact hs _
    · exact hD
    · exact ih (fun i => f ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩)
               (fun i => s ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩)
               (fun i => hs _) (fun i => hb _)
    · exact hb _

theorem normSq_weighted_sum_le (n : Nat) (w : Fin n → Int) (z : Fin n → GaussInt) (D : Int)
    (hw : ∀ i, 0 ≤ w i) (hD : 0 ≤ D)
    (hz : ∀ i, GaussInt.normSq (z i) ≤ D) :
    GaussInt.normSq (cFinSum n (fun i => GaussInt.scale (w i) (z i))) ≤
      finSum n w * finSum n w * D := by
  apply normSq_cFinSum_le n (fun i => GaussInt.scale (w i) (z i)) w D hw hD
  intro i
  rw [GaussInt.normSq_scale]
  exact Int.mul_le_mul (Int.le_refl _) (hz i) (GaussInt.normSq_nonneg _) (int_sq_nonneg _)

/-! ## 4. Integer Matrices `IMat n`, Powers, Determinants, and PF Predicates -/

abbrev IMat (n : Nat) := Fin n → Fin n → Int
abbrev IVec (n : Nat) := Fin n → Int
abbrev CVec (n : Nat) := Fin n → GaussInt

def matId (n : Nat) : IMat n := fun i j => if i = j then 1 else 0

def matMul {n : Nat} (A B : IMat n) : IMat n :=
  fun i j => finSum n (fun k => A i k * B k j)

def matPow {n : Nat} (A : IMat n) : Nat → IMat n
  | 0 => matId n
  | k + 1 => matMul (matPow A k) A

def matVec {n : Nat} (A : IMat n) (v : IVec n) : IVec n :=
  fun i => finSum n (fun j => A i j * v j)

def cMatVec {n : Nat} (A : IMat n) (v : CVec n) : CVec n :=
  fun i => cFinSum n (fun j => GaussInt.scale (A i j) (v j))

def rowSum {n : Nat} (A : IMat n) (i : Fin n) : Int :=
  finSum n (fun j => A i j)

/-- Minimum of a vector on `Fin (m + 1)`. -/
def finMin : {m : Nat} → (Fin (m + 1) → Int) → Int
  | 0, f => f ⟨0, Nat.zero_lt_succ 0⟩
  | m + 1, f =>
      let prev := finMin (fun i : Fin (m + 1) => f ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩)
      let last := f ⟨m + 1, Nat.lt_succ_self (m + 1)⟩
      if prev ≤ last then prev else last

/-- Maximum of a vector on `Fin (m + 1)`. -/
def finMax : {m : Nat} → (Fin (m + 1) → Int) → Int
  | 0, f => f ⟨0, Nat.zero_lt_succ 0⟩
  | m + 1, f =>
      let prev := finMax (fun i : Fin (m + 1) => f ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩)
      let last := f ⟨m + 1, Nat.lt_succ_self (m + 1)⟩
      if last ≤ prev then prev else last

theorem finMin_le {m : Nat} (f : Fin (m + 1) → Int) (i : Fin (m + 1)) :
    finMin f ≤ f i := by
  induction m with
  | zero =>
    have hi : i = ⟨0, Nat.zero_lt_succ 0⟩ := Fin.ext (by omega)
    subst hi; exact Int.le_refl _
  | succ m ih =>
    simp only [finMin]
    by_cases hi : i.val = m + 1
    · have hieq : i = ⟨m + 1, Nat.lt_succ_self (m + 1)⟩ := Fin.ext hi
      subst hieq; split <;> omega
    · have hilt : i.val < m + 1 := by omega
      have hprev := ih (fun j => f ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩) ⟨i.val, hilt⟩
      have hieq : (⟨i.val, Nat.lt_succ_of_lt hilt⟩ : Fin (m + 2)) = i := Fin.ext rfl
      rw [hieq] at hprev; split <;> omega

theorem le_finMin {m : Nat} (f : Fin (m + 1) → Int) (c : Int) (h : ∀ i, c ≤ f i) :
    c ≤ finMin f := by
  induction m with
  | zero => exact h ⟨0, Nat.zero_lt_succ 0⟩
  | succ m ih =>
    simp only [finMin]
    have hprev := ih (fun j => f ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩) (fun j => h _)
    have hlast := h ⟨m + 1, Nat.lt_succ_self (m + 1)⟩
    split <;> omega

theorem finMin_mem {m : Nat} (f : Fin (m + 1) → Int) :
    ∃ i : Fin (m + 1), finMin f = f i := by
  induction m with
  | zero => exact ⟨⟨0, Nat.zero_lt_succ 0⟩, rfl⟩
  | succ m ih =>
    simp only [finMin]
    rcases ih (fun j => f ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩) with ⟨i₀, hi₀⟩
    split
    · exact ⟨⟨i₀.val, Nat.lt_succ_of_lt i₀.isLt⟩, hi₀⟩
    · exact ⟨⟨m + 1, Nat.lt_succ_self (m + 1)⟩, rfl⟩

theorem le_finMax {m : Nat} (f : Fin (m + 1) → Int) (i : Fin (m + 1)) :
    f i ≤ finMax f := by
  induction m with
  | zero =>
    have hi : i = ⟨0, Nat.zero_lt_succ 0⟩ := Fin.ext (by omega)
    subst hi; exact Int.le_refl _
  | succ m ih =>
    simp only [finMax]
    by_cases hi : i.val = m + 1
    · have hieq : i = ⟨m + 1, Nat.lt_succ_self (m + 1)⟩ := Fin.ext hi
      subst hieq; split <;> omega
    · have hilt : i.val < m + 1 := by omega
      have hprev := ih (fun j => f ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩) ⟨i.val, hilt⟩
      have hieq : (⟨i.val, Nat.lt_succ_of_lt hilt⟩ : Fin (m + 2)) = i := Fin.ext rfl
      rw [hieq] at hprev; split <;> omega

theorem finMax_mem {m : Nat} (f : Fin (m + 1) → Int) :
    ∃ i : Fin (m + 1), finMax f = f i := by
  induction m with
  | zero => exact ⟨⟨0, Nat.zero_lt_succ 0⟩, rfl⟩
  | succ m ih =>
    simp only [finMax]
    rcases ih (fun j => f ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩) with ⟨i₀, hi₀⟩
    split
    · exact ⟨⟨i₀.val, Nat.lt_succ_of_lt i₀.isLt⟩, hi₀⟩
    · exact ⟨⟨m + 1, Nat.lt_succ_self (m + 1)⟩, rfl⟩

/-- Entrywise minimum `m(A) = min_{i,j} A_{i,j}` (positivity modulus floor) on `(m+1) × (m+1)`. -/
def posModulusMin {m : Nat} (A : IMat (m + 1)) : Int :=
  finMin (fun i => finMin (fun j => A i j))

/-- Column minimum `min_i A_{i,j}` and Doeblin column-minimum sum `δ(A) = ∑_j min_i A_{i,j}`. -/
def colMin {m : Nat} (A : IMat (m + 1)) (j : Fin (m + 1)) : Int :=
  finMin (fun i => A i j)

def doeblinModulus {m : Nat} (A : IMat (m + 1)) : Int :=
  finSum (m + 1) (fun j => colMin A j)

/-- Entrywise maximum `M(A) = max_{i,j} A_{i,j}`. -/
def entryMax {m : Nat} (A : IMat (m + 1)) : Int :=
  finMax (fun i => finMax (fun j => A i j))

theorem posModulusMin_le {m : Nat} (A : IMat (m + 1)) (i j : Fin (m + 1)) :
    posModulusMin A ≤ A i j := by
  unfold posModulusMin
  exact Int.le_trans (finMin_le (fun r => finMin (fun c => A r c)) i) (finMin_le (fun c => A i c) j)

theorem le_posModulusMin {m : Nat} (A : IMat (m + 1)) (c : Int) (h : ∀ i j, c ≤ A i j) :
    c ≤ posModulusMin A := by
  unfold posModulusMin
  apply le_finMin
  intro i
  apply le_finMin
  intro j
  exact h i j

theorem entryMax_ge {m : Nat} (A : IMat (m + 1)) (i j : Fin (m + 1)) :
    A i j ≤ entryMax A := by
  unfold entryMax
  exact Int.le_trans (le_finMax (fun c => A i c) j) (le_finMax (fun r => finMax (fun c => A r c)) i)

theorem doeblinModulus_ge_dim_mul_posModulusMin {m : Nat} (A : IMat (m + 1)) :
    ((m + 1 : Nat) : Int) * posModulusMin A ≤ doeblinModulus A := by
  unfold doeblinModulus
  rw [← finSum_const (m + 1) (posModulusMin A)]
  apply finSum_le
  intro j
  unfold colMin
  apply le_finMin
  intro i
  exact posModulusMin_le A i j

/-! ## 5. Recursive Laplace Cofactor Determinant and Characteristic Polynomial -/

def skipFin {n : Nat} (k : Fin (n + 1)) (i : Fin n) : Fin (n + 1) :=
  if i.val < k.val then ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩
  else ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩

def submatrix {n : Nat} (A : IMat (n + 1)) (r c : Fin (n + 1)) : IMat n :=
  fun i j => A (skipFin r i) (skipFin c j)

def det : {n : Nat} → IMat n → Int
  | 0, _ => 1
  | n + 1, A =>
      finSum (n + 1) (fun j =>
        let sign : Int := if j.val % 2 == 0 then 1 else -1
        sign * A ⟨0, Nat.zero_lt_succ n⟩ j * det (submatrix A ⟨0, Nat.zero_lt_succ n⟩ j))

def charMat {n : Nat} (A : IMat n) (x : Int) : IMat n :=
  fun i j => (if i = j then x else 0) - A i j

def charPolyEval {n : Nat} (A : IMat n) (x : Int) : Int :=
  det (charMat A x)

/-! ## 6. Perron–Frobenius Structural Predicates -/

def IsNonneg {n : Nat} (A : IMat n) : Prop :=
  ∀ i j : Fin n, 0 ≤ A i j

def IsStrictlyPositive {n : Nat} (A : IMat n) : Prop :=
  ∀ i j : Fin n, 0 < A i j

def IsSymmetric {n : Nat} (A : IMat n) : Prop :=
  ∀ i j : Fin n, A i j = A j i

def HasConstantRowSum {n : Nat} (A : IMat n) (R : Int) : Prop :=
  ∀ i : Fin n, rowSum A i = R

def IsEigenpair {n : Nat} (A : IMat n) (lam : Int) (v : IVec n) : Prop :=
  (∃ i : Fin n, v i ≠ 0) ∧ matVec A v = fun i => lam * v i

def IsComplexEigenpair {n : Nat} (A : IMat n) (lam : GaussInt) (v : CVec n) : Prop :=
  (∃ i : Fin n, v i ≠ GaussInt.zero) ∧ cMatVec A v = fun i => lam * v i

/-- Standard graph-theoretic irreducibility: every ordered pair communicates via some `A^k` (`k ≥ 1`). -/
def IsIrreducible {n : Nat} (A : IMat n) : Prop :=
  ∀ i j : Fin n, ∃ k : Nat, 1 ≤ k ∧ 0 < matPow A k i j

/-- Standard primitivity: a single power `A^k` (`k ≥ 1`) is entrywise strictly positive. -/
def IsPrimitive {n : Nat} (A : IMat n) : Prop :=
  ∃ k : Nat, 1 ≤ k ∧ ∀ i j : Fin n, 0 < matPow A k i j

/-- Almost irreducibility (single essential Frobenius class): any two indices with positive
    self-return walks communicate with each other. -/
def HasSingleEssentialClass {n : Nat} (A : IMat n) : Prop :=
  ∀ i j : Fin n,
    (∃ k₁ : Nat, 1 ≤ k₁ ∧ 0 < matPow A k₁ i i) →
    (∃ k₂ : Nat, 1 ≤ k₂ ∧ 0 < matPow A k₂ j j) →
    (∃ r : Nat, 1 ≤ r ∧ 0 < matPow A r i j)

/-- Almost-irreducible primitivity via a single primitive principal block and zeros outside it. -/
def IsBlockSupportedPrimitive {n : Nat} (A : IMat n) : Prop :=
  ∃ S : Fin n → Bool,
    (∃ i : Fin n, S i = true) ∧
    (∀ i j : Fin n, (S i = false ∨ S j = false) → A i j = 0) ∧
    (∃ k : Nat, 1 ≤ k ∧ ∀ i j : Fin n, S i = true → S j = true → 0 < matPow A k i j)

theorem matPow_one {n : Nat} (A : IMat n) (i j : Fin n) :
    matPow A 1 i j = A i j := by
  simp only [matPow, matMul, matId]
  have hc : ∀ t : Fin n, (if i = t then (1 : Int) else 0) * A t j =
      (if t = i then A i j else 0) := by
    intro t
    by_cases hit : i = t
    · subst hit; simp
    · have hti : t ≠ i := fun h' => hit h'.symm
      simp [hit, hti]
  rw [finSum_congr hc, finSum_ite_eq i (A i j)]

theorem primitive_imp_irreducible {n : Nat} {A : IMat n} (h : IsPrimitive A) :
    IsIrreducible A := by
  rcases h with ⟨k, hk, hpos⟩
  intro i j
  exact ⟨k, hk, hpos i j⟩

theorem irreducible_imp_singleEssentialClass {n : Nat} {A : IMat n} (h : IsIrreducible A) :
    HasSingleEssentialClass A := by
  intro i j _ _
  exact h i j

theorem strictlyPositive_imp_primitive {n : Nat} {A : IMat n} (h : IsStrictlyPositive A) :
    IsPrimitive A := by
  refine ⟨1, Nat.le_refl 1, ?_⟩
  intro i j
  rw [matPow_one]
  exact h i j

theorem primitive_imp_blockSupportedPrimitive {m : Nat} {A : IMat (m + 1)} (h : IsPrimitive A) :
    IsBlockSupportedPrimitive A := by
  rcases h with ⟨k, hk, hpos⟩
  refine ⟨fun _ => true, ⟨⟨0, Nat.zero_lt_succ m⟩, rfl⟩, ?_, ⟨k, hk, fun i j _ _ => hpos i j⟩⟩
  intro _ _ hfalse
  rcases hfalse with hf | hf <;> cases hf

end Conjecture00000007163
