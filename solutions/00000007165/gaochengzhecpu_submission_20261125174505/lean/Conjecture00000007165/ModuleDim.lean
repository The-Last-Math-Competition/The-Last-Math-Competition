/-
  Conjecture 00000007165 — First-Principles Module & Dimension Theory
  Core Lean 4.19.0 (zero external dependencies).

  Establishes:
  1. Finite summation over `Fin d` and double-sum commutation (`finSum_comm`).
  2. Exact Gaussian integers `GaussInt` (`ℤ[i]`) for complex vectors and Hermitian matrices.
  3. Module structures `ZMod` (over `ℤ`, capturing real rank/dimension) and `CMod`
     (over `ℤ[i]`, capturing complex rank/dimension).
  4. Genuine basis predicates (`HasBasis`, `HasDim`, `HasCBasis`, `HasCDim`),
     dimension uniqueness (`hasDim_unique`, `hasCDim_unique`) proved from first
     principles via the trace commutation identity `tr(P Q) = tr(Q P)`, and
     direct-sum dimension additivity (`hasDim_directSum`).
-/

namespace Conjecture00000007165

/-! ## 1. Finite Sums over `Fin d` (for `Int`) -/

def intSum : (d : Nat) → (Fin d → Int) → Int
  | 0, _ => 0
  | d + 1, f =>
      intSum d (fun i => f ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩) + f ⟨d, Nat.lt_succ_self d⟩

theorem intSum_zero_fn (d : Nat) : intSum d (fun _ => 0) = 0 := by
  induction d with
  | zero => rfl
  | succ d ih =>
    simp [intSum, ih]

theorem intSum_congr {d : Nat} {f g : Fin d → Int} (h : ∀ i, f i = g i) :
    intSum d f = intSum d g := by
  induction d with
  | zero => rfl
  | succ d ih =>
    simp only [intSum]
    rw [ih (fun i => h _), h _]

theorem intSum_add (d : Nat) (f g : Fin d → Int) :
    intSum d (fun i => f i + g i) = intSum d f + intSum d g := by
  induction d with
  | zero => simp [intSum]
  | succ d ih =>
    simp only [intSum]
    rw [ih]
    omega

theorem intSum_mul_left (d : Nat) (c : Int) (f : Fin d → Int) :
    intSum d (fun i => c * f i) = c * intSum d f := by
  induction d with
  | zero => simp [intSum]
  | succ d ih =>
    simp only [intSum]
    rw [ih, Int.mul_add]

theorem intSum_mul_right (d : Nat) (f : Fin d → Int) (c : Int) :
    intSum d (fun i => f i * c) = intSum d f * c := by
  induction d with
  | zero => simp [intSum]
  | succ d ih =>
    simp only [intSum]
    rw [ih, Int.add_mul]

theorem intSum_const_one (d : Nat) : intSum d (fun _ => 1) = (d : Int) := by
  induction d with
  | zero => rfl
  | succ d ih =>
    simp only [intSum, ih]
    omega

theorem intSum_comm (d₁ d₂ : Nat) (f : Fin d₁ → Fin d₂ → Int) :
    intSum d₁ (fun i => intSum d₂ (fun j => f i j)) =
      intSum d₂ (fun j => intSum d₁ (fun i => f i j)) := by
  induction d₁ with
  | zero =>
    simp [intSum, intSum_zero_fn]
  | succ d₁ ih =>
    simp only [intSum]
    rw [ih, ← intSum_add]

theorem intSum_ite_eq (d : Nat) (i₀ : Fin d) (f : Fin d → Int) :
    intSum d (fun i => if i = i₀ then f i else 0) = f i₀ := by
  induction d with
  | zero => exact Fin.elim0 i₀
  | succ d ih =>
    simp only [intSum]
    by_cases hlast : i₀.val = d
    · have hi₀ : i₀ = ⟨d, Nat.lt_succ_self d⟩ := Fin.ext hlast
      subst hi₀
      have hzero : intSum d (fun i : Fin d =>
          if (⟨i.val, Nat.lt_succ_of_lt i.isLt⟩ : Fin (d + 1)) = ⟨d, Nat.lt_succ_self d⟩
          then f ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩ else 0) = 0 := by
        rw [intSum_congr (g := fun _ => 0)]
        · exact intSum_zero_fn d
        · intro i
          have hne : (⟨i.val, Nat.lt_succ_of_lt i.isLt⟩ : Fin (d + 1)) ≠ ⟨d, Nat.lt_succ_self d⟩ := by
            intro heq
            have hv : i.val = d := congrArg Fin.val heq
            omega
          simp [hne]
      rw [hzero]
      simp
    · have hlt : i₀.val < d := by omega
      let i' : Fin d := ⟨i₀.val, hlt⟩
      have hne_last : (⟨d, Nat.lt_succ_self d⟩ : Fin (d + 1)) ≠ i₀ := by
        intro heq
        have hv : d = i₀.val := congrArg Fin.val heq
        omega
      have hsub : intSum d (fun i : Fin d =>
          if (⟨i.val, Nat.lt_succ_of_lt i.isLt⟩ : Fin (d + 1)) = i₀
          then f ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩ else 0) = f i₀ := by
        have hcong : intSum d (fun i : Fin d =>
            if (⟨i.val, Nat.lt_succ_of_lt i.isLt⟩ : Fin (d + 1)) = i₀
            then f ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩ else 0) =
            intSum d (fun i : Fin d => if i = i' then f ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩ else 0) := by
          apply intSum_congr
          intro i
          have heq_iff : ((⟨i.val, Nat.lt_succ_of_lt i.isLt⟩ : Fin (d + 1)) = i₀) ↔ (i = i') := by
            constructor
            · intro h; exact Fin.ext (by have hv := congrArg Fin.val h; exact hv)
            · intro h; exact Fin.ext (by have hv := congrArg Fin.val h; exact hv)
          by_cases hi : i = i'
          · have hi2 : (⟨i.val, Nat.lt_succ_of_lt i.isLt⟩ : Fin (d + 1)) = i₀ := heq_iff.mpr hi
            rw [if_pos hi2, if_pos hi]
          · have hi2 : (⟨i.val, Nat.lt_succ_of_lt i.isLt⟩ : Fin (d + 1)) ≠ i₀ :=
              fun hc => hi (heq_iff.mp hc)
            rw [if_neg hi2, if_neg hi]
        rw [hcong, ih i']
      rw [hsub]
      simp [hne_last]

theorem intSum_nonneg {d : Nat} {f : Fin d → Int} (h : ∀ i, 0 ≤ f i) :
    0 ≤ intSum d f := by
  induction d with
  | zero => simp [intSum]
  | succ d ih =>
    simp only [intSum]
    have h1 := ih (f := fun i => f ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩)
      (fun i => h ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩)
    have h2 := h ⟨d, Nat.lt_succ_self d⟩
    omega

theorem intSum_eq_zero_iff_of_nonneg {d : Nat} {f : Fin d → Int} (h : ∀ i, 0 ≤ f i) :
    intSum d f = 0 ↔ ∀ i, f i = 0 := by
  induction d with
  | zero =>
    simp [intSum]
    intro i; exact Fin.elim0 i
  | succ d ih =>
    simp only [intSum]
    have hsub_nonneg : 0 ≤ intSum d (fun i => f ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩) :=
      intSum_nonneg (fun i => h ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩)
    have hlast_nonneg : 0 ≤ f ⟨d, Nat.lt_succ_self d⟩ := h _
    constructor
    · intro hsum i
      have hsub0 : intSum d (fun j => f ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩) = 0 := by omega
      have hlast0 : f ⟨d, Nat.lt_succ_self d⟩ = 0 := by omega
      by_cases hi : i.val = d
      · have heq : i = ⟨d, Nat.lt_succ_self d⟩ := Fin.ext hi
        rw [heq]; exact hlast0
      · have hlt : i.val < d := by omega
        have hall := (ih (f := fun j => f ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩)
          (fun j => h ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩)).mp hsub0 ⟨i.val, hlt⟩
        exact hall
    · intro hall
      have hsub0 : intSum d (fun j => f ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩) = 0 :=
        (ih (f := fun j => f ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩)
          (fun j => h ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩)).mpr (fun j => hall _)
      rw [hsub0, hall ⟨d, Nat.lt_succ_self d⟩]
      rfl

/-! ## 2. Exact Gaussian Integers `GaussInt` (`ℤ[i]`) -/

@[ext]
structure GaussInt where
  re : Int
  im : Int
  deriving DecidableEq, Repr

namespace GaussInt

def zero : GaussInt := ⟨0, 0⟩
def one : GaussInt := ⟨1, 0⟩
def I : GaussInt := ⟨0, 1⟩
def ofInt (n : Int) : GaussInt := ⟨n, 0⟩

def add (z w : GaussInt) : GaussInt := ⟨z.re + w.re, z.im + w.im⟩
def neg (z : GaussInt) : GaussInt := ⟨-z.re, -z.im⟩
def sub (z w : GaussInt) : GaussInt := ⟨z.re - w.re, z.im - w.im⟩
def mul (z w : GaussInt) : GaussInt := ⟨z.re * w.re - z.im * w.im, z.re * w.im + z.im * w.re⟩
def conj (z : GaussInt) : GaussInt := ⟨z.re, -z.im⟩
def normSq (z : GaussInt) : Int := z.re * z.re + z.im * z.im

theorem add_comm (z w : GaussInt) : add z w = add w z := by
  ext <;> simp [add] <;> omega

theorem add_assoc (a b c : GaussInt) : add (add a b) c = add a (add b c) := by
  ext <;> simp [add] <;> omega

theorem zero_add (z : GaussInt) : add zero z = z := by
  ext <;> simp [add, zero]

theorem add_zero (z : GaussInt) : add z zero = z := by
  ext <;> simp [add, zero]

theorem add_left_neg (z : GaussInt) : add (neg z) z = zero := by
  ext <;> simp [add, neg, zero] <;> omega

theorem mul_comm (z w : GaussInt) : mul z w = mul w z := by
  ext <;> simp [mul, Int.mul_comm] <;> omega

theorem mul_assoc (a b c : GaussInt) : mul (mul a b) c = mul a (mul b c) := by
  ext <;> simp [mul, Int.mul_add, Int.add_mul, Int.mul_sub, Int.sub_mul, Int.mul_assoc] <;> omega

theorem one_mul (z : GaussInt) : mul one z = z := by
  ext <;> simp [mul, one]

theorem mul_one (z : GaussInt) : mul z one = z := by
  ext <;> simp [mul, one]

theorem zero_mul (z : GaussInt) : mul zero z = zero := by
  ext <;> simp [mul, zero]

theorem mul_zero (z : GaussInt) : mul z zero = zero := by
  ext <;> simp [mul, zero]

theorem mul_add (a b c : GaussInt) : mul a (add b c) = add (mul a b) (mul a c) := by
  ext <;> simp [mul, add, Int.mul_add] <;> omega

theorem add_mul (a b c : GaussInt) : mul (add a b) c = add (mul a c) (mul b c) := by
  ext <;> simp [mul, add, Int.add_mul] <;> omega

theorem conj_conj (z : GaussInt) : conj (conj z) = z := by
  ext <;> simp [conj]

theorem conj_add (z w : GaussInt) : conj (add z w) = add (conj z) (conj w) := by
  ext <;> simp [conj, add] <;> omega

theorem conj_mul (z w : GaussInt) : conj (mul z w) = mul (conj w) (conj z) := by
  ext <;> simp [conj, mul, Int.neg_mul, Int.mul_neg, Int.mul_comm] <;> omega

theorem conj_mul_self (z : GaussInt) : mul (conj z) z = ofInt (normSq z) := by
  ext <;> simp [conj, mul, ofInt, normSq, Int.neg_mul, Int.mul_neg, Int.mul_comm] <;> omega

end GaussInt

theorem int_sq_nonneg (x : Int) : 0 ≤ x * x := by
  by_cases hx : 0 ≤ x
  · exact Int.mul_nonneg hx hx
  · have hneg : 0 ≤ -x := by omega
    have hmul : (-x) * (-x) = x * x := by simp [Int.neg_mul_neg]
    rw [← hmul]
    exact Int.mul_nonneg hneg hneg

theorem int_sq_eq_zero_iff (x : Int) : x * x = 0 ↔ x = 0 := by
  constructor
  · intro h
    cases Int.mul_eq_zero.mp h with
    | inl h1 => exact h1
    | inr h2 => exact h2
  · intro h; rw [h]; rfl

theorem GaussInt.normSq_nonneg (z : GaussInt) : 0 ≤ z.normSq := by
  unfold GaussInt.normSq
  have h1 := int_sq_nonneg z.re
  have h2 := int_sq_nonneg z.im
  omega

theorem GaussInt.normSq_eq_zero_iff (z : GaussInt) : z.normSq = 0 ↔ z = GaussInt.zero := by
  unfold GaussInt.normSq
  have h1 := int_sq_nonneg z.re
  have h2 := int_sq_nonneg z.im
  constructor
  · intro h
    have hre2 : z.re * z.re = 0 := by omega
    have him2 : z.im * z.im = 0 := by omega
    have hre := (int_sq_eq_zero_iff z.re).mp hre2
    have him := (int_sq_eq_zero_iff z.im).mp him2
    ext <;> simp [GaussInt.zero, hre, him]
  · intro h
    rw [h]
    rfl

/-! ## 3. `ZMod`: Modules over `ℤ` and Exact Rank / Dimension Theory -/

structure ZMod (V : Type) where
  zero : V
  add : V → V → V
  neg : V → V
  smul : Int → V → V
  add_assoc : ∀ a b c, add (add a b) c = add a (add b c)
  add_comm : ∀ a b, add a b = add b a
  zero_add : ∀ a, add zero a = a
  add_zero : ∀ a, add a zero = a
  add_left_neg : ∀ a, add (neg a) a = zero
  one_smul : ∀ a, smul 1 a = a
  zero_smul : ∀ a, smul 0 a = zero
  smul_zero : ∀ c, smul c zero = zero
  add_smul : ∀ c₁ c₂ a, smul (c₁ + c₂) a = add (smul c₁ a) (smul c₂ a)
  smul_add : ∀ c a b, smul c (add a b) = add (smul c a) (smul c b)
  mul_smul : ∀ c₁ c₂ a, smul (c₁ * c₂) a = smul c₁ (smul c₂ a)

namespace ZMod

def sub {V : Type} (M : ZMod V) (a b : V) : V := M.add a (M.neg b)

theorem add_right_neg {V : Type} (M : ZMod V) (a : V) : M.add a (M.neg a) = M.zero := by
  rw [M.add_comm, M.add_left_neg]

theorem sub_eq_zero_iff {V : Type} (M : ZMod V) (a b : V) :
    M.sub a b = M.zero ↔ a = b := by
  unfold sub
  constructor
  · intro h
    have h2 : M.add (M.add a (M.neg b)) b = M.add M.zero b := congrArg (fun x => M.add x b) h
    rw [M.add_assoc, M.add_left_neg, M.add_zero, M.zero_add] at h2
    exact h2
  · intro h
    rw [h]
    exact M.add_right_neg b

theorem neg_one_smul {V : Type} (M : ZMod V) (a : V) : M.smul (-1) a = M.neg a := by
  have h0 : M.add (M.smul (-1) a) a = M.zero := by
    conv => lhs; rhs; rw [← M.one_smul a]
    rw [← M.add_smul]
    simp [M.zero_smul]
  have h1 : M.add (M.add (M.smul (-1) a) a) (M.neg a) = M.add M.zero (M.neg a) :=
    congrArg (fun x => M.add x (M.neg a)) h0
  rw [M.add_assoc, M.add_right_neg, M.add_zero, M.zero_add] at h1
  exact h1

def finSum {V : Type} (M : ZMod V) : (d : Nat) → (Fin d → V) → V
  | 0, _ => M.zero
  | d + 1, f =>
      M.add (finSum M d (fun i => f ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩))
            (f ⟨d, Nat.lt_succ_self d⟩)

theorem finSum_congr {V : Type} (M : ZMod V) {d : Nat} {f g : Fin d → V}
    (h : ∀ i, f i = g i) : finSum M d f = finSum M d g := by
  induction d with
  | zero => rfl
  | succ d ih =>
    simp only [finSum]
    rw [ih (fun i => h _), h _]

theorem finSum_zero_fn {V : Type} (M : ZMod V) (d : Nat) :
    finSum M d (fun _ => M.zero) = M.zero := by
  induction d with
  | zero => rfl
  | succ d ih =>
    simp only [finSum]
    rw [ih, M.add_zero]

theorem finSum_add {V : Type} (M : ZMod V) (d : Nat) (f g : Fin d → V) :
    finSum M d (fun i => M.add (f i) (g i)) = M.add (finSum M d f) (finSum M d g) := by
  induction d with
  | zero =>
    simp [finSum, M.add_zero]
  | succ d ih =>
    simp only [finSum]
    rw [ih]
    -- Rearrange (S_f + S_g) + (f_d + g_d) = (S_f + f_d) + (S_g + g_d)
    rw [M.add_assoc (finSum M d _) (finSum M d _) _]
    rw [← M.add_assoc (finSum M d _) (f _) (g _)]
    rw [M.add_comm (finSum M d _) (f _)]
    rw [M.add_assoc (f _) (finSum M d _) (g _)]
    rw [← M.add_assoc (finSum M d _) (f _) _]

theorem smul_finSum {V : Type} (M : ZMod V) (d : Nat) (c : Int) (f : Fin d → V) :
    M.smul c (finSum M d f) = finSum M d (fun i => M.smul c (f i)) := by
  induction d with
  | zero => simp [finSum, M.smul_zero]
  | succ d ih =>
    simp only [finSum]
    rw [M.smul_add, ih]

theorem intSum_smul {V : Type} (M : ZMod V) (d : Nat) (c : Fin d → Int) (v : V) :
    M.smul (intSum d c) v = finSum M d (fun i => M.smul (c i) v) := by
  induction d with
  | zero => simp [intSum, finSum, M.zero_smul]
  | succ d ih =>
    simp only [intSum, finSum]
    rw [M.add_smul, ih]

theorem finSum_comm {V : Type} (M : ZMod V) (d₁ d₂ : Nat) (f : Fin d₁ → Fin d₂ → V) :
    finSum M d₁ (fun i => finSum M d₂ (fun j => f i j)) =
      finSum M d₂ (fun j => finSum M d₁ (fun i => f i j)) := by
  induction d₁ with
  | zero =>
    simp [finSum, finSum_zero_fn]
  | succ d₁ ih =>
    simp only [finSum]
    rw [ih, ← finSum_add]

theorem finSum_ite_eq {V : Type} (M : ZMod V) (d : Nat) (i₀ : Fin d) (v : V) :
    finSum M d (fun i => if i = i₀ then v else M.zero) = v := by
  induction d with
  | zero => exact Fin.elim0 i₀
  | succ d ih =>
    simp only [finSum]
    by_cases hlast : i₀.val = d
    · have hi₀ : i₀ = ⟨d, Nat.lt_succ_self d⟩ := Fin.ext hlast
      subst hi₀
      have hzero : finSum M d (fun i : Fin d =>
          if (⟨i.val, Nat.lt_succ_of_lt i.isLt⟩ : Fin (d + 1)) = ⟨d, Nat.lt_succ_self d⟩
          then v else M.zero) = M.zero := by
        rw [finSum_congr M (g := fun _ => M.zero)]
        · exact finSum_zero_fn M d
        · intro i
          have hne : (⟨i.val, Nat.lt_succ_of_lt i.isLt⟩ : Fin (d + 1)) ≠ ⟨d, Nat.lt_succ_self d⟩ := by
            intro heq
            have hv : i.val = d := congrArg Fin.val heq
            omega
          simp [hne]
      rw [hzero, M.zero_add]
      simp
    · have hlt : i₀.val < d := by omega
      let i' : Fin d := ⟨i₀.val, hlt⟩
      have hne_last : (⟨d, Nat.lt_succ_self d⟩ : Fin (d + 1)) ≠ i₀ := by
        intro heq
        have hv : d = i₀.val := congrArg Fin.val heq
        omega
      have hsub : finSum M d (fun i : Fin d =>
          if (⟨i.val, Nat.lt_succ_of_lt i.isLt⟩ : Fin (d + 1)) = i₀ then v else M.zero) = v := by
        have hcong : finSum M d (fun i : Fin d =>
            if (⟨i.val, Nat.lt_succ_of_lt i.isLt⟩ : Fin (d + 1)) = i₀ then v else M.zero) =
            finSum M d (fun i : Fin d => if i = i' then v else M.zero) := by
          apply finSum_congr
          intro i
          have heq_iff : ((⟨i.val, Nat.lt_succ_of_lt i.isLt⟩ : Fin (d + 1)) = i₀) ↔ (i = i') := by
            constructor
            · intro h; exact Fin.ext (by have hv := congrArg Fin.val h; exact hv)
            · intro h; exact Fin.ext (by have hv := congrArg Fin.val h; exact hv)
          by_cases hi : i = i'
          · have hi2 : (⟨i.val, Nat.lt_succ_of_lt i.isLt⟩ : Fin (d + 1)) = i₀ := heq_iff.mpr hi
            rw [if_pos hi2, if_pos hi]
          · have hi2 : (⟨i.val, Nat.lt_succ_of_lt i.isLt⟩ : Fin (d + 1)) ≠ i₀ :=
              fun hc => hi (heq_iff.mp hc)
            rw [if_neg hi2, if_neg hi]
        rw [hcong, ih i']
      rw [hsub]
      simp [hne_last, M.add_zero]

def linComb {V : Type} (M : ZMod V) {d : Nat} (b : Fin d → V) (c : Fin d → Int) : V :=
  finSum M d (fun i => M.smul (c i) (b i))

theorem linComb_sub {V : Type} (M : ZMod V) {d : Nat} (b : Fin d → V) (c₁ c₂ : Fin d → Int) :
    M.sub (linComb M b c₁) (linComb M b c₂) = linComb M b (fun i => c₁ i - c₂ i) := by
  unfold sub linComb
  have hneg : M.neg (finSum M d (fun i => M.smul (c₂ i) (b i))) =
      finSum M d (fun i => M.smul (- c₂ i) (b i)) := by
    rw [← neg_one_smul M, smul_finSum]
    apply finSum_congr
    intro i
    rw [← M.mul_smul]
    simp
  rw [hneg, ← finSum_add]
  apply finSum_congr
  intro i
  simp only []
  have hsub : c₁ i - c₂ i = c₁ i + (- c₂ i) := by omega
  rw [hsub, M.add_smul]

def LinIndep {V : Type} (M : ZMod V) {d : Nat} (b : Fin d → V) : Prop :=
  ∀ c : Fin d → Int, linComb M b c = M.zero → ∀ i, c i = 0

theorem linComb_inj {V : Type} (M : ZMod V) {d : Nat} {b : Fin d → V}
    (hind : LinIndep M b) {c₁ c₂ : Fin d → Int}
    (heq : linComb M b c₁ = linComb M b c₂) : ∀ i, c₁ i = c₂ i := by
  intro i
  have h0 : M.sub (linComb M b c₁) (linComb M b c₂) = M.zero :=
    (sub_eq_zero_iff M _ _).mpr heq
  rw [linComb_sub] at h0
  have hdiff := hind (fun j => c₁ j - c₂ j) h0 i
  omega

def Spans {V : Type} (M : ZMod V) (W : V → Prop) {d : Nat} (b : Fin d → V) : Prop :=
  ∀ v, W v → ∃ c : Fin d → Int, v = linComb M b c

def HasBasis {V : Type} (M : ZMod V) (W : V → Prop) {d : Nat} (b : Fin d → V) : Prop :=
  (∀ i, W (b i)) ∧ LinIndep M b ∧ Spans M W b

def HasDim {V : Type} (M : ZMod V) (W : V → Prop) (d : Nat) : Prop :=
  ∃ b : Fin d → V, HasBasis M W b

/-- First-principles rank / dimension uniqueness via `tr(P Q) = tr(Q P)`. -/
theorem hasBasis_unique_dim {V : Type} (M : ZMod V) {W : V → Prop}
    {d₁ d₂ : Nat} {b₁ : Fin d₁ → V} {b₂ : Fin d₂ → V}
    (hb₁ : HasBasis M W b₁) (hb₂ : HasBasis M W b₂) : d₁ = d₂ := by
  rcases hb₁ with ⟨hmem₁, hind₁, hspan₁⟩
  rcases hb₂ with ⟨hmem₂, hind₂, hspan₂⟩
  -- Express each `b₂ j` in `b₁`, and each `b₁ i` in `b₂`
  have hexP : ∀ j : Fin d₂, ∃ p : Fin d₁ → Int, b₂ j = linComb M b₁ p :=
    fun j => hspan₁ (b₂ j) (hmem₂ j)
  have hexQ : ∀ i : Fin d₁, ∃ q : Fin d₂ → Int, b₁ i = linComb M b₂ q :=
    fun i => hspan₂ (b₁ i) (hmem₁ i)
  let P : Fin d₁ → Fin d₂ → Int := fun i j => Classical.choose (hexP j) i
  let Qm : Fin d₂ → Fin d₁ → Int := fun j i => Classical.choose (hexQ i) j
  have hP : ∀ j : Fin d₂, b₂ j = linComb M b₁ (fun i => P i j) :=
    fun j => Classical.choose_spec (hexP j)
  have hQ : ∀ i : Fin d₁, b₁ i = linComb M b₂ (fun j => Qm j i) :=
    fun i => Classical.choose_spec (hexQ i)
  -- Show `∑ j, P i' j * Qm j i = (if i' = i then 1 else 0)`
  have hPQ : ∀ i : Fin d₁, intSum d₂ (fun j => P i j * Qm j i) = 1 := by
    intro i
    have hsub1 : b₁ i = linComb M b₁ (fun i' => intSum d₂ (fun j => P i' j * Qm j i)) := by
      have step1 := hQ i
      unfold linComb at step1 ⊢
      rw [step1]
      have step2 : finSum M d₂ (fun j => M.smul (Qm j i) (b₂ j)) =
          finSum M d₂ (fun j => finSum M d₁ (fun i' => M.smul (P i' j * Qm j i) (b₁ i'))) := by
        apply finSum_congr
        intro j
        rw [hP j]
        unfold linComb
        rw [smul_finSum]
        apply finSum_congr
        intro i'
        rw [← M.mul_smul, Int.mul_comm]
      rw [step2, finSum_comm]
      apply finSum_congr
      intro i'
      rw [← intSum_smul]
    have hsub2 : b₁ i = linComb M b₁ (fun i' => if i' = i then 1 else 0) := by
      unfold linComb
      have hcong : finSum M d₁ (fun i' => M.smul (if i' = i then 1 else 0) (b₁ i')) =
          finSum M d₁ (fun i' => if i' = i then b₁ i else M.zero) := by
        apply finSum_congr
        intro i'
        by_cases h : i' = i
        · subst h; simp [M.one_smul]
        · simp [h, M.zero_smul]
      rw [hcong, finSum_ite_eq]
    have hinj := linComb_inj M hind₁ (hsub1.symm.trans hsub2) i
    simpa using hinj
  -- Symmetrically `∑ i, Qm j i * P i j = 1`
  have hQP : ∀ j : Fin d₂, intSum d₁ (fun i => Qm j i * P i j) = 1 := by
    intro j
    have hsub1 : b₂ j = linComb M b₂ (fun j' => intSum d₁ (fun i => Qm j' i * P i j)) := by
      have step1 := hP j
      unfold linComb at step1 ⊢
      rw [step1]
      have step2 : finSum M d₁ (fun i => M.smul (P i j) (b₁ i)) =
          finSum M d₁ (fun i => finSum M d₂ (fun j' => M.smul (Qm j' i * P i j) (b₂ j'))) := by
        apply finSum_congr
        intro i
        rw [hQ i]
        unfold linComb
        rw [smul_finSum]
        apply finSum_congr
        intro j'
        rw [← M.mul_smul, Int.mul_comm]
      rw [step2, finSum_comm]
      apply finSum_congr
      intro j'
      rw [← intSum_smul]
    have hsub2 : b₂ j = linComb M b₂ (fun j' => if j' = j then 1 else 0) := by
      unfold linComb
      have hcong : finSum M d₂ (fun j' => M.smul (if j' = j then 1 else 0) (b₂ j')) =
          finSum M d₂ (fun j' => if j' = j then b₂ j else M.zero) := by
        apply finSum_congr
        intro j'
        by_cases h : j' = j
        · subst h; simp [M.one_smul]
        · simp [h, M.zero_smul]
      rw [hcong, finSum_ite_eq]
    have hinj := linComb_inj M hind₂ (hsub1.symm.trans hsub2) j
    simpa using hinj
  -- Equate traces: `d₁ = ∑ i, ∑ j, P i j * Qm j i = ∑ j, ∑ i, Qm j i * P i j = d₂`
  have htr1 : (d₁ : Int) = intSum d₁ (fun i => intSum d₂ (fun j => P i j * Qm j i)) := by
    rw [intSum_congr hPQ, intSum_const_one]
  have htr2 : (d₂ : Int) = intSum d₂ (fun j => intSum d₁ (fun i => P i j * Qm j i)) := by
    have hcomm_mul : intSum d₂ (fun j => intSum d₁ (fun i => P i j * Qm j i)) =
        intSum d₂ (fun j => intSum d₁ (fun i => Qm j i * P i j)) := by
      apply intSum_congr; intro j; apply intSum_congr; intro i; exact Int.mul_comm _ _
    rw [hcomm_mul, intSum_congr hQP, intSum_const_one]
  have heq_int : (d₁ : Int) = (d₂ : Int) := by
    rw [htr1, intSum_comm, ← htr2]
  omega

theorem hasDim_unique {V : Type} (M : ZMod V) {W : V → Prop} {d₁ d₂ : Nat}
    (h₁ : HasDim M W d₁) (h₂ : HasDim M W d₂) : d₁ = d₂ := by
  rcases h₁ with ⟨b₁, hb₁⟩
  rcases h₂ with ⟨b₂, hb₂⟩
  exact hasBasis_unique_dim M hb₁ hb₂

theorem not_hasDim_of_ne {V : Type} (M : ZMod V) {W : V → Prop} {d m : Nat}
    (hd : HasDim M W d) (hne : d ≠ m) : ¬ HasDim M W m := by
  intro hm
  exact hne (hasDim_unique M hd hm)

/-- Splitting a sum over `Fin (d₁ + d₂)` into its first `d₁` and last `d₂` terms. -/
theorem finSum_append {V : Type} (M : ZMod V) (d₁ d₂ : Nat) (f : Fin (d₁ + d₂) → V) :
    finSum M (d₁ + d₂) f =
      M.add (finSum M d₁ (fun i => f ⟨i.val, by omega⟩))
            (finSum M d₂ (fun j => f ⟨d₁ + j.val, by omega⟩)) := by
  induction d₂ with
  | zero =>
    have hd : d₁ + 0 = d₁ := Nat.add_zero d₁
    cases hd
    simp [finSum, M.add_zero]
  | succ d₂ ih =>
    -- Unfold `finSum M (d₁ + (d₂ + 1))` cleanly via `(d₁ + d₂) + 1`
    change finSum M ((d₁ + d₂) + 1) f =
      M.add (finSum M d₁ (fun i => f ⟨i.val, by omega⟩))
            (M.add (finSum M d₂ (fun j => f ⟨d₁ + j.val, by omega⟩))
                   (f ⟨d₁ + d₂, by omega⟩))
    simp only [finSum]
    rw [ih (fun k => f ⟨k.val, by omega⟩), M.add_assoc]

/-- Direct-sum dimension additivity: if `W = W₁ ⊕ W₂`, then `dim W = dim W₁ + dim W₂`. -/
theorem hasDim_directSum {V : Type} (M : ZMod V)
    {W W₁ W₂ : V → Prop} {d₁ d₂ : Nat}
    (hd₁ : HasDim M W₁ d₁) (hd₂ : HasDim M W₂ d₂)
    (hclosed₁ : ∀ v, W₁ v → (∀ c : Int, W₁ (M.smul c v)))
    (hclosed₂ : ∀ v, W₂ v → (∀ c : Int, W₂ (M.smul c v)))
    (hadd₁ : ∀ u v, W₁ u → W₁ v → W₁ (M.add u v))
    (hadd₂ : ∀ u v, W₂ u → W₂ v → W₂ (M.add u v))
    (hzero₁ : W₁ M.zero) (hzero₂ : W₂ M.zero)
    (hsub₁ : ∀ v, W₁ v → W v) (hsub₂ : ∀ v, W₂ v → W v)
    (_haddW : ∀ u v, W u → W v → W (M.add u v))
    (hdecomp : ∀ v, W v → ∃ v₁ v₂, W₁ v₁ ∧ W₂ v₂ ∧ v = M.add v₁ v₂)
    (hdisj : ∀ v₁ v₂, W₁ v₁ → W₂ v₂ → M.add v₁ v₂ = M.zero → v₁ = M.zero ∧ v₂ = M.zero) :
    HasDim M W (d₁ + d₂) := by
  rcases hd₁ with ⟨b₁, hmem₁, hind₁, hspan₁⟩
  rcases hd₂ with ⟨b₂, hmem₂, hind₂, hspan₂⟩
  let b : Fin (d₁ + d₂) → V := fun k =>
    if hk : k.val < d₁ then b₁ ⟨k.val, hk⟩
    else b₂ ⟨k.val - d₁, by omega⟩
  have hlinComb_mem₁ : ∀ c₁ : Fin d₁ → Int, W₁ (linComb M b₁ c₁) := by
    intro c₁
    unfold linComb
    have haux : ∀ k : Nat, (hk : k ≤ d₁) →
        W₁ (finSum M k (fun i => M.smul (c₁ ⟨i.val, by omega⟩) (b₁ ⟨i.val, by omega⟩))) := by
      intro k hk
      induction k with
      | zero => exact hzero₁
      | succ k ih =>
        simp only [finSum]
        exact hadd₁ _ _ (ih (by omega)) (hclosed₁ _ (hmem₁ _) _)
    exact haux d₁ (Nat.le_refl d₁)
  have hlinComb_mem₂ : ∀ c₂ : Fin d₂ → Int, W₂ (linComb M b₂ c₂) := by
    intro c₂
    unfold linComb
    have haux : ∀ k : Nat, (hk : k ≤ d₂) →
        W₂ (finSum M k (fun j => M.smul (c₂ ⟨j.val, by omega⟩) (b₂ ⟨j.val, by omega⟩))) := by
      intro k hk
      induction k with
      | zero => exact hzero₂
      | succ k ih =>
        simp only [finSum]
        exact hadd₂ _ _ (ih (by omega)) (hclosed₂ _ (hmem₂ _) _)
    exact haux d₂ (Nat.le_refl d₂)
  have hsplit_lc : ∀ c : Fin (d₁ + d₂) → Int,
      linComb M b c = M.add (linComb M b₁ (fun i => c ⟨i.val, by omega⟩))
                            (linComb M b₂ (fun j => c ⟨d₁ + j.val, by omega⟩)) := by
    intro c
    unfold linComb
    rw [finSum_append]
    have hleft : finSum M d₁ (fun i : Fin d₁ => M.smul (c ⟨i.val, by omega⟩) (b ⟨i.val, by omega⟩)) =
        finSum M d₁ (fun i : Fin d₁ => M.smul (c ⟨i.val, by omega⟩) (b₁ i)) := by
      apply finSum_congr
      intro i
      have hi : (⟨i.val, by omega⟩ : Fin (d₁ + d₂)).val < d₁ := i.isLt
      simp [b, hi]
    have hright : finSum M d₂ (fun j : Fin d₂ =>
          M.smul (c ⟨d₁ + j.val, by omega⟩) (b ⟨d₁ + j.val, by omega⟩)) =
        finSum M d₂ (fun j : Fin d₂ => M.smul (c ⟨d₁ + j.val, by omega⟩) (b₂ j)) := by
      apply finSum_congr
      intro j
      have hj : ¬ ((⟨d₁ + j.val, by omega⟩ : Fin (d₁ + d₂)).val < d₁) := by simp
      simp only [b, hj, ↓reduceDIte]
      exact congrArg (M.smul (c ⟨d₁ + j.val, by omega⟩)) (congrArg b₂ (by ext; simp; omega))
    rw [hleft, hright]
  refine ⟨b, ?_, ?_, ?_⟩
  · intro k
    by_cases hk : k.val < d₁
    · simp [b, hk]; exact hsub₁ _ (hmem₁ _)
    · simp [b, hk]; exact hsub₂ _ (hmem₂ _)
  · intro c hc0 k
    rw [hsplit_lc c] at hc0
    have ⟨hz₁, hz₂⟩ := hdisj _ _ (hlinComb_mem₁ _) (hlinComb_mem₂ _) hc0
    by_cases hk : k.val < d₁
    · have hk_eq : k = ⟨k.val, by omega⟩ := Fin.ext rfl
      rw [hk_eq]
      exact hind₁ (fun i => c ⟨i.val, by omega⟩) hz₁ ⟨k.val, hk⟩
    · let j : Fin d₂ := ⟨k.val - d₁, by omega⟩
      have hk_eq : k = ⟨d₁ + j.val, by omega⟩ := by
        ext; simp [j]; omega
      rw [hk_eq]
      exact hind₂ (fun j' => c ⟨d₁ + j'.val, by omega⟩) hz₂ j
  · intro v hv
    rcases hdecomp v hv with ⟨v₁, v₂, hv₁, hv₂, rfl⟩
    rcases hspan₁ v₁ hv₁ with ⟨c₁, rfl⟩
    rcases hspan₂ v₂ hv₂ with ⟨c₂, rfl⟩
    let c : Fin (d₁ + d₂) → Int := fun k =>
      if hk : k.val < d₁ then c₁ ⟨k.val, hk⟩ else c₂ ⟨k.val - d₁, by omega⟩
    refine ⟨c, ?_⟩
    rw [hsplit_lc c]
    have hc₁ : (fun i : Fin d₁ => c ⟨i.val, by omega⟩) = c₁ := by
      funext i; simp [c, i.isLt]
    have hc₂ : (fun j : Fin d₂ => c ⟨d₁ + j.val, by omega⟩) = c₂ := by
      funext j
      have hj : ¬ (d₁ + j.val < d₁) := by omega
      simp only [c, hj, ↓reduceDIte]
      exact congrArg c₂ (by ext; simp; omega)
    rw [hc₁, hc₂]

/-- Coordinate extraction helper: if linear functionals `φ` are biorthogonal to `b` and
    reconstruct every `v ∈ W`, then `b` is a genuine basis of `W`. -/
theorem hasDim_of_coords {V : Type} (M : ZMod V) {W : V → Prop} {d : Nat}
    (b : Fin d → V) (coord : V → Fin d → Int)
    (hmem : ∀ i, W (b i))
    (hcoord_linComb : ∀ c : Fin d → Int, ∀ i, coord (linComb M b c) i = c i)
    (hcoord_zero : ∀ i, coord M.zero i = 0)
    (hspan : ∀ v, W v → v = linComb M b (coord v)) :
    HasDim M W d := by
  refine ⟨b, hmem, ?_, ?_⟩
  · intro c hc i
    have h1 := hcoord_linComb c i
    rw [hc, hcoord_zero i] at h1
    exact h1.symm
  · intro v hv
    exact ⟨coord v, hspan v hv⟩

end ZMod

/-! ## 4. Finite Sums & Rank Uniqueness over `GaussInt` (`ℤ[i]`-Modules) -/

def gaussSum : (d : Nat) → (Fin d → GaussInt) → GaussInt
  | 0, _ => GaussInt.zero
  | d + 1, f =>
      GaussInt.add (gaussSum d (fun i => f ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩))
                   (f ⟨d, Nat.lt_succ_self d⟩)

theorem gaussSum_re (d : Nat) (f : Fin d → GaussInt) :
    (gaussSum d f).re = intSum d (fun i => (f i).re) := by
  induction d with
  | zero => rfl
  | succ d ih =>
    simp [gaussSum, intSum, GaussInt.add, ih]

theorem gaussSum_im (d : Nat) (f : Fin d → GaussInt) :
    (gaussSum d f).im = intSum d (fun i => (f i).im) := by
  induction d with
  | zero => rfl
  | succ d ih =>
    simp [gaussSum, intSum, GaussInt.add, ih]

theorem gaussSum_congr {d : Nat} {f g : Fin d → GaussInt} (h : ∀ i, f i = g i) :
    gaussSum d f = gaussSum d g := by
  ext
  · rw [gaussSum_re, gaussSum_re]; exact intSum_congr (fun i => congrArg GaussInt.re (h i))
  · rw [gaussSum_im, gaussSum_im]; exact intSum_congr (fun i => congrArg GaussInt.im (h i))

theorem gaussSum_const_one_re (d : Nat) :
    (gaussSum d (fun _ => GaussInt.one)).re = (d : Int) := by
  rw [gaussSum_re]
  exact intSum_const_one d

theorem gaussSum_comm (d₁ d₂ : Nat) (f : Fin d₁ → Fin d₂ → GaussInt) :
    gaussSum d₁ (fun i => gaussSum d₂ (fun j => f i j)) =
      gaussSum d₂ (fun j => gaussSum d₁ (fun i => f i j)) := by
  ext
  · simp only [gaussSum_re]
    exact intSum_comm d₁ d₂ (fun i j => (f i j).re)
  · simp only [gaussSum_im]
    exact intSum_comm d₁ d₂ (fun i j => (f i j).im)

structure CMod (V : Type) where
  toZMod : ZMod V
  csmul : GaussInt → V → V
  one_csmul : ∀ a, csmul GaussInt.one a = a
  zero_csmul : ∀ a, csmul GaussInt.zero a = toZMod.zero
  csmul_zero : ∀ z, csmul z toZMod.zero = toZMod.zero
  add_csmul : ∀ z₁ z₂ a, csmul (GaussInt.add z₁ z₂) a = toZMod.add (csmul z₁ a) (csmul z₂ a)
  csmul_add : ∀ z a b, csmul z (toZMod.add a b) = toZMod.add (csmul z a) (csmul z b)
  mul_csmul : ∀ z₁ z₂ a, csmul (GaussInt.mul z₁ z₂) a = csmul z₁ (csmul z₂ a)

namespace CMod

def clinComb {V : Type} (C : CMod V) {d : Nat} (b : Fin d → V) (c : Fin d → GaussInt) : V :=
  ZMod.finSum C.toZMod d (fun i => C.csmul (c i) (b i))

theorem csmul_finSum {V : Type} (C : CMod V) (d : Nat) (z : GaussInt) (f : Fin d → V) :
    C.csmul z (ZMod.finSum C.toZMod d f) = ZMod.finSum C.toZMod d (fun i => C.csmul z (f i)) := by
  induction d with
  | zero => simp [ZMod.finSum, C.csmul_zero]
  | succ d ih =>
    simp only [ZMod.finSum]
    rw [C.csmul_add, ih]

theorem gaussSum_csmul {V : Type} (C : CMod V) (d : Nat) (c : Fin d → GaussInt) (v : V) :
    C.csmul (gaussSum d c) v = ZMod.finSum C.toZMod d (fun i => C.csmul (c i) v) := by
  induction d with
  | zero => simp [gaussSum, ZMod.finSum, C.zero_csmul]
  | succ d ih =>
    simp only [gaussSum, ZMod.finSum]
    rw [C.add_csmul, ih]

theorem neg_csmul {V : Type} (C : CMod V) (z : GaussInt) (v : V) :
    C.csmul (GaussInt.neg z) v = C.toZMod.neg (C.csmul z v) := by
  have h0 : C.toZMod.add (C.csmul (GaussInt.neg z) v) (C.csmul z v) = C.toZMod.zero := by
    rw [← C.add_csmul, GaussInt.add_left_neg, C.zero_csmul]
  have h1 : C.toZMod.add (C.toZMod.add (C.csmul (GaussInt.neg z) v) (C.csmul z v))
      (C.toZMod.neg (C.csmul z v)) = C.toZMod.add C.toZMod.zero (C.toZMod.neg (C.csmul z v)) :=
    congrArg (fun x => C.toZMod.add x (C.toZMod.neg (C.csmul z v))) h0
  rw [C.toZMod.add_assoc, ZMod.add_right_neg, C.toZMod.add_zero, C.toZMod.zero_add] at h1
  exact h1

def CLinIndep {V : Type} (C : CMod V) {d : Nat} (b : Fin d → V) : Prop :=
  ∀ c : Fin d → GaussInt, clinComb C b c = C.toZMod.zero → ∀ i, c i = GaussInt.zero

def CSpans {V : Type} (C : CMod V) (W : V → Prop) {d : Nat} (b : Fin d → V) : Prop :=
  ∀ v, W v → ∃ c : Fin d → GaussInt, v = clinComb C b c

def HasCBasis {V : Type} (C : CMod V) (W : V → Prop) {d : Nat} (b : Fin d → V) : Prop :=
  (∀ i, W (b i)) ∧ CLinIndep C b ∧ CSpans C W b

def HasCDim {V : Type} (C : CMod V) (W : V → Prop) (d : Nat) : Prop :=
  ∃ b : Fin d → V, HasCBasis C W b

theorem clinComb_inj {V : Type} (C : CMod V) {d : Nat} {b : Fin d → V}
    (hind : CLinIndep C b) {c₁ c₂ : Fin d → GaussInt}
    (heq : clinComb C b c₁ = clinComb C b c₂) : ∀ i, c₁ i = c₂ i := by
  intro i
  have h0 : ZMod.sub C.toZMod (clinComb C b c₁) (clinComb C b c₂) = C.toZMod.zero :=
    (ZMod.sub_eq_zero_iff C.toZMod _ _).mpr heq
  have hsub_lc : ZMod.sub C.toZMod (clinComb C b c₁) (clinComb C b c₂) =
      clinComb C b (fun j => GaussInt.sub (c₁ j) (c₂ j)) := by
    unfold ZMod.sub clinComb
    have hneg : C.toZMod.neg (ZMod.finSum C.toZMod d (fun j => C.csmul (c₂ j) (b j))) =
        ZMod.finSum C.toZMod d (fun j => C.csmul (GaussInt.neg (c₂ j)) (b j)) := by
      rw [← ZMod.neg_one_smul C.toZMod, ZMod.smul_finSum]
      apply ZMod.finSum_congr
      intro j
      rw [ZMod.neg_one_smul, neg_csmul]
    rw [hneg, ← ZMod.finSum_add]
    apply ZMod.finSum_congr
    intro j
    simp only []
    have hgs : GaussInt.sub (c₁ j) (c₂ j) = GaussInt.add (c₁ j) (GaussInt.neg (c₂ j)) := by
      ext <;> simp [GaussInt.sub, GaussInt.add, GaussInt.neg] <;> omega
    rw [hgs, C.add_csmul]
  rw [hsub_lc] at h0
  have hd := hind _ h0 i
  ext
  · have hre : (GaussInt.sub (c₁ i) (c₂ i)).re = 0 := congrArg GaussInt.re hd
    simp [GaussInt.sub] at hre; omega
  · have him : (GaussInt.sub (c₁ i) (c₂ i)).im = 0 := congrArg GaussInt.im hd
    simp [GaussInt.sub] at him; omega

theorem hasCDim_unique {V : Type} (C : CMod V) {W : V → Prop} {d₁ d₂ : Nat}
    (h₁ : HasCDim C W d₁) (h₂ : HasCDim C W d₂) : d₁ = d₂ := by
  rcases h₁ with ⟨b₁, hmem₁, hind₁, hspan₁⟩
  rcases h₂ with ⟨b₂, hmem₂, hind₂, hspan₂⟩
  have hexP : ∀ j : Fin d₂, ∃ p : Fin d₁ → GaussInt, b₂ j = clinComb C b₁ p :=
    fun j => hspan₁ (b₂ j) (hmem₂ j)
  have hexQ : ∀ i : Fin d₁, ∃ q : Fin d₂ → GaussInt, b₁ i = clinComb C b₂ q :=
    fun i => hspan₂ (b₁ i) (hmem₁ i)
  let P : Fin d₁ → Fin d₂ → GaussInt := fun i j => Classical.choose (hexP j) i
  let Qm : Fin d₂ → Fin d₁ → GaussInt := fun j i => Classical.choose (hexQ i) j
  have hP : ∀ j : Fin d₂, b₂ j = clinComb C b₁ (fun i => P i j) :=
    fun j => Classical.choose_spec (hexP j)
  have hQ : ∀ i : Fin d₁, b₁ i = clinComb C b₂ (fun j => Qm j i) :=
    fun i => Classical.choose_spec (hexQ i)
  have hPQ : ∀ i : Fin d₁, gaussSum d₂ (fun j => GaussInt.mul (P i j) (Qm j i)) = GaussInt.one := by
    intro i
    have hsub1 : b₁ i = clinComb C b₁ (fun i' => gaussSum d₂ (fun j => GaussInt.mul (P i' j) (Qm j i))) := by
      have step1 := hQ i
      unfold clinComb at step1 ⊢
      rw [step1]
      have step2 : ZMod.finSum C.toZMod d₂ (fun j => C.csmul (Qm j i) (b₂ j)) =
          ZMod.finSum C.toZMod d₂ (fun j =>
            ZMod.finSum C.toZMod d₁ (fun i' => C.csmul (GaussInt.mul (P i' j) (Qm j i)) (b₁ i'))) := by
        apply ZMod.finSum_congr
        intro j
        rw [hP j]
        unfold clinComb
        rw [csmul_finSum]
        apply ZMod.finSum_congr
        intro i'
        rw [← C.mul_csmul, GaussInt.mul_comm]
      rw [step2, ZMod.finSum_comm]
      apply ZMod.finSum_congr
      intro i'
      rw [← gaussSum_csmul]
    have hsub2 : b₁ i = clinComb C b₁ (fun i' => if i' = i then GaussInt.one else GaussInt.zero) := by
      unfold clinComb
      have hcong : ZMod.finSum C.toZMod d₁
          (fun i' => C.csmul (if i' = i then GaussInt.one else GaussInt.zero) (b₁ i')) =
          ZMod.finSum C.toZMod d₁ (fun i' => if i' = i then b₁ i else C.toZMod.zero) := by
        apply ZMod.finSum_congr
        intro i'
        by_cases h : i' = i
        · subst h; simp [C.one_csmul]
        · simp [h, C.zero_csmul]
      rw [hcong, ZMod.finSum_ite_eq]
    have hinj := clinComb_inj C hind₁ (hsub1.symm.trans hsub2) i
    simpa using hinj
  have hQP : ∀ j : Fin d₂, gaussSum d₁ (fun i => GaussInt.mul (Qm j i) (P i j)) = GaussInt.one := by
    intro j
    have hsub1 : b₂ j = clinComb C b₂ (fun j' => gaussSum d₁ (fun i => GaussInt.mul (Qm j' i) (P i j))) := by
      have step1 := hP j
      unfold clinComb at step1 ⊢
      rw [step1]
      have step2 : ZMod.finSum C.toZMod d₁ (fun i => C.csmul (P i j) (b₁ i)) =
          ZMod.finSum C.toZMod d₁ (fun i =>
            ZMod.finSum C.toZMod d₂ (fun j' => C.csmul (GaussInt.mul (Qm j' i) (P i j)) (b₂ j'))) := by
        apply ZMod.finSum_congr
        intro i
        rw [hQ i]
        unfold clinComb
        rw [csmul_finSum]
        apply ZMod.finSum_congr
        intro j'
        rw [← C.mul_csmul, GaussInt.mul_comm]
      rw [step2, ZMod.finSum_comm]
      apply ZMod.finSum_congr
      intro j'
      rw [← gaussSum_csmul]
    have hsub2 : b₂ j = clinComb C b₂ (fun j' => if j' = j then GaussInt.one else GaussInt.zero) := by
      unfold clinComb
      have hcong : ZMod.finSum C.toZMod d₂
          (fun j' => C.csmul (if j' = j then GaussInt.one else GaussInt.zero) (b₂ j')) =
          ZMod.finSum C.toZMod d₂ (fun j' => if j' = j then b₂ j else C.toZMod.zero) := by
        apply ZMod.finSum_congr
        intro j'
        by_cases h : j' = j
        · subst h; simp [C.one_csmul]
        · simp [h, C.zero_csmul]
      rw [hcong, ZMod.finSum_ite_eq]
    have hinj := clinComb_inj C hind₂ (hsub1.symm.trans hsub2) j
    simpa using hinj
  have htr : gaussSum d₁ (fun i => gaussSum d₂ (fun j => GaussInt.mul (P i j) (Qm j i))) =
      gaussSum d₂ (fun j => gaussSum d₁ (fun i => GaussInt.mul (Qm j i) (P i j))) := by
    rw [gaussSum_comm]
    apply gaussSum_congr; intro j; apply gaussSum_congr; intro i
    exact GaussInt.mul_comm _ _
  rw [gaussSum_congr hPQ, gaussSum_congr hQP] at htr
  have hre : (gaussSum d₁ (fun _ => GaussInt.one)).re = (gaussSum d₂ (fun _ => GaussInt.one)).re :=
    congrArg GaussInt.re htr
  rw [gaussSum_const_one_re, gaussSum_const_one_re] at hre
  omega

theorem not_hasCDim_of_ne {V : Type} (C : CMod V) {W : V → Prop} {d m : Nat}
    (hd : HasCDim C W d) (hne : d ≠ m) : ¬ HasCDim C W m := by
  intro hm
  exact hne (hasCDim_unique C hd hm)

theorem hasCDim_of_coords {V : Type} (C : CMod V) {W : V → Prop} {d : Nat}
    (b : Fin d → V) (coord : V → Fin d → GaussInt)
    (hmem : ∀ i, W (b i))
    (hcoord_clinComb : ∀ c : Fin d → GaussInt, ∀ i, coord (clinComb C b c) i = c i)
    (hcoord_zero : ∀ i, coord C.toZMod.zero i = GaussInt.zero)
    (hspan : ∀ v, W v → v = clinComb C b (coord v)) :
    HasCDim C W d := by
  refine ⟨b, hmem, ?_, ?_⟩
  · intro c hc i
    have h1 := hcoord_clinComb c i
    rw [hc, hcoord_zero i] at h1
    exact h1.symm
  · intro v hv
    exact ⟨coord v, hspan v hv⟩

end CMod

end Conjecture00000007165
