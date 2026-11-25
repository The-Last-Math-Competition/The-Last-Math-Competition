/-
Copyright (c) 2026. All rights reserved.
 Formalization of Conjecture 00000000593:
 Univariate integer polynomials, formal power series, and cyclotomic factor chains.
-/

namespace Conjecture00000000593

/-- Univariate polynomials over `Int`, represented by ascending coefficient lists
`[c₀, c₁, ..., c_d]` corresponding to `c₀ + c₁ t + ... + c_d t^d`. -/
abbrev ZPoly := List Int

/-- Formal power series over `Int`, represented by coefficient sequences `Nat → Int`. -/
abbrev Series := Nat → Int

/-- Extract the `n`-th coefficient of a polynomial `P`. -/
def coeff : ZPoly → Nat → Int
  | [], _ => 0
  | c :: _, 0 => c
  | _ :: cs, n + 1 => coeff cs n

/-- Coefficient-wise equality of two `ZPoly` representations in `ℤ[t]`. -/
def PolyEq (P Q : ZPoly) : Prop :=
  ∀ n : Nat, coeff P n = coeff Q n

theorem polyEq_refl (P : ZPoly) : PolyEq P P :=
  fun _ => rfl

theorem polyEq_symm {P Q : ZPoly} (h : PolyEq P Q) : PolyEq Q P :=
  fun n => (h n).symm

theorem polyEq_trans {P Q R : ZPoly} (h₁ : PolyEq P Q) (h₂ : PolyEq Q R) : PolyEq P R :=
  fun n => (h₁ n).trans (h₂ n)

theorem polyEq_of_eq {P Q : ZPoly} (h : P = Q) : PolyEq P Q := by
  subst h
  exact polyEq_refl P

/-- Evaluate a polynomial `P ∈ ℤ[t]` at `x ∈ ℤ`. -/
def eval : ZPoly → Int → Int
  | [], _ => 0
  | c :: cs, x => c + x * eval cs x

/-- Scalar multiplication `c * P` in `ℤ[t]`. -/
def scale (c : Int) : ZPoly → ZPoly
  | [] => []
  | a :: as => (c * a) :: scale c as

/-- Polynomial addition `P + Q` in `ℤ[t]`. -/
def add : ZPoly → ZPoly → ZPoly
  | [], bs => bs
  | as, [] => as
  | a :: as, b :: bs => (a + b) :: add as bs

/-- Polynomial multiplication `P * Q` in `ℤ[t]`. -/
def mul : ZPoly → ZPoly → ZPoly
  | [], _ => []
  | a :: as, bs => add (scale a bs) (0 :: mul as bs)

theorem coeff_nil (n : Nat) : coeff [] n = 0 := rfl

theorem coeff_scale (c : Int) (P : ZPoly) (n : Nat) :
    coeff (scale c P) n = c * coeff P n := by
  induction P generalizing n with
  | nil =>
    simp [scale, coeff]
  | cons a as ih =>
    cases n with
    | zero => rfl
    | succ m => exact ih m

theorem coeff_add (P Q : ZPoly) (n : Nat) :
    coeff (add P Q) n = coeff P n + coeff Q n := by
  induction P generalizing Q n with
  | nil =>
    simp [add, coeff]
  | cons a as ih =>
    cases Q with
    | nil =>
      simp [add, coeff]
    | cons b bs =>
      cases n with
      | zero => rfl
      | succ m => exact ih bs m

theorem mul_nil_right (P : ZPoly) : PolyEq (mul P []) [] := by
  induction P with
  | nil => intro _; rfl
  | cons a as ih =>
    intro n
    cases n with
    | zero => rfl
    | succ m =>
      simp only [mul, scale, add, coeff]
      exact ih m

theorem mul_cons_right (P : ZPoly) (b : Int) (bs : ZPoly) :
    PolyEq (mul P (b :: bs)) (add (scale b P) (0 :: mul P bs)) := by
  induction P with
  | nil =>
    intro n
    cases n <;> rfl
  | cons a as ih =>
    intro n
    cases n with
    | zero =>
      simp only [mul, scale, add, coeff, Int.add_zero]
      exact Int.mul_comm a b
    | succ m =>
      change coeff (add (scale a (b :: bs)) (0 :: mul as (b :: bs))) (m + 1) =
        coeff (add (scale b (a :: as)) (0 :: add (scale a bs) (0 :: mul as bs))) (m + 1)
      rw [coeff_add, coeff_add]
      have h1 : coeff (0 :: mul as (b :: bs)) (m + 1) = coeff (mul as (b :: bs)) m := rfl
      have h2 : coeff (0 :: add (scale a bs) (0 :: mul as bs)) (m + 1) =
          coeff (add (scale a bs) (0 :: mul as bs)) m := rfl
      have h3 : coeff (scale a (b :: bs)) (m + 1) = coeff (scale a bs) m := rfl
      have h4 : coeff (scale b (a :: as)) (m + 1) = coeff (scale b as) m := rfl
      rw [h1, h2, h3, h4, ih m, coeff_add, coeff_add]
      omega

theorem mul_comm_polyEq (P Q : ZPoly) : PolyEq (mul P Q) (mul Q P) := by
  induction P with
  | nil =>
    exact polyEq_symm (mul_nil_right Q)
  | cons a as ih =>
    intro n
    have hr := mul_cons_right Q a as n
    rw [hr]
    simp only [mul]
    rw [coeff_add, coeff_add]
    cases n with
    | zero =>
      have h0 : coeff (0 :: mul as Q) 0 = 0 := rfl
      have h0' : coeff (0 :: mul Q as) 0 = 0 := rfl
      rw [h0, h0']
    | succ m =>
      have h1 : coeff (0 :: mul as Q) (m + 1) = coeff (mul as Q) m := rfl
      have h2 : coeff (0 :: mul Q as) (m + 1) = coeff (mul Q as) m := rfl
      rw [h1, h2, ih m]

theorem coeff_gt_length (P : ZPoly) (n : Nat) (h : P.length ≤ n) : coeff P n = 0 := by
  induction P generalizing n with
  | nil => rfl
  | cons a as ih =>
    simp only [List.length_cons] at h
    cases n with
    | zero => omega
    | succ m => exact ih m (by omega)

theorem eval_eq_zero_of_all_zero (P : ZPoly) (h : ∀ n : Nat, coeff P n = 0) (x : Int) :
    eval P x = 0 := by
  induction P with
  | nil => rfl
  | cons a as ih =>
    have ha : a = 0 := h 0
    have has : ∀ m : Nat, coeff as m = 0 := fun m => h (m + 1)
    simp only [eval, ha, ih has, Int.mul_zero, Int.add_zero]

theorem eval_eq_of_polyEq {P Q : ZPoly} (h : PolyEq P Q) (x : Int) :
    eval P x = eval Q x := by
  induction P generalizing Q with
  | nil =>
    have hQ : ∀ n : Nat, coeff Q n = 0 := fun n => (h n).symm
    exact (eval_eq_zero_of_all_zero Q hQ x).symm
  | cons a as ih =>
    cases Q with
    | nil =>
      exact eval_eq_zero_of_all_zero (a :: as) h x
    | cons b bs =>
      have hab : a = b := h 0
      have hbs : PolyEq as bs := fun m => h (m + 1)
      simp only [eval, hab, ih hbs]

theorem eval_scale (c : Int) (P : ZPoly) (x : Int) :
    eval (scale c P) x = c * eval P x := by
  induction P with
  | nil => simp [scale, eval]
  | cons a as ih =>
    simp only [scale, eval, ih]
    rw [Int.mul_add, Int.mul_left_comm]

theorem eval_add (P Q : ZPoly) (x : Int) :
    eval (add P Q) x = eval P x + eval Q x := by
  induction P generalizing Q with
  | nil => simp [add, eval]
  | cons a as ih =>
    cases Q with
    | nil => simp [add, eval]
    | cons b bs =>
      simp only [add, eval, ih bs]
      rw [Int.mul_add]
      omega

theorem eval_mul (P Q : ZPoly) (x : Int) :
    eval (mul P Q) x = eval P x * eval Q x := by
  induction P with
  | nil => simp [mul, eval]
  | cons a as ih =>
    simp only [mul, eval]
    rw [eval_add, eval_scale]
    simp only [eval, Int.zero_add, ih]
    rw [Int.add_mul, Int.mul_assoc]

/-- Action of a polynomial `P ∈ ℤ[t]` on a formal power series `a ∈ ℤ[[t]]` via Cauchy product. -/
def mulPolySeries : ZPoly → Series → Series
  | [], _ => fun _ => 0
  | c :: cs, a => fun m =>
      match m with
      | 0 => c * a 0
      | m' + 1 => c * a (m' + 1) + mulPolySeries cs a m'

/-- The multiplicative identity `1 ∈ ℤ[[t]]`. -/
def unitSeries : Series :=
  fun m => if m = 0 then 1 else 0

theorem mulPolySeries_one_poly (a : Series) :
    mulPolySeries [1] a = a := by
  funext m
  cases m <;> simp [mulPolySeries]

theorem mulPolySeries_unit (P : ZPoly) (m : Nat) :
    mulPolySeries P unitSeries m = coeff P m := by
  induction P generalizing m with
  | nil => rfl
  | cons c cs ih =>
    cases m with
    | zero =>
      simp [mulPolySeries, unitSeries, coeff]
    | succ m' =>
      have hz : m' + 1 ≠ 0 := Nat.succ_ne_zero m'
      simp [mulPolySeries, unitSeries, coeff, hz, ih m']

theorem mulPolySeries_scale (c : Int) (P : ZPoly) (a : Series) (m : Nat) :
    mulPolySeries (scale c P) a m = c * mulPolySeries P a m := by
  induction P generalizing m with
  | nil => simp [scale, mulPolySeries]
  | cons b bs ih =>
    cases m with
    | zero =>
      simp only [scale, mulPolySeries, Int.mul_assoc]
    | succ m' =>
      simp only [scale, mulPolySeries, ih m', Int.mul_add, Int.mul_assoc]

theorem mulPolySeries_add (P Q : ZPoly) (a : Series) (m : Nat) :
    mulPolySeries (add P Q) a m = mulPolySeries P a m + mulPolySeries Q a m := by
  induction P generalizing Q m with
  | nil => simp [add, mulPolySeries]
  | cons b bs ih =>
    cases Q with
    | nil => simp [add, mulPolySeries]
    | cons c cs =>
      cases m with
      | zero =>
        simp only [add, mulPolySeries, Int.add_mul]
      | succ m' =>
        simp only [add, mulPolySeries, ih cs m', Int.add_mul]
        omega

theorem mulPolySeries_mul (P Q : ZPoly) (a : Series) :
    mulPolySeries (mul P Q) a = mulPolySeries P (mulPolySeries Q a) := by
  induction P with
  | nil => rfl
  | cons c cs ih =>
    funext m
    cases m with
    | zero =>
      simp only [mul, mulPolySeries]
      rw [mulPolySeries_add, mulPolySeries_scale]
      simp [mulPolySeries]
    | succ m' =>
      simp only [mul, mulPolySeries]
      rw [mulPolySeries_add, mulPolySeries_scale]
      have hz : mulPolySeries (0 :: mul cs Q) a (m' + 1) = mulPolySeries (mul cs Q) a m' := by
        simp [mulPolySeries]
      rw [hz, ih]

theorem mul_assoc_polyEq (P Q R : ZPoly) :
    PolyEq (mul (mul P Q) R) (mul P (mul Q R)) := by
  intro m
  rw [← mulPolySeries_unit (mul (mul P Q) R) m, ← mulPolySeries_unit (mul P (mul Q R)) m]
  rw [mulPolySeries_mul (mul P Q) R unitSeries]
  rw [mulPolySeries_mul P Q (mulPolySeries R unitSeries)]
  rw [mulPolySeries_mul P (mul Q R) unitSeries]
  rw [mulPolySeries_mul Q R unitSeries]

theorem mulPolySeries_eq_zero_of_all_zero (P : ZPoly) (h : ∀ n : Nat, coeff P n = 0)
    (a : Series) (m : Nat) : mulPolySeries P a m = 0 := by
  induction P generalizing m with
  | nil => rfl
  | cons c cs ih =>
    have hc : c = 0 := h 0
    have hcs : ∀ n : Nat, coeff cs n = 0 := fun n => h (n + 1)
    cases m with
    | zero => simp [mulPolySeries, hc]
    | succ m' => simp [mulPolySeries, hc, ih hcs m']

theorem mulPolySeries_congr_left {P Q : ZPoly} (h : PolyEq P Q) (a : Series) :
    mulPolySeries P a = mulPolySeries Q a := by
  induction P generalizing Q with
  | nil =>
    funext m
    exact (mulPolySeries_eq_zero_of_all_zero Q (fun n => (h n).symm) a m).symm
  | cons b bs ih =>
    cases Q with
    | nil =>
      funext m
      exact mulPolySeries_eq_zero_of_all_zero (b :: bs) h a m
    | cons c cs =>
      funext m
      have hbc : b = c := h 0
      have hcs : PolyEq bs cs := fun n => h (n + 1)
      cases m with
      | zero => simp [mulPolySeries, hbc]
      | succ m' =>
        simp only [mulPolySeries, hbc]
        rw [ih hcs]

theorem mul_congr {P₁ P₂ Q₁ Q₂ : ZPoly} (hP : PolyEq P₁ P₂) (hQ : PolyEq Q₁ Q₂) :
    PolyEq (mul P₁ Q₁) (mul P₂ Q₂) := by
  intro m
  rw [← mulPolySeries_unit (mul P₁ Q₁) m, ← mulPolySeries_unit (mul P₂ Q₂) m]
  rw [mulPolySeries_mul, mulPolySeries_mul]
  have hQ' : mulPolySeries Q₁ unitSeries = mulPolySeries Q₂ unitSeries :=
    mulPolySeries_congr_left hQ unitSeries
  rw [hQ']
  exact congrFun (mulPolySeries_congr_left hP (mulPolySeries Q₂ unitSeries)) m

/-- Polynomial divisibility `P ∣ Q` in `ℤ[t]`. -/
def PolyDvd (P Q : ZPoly) : Prop :=
  ∃ R : ZPoly, PolyEq Q (mul P R)

theorem polyDvd_refl (P : ZPoly) : PolyDvd P P := by
  refine ⟨[1], ?_⟩
  intro m
  rw [← mulPolySeries_unit P m, ← mulPolySeries_unit (mul P [1]) m]
  rw [mulPolySeries_mul P [1] unitSeries, mulPolySeries_one_poly]

theorem polyDvd_trans {P Q R : ZPoly} (h₁ : PolyDvd P Q) (h₂ : PolyDvd Q R) :
    PolyDvd P R := by
  rcases h₁ with ⟨A, hA⟩
  rcases h₂ with ⟨B, hB⟩
  refine ⟨mul A B, ?_⟩
  exact polyEq_trans hB (polyEq_trans (mul_congr hA (polyEq_refl B)) (mul_assoc_polyEq P A B))

theorem polyDvd_mul {P₁ Q₁ P₂ Q₂ : ZPoly} (h₁ : PolyDvd P₁ Q₁) (h₂ : PolyDvd P₂ Q₂) :
    PolyDvd (mul P₁ P₂) (mul Q₁ Q₂) := by
  rcases h₁ with ⟨A, hA⟩
  rcases h₂ with ⟨B, hB⟩
  refine ⟨mul A B, ?_⟩
  have s1 : PolyEq (mul Q₁ Q₂) (mul (mul P₁ A) (mul P₂ B)) := mul_congr hA hB
  have s2 : PolyEq (mul (mul P₁ A) (mul P₂ B)) (mul P₁ (mul A (mul P₂ B))) :=
    mul_assoc_polyEq P₁ A (mul P₂ B)
  have s3 : PolyEq (mul A (mul P₂ B)) (mul (mul A P₂) B) :=
    polyEq_symm (mul_assoc_polyEq A P₂ B)
  have s4 : PolyEq (mul (mul A P₂) B) (mul (mul P₂ A) B) :=
    mul_congr (mul_comm_polyEq A P₂) (polyEq_refl B)
  have s5 : PolyEq (mul (mul P₂ A) B) (mul P₂ (mul A B)) :=
    mul_assoc_polyEq P₂ A B
  have s6 : PolyEq (mul P₁ (mul A (mul P₂ B))) (mul P₁ (mul P₂ (mul A B))) :=
    mul_congr (polyEq_refl P₁) (polyEq_trans s3 (polyEq_trans s4 s5))
  have s7 : PolyEq (mul P₁ (mul P₂ (mul A B))) (mul (mul P₁ P₂) (mul A B)) :=
    polyEq_symm (mul_assoc_polyEq P₁ P₂ (mul A B))
  exact polyEq_trans s1 (polyEq_trans s2 (polyEq_trans s6 s7))

/-- Monomial `t^d` in `ℤ[t]`. -/
def tPow : Nat → ZPoly
  | 0 => [1]
  | d + 1 => 0 :: tPow d

theorem coeff_tPow (d m : Nat) : coeff (tPow d) m = if m = d then 1 else 0 := by
  induction d generalizing m with
  | zero =>
    cases m <;> rfl
  | succ d' ih =>
    cases m with
    | zero => rfl
    | succ m' =>
      simp only [tPow, coeff, ih m']
      by_cases h : m' = d' <;> simp [h]

theorem eval_tPow_one (d : Nat) : eval (tPow d) 1 = 1 := by
  induction d with
  | zero => rfl
  | succ _ ih => simp [tPow, eval, ih]

theorem mulPolySeries_tPow (d : Nat) (a : Series) (m : Nat) :
    mulPolySeries (tPow d) a m = if m < d then 0 else a (m - d) := by
  induction d generalizing m with
  | zero =>
    cases m <;> simp [tPow, mulPolySeries]
  | succ d' ih =>
    cases m with
    | zero => simp [tPow, mulPolySeries]
    | succ m' =>
      simp only [tPow, mulPolySeries, Int.zero_mul, Int.zero_add, ih m']
      by_cases h : m' < d'
      · have h2 : m' + 1 < d' + 1 := by omega
        simp [h, h2]
      · have h2 : ¬ (m' + 1 < d' + 1) := by omega
        have h3 : m' + 1 - (d' + 1) = m' - d' := by omega
        simp [h, h2, h3]

/-- The cyclotomic-chain factor `1 - t^d` in `ℤ[t]`. -/
def oneMinusTPow (d : Nat) : ZPoly :=
  add [1] (scale (-1) (tPow d))

theorem coeff_oneMinusTPow_zero {d : Nat} (hd : 1 ≤ d) :
    coeff (oneMinusTPow d) 0 = 1 := by
  cases d with
  | zero => omega
  | succ _ => rfl

theorem eval_oneMinusTPow_one (d : Nat) : eval (oneMinusTPow d) 1 = 0 := by
  unfold oneMinusTPow
  rw [eval_add, eval_scale, eval_tPow_one]
  simp [eval]

/-- The shift-subtract operator `((1 - t^d) · a)_m` on formal power series. -/
def shiftSub (d : Nat) (a : Series) : Series :=
  fun m => if m < d then a m else a m - a (m - d)

theorem mulPolySeries_oneMinusTPow {d : Nat} (hd : 1 ≤ d) (a : Series) :
    mulPolySeries (oneMinusTPow d) a = shiftSub d a := by
  funext m
  have _ := hd
  unfold oneMinusTPow shiftSub
  rw [mulPolySeries_add, mulPolySeries_scale, mulPolySeries_tPow, mulPolySeries_one_poly]
  by_cases hm : m < d
  · simp [hm]
  · simp [hm]
    omega

/-- Product `∏_{d ∈ ds} (1 - t^d)` of a finite chain of factors `(1 - t^d)`. -/
def chainProd : List Nat → ZPoly
  | [] => [1]
  | d :: ds => mul (oneMinusTPow d) (chainProd ds)

theorem coeff_chainProd_zero : ∀ {ds : List Nat}, (∀ d ∈ ds, 1 ≤ d) → coeff (chainProd ds) 0 = 1
  | [], _ => rfl
  | d :: ds, h => by
    have hd : 1 ≤ d := h d (List.mem_cons_self ..)
    have hds : ∀ x ∈ ds, 1 ≤ x := fun x hx => h x (List.mem_cons_of_mem d hx)
    rw [← mulPolySeries_unit (chainProd (d :: ds)) 0]
    simp only [chainProd]
    rw [mulPolySeries_mul, mulPolySeries_oneMinusTPow hd]
    unfold shiftSub
    have hlt : 0 < d := by omega
    simp only [hlt, ↓reduceIte]
    rw [mulPolySeries_unit]
    exact coeff_chainProd_zero hds

theorem mulPolySeries_chainProd : ∀ {ds : List Nat}, (∀ d ∈ ds, 1 ≤ d) → ∀ (a : Series),
    mulPolySeries (chainProd ds) a = ds.foldr shiftSub a
  | [], _, a => mulPolySeries_one_poly a
  | d :: ds, h, a => by
    have hd : 1 ≤ d := h d (List.mem_cons_self ..)
    have hds : ∀ x ∈ ds, 1 ≤ x := fun x hx => h x (List.mem_cons_of_mem d hx)
    simp only [chainProd, List.foldr_cons]
    rw [mulPolySeries_mul, mulPolySeries_oneMinusTPow hd, mulPolySeries_chainProd hds a]

/-- `f` vanishes at all degrees `m ≥ B` (i.e., `f` is a polynomial of degree `< B`). -/
def IsPolyBelow (B : Nat) (f : Series) : Prop :=
  ∀ m : Nat, B ≤ m → f m = 0

/-- `f ∈ ℤ[[t]]` is a polynomial (`f ∈ ℤ[t]`, finitely many nonzero terms). -/
def IsPolynomialSeries (f : Series) : Prop :=
  ∃ B : Nat, IsPolyBelow B f

/-- `a ∈ ℤ[[t]]` represents a rational function `P(t) / Q(t) ∈ ℚ(t)` (`Q(0) = 1`)
whose reduced denominator `Q(t)` divides `C(t)` (`C(0) = 1`): equivalently, `C(t) · a(t) ∈ ℤ[t]`. -/
def HasDenominatorDividing (C : ZPoly) (a : Series) : Prop :=
  coeff C 0 = 1 ∧ IsPolynomialSeries (mulPolySeries C a)

theorem isPolyBelow_mulPolySeries (R : ZPoly) {B : Nat} {f : Series}
    (hf : IsPolyBelow B f) : IsPolyBelow (B + R.length) (mulPolySeries R f) := by
  induction R generalizing B with
  | nil =>
    intro m _
    rfl
  | cons c cs ih =>
    intro m hm
    cases m with
    | zero =>
      simp only [List.length_cons] at hm
      omega
    | succ m' =>
      simp only [mulPolySeries]
      have h1 : B ≤ m' + 1 := by simp only [List.length_cons] at hm; omega
      have h2 : B + cs.length ≤ m' := by simp only [List.length_cons] at hm; omega
      rw [hf (m' + 1) h1, ih hf m' h2]
      simp

/-- Monotonicity of denominator divisibility: if `C₁ ∣ C₂` in `ℤ[t]` (`C₂(0) = 1`),
any series with denominator dividing `C₁` also has denominator dividing `C₂`. -/
theorem hasDenominatorDividing_mono {C₁ C₂ : ZPoly} {a : Series}
    (hdvd : PolyDvd C₁ C₂) (hC₂ : coeff C₂ 0 = 1)
    (ha : HasDenominatorDividing C₁ a) : HasDenominatorDividing C₂ a := by
  refine ⟨hC₂, ?_⟩
  rcases hdvd with ⟨R, hR⟩
  rcases ha.2 with ⟨B, hB⟩
  have hcomm : PolyEq C₂ (mul R C₁) := polyEq_trans hR (mul_comm_polyEq C₁ R)
  have hser : mulPolySeries C₂ a = mulPolySeries R (mulPolySeries C₁ a) := by
    rw [mulPolySeries_congr_left hcomm a, mulPolySeries_mul]
  rw [hser]
  exact ⟨B + R.length, isPolyBelow_mulPolySeries R hB⟩

end Conjecture00000000593
