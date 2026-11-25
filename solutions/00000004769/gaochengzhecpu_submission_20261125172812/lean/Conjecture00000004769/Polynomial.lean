/-
  Conjecture00000004769/Polynomial.lean
  First-principles univariate integer polynomials Z[q] in Core Lean 4.19.0.
  Includes normalized representation, ring laws, evaluation, coefficient reversal,
  palindromic polynomials, and exact monic Euclidean division.
-/

namespace Conjecture00000004769

/-- Normalized little-endian coefficient list `[c_0, c_1, ..., c_d]` for `Z[q]`. -/
abbrev Poly := List Int

/-- Coefficient of `q^k` in `p`. -/
def coeff : Poly → Nat → Int
  | [], _ => 0
  | c :: _, 0 => c
  | _ :: cs, k + 1 => coeff cs k

theorem coeff_congr {p q : Poly} (h : p = q) (k : Nat) : coeff p k = coeff q k :=
  h ▸ rfl

theorem int_pow_add (x : Int) (a b : Nat) : x ^ (a + b) = x ^ a * x ^ b := by
  induction b with
  | zero => simp [Int.pow_zero, Int.mul_one]
  | succ b ih =>
    rw [Nat.add_succ, Int.pow_succ, ih, Int.pow_succ, Int.mul_assoc]

theorem int_one_pow (n : Nat) : (1 : Int) ^ n = 1 := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Int.pow_succ, ih, Int.mul_one]

/-- Strip trailing zeros so that equal polynomials have identical list representations. -/
def trim : Poly → Poly
  | [] => []
  | c :: cs =>
    let cs' := trim cs
    if cs' = [] ∧ c = 0 then [] else c :: cs'

theorem coeff_nil (k : Nat) : coeff [] k = 0 := rfl

theorem coeff_trim (p : Poly) : ∀ k, coeff (trim p) k = coeff p k := by
  induction p with
  | nil => intro _; rfl
  | cons c cs ih =>
    intro k
    dsimp only [trim]
    split
    · next h =>
      rcases h with ⟨hcs, hc⟩
      cases k with
      | zero => simp [coeff, hc]
      | succ k' =>
        simp only [coeff]
        have h0 : coeff (trim cs) k' = 0 := by rw [hcs]; rfl
        rw [← ih k', h0]
    · cases k with
      | zero => rfl
      | succ k' => exact ih k'

theorem trim_eq_nil_iff (p : Poly) : trim p = [] ↔ ∀ k, coeff p k = 0 := by
  induction p with
  | nil =>
    constructor
    · intro _ _; rfl
    · intro _; rfl
  | cons c cs ih =>
    dsimp only [trim]
    constructor
    · intro h k
      split at h
      · next hc =>
        rcases hc with ⟨hcs, hc0⟩
        cases k with
        | zero => exact hc0
        | succ k' => exact (ih.mp hcs) k'
      · contradiction
    · intro hall
      have hc0 : c = 0 := hall 0
      have hcs : trim cs = [] := ih.mpr (fun k => hall (k + 1))
      simp [hcs, hc0]

theorem trim_idem (p : Poly) : trim (trim p) = trim p := by
  induction p with
  | nil => rfl
  | cons c cs ih =>
    dsimp only [trim]
    split
    · rfl
    · next h =>
      dsimp only [trim]
      rw [ih]
      exact if_neg h

theorem trim_tail_of_trimmed {c : Int} {cs : Poly} (hp : trim (c :: cs) = c :: cs) :
    trim cs = cs ∧ ¬(cs = [] ∧ c = 0) := by
  dsimp only [trim] at hp
  split at hp
  · contradiction
  · next h =>
    have htl : trim cs = cs := List.cons.inj hp |>.2
    refine ⟨htl, ?_⟩
    rw [htl] at h
    exact h

theorem poly_ext {p q : Poly} (hp : trim p = p) (hq : trim q = q)
    (h : ∀ k, coeff p k = coeff q k) : p = q := by
  induction p generalizing q with
  | nil =>
    have hall : ∀ k, coeff q k = 0 := fun k => (h k).symm
    have hq0 : trim q = [] := (trim_eq_nil_iff q).mpr hall
    rw [← hq, hq0]
  | cons c cs ih =>
    rcases trim_tail_of_trimmed hp with ⟨hcs_trim, hne_p⟩
    cases q with
    | nil =>
      exfalso
      apply hne_p
      have hc0 : c = 0 := h 0
      have hcs0 : trim cs = [] := (trim_eq_nil_iff cs).mpr (fun k => h (k + 1))
      rw [← hcs_trim, hcs0]
      exact ⟨rfl, hc0⟩
    | cons d ds =>
      rcases trim_tail_of_trimmed hq with ⟨hds_trim, _⟩
      have hcd : c = d := h 0
      have hcs_ds : cs = ds := ih hcs_trim hds_trim (fun k => h (k + 1))
      rw [hcd, hcs_ds]

theorem trim_eq_of_coeff_eq {p q : Poly} (h : ∀ k, coeff p k = coeff q k) :
    trim p = trim q := by
  apply poly_ext (trim_idem p) (trim_idem q)
  intro k
  rw [coeff_trim, coeff_trim, h k]

/-- Finite integer sum `∑_{i=0}^{n-1} f i`. -/
def sumRange : Nat → (Nat → Int) → Int
  | 0, _ => 0
  | n + 1, f => sumRange n f + f n

theorem sumRange_congr {n : Nat} {f g : Nat → Int} (h : ∀ i, i < n → f i = g i) :
    sumRange n f = sumRange n g := by
  induction n with
  | zero => rfl
  | succ n ih =>
    dsimp only [sumRange]
    rw [ih (fun i hi => h i (Nat.lt_succ_of_lt hi)), h n (Nat.lt_succ_self n)]

theorem sumRange_zero (n : Nat) : sumRange n (fun _ => 0) = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => dsimp only [sumRange]; rw [ih]; rfl

theorem sumRange_add (n : Nat) (f g : Nat → Int) :
    sumRange n (fun i => f i + g i) = sumRange n f + sumRange n g := by
  induction n with
  | zero => rfl
  | succ n ih =>
    dsimp only [sumRange]
    rw [ih]; omega

theorem sumRange_neg (n : Nat) (f : Nat → Int) :
    sumRange n (fun i => -f i) = -sumRange n f := by
  induction n with
  | zero => rfl
  | succ n ih =>
    dsimp only [sumRange]
    rw [ih]; omega

theorem sumRange_mul_left (n : Nat) (c : Int) (f : Nat → Int) :
    sumRange n (fun i => c * f i) = c * sumRange n f := by
  induction n with
  | zero => simp [sumRange]
  | succ n ih =>
    dsimp only [sumRange]
    rw [ih, Int.mul_add]

theorem sumRange_mul_right (n : Nat) (f : Nat → Int) (c : Int) :
    sumRange n (fun i => f i * c) = sumRange n f * c := by
  induction n with
  | zero => simp [sumRange]
  | succ n ih =>
    dsimp only [sumRange]
    rw [ih, Int.add_mul]

theorem sumRange_split_first (n : Nat) (f : Nat → Int) :
    sumRange (n + 1) f = f 0 + sumRange n (fun i => f (i + 1)) := by
  induction n with
  | zero => dsimp only [sumRange]; omega
  | succ n ih =>
    rw [sumRange, ih]
    conv => rhs; rw [sumRange]
    omega

theorem sumRange_rev (n : Nat) (f : Nat → Int) :
    sumRange (n + 1) f = sumRange (n + 1) (fun i => f (n - i)) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [sumRange_split_first (n + 1) (fun i => f (n + 1 - i))]
    simp only [Nat.sub_zero]
    have hsub : sumRange (n + 1) (fun i => f (n + 1 - (i + 1))) =
        sumRange (n + 1) (fun i => f (n - i)) := by
      apply sumRange_congr
      intro i _
      have : n + 1 - (i + 1) = n - i := by omega
      rw [this]
    rw [hsub, ← ih]
    rw [sumRange]
    omega

theorem sumRange_single {n k : Nat} (hk : k < n) (v : Int) :
    sumRange n (fun i => if i = k then v else 0) = v := by
  induction n with
  | zero => omega
  | succ n ih =>
    rw [sumRange]
    by_cases hkn : n = k
    · rw [if_pos hkn]
      have hz : sumRange n (fun i => if i = k then v else 0) = 0 := by
        rw [sumRange_congr (g := fun _ => 0)]
        · exact sumRange_zero n
        · intro i hi
          have hne : i ≠ k := by omega
          exact if_neg hne
      rw [hz, Int.zero_add]
    · rw [if_neg hkn, ih (by omega), Int.add_zero]

theorem sumRange_extend {n m : Nat} (hnm : n ≤ m) (f : Nat → Int)
    (hz : ∀ i, n ≤ i → i < m → f i = 0) :
    sumRange n f = sumRange m f := by
  induction m with
  | zero =>
    have hn0 : n = 0 := by omega
    rw [hn0]
  | succ m ih =>
    by_cases hnm' : n ≤ m
    · rw [sumRange]
      rw [ih hnm' (fun i h1 h2 => hz i h1 (Nat.lt_succ_of_lt h2))]
      rw [hz m hnm' (Nat.lt_succ_self m), Int.add_zero]
    · have hneq : n = m + 1 := by omega
      rw [hneq]

theorem sumRange_swap (m n : Nat) (f : Nat → Nat → Int) :
    sumRange m (fun i => sumRange n (fun j => f i j)) =
    sumRange n (fun j => sumRange m (fun i => f i j)) := by
  induction m with
  | zero =>
    dsimp only [sumRange]
    rw [sumRange_zero]
  | succ m ih =>
    dsimp only [sumRange]
    rw [ih, ← sumRange_add]

/-- Build a normalized polynomial of length at most `len` from its coefficient function. -/
def ofFnAux : Nat → (Nat → Int) → Poly
  | 0, _ => []
  | n + 1, f => f 0 :: ofFnAux n (fun k => f (k + 1))

def ofFn (len : Nat) (f : Nat → Int) : Poly :=
  trim (ofFnAux len f)

theorem coeff_ofFnAux (len : Nat) (f : Nat → Int) (k : Nat) :
    coeff (ofFnAux len f) k = if k < len then f k else 0 := by
  induction len generalizing f k with
  | zero => simp [ofFnAux, coeff]
  | succ len ih =>
    cases k with
    | zero => simp [ofFnAux, coeff]
    | succ k' =>
      dsimp only [ofFnAux, coeff]
      rw [ih]
      have : (k' + 1 < len + 1) ↔ (k' < len) := by omega
      simp [this]

theorem coeff_ofFn (len : Nat) (f : Nat → Int) (k : Nat) :
    coeff (ofFn len f) k = if k < len then f k else 0 := by
  rw [ofFn, coeff_trim, coeff_ofFnAux]

theorem trim_ofFn (len : Nat) (f : Nat → Int) : trim (ofFn len f) = ofFn len f :=
  trim_idem _

theorem coeff_eq_zero_of_ge_length (p : Poly) {k : Nat} (hk : p.length ≤ k) :
    coeff p k = 0 := by
  induction p generalizing k with
  | nil => rfl
  | cons _ cs ih =>
    cases k with
    | zero => simp at hk
    | succ k' =>
      simp only [List.length_cons] at hk
      exact ih (by omega)

/-- Standard ring constructors and operations on `Poly`. -/
def zero : Poly := []
def one : Poly := [1]
def constPoly (c : Int) : Poly := trim [c]
def X : Poly := [0, 1]

def add (p q : Poly) : Poly :=
  ofFn (max p.length q.length) (fun k => coeff p k + coeff q k)

def neg (p : Poly) : Poly :=
  ofFn p.length (fun k => -coeff p k)

def sub (p q : Poly) : Poly :=
  ofFn (max p.length q.length) (fun k => coeff p k - coeff q k)

def scale (c : Int) (p : Poly) : Poly :=
  ofFn p.length (fun k => c * coeff p k)

def shift (p : Poly) (s : Nat) : Poly :=
  ofFn (p.length + s) (fun k => if k < s then 0 else coeff p (k - s))

def mul (p q : Poly) : Poly :=
  ofFn (p.length + q.length) (fun k => sumRange (k + 1) (fun i => coeff p i * coeff q (k - i)))

theorem trim_zero : trim zero = zero := rfl
theorem trim_one : trim one = one := rfl
theorem trim_const (c : Int) : trim (constPoly c) = constPoly c := trim_idem _
theorem trim_add (p q : Poly) : trim (add p q) = add p q := trim_ofFn _ _
theorem trim_neg (p : Poly) : trim (neg p) = neg p := trim_ofFn _ _
theorem trim_sub (p q : Poly) : trim (sub p q) = sub p q := trim_ofFn _ _
theorem trim_scale (c : Int) (p : Poly) : trim (scale c p) = scale c p := trim_ofFn _ _
theorem trim_shift (p : Poly) (s : Nat) : trim (shift p s) = shift p s := trim_ofFn _ _
theorem trim_mul (p q : Poly) : trim (mul p q) = mul p q := trim_ofFn _ _

theorem coeff_zero (k : Nat) : coeff zero k = 0 := rfl

theorem coeff_one (k : Nat) : coeff one k = if k = 0 then 1 else 0 := by
  cases k with
  | zero => rfl
  | succ k' => cases k' <;> rfl

theorem coeff_const (c : Int) (k : Nat) : coeff (constPoly c) k = if k = 0 then c else 0 := by
  rw [constPoly, coeff_trim]
  cases k with
  | zero => rfl
  | succ k' => cases k' <;> rfl

theorem coeff_add (p q : Poly) (k : Nat) : coeff (add p q) k = coeff p k + coeff q k := by
  rw [add, coeff_ofFn]
  split
  · rfl
  · next h =>
    have hp : p.length ≤ k := by omega
    have hq : q.length ≤ k := by omega
    rw [coeff_eq_zero_of_ge_length p hp, coeff_eq_zero_of_ge_length q hq]
    omega

theorem coeff_neg (p : Poly) (k : Nat) : coeff (neg p) k = -coeff p k := by
  rw [neg, coeff_ofFn]
  split
  · rfl
  · next h =>
    have hp : p.length ≤ k := by omega
    rw [coeff_eq_zero_of_ge_length p hp]
    omega

theorem coeff_sub (p q : Poly) (k : Nat) : coeff (sub p q) k = coeff p k - coeff q k := by
  rw [sub, coeff_ofFn]
  split
  · rfl
  · next h =>
    have hp : p.length ≤ k := by omega
    have hq : q.length ≤ k := by omega
    rw [coeff_eq_zero_of_ge_length p hp, coeff_eq_zero_of_ge_length q hq]
    omega

theorem coeff_scale (c : Int) (p : Poly) (k : Nat) : coeff (scale c p) k = c * coeff p k := by
  rw [scale, coeff_ofFn]
  split
  · rfl
  · next h =>
    have hp : p.length ≤ k := by omega
    rw [coeff_eq_zero_of_ge_length p hp, Int.mul_zero]

theorem coeff_shift (p : Poly) (s k : Nat) :
    coeff (shift p s) k = if k < s then 0 else coeff p (k - s) := by
  rw [shift, coeff_ofFn]
  split
  · rfl
  · next h =>
    split
    · omega
    · next hks =>
      have hp : p.length ≤ k - s := by omega
      rw [coeff_eq_zero_of_ge_length p hp]

theorem coeff_mul (p q : Poly) (k : Nat) :
    coeff (mul p q) k = sumRange (k + 1) (fun i => coeff p i * coeff q (k - i)) := by
  rw [mul, coeff_ofFn]
  split
  · rfl
  · next h =>
    symm
    rw [sumRange_congr (g := fun _ => 0)]
    · exact sumRange_zero (k + 1)
    · intro i _
      by_cases hip : p.length ≤ i
      · rw [coeff_eq_zero_of_ge_length p hip, Int.zero_mul]
      · have hiq : q.length ≤ k - i := by omega
        rw [coeff_eq_zero_of_ge_length q hiq, Int.mul_zero]

/-- Two-dimensional convolution representation when degrees are bounded by `dp` and `dq`. -/
theorem coeff_mul_rect {p q : Poly} {dp dq : Nat}
    (hp : ∀ i, dp < i → coeff p i = 0) (hq : ∀ j, dq < j → coeff q j = 0) (k : Nat) :
    coeff (mul p q) k =
      sumRange (dp + 1) (fun i =>
        sumRange (dq + 1) (fun j => if i + j = k then coeff p i * coeff q j else 0)) := by
  rw [coeff_mul]
  let m := max (k + 1) (dp + 1)
  have hm1 : k + 1 ≤ m := Nat.le_max_left _ _
  have hm2 : dp + 1 ≤ m := Nat.le_max_right _ _
  have hL : sumRange (k + 1) (fun i => coeff p i * coeff q (k - i)) =
      sumRange m (fun i => if i ≤ k then coeff p i * coeff q (k - i) else 0) := by
    have h1 : sumRange (k + 1) (fun i => coeff p i * coeff q (k - i)) =
        sumRange (k + 1) (fun i => if i ≤ k then coeff p i * coeff q (k - i) else 0) := by
      apply sumRange_congr
      intro i hi
      exact (if_pos (by omega : i ≤ k)).symm
    rw [h1]
    apply sumRange_extend hm1
    intro i hge _
    exact if_neg (by omega : ¬(i ≤ k))
  have hR : sumRange (dp + 1) (fun i =>
        sumRange (dq + 1) (fun j => if i + j = k then coeff p i * coeff q j else 0)) =
      sumRange m (fun i =>
        sumRange (dq + 1) (fun j => if i + j = k then coeff p i * coeff q j else 0)) := by
    apply sumRange_extend hm2
    intro i h1 _
    have hpi : coeff p i = 0 := hp i (by omega)
    rw [sumRange_congr (g := fun _ => 0)]
    · exact sumRange_zero (dq + 1)
    · intro j _
      rw [hpi, Int.zero_mul]
      split <;> rfl
  rw [hL, hR]
  apply sumRange_congr
  intro i _
  by_cases hik : i ≤ k
  · rw [if_pos hik]
    by_cases hjdq : k - i ≤ dq
    · have hlt : k - i < dq + 1 := by omega
      have hcongr : sumRange (dq + 1) (fun j => if i + j = k then coeff p i * coeff q j else 0) =
          sumRange (dq + 1) (fun j => if j = k - i then coeff p i * coeff q (k - i) else 0) := by
        apply sumRange_congr
        intro j _
        by_cases hjk : i + j = k
        · have hj_eq : j = k - i := by omega
          rw [if_pos hjk, if_pos hj_eq, hj_eq]
        · have hj_ne : j ≠ k - i := by omega
          rw [if_neg hjk, if_neg hj_ne]
      rw [hcongr, sumRange_single hlt]
    · have hq0 : coeff q (k - i) = 0 := hq (k - i) (by omega)
      rw [hq0, Int.mul_zero]
      symm
      rw [sumRange_congr (g := fun _ => 0)]
      · exact sumRange_zero (dq + 1)
      · intro j hj
        exact if_neg (by omega : i + j ≠ k)
  · rw [if_neg hik]
    symm
    rw [sumRange_congr (g := fun _ => 0)]
    · exact sumRange_zero (dq + 1)
    · intro j _
      exact if_neg (by omega : i + j ≠ k)

/-- Basic algebraic laws on normalized polynomials. -/
theorem add_comm (p q : Poly) : add p q = add q p := by
  apply poly_ext (trim_add p q) (trim_add q p)
  intro k; rw [coeff_add, coeff_add, Int.add_comm]

theorem add_assoc (p q r : Poly) : add (add p q) r = add p (add q r) := by
  apply poly_ext (trim_add _ _) (trim_add _ _)
  intro k; simp [coeff_add, Int.add_assoc]

theorem add_zero_right (p : Poly) (hp : trim p = p) : add p zero = p := by
  apply poly_ext (trim_add _ _) hp
  intro k; simp [coeff_add, coeff_zero]

theorem zero_add_left (p : Poly) (hp : trim p = p) : add zero p = p := by
  rw [add_comm]; exact add_zero_right p hp

theorem sub_eq_add_neg (p q : Poly) : sub p q = add p (neg q) := by
  apply poly_ext (trim_sub _ _) (trim_add _ _)
  intro k; rw [coeff_sub, coeff_add, coeff_neg, Int.sub_eq_add_neg]

theorem mul_comm (p q : Poly) : mul p q = mul q p := by
  apply poly_ext (trim_mul p q) (trim_mul q p)
  intro k
  rw [coeff_mul, coeff_mul, sumRange_rev k (fun i => coeff p i * coeff q (k - i))]
  apply sumRange_congr
  intro i hi
  have : k - (k - i) = i := by omega
  rw [this, Int.mul_comm]

theorem mul_one_eq_trim (p : Poly) : mul p one = trim p := by
  apply poly_ext (trim_mul p one) (trim_idem p)
  intro k
  rw [coeff_mul, coeff_trim]
  have hcongr : sumRange (k + 1) (fun i => coeff p i * coeff one (k - i)) =
      sumRange (k + 1) (fun i => if i = k then coeff p k else 0) := by
    apply sumRange_congr
    intro i hi
    rw [coeff_one]
    by_cases hik : i = k
    · rw [hik, Nat.sub_self, if_pos rfl, if_pos rfl, Int.mul_one]
    · rw [if_neg (by omega : k - i ≠ 0), if_neg hik, Int.mul_zero]
  rw [hcongr, sumRange_single (Nat.lt_succ_self k)]

theorem one_mul_eq_trim (p : Poly) : mul one p = trim p := by
  rw [mul_comm, mul_one_eq_trim]

theorem mul_one_right (p : Poly) (hp : trim p = p) : mul p one = p := by
  rw [mul_one_eq_trim, hp]

theorem one_mul_left (p : Poly) (hp : trim p = p) : mul one p = p := by
  rw [one_mul_eq_trim, hp]

theorem mul_zero_right (p : Poly) : mul p zero = zero := by
  apply poly_ext (trim_mul p zero) trim_zero
  intro k
  rw [coeff_mul, coeff_zero, sumRange_congr (g := fun _ => 0)]
  · exact sumRange_zero (k + 1)
  · intro i _; simp [coeff_zero]

theorem mul_add (p q r : Poly) : mul p (add q r) = add (mul p q) (mul p r) := by
  apply poly_ext (trim_mul _ _) (trim_add _ _)
  intro k
  rw [coeff_mul, coeff_add, coeff_mul, coeff_mul, ← sumRange_add]
  apply sumRange_congr
  intro i _
  rw [coeff_add, Int.mul_add]

theorem add_mul (p q r : Poly) : mul (add p q) r = add (mul p r) (mul q r) := by
  rw [mul_comm, mul_add, mul_comm p r, mul_comm q r]

theorem mul_sub (p q r : Poly) : mul p (sub q r) = sub (mul p q) (mul p r) := by
  apply poly_ext (trim_mul _ _) (trim_sub _ _)
  intro k
  rw [coeff_mul, coeff_sub, coeff_mul, coeff_mul]
  have h1 : sumRange (k + 1) (fun i => coeff p i * coeff (sub q r) (k - i)) =
      sumRange (k + 1) (fun i => coeff p i * coeff q (k - i) + -(coeff p i * coeff r (k - i))) := by
    apply sumRange_congr
    intro i _
    rw [coeff_sub, Int.mul_sub, Int.sub_eq_add_neg]
  rw [h1, sumRange_add, sumRange_neg, ← Int.sub_eq_add_neg]

theorem scale_mul_left (c : Int) (p q : Poly) : mul (scale c p) q = scale c (mul p q) := by
  apply poly_ext (trim_mul _ _) (trim_scale _ _)
  intro k
  rw [coeff_mul, coeff_scale, coeff_mul, ← sumRange_mul_left]
  apply sumRange_congr
  intro i _; rw [coeff_scale, Int.mul_assoc]

theorem mul_assoc (p q r : Poly) : mul (mul p q) r = mul p (mul q r) := by
  apply poly_ext (trim_mul _ _) (trim_mul _ _)
  intro k
  let dp := p.length
  let dq := q.length
  let dr := r.length
  have hp : ∀ i, dp < i → coeff p i = 0 := fun i hi => coeff_eq_zero_of_ge_length p (by omega)
  have hq : ∀ i, dq < i → coeff q i = 0 := fun i hi => coeff_eq_zero_of_ge_length q (by omega)
  have hr : ∀ i, dr < i → coeff r i = 0 := fun i hi => coeff_eq_zero_of_ge_length r (by omega)
  have hpq : ∀ i, dp + dq < i → coeff (mul p q) i = 0 := by
    intro i hi
    rw [coeff_mul_rect hp hq]
    rw [sumRange_congr (g := fun _ => 0)]
    · exact sumRange_zero _
    · intro a ha
      rw [sumRange_congr (g := fun _ => 0)]
      · exact sumRange_zero _
      · intro b hb; exact if_neg (by omega : a + b ≠ i)
  have hqr : ∀ i, dq + dr < i → coeff (mul q r) i = 0 := by
    intro i hi
    rw [coeff_mul_rect hq hr]
    rw [sumRange_congr (g := fun _ => 0)]
    · exact sumRange_zero _
    · intro a ha
      rw [sumRange_congr (g := fun _ => 0)]
      · exact sumRange_zero _
      · intro b hb; exact if_neg (by omega : a + b ≠ i)
  rw [coeff_mul_rect hpq hr, coeff_mul_rect hp hqr]
  have hL : sumRange (dp + dq + 1) (fun u =>
        sumRange (dr + 1) (fun c => if u + c = k then coeff (mul p q) u * coeff r c else 0)) =
      sumRange (dp + 1) (fun a =>
        sumRange (dq + 1) (fun b =>
          sumRange (dr + 1) (fun c => if a + b + c = k then coeff p a * coeff q b * coeff r c else 0))) := by
    rw [sumRange_swap (dp + dq + 1) (dr + 1)]
    have step1 : sumRange (dr + 1) (fun c =>
          sumRange (dp + dq + 1) (fun u => if u + c = k then coeff (mul p q) u * coeff r c else 0)) =
        sumRange (dr + 1) (fun c =>
          sumRange (dp + 1) (fun a =>
            sumRange (dq + 1) (fun b => if a + b + c = k then coeff p a * coeff q b * coeff r c else 0))) := by
      apply sumRange_congr
      intro c _
      by_cases hck : c ≤ k
      · by_cases hub : k - c ≤ dp + dq
        · have hlt : k - c < dp + dq + 1 := by omega
          have h1 : sumRange (dp + dq + 1) (fun u => if u + c = k then coeff (mul p q) u * coeff r c else 0) =
              sumRange (dp + dq + 1) (fun u => if u = k - c then coeff (mul p q) (k - c) * coeff r c else 0) := by
            apply sumRange_congr
            intro u _
            by_cases huc : u + c = k
            · have hueq : u = k - c := by omega
              rw [if_pos huc, if_pos hueq, hueq]
            · have hune : u ≠ k - c := by omega
              rw [if_neg huc, if_neg hune]
          rw [h1, sumRange_single hlt, coeff_mul_rect hp hq (k - c), ← sumRange_mul_right]
          apply sumRange_congr
          intro a _
          rw [← sumRange_mul_right]
          apply sumRange_congr
          intro b _
          by_cases hab : a + b = k - c
          · have habc : a + b + c = k := by omega
            rw [if_pos hab, if_pos habc]
          · have habc : a + b + c ≠ k := by omega
            rw [if_neg hab, if_neg habc, Int.zero_mul]
        · have h0L : sumRange (dp + dq + 1) (fun u => if u + c = k then coeff (mul p q) u * coeff r c else 0) = 0 := by
            rw [sumRange_congr (g := fun _ => 0)]
            · exact sumRange_zero _
            · intro u hu; exact if_neg (by omega : u + c ≠ k)
          have h0R : sumRange (dp + 1) (fun a =>
              sumRange (dq + 1) (fun b => if a + b + c = k then coeff p a * coeff q b * coeff r c else 0)) = 0 := by
            rw [sumRange_congr (g := fun _ => 0)]
            · exact sumRange_zero _
            · intro a ha
              rw [sumRange_congr (g := fun _ => 0)]
              · exact sumRange_zero _
              · intro b hb; exact if_neg (by omega : a + b + c ≠ k)
          rw [h0L, h0R]
      · have h0L : sumRange (dp + dq + 1) (fun u => if u + c = k then coeff (mul p q) u * coeff r c else 0) = 0 := by
          rw [sumRange_congr (g := fun _ => 0)]
          · exact sumRange_zero _
          · intro u _; exact if_neg (by omega : u + c ≠ k)
        have h0R : sumRange (dp + 1) (fun a =>
            sumRange (dq + 1) (fun b => if a + b + c = k then coeff p a * coeff q b * coeff r c else 0)) = 0 := by
          rw [sumRange_congr (g := fun _ => 0)]
          · exact sumRange_zero _
          · intro a _
            rw [sumRange_congr (g := fun _ => 0)]
            · exact sumRange_zero _
            · intro b _; exact if_neg (by omega : a + b + c ≠ k)
        rw [h0L, h0R]
    rw [step1, sumRange_swap (dr + 1) (dp + 1)]
    apply sumRange_congr
    intro a _
    exact sumRange_swap (dr + 1) (dq + 1) _
  rw [hL]
  apply sumRange_congr
  intro a ha
  by_cases hak : a ≤ k
  · by_cases hbc : k - a ≤ dq + dr
    · have hlt : k - a < dq + dr + 1 := by omega
      have h1 : sumRange (dq + dr + 1) (fun v => if a + v = k then coeff p a * coeff (mul q r) v else 0) =
          sumRange (dq + dr + 1) (fun v => if v = k - a then coeff p a * coeff (mul q r) (k - a) else 0) := by
        apply sumRange_congr
        intro v _
        by_cases hav : a + v = k
        · have hveq : v = k - a := by omega
          rw [if_pos hav, if_pos hveq, hveq]
        · have hvne : v ≠ k - a := by omega
          rw [if_neg hav, if_neg hvne]
      rw [h1, sumRange_single hlt, coeff_mul_rect hq hr (k - a), ← sumRange_mul_left]
      apply sumRange_congr
      intro b _
      rw [← sumRange_mul_left]
      apply sumRange_congr
      intro c _
      by_cases hbc' : b + c = k - a
      · have habc : a + b + c = k := by omega
        rw [if_pos habc, if_pos hbc', Int.mul_assoc]
      · have habc : a + b + c ≠ k := by omega
        rw [if_neg habc, if_neg hbc', Int.mul_zero]
    · have h0R : sumRange (dq + dr + 1) (fun v => if a + v = k then coeff p a * coeff (mul q r) v else 0) = 0 := by
        rw [sumRange_congr (g := fun _ => 0)]
        · exact sumRange_zero _
        · intro v hv; exact if_neg (by omega : a + v ≠ k)
      have h0L : sumRange (dq + 1) (fun b =>
          sumRange (dr + 1) (fun c => if a + b + c = k then coeff p a * coeff q b * coeff r c else 0)) = 0 := by
        rw [sumRange_congr (g := fun _ => 0)]
        · exact sumRange_zero _
        · intro b hb
          rw [sumRange_congr (g := fun _ => 0)]
          · exact sumRange_zero _
          · intro c hc; exact if_neg (by omega : a + b + c ≠ k)
      rw [h0L, h0R]
  · have h0R : sumRange (dq + dr + 1) (fun v => if a + v = k then coeff p a * coeff (mul q r) v else 0) = 0 := by
      rw [sumRange_congr (g := fun _ => 0)]
      · exact sumRange_zero _
      · intro v _; exact if_neg (by omega : a + v ≠ k)
    have h0L : sumRange (dq + 1) (fun b =>
        sumRange (dr + 1) (fun c => if a + b + c = k then coeff p a * coeff q b * coeff r c else 0)) = 0 := by
      rw [sumRange_congr (g := fun _ => 0)]
      · exact sumRange_zero _
      · intro b _
        rw [sumRange_congr (g := fun _ => 0)]
        · exact sumRange_zero _
        · intro c _; exact if_neg (by omega : a + b + c ≠ k)
    rw [h0L, h0R]

/-- Product of a list of polynomials mapped by `f`. -/
def polyProd : List α → (α → Poly) → Poly
  | [], _ => one
  | x :: xs, f => mul (f x) (polyProd xs f)

theorem trim_polyProd (xs : List α) (f : α → Poly) :
    trim (polyProd xs f) = polyProd xs f := by
  induction xs with
  | nil => rfl
  | cons _ _ _ => exact trim_mul _ _

theorem polyProd_append (xs ys : List α) (f : α → Poly) :
    polyProd (xs ++ ys) f = mul (polyProd xs f) (polyProd ys f) := by
  induction xs with
  | nil =>
    simp only [List.nil_append, polyProd]
    rw [one_mul_left _ (trim_polyProd ys f)]
  | cons x xs ih =>
    simp only [List.cons_append, polyProd, ih, mul_assoc]

/-- Polynomial evaluation at `x : Int`. -/
def eval : Poly → Int → Int
  | [], _ => 0
  | c :: cs, x => c + x * eval cs x

theorem eval_trim (p : Poly) (x : Int) : eval (trim p) x = eval p x := by
  induction p with
  | nil => rfl
  | cons c cs ih =>
    dsimp only [trim]
    split
    · next h =>
      rcases h with ⟨hcs, hc⟩
      have h0 : eval (trim cs) x = 0 := by rw [hcs]; rfl
      rw [ih] at h0
      simp [eval, hc, h0]
    · simp [eval, ih]

theorem eval_eq_sumRange (p : Poly) (n : Nat) (h : ∀ k, n ≤ k → coeff p k = 0) (x : Int) :
    eval p x = sumRange n (fun k => coeff p k * x ^ k) := by
  induction p generalizing n with
  | nil =>
    simp only [eval]
    symm
    rw [sumRange_congr (g := fun _ => 0)]
    · exact sumRange_zero n
    · intro k _; simp [coeff]
  | cons c cs ih =>
    cases n with
    | zero =>
      have hc0 : c = 0 := h 0 (Nat.le_refl 0)
      have hcs : eval cs x = sumRange 0 (fun k => coeff cs k * x ^ k) :=
        ih 0 (fun k _ => h (k + 1) (Nat.zero_le _))
      simp [eval, hc0, hcs, sumRange]
    | succ n =>
      rw [sumRange_split_first n]
      simp only [coeff, Int.pow_zero, Int.mul_one]
      rw [eval, ih n (fun k hk => h (k + 1) (by omega))]
      have hpow : sumRange n (fun i => coeff cs i * x ^ (i + 1)) =
          x * sumRange n (fun i => coeff cs i * x ^ i) := by
        rw [← sumRange_mul_left]
        apply sumRange_congr
        intro i _
        rw [Int.pow_succ]
        rw [Int.mul_comm x _, Int.mul_assoc]
      rw [hpow]

theorem eval_one_poly (x : Int) : eval one x = 1 := by
  simp [one, eval]

theorem eval_add (p q : Poly) (x : Int) : eval (add p q) x = eval p x + eval q x := by
  let m := max p.length q.length + 1
  rw [eval_eq_sumRange (add p q) m (fun k hk => by
        rw [coeff_add, coeff_eq_zero_of_ge_length p (by omega),
            coeff_eq_zero_of_ge_length q (by omega)]; rfl) x,
      eval_eq_sumRange p m (fun k hk => coeff_eq_zero_of_ge_length p (by omega)) x,
      eval_eq_sumRange q m (fun k hk => coeff_eq_zero_of_ge_length q (by omega)) x,
      ← sumRange_add]
  apply sumRange_congr
  intro k _; rw [coeff_add, Int.add_mul]

theorem eval_sub (p q : Poly) (x : Int) : eval (sub p q) x = eval p x - eval q x := by
  let m := max p.length q.length + 1
  rw [eval_eq_sumRange (sub p q) m (fun k hk => by
        rw [coeff_sub, coeff_eq_zero_of_ge_length p (by omega),
            coeff_eq_zero_of_ge_length q (by omega)]; rfl) x,
      eval_eq_sumRange p m (fun k hk => coeff_eq_zero_of_ge_length p (by omega)) x,
      eval_eq_sumRange q m (fun k hk => coeff_eq_zero_of_ge_length q (by omega)) x]
  have h1 : sumRange m (fun k => coeff (sub p q) k * x ^ k) =
      sumRange m (fun k => coeff p k * x ^ k + -(coeff q k * x ^ k)) := by
    apply sumRange_congr
    intro k _; rw [coeff_sub, Int.sub_mul, Int.sub_eq_add_neg]
  rw [h1, sumRange_add, sumRange_neg, ← Int.sub_eq_add_neg]

theorem eval_mul (p q : Poly) (x : Int) : eval (mul p q) x = eval p x * eval q x := by
  let dp := p.length
  let dq := q.length
  have hp : ∀ i, dp < i → coeff p i = 0 := fun i hi => coeff_eq_zero_of_ge_length p (by omega)
  have hq : ∀ j, dq < j → coeff q j = 0 := fun j hj => coeff_eq_zero_of_ge_length q (by omega)
  have hpq : ∀ k, dp + dq + 1 ≤ k → coeff (mul p q) k = 0 := by
    intro k hk
    rw [coeff_mul_rect hp hq]
    rw [sumRange_congr (g := fun _ => 0)]
    · exact sumRange_zero _
    · intro i hi
      rw [sumRange_congr (g := fun _ => 0)]
      · exact sumRange_zero _
      · intro j hj; exact if_neg (by omega : i + j ≠ k)
  rw [eval_eq_sumRange (mul p q) (dp + dq + 1) hpq x,
      eval_eq_sumRange p (dp + 1) (fun i hi => hp i (by omega)) x,
      eval_eq_sumRange q (dq + 1) (fun j hj => hq j (by omega)) x]
  have step1 : sumRange (dp + dq + 1) (fun k => coeff (mul p q) k * x ^ k) =
      sumRange (dp + 1) (fun i =>
        sumRange (dq + 1) (fun j => (coeff p i * x ^ i) * (coeff q j * x ^ j))) := by
    have hswap : sumRange (dp + dq + 1) (fun k => coeff (mul p q) k * x ^ k) =
        sumRange (dp + dq + 1) (fun k =>
          sumRange (dp + 1) (fun i =>
            sumRange (dq + 1) (fun j =>
              if i + j = k then (coeff p i * coeff q j) * x ^ k else 0))) := by
      apply sumRange_congr
      intro k _
      rw [coeff_mul_rect hp hq k, ← sumRange_mul_right]
      apply sumRange_congr
      intro i _
      rw [← sumRange_mul_right]
      apply sumRange_congr
      intro j _
      split <;> simp
    rw [hswap, sumRange_swap (dp + dq + 1) (dp + 1)]
    apply sumRange_congr
    intro i hi
    rw [sumRange_swap (dp + dq + 1) (dq + 1)]
    apply sumRange_congr
    intro j hj
    have hlt : i + j < dp + dq + 1 := by omega
    have h1 : sumRange (dp + dq + 1) (fun k =>
          if i + j = k then (coeff p i * coeff q j) * x ^ k else 0) =
        sumRange (dp + dq + 1) (fun k =>
          if k = i + j then (coeff p i * coeff q j) * x ^ (i + j) else 0) := by
      apply sumRange_congr
      intro k _
      by_cases hijk : i + j = k
      · rw [if_pos hijk, if_pos hijk.symm, hijk]
      · have hne : k ≠ i + j := fun h => hijk h.symm
        rw [if_neg hijk, if_neg hne]
    rw [h1, sumRange_single hlt, int_pow_add]
    rw [Int.mul_assoc, Int.mul_left_comm (coeff q j) (x ^ i) (x ^ j), ← Int.mul_assoc]
  rw [step1, ← sumRange_mul_right]
  apply sumRange_congr
  intro i _
  rw [← sumRange_mul_left]

theorem eval_polyProd (xs : List α) (f : α → Poly) (x : Int) :
    eval (polyProd xs f) x = (xs.map (fun a => eval (f a) x)).foldr (· * ·) 1 := by
  induction xs with
  | nil => simp [polyProd, eval_one_poly]
  | cons a xs ih => simp [polyProd, eval_mul, ih]

/-- Degree, monicity, coefficient reversal, and palindromic polynomials. -/
def IsMonicOfDeg (p : Poly) (d : Nat) : Prop :=
  trim p = p ∧ coeff p d = 1 ∧ ∀ k, d < k → coeff p k = 0

def IsPalindromicOfDeg (p : Poly) (d : Nat) : Prop :=
  IsMonicOfDeg p d ∧ coeff p 0 = 1 ∧ ∀ k, k ≤ d → coeff p k = coeff p (d - k)

def revPoly (d : Nat) (p : Poly) : Poly :=
  ofFn (d + 1) (fun k => coeff p (d - k))

theorem trim_revPoly (d : Nat) (p : Poly) : trim (revPoly d p) = revPoly d p :=
  trim_ofFn _ _

theorem coeff_revPoly (d : Nat) (p : Poly) (k : Nat) :
    coeff (revPoly d p) k = if k ≤ d then coeff p (d - k) else 0 := by
  rw [revPoly, coeff_ofFn]
  have : (k < d + 1) ↔ (k ≤ d) := by omega
  simp [this]

theorem revPoly_mul {p q : Poly} {dp dq : Nat}
    (hp : ∀ i, dp < i → coeff p i = 0) (hq : ∀ j, dq < j → coeff q j = 0) :
    revPoly (dp + dq) (mul p q) = mul (revPoly dp p) (revPoly dq q) := by
  apply poly_ext (trim_revPoly _ _) (trim_mul _ _)
  intro k
  have hrp : ∀ i, dp < i → coeff (revPoly dp p) i = 0 := by
    intro i hi; rw [coeff_revPoly]; exact if_neg (by omega : ¬(i ≤ dp))
  have hrq : ∀ j, dq < j → coeff (revPoly dq q) j = 0 := by
    intro j hj; rw [coeff_revPoly]; exact if_neg (by omega : ¬(j ≤ dq))
  rw [coeff_revPoly, coeff_mul_rect hrp hrq]
  by_cases hkd : k ≤ dp + dq
  · rw [if_pos hkd, coeff_mul_rect hp hq (dp + dq - k), sumRange_rev dp]
    apply sumRange_congr
    intro i hi
    rw [sumRange_rev dq]
    apply sumRange_congr
    intro j hj
    have hi_le : i ≤ dp := by omega
    have hj_le : j ≤ dq := by omega
    rw [coeff_revPoly dp p i, coeff_revPoly dq q j, if_pos hi_le, if_pos hj_le]
    by_cases hsum : i + j = k
    · have hrev : (dp - i) + (dq - j) = dp + dq - k := by omega
      rw [if_pos hsum, if_pos hrev]
    · have hrev : (dp - i) + (dq - j) ≠ dp + dq - k := by omega
      rw [if_neg hsum, if_neg hrev]
  · rw [if_neg hkd]
    symm
    rw [sumRange_congr (g := fun _ => 0)]
    · exact sumRange_zero _
    · intro i _
      rw [sumRange_congr (g := fun _ => 0)]
      · exact sumRange_zero _
      · intro j _; exact if_neg (by omega : i + j ≠ k)

theorem mul_monicOfDeg {p q : Poly} {dp dq : Nat}
    (hp : IsMonicOfDeg p dp) (hq : IsMonicOfDeg q dq) :
    IsMonicOfDeg (mul p q) (dp + dq) := by
  refine ⟨trim_mul p q, ?_, ?_⟩
  · rw [coeff_mul_rect hp.2.2 hq.2.2 (dp + dq)]
    have hlt1 : dp < dp + 1 := Nat.lt_succ_self dp
    have hlt2 : dq < dq + 1 := Nat.lt_succ_self dq
    have h1 : sumRange (dp + 1) (fun i =>
          sumRange (dq + 1) (fun j => if i + j = dp + dq then coeff p i * coeff q j else 0)) =
        sumRange (dp + 1) (fun i => if i = dp then coeff p dp * coeff q dq else 0) := by
      apply sumRange_congr
      intro i hi
      by_cases hid : i = dp
      · rw [hid, if_pos rfl]
        have h2 : sumRange (dq + 1) (fun j => if dp + j = dp + dq then coeff p dp * coeff q j else 0) =
            sumRange (dq + 1) (fun j => if j = dq then coeff p dp * coeff q dq else 0) := by
          apply sumRange_congr
          intro j _
          by_cases hjd : j = dq
          · rw [hjd, if_pos rfl, if_pos rfl]
          · rw [if_neg (by omega : dp + j ≠ dp + dq), if_neg hjd]
        rw [h2, sumRange_single hlt2]
      · rw [if_neg hid]
        rw [sumRange_congr (g := fun _ => 0)]
        · exact sumRange_zero _
        · intro j hj; exact if_neg (by omega : i + j ≠ dp + dq)
    rw [h1, sumRange_single hlt1, hp.2.1, hq.2.1]
    rfl
  · intro k hk
    rw [coeff_mul_rect hp.2.2 hq.2.2 k]
    rw [sumRange_congr (g := fun _ => 0)]
    · exact sumRange_zero _
    · intro i hi
      rw [sumRange_congr (g := fun _ => 0)]
      · exact sumRange_zero _
      · intro j hj; exact if_neg (by omega : i + j ≠ k)

theorem revPoly_eq_self_of_palindromic {p : Poly} {d : Nat} (hp : IsPalindromicOfDeg p d) :
    revPoly d p = p := by
  apply poly_ext (trim_revPoly d p) hp.1.1
  intro m
  rw [coeff_revPoly]
  by_cases hmd : m ≤ d
  · rw [if_pos hmd, ← hp.2.2 m hmd]
  · rw [if_neg hmd, hp.1.2.2 m (by omega)]

theorem mul_palindromic {p q : Poly} {dp dq : Nat}
    (hp : IsPalindromicOfDeg p dp) (hq : IsPalindromicOfDeg q dq) :
    IsPalindromicOfDeg (mul p q) (dp + dq) := by
  have hm := mul_monicOfDeg hp.1 hq.1
  refine ⟨hm, ?_, ?_⟩
  · rw [coeff_mul, sumRange]
    simp [sumRange, hp.2.1, hq.2.1]
  · intro k hk
    have hrev_pq : revPoly (dp + dq) (mul p q) = mul p q := by
      rw [revPoly_mul hp.1.2.2 hq.1.2.2,
          revPoly_eq_self_of_palindromic hp,
          revPoly_eq_self_of_palindromic hq]
    have hc := coeff_congr hrev_pq k
    rw [coeff_revPoly, if_pos hk] at hc
    exact hc.symm

/-- Highest nonzero index of a nonzero polynomial. -/
theorem exists_top_deg {q : Poly} (hq : trim q = q) (hne : q ≠ zero) :
    ∃ d : Nat, coeff q d ≠ 0 ∧ ∀ k, d < k → coeff q k = 0 := by
  have hnotall : ¬(∀ k, coeff q k = 0) := by
    intro hall
    have : trim q = [] := (trim_eq_nil_iff q).mpr hall
    rw [hq] at this
    exact hne this
  have haux : ∀ m, (∃ k, k < m ∧ coeff q k ≠ 0) →
      ∃ d, d < m ∧ coeff q d ≠ 0 ∧ ∀ k, d < k → k < m → coeff q k = 0 := by
    intro m
    induction m with
    | zero =>
      rintro ⟨k, hk, _⟩; omega
    | succ m ih =>
      rintro ⟨k, hk, hck⟩
      by_cases hcm : coeff q m = 0
      · have hklt : k < m := by
          by_cases hkm : k = m
          · rw [hkm] at hck; exact False.elim (hck hcm)
          · omega
        rcases ih ⟨k, hklt, hck⟩ with ⟨d, hdm, hd0, hdmax⟩
        refine ⟨d, by omega, hd0, ?_⟩
        intro j hdj hjm1
        by_cases hjm : j = m
        · rw [hjm]; exact hcm
        · exact hdmax j hdj (by omega)
      · refine ⟨m, Nat.lt_succ_self m, hcm, ?_⟩
        intro j hmj hjm1; omega
  have hex : ∃ k, k < q.length ∧ coeff q k ≠ 0 := by
    apply Classical.byContradiction
    intro hnone
    apply hnotall
    intro k
    by_cases hkl : k < q.length
    · apply Classical.byContradiction
      intro hck
      exact hnone ⟨k, hkl, hck⟩
    · exact coeff_eq_zero_of_ge_length q (by omega)
  rcases haux q.length hex with ⟨d, _, hd0, hdmax⟩
  refine ⟨d, hd0, ?_⟩
  intro k hdk
  by_cases hkl : k < q.length
  · exact hdmax k hdk hkl
  · exact coeff_eq_zero_of_ge_length q (by omega)

/-- Cancellation of a monic factor in `Z[q]`. -/
theorem mul_eq_zero_of_monic {p q : Poly} {dp : Nat}
    (hp : IsMonicOfDeg p dp) (hq : trim q = q) (hmul : mul p q = zero) : q = zero := by
  by_cases hq0 : q = zero
  · exact hq0
  · exfalso
    rcases exists_top_deg hq hq0 with ⟨dq, hdq0, hdq_top⟩
    have hc : coeff (mul p q) (dp + dq) = 0 := by rw [hmul]; rfl
    rw [coeff_mul_rect hp.2.2 hdq_top (dp + dq)] at hc
    have hlt1 : dp < dp + 1 := Nat.lt_succ_self dp
    have hlt2 : dq < dq + 1 := Nat.lt_succ_self dq
    have h1 : sumRange (dp + 1) (fun i =>
          sumRange (dq + 1) (fun j => if i + j = dp + dq then coeff p i * coeff q j else 0)) =
        sumRange (dp + 1) (fun i => if i = dp then coeff p dp * coeff q dq else 0) := by
      apply sumRange_congr
      intro i hi
      by_cases hid : i = dp
      · rw [hid, if_pos rfl]
        have h2 : sumRange (dq + 1) (fun j => if dp + j = dp + dq then coeff p dp * coeff q j else 0) =
            sumRange (dq + 1) (fun j => if j = dq then coeff p dp * coeff q dq else 0) := by
          apply sumRange_congr
          intro j _
          by_cases hjd : j = dq
          · rw [hjd, if_pos rfl, if_pos rfl]
          · rw [if_neg (by omega : dp + j ≠ dp + dq), if_neg hjd]
        rw [h2, sumRange_single hlt2]
      · rw [if_neg hid]
        rw [sumRange_congr (g := fun _ => 0)]
        · exact sumRange_zero _
        · intro j hj; exact if_neg (by omega : i + j ≠ dp + dq)
    rw [h1, sumRange_single hlt1, hp.2.1, Int.one_mul] at hc
    exact hdq0 hc

theorem mul_monic_cancel_left {p q r : Poly} {dp : Nat}
    (hp : IsMonicOfDeg p dp) (hq : trim q = q) (hr : trim r = r)
    (heq : mul p q = mul p r) : q = r := by
  have hsub : mul p (sub q r) = zero := by
    rw [mul_sub, heq]
    apply poly_ext (trim_sub _ _) trim_zero
    intro k; rw [coeff_sub]; simp [coeff_zero]
  have hqr0 : sub q r = zero := mul_eq_zero_of_monic hp (trim_sub q r) hsub
  apply poly_ext hq hr
  intro k
  have hk : coeff (sub q r) k = 0 := by rw [hqr0]; rfl
  rw [coeff_sub] at hk
  omega

/-- Top-down monic division step from degree `db + steps` down to `db`. -/
def monicDivStep (b : Poly) (db : Nat) : Nat → Poly → Poly × Poly
  | 0, rem => (zero, trim rem)
  | steps + 1, rem =>
    let top := db + steps
    let c := coeff rem top
    let term := shift (constPoly c) steps
    let rem' := sub rem (mul term b)
    let (qRest, rFinal) := monicDivStep b db steps rem'
    (add term qRest, rFinal)

def monicDiv (a b : Poly) (db : Nat) : Poly :=
  (monicDivStep b db (a.length + 1) a).1

def monicRem (a b : Poly) (db : Nat) : Poly :=
  (monicDivStep b db (a.length + 1) a).2

theorem coeff_shift_const (c : Int) (s k : Nat) :
    coeff (shift (constPoly c) s) k = if k = s then c else 0 := by
  rw [coeff_shift]
  by_cases hks : k < s
  · rw [if_pos hks, if_neg (by omega : k ≠ s)]
  · rw [if_neg hks, coeff_const]
    by_cases heq : k = s
    · rw [heq, Nat.sub_self, if_pos rfl, if_pos rfl]
    · rw [if_neg (by omega : k - s ≠ 0), if_neg heq]

theorem coeff_mul_shift_const (c : Int) (s : Nat) (b : Poly) (k : Nat) :
    coeff (mul (shift (constPoly c) s) b) k =
      if s ≤ k then c * coeff b (k - s) else 0 := by
  rw [coeff_mul]
  by_cases hsk : s ≤ k
  · rw [if_pos hsk]
    have hlt : s < k + 1 := by omega
    have h1 : sumRange (k + 1) (fun i => coeff (shift (constPoly c) s) i * coeff b (k - i)) =
        sumRange (k + 1) (fun i => if i = s then c * coeff b (k - s) else 0) := by
      apply sumRange_congr
      intro i _
      rw [coeff_shift_const]
      by_cases his : i = s
      · rw [his, if_pos rfl, if_pos rfl]
      · rw [if_neg his, if_neg his, Int.zero_mul]
    rw [h1, sumRange_single hlt]
  · rw [if_neg hsk]
    rw [sumRange_congr (g := fun _ => 0)]
    · exact sumRange_zero _
    · intro i hi
      rw [coeff_shift_const, if_neg (by omega : i ≠ s), Int.zero_mul]

theorem monicDivStep_spec {b : Poly} {db : Nat} (hb : IsMonicOfDeg b db) :
    ∀ (steps : Nat) (rem : Poly),
      (∀ k, db + steps ≤ k → coeff rem k = 0) →
      let res := monicDivStep b db steps rem
      trim res.1 = res.1 ∧ trim res.2 = res.2 ∧
      trim rem = add (mul res.1 b) res.2 ∧
      (∀ k, db ≤ k → coeff res.2 k = 0) := by
  intro steps
  induction steps with
  | zero =>
    intro rem hrem
    dsimp only [monicDivStep]
    refine ⟨trim_zero, trim_idem rem, ?_, ?_⟩
    · have hz : mul zero b = zero := by rw [mul_comm, mul_zero_right]
      rw [hz, zero_add_left _ (trim_idem rem)]
    · intro k hk
      rw [coeff_trim]
      exact hrem k (by omega)
  | succ steps ih =>
    intro rem hrem
    dsimp only [monicDivStep]
    let top := db + steps
    let c := coeff rem top
    let term := shift (constPoly c) steps
    let rem' := sub rem (mul term b)
    have hrem' : ∀ k, db + steps ≤ k → coeff rem' k = 0 := by
      intro k hk
      dsimp only [rem', term, c, top]
      rw [coeff_sub, coeff_mul_shift_const]
      by_cases htop : k = db + steps
      · rw [htop, if_pos (by omega : steps ≤ db + steps)]
        have hsub : db + steps - steps = db := by omega
        rw [hsub, hb.2.1, Int.mul_one, Int.sub_self]
      · have hgt : db + (steps + 1) ≤ k := by omega
        have hr0 : coeff rem k = 0 := hrem k hgt
        rw [hr0, if_pos (by omega : steps ≤ k), hb.2.2 (k - steps) (by omega), Int.mul_zero, Int.sub_self]
    rcases ih rem' hrem' with ⟨hqT, hrT, heq', hdegR⟩
    refine ⟨trim_add _ _, hrT, ?_, hdegR⟩
    rw [add_mul, add_assoc, ← heq']
    apply poly_ext (trim_idem rem) (trim_add _ _)
    intro k
    dsimp only [rem', term, c, top]
    rw [coeff_trim, coeff_add, coeff_trim, coeff_sub]
    omega

theorem monicDiv_rem_spec (a : Poly) {b : Poly} {db : Nat} (hb : IsMonicOfDeg b db) :
    trim (monicDiv a b db) = monicDiv a b db ∧
    trim (monicRem a b db) = monicRem a b db ∧
    trim a = add (mul (monicDiv a b db) b) (monicRem a b db) ∧
    (∀ k, db ≤ k → coeff (monicRem a b db) k = 0) := by
  have ha : ∀ k, db + (a.length + 1) ≤ k → coeff a k = 0 :=
    fun k hk => coeff_eq_zero_of_ge_length a (by omega)
  exact monicDivStep_spec hb (a.length + 1) a ha

/-- Key integer-cancellation lemma: if `b` is monic and `m * a = p * b` for an integer `m ≠ 0`,
    then `b` divides `a` in `Z[q]`. -/
theorem dvd_of_scale_dvd {a b p : Poly} {db : Nat} {m : Int}
    (ha : trim a = a) (hb : IsMonicOfDeg b db) (hm : m ≠ 0)
    (hscale : scale m a = mul p b) :
    monicRem a b db = zero ∧ a = mul (monicDiv a b db) b := by
  rcases monicDiv_rem_spec a hb with ⟨hqT, hrT, ha_eq, hr_deg⟩
  let q := monicDiv a b db
  let r := monicRem a b db
  have ha_qr : a = add (mul q b) r := by
    rw [← ha]; exact ha_eq
  have h1 : mul p b = add (mul (scale m q) b) (scale m r) := by
    rw [← hscale, scale_mul_left]
    apply poly_ext (trim_scale m a) (trim_add _ _)
    intro k
    rw [coeff_scale, coeff_congr ha_qr k, coeff_add, coeff_add, coeff_scale, coeff_scale, Int.mul_add]
  have hdiff : mul (sub p (scale m q)) b = scale m r := by
    apply poly_ext (trim_mul _ _) (trim_scale _ _)
    intro k
    have hk := coeff_congr h1 k
    rw [coeff_add] at hk
    have hmul_sub : mul (sub p (scale m q)) b = sub (mul p b) (mul (scale m q) b) := by
      rw [mul_comm, mul_sub, mul_comm b p, mul_comm b _]
    rw [hmul_sub, coeff_sub]
    omega
  have hsub0 : sub p (scale m q) = zero := by
    by_cases h0 : sub p (scale m q) = zero
    · exact h0
    · exfalso
      rcases exists_top_deg (trim_sub p (scale m q)) h0 with ⟨du, hdu0, hdu_top⟩
      have hc := coeff_congr hdiff (du + db)
      rw [coeff_scale, hr_deg (du + db) (by omega), Int.mul_zero] at hc
      rw [mul_comm, coeff_mul_rect hb.2.2 hdu_top (du + db)] at hc
      have hlt1 : db < db + 1 := Nat.lt_succ_self db
      have hlt2 : du < du + 1 := Nat.lt_succ_self du
      have hsum : sumRange (db + 1) (fun i =>
            sumRange (du + 1) (fun j => if i + j = du + db then coeff b i * coeff (sub p (scale m q)) j else 0)) =
          sumRange (db + 1) (fun i => if i = db then coeff b db * coeff (sub p (scale m q)) du else 0) := by
        apply sumRange_congr
        intro i hi
        by_cases hid : i = db
        · rw [hid, if_pos rfl]
          have h2 : sumRange (du + 1) (fun j => if db + j = du + db then coeff b db * coeff (sub p (scale m q)) j else 0) =
              sumRange (du + 1) (fun j => if j = du then coeff b db * coeff (sub p (scale m q)) du else 0) := by
            apply sumRange_congr
            intro j _
            by_cases hju : j = du
            · rw [hju, if_pos (by omega : db + du = du + db), if_pos rfl]
            · rw [if_neg (by omega : db + j ≠ du + db), if_neg hju]
          rw [h2, sumRange_single hlt2]
        · rw [if_neg hid]
          rw [sumRange_congr (g := fun _ => 0)]
          · exact sumRange_zero _
          · intro j hj; exact if_neg (by omega : i + j ≠ du + db)
      rw [hsum, sumRange_single hlt1, hb.2.1, Int.one_mul] at hc
      exact hdu0 hc
  have hmr0 : scale m r = zero := by
    rw [← hdiff, hsub0, mul_comm, mul_zero_right]
  have hr0 : r = zero := by
    apply poly_ext hrT trim_zero
    intro k
    have hk : coeff (scale m r) k = 0 := by rw [hmr0]; rfl
    rw [coeff_scale] at hk
    rcases Int.mul_eq_zero.mp hk with hm0 | hrk0
    · exact False.elim (hm hm0)
    · exact hrk0
  refine ⟨hr0, ?_⟩
  change a = mul q b
  rw [ha_qr, hr0, add_zero_right _ (trim_mul _ _)]

/-- If `a * b` is palindromic of degree `da + db` and `a` is palindromic of degree `da`,
    then `b` (monic of degree `db`) is palindromic of degree `db`. -/
theorem palindromic_right_of_mul {a b : Poly} {da db : Nat}
    (ha : IsPalindromicOfDeg a da) (hb : IsMonicOfDeg b db)
    (hab : IsPalindromicOfDeg (mul a b) (da + db)) :
    IsPalindromicOfDeg b db := by
  refine ⟨hb, ?_, ?_⟩
  · have hc0 := hab.2.1
    rw [coeff_mul, sumRange] at hc0
    simp only [sumRange, Nat.sub_zero, Int.zero_add, ha.2.1, Int.one_mul] at hc0
    exact hc0
  · have hrev_a : revPoly da a = a := revPoly_eq_self_of_palindromic ha
    have hrev_ab : revPoly (da + db) (mul a b) = mul a b := revPoly_eq_self_of_palindromic hab
    have hmul_rev : mul a (revPoly db b) = mul a b := by
      have hr := revPoly_mul ha.1.2.2 hb.2.2
      rw [hrev_ab, hrev_a] at hr
      exact hr.symm
    have hrev_b : revPoly db b = b :=
      mul_monic_cancel_left ha.1 (trim_revPoly db b) hb.1 hmul_rev
    intro k hkb
    have hc := coeff_congr hrev_b k
    rw [coeff_revPoly, if_pos hkb] at hc
    exact hc.symm

end Conjecture00000004769
