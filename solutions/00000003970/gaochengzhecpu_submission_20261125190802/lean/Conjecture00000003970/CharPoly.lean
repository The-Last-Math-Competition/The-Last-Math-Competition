/-
  Conjecture 00000003970 — Polynomials over ℤ, Laplace Determinant det(xI - A_G),
  Adjacency Characteristic Polynomial, and Isomorphism Invariance
  Pure Core Lean 4.19.0 (zero external dependencies).
-/

import Conjecture00000003970.Graph

namespace Conjecture00000003970

/-! ### Canonical Univariate Polynomials over `Int` (`Poly := List Int`) -/

/-- Univariate polynomial over `ℤ`, stored in ascending degree `[c₀, c₁, ..., c_d]`
    with trailing zeros stripped by `normPoly`. -/
abbrev Poly := List Int

/-- Strip trailing zero coefficients so every polynomial in `ℤ[x]` has a unique representation. -/
def normPoly : List Int → Poly
  | [] => []
  | c :: cs =>
    match normPoly cs with
    | [] => if c == 0 then [] else [c]
    | cs' => c :: cs'

/-- Coefficient of `x^d` in `p`. -/
def coeff : List Int → Nat → Int
  | [], _ => 0
  | c :: _, 0 => c
  | _ :: cs, d + 1 => coeff cs d

theorem coeff_normPoly (p : List Int) : ∀ d : Nat, coeff (normPoly p) d = coeff p d := by
  induction p with
  | nil => intro _; rfl
  | cons c cs ih =>
    intro d
    unfold normPoly
    cases hcs : normPoly cs with
    | nil =>
      by_cases hc : (c == 0) = true
      · have hc0 : c = 0 := of_decide_eq_true (by simpa using hc)
        simp only [hc, ↓reduceIte]
        cases d with
        | zero => simp [coeff, hc0]
        | succ d' =>
          have := ih d'
          rw [hcs] at this
          simpa [coeff] using this
      · have hcf : (c == 0) = false := Bool.eq_false_iff.mpr hc
        simp only [hcf, Bool.false_eq_true, ↓reduceIte]
        cases d with
        | zero => rfl
        | succ d' =>
          have := ih d'
          rw [hcs] at this
          simpa [coeff] using this
    | cons b bs =>
      cases d with
      | zero => rfl
      | succ d' =>
        have := ih d'
        rw [hcs] at this
        simpa [coeff] using this

theorem normPoly_eq_nil_of_coeff_zero (p : List Int) (h : ∀ d, coeff p d = 0) :
    normPoly p = [] := by
  induction p with
  | nil => rfl
  | cons c cs ih =>
    have hc : c = 0 := h 0
    have hcs : normPoly cs = [] := ih (fun d => h (d + 1))
    simp [normPoly, hcs, hc]

theorem normPoly_eq_of_coeff_eq {p q : List Int} (h : ∀ d, coeff p d = coeff q d) :
    normPoly p = normPoly q := by
  induction p generalizing q with
  | nil =>
    exact (normPoly_eq_nil_of_coeff_zero q (fun d => (h d).symm)).symm
  | cons a as ih =>
    cases q with
    | nil =>
      exact normPoly_eq_nil_of_coeff_zero (a :: as) h
    | cons b bs =>
      have hab : a = b := h 0
      have hasbs : normPoly as = normPoly bs := ih (fun d => h (d + 1))
      simp [normPoly, hab, hasbs]

@[simp] theorem normPoly_idem (p : List Int) : normPoly (normPoly p) = normPoly p :=
  normPoly_eq_of_coeff_eq (coeff_normPoly p)

def rawAdd : List Int → List Int → List Int
  | [], q => q
  | p, [] => p
  | a :: as, b :: bs => (a + b) :: rawAdd as bs

def rawNeg : List Int → List Int
  | [] => []
  | a :: as => (-a) :: rawNeg as

def rawScale (c : Int) : List Int → List Int
  | [] => []
  | a :: as => (c * a) :: rawScale c as

def rawMul : List Int → List Int → List Int
  | [], _ => []
  | a :: as, q => rawAdd (rawScale a q) (0 :: rawMul as q)

def polyZero : Poly := []
def polyConst (c : Int) : Poly := normPoly [c]
def polyX : Poly := [0, 1]
def polyAdd (p q : Poly) : Poly := normPoly (rawAdd p q)
def polyNeg (p : Poly) : Poly := normPoly (rawNeg p)
def polySub (p q : Poly) : Poly := polyAdd p (polyNeg q)
def polyMul (p q : Poly) : Poly := normPoly (rawMul p q)

/-- Evaluate polynomial `p` at an integer `x`. -/
def polyEval : Poly → Int → Int
  | [], _ => 0
  | c :: cs, x => c + x * polyEval cs x

theorem coeff_rawAdd (p q : List Int) (d : Nat) :
    coeff (rawAdd p q) d = coeff p d + coeff q d := by
  induction p generalizing q d with
  | nil => simp [rawAdd, coeff]
  | cons a as ih =>
    cases q with
    | nil => simp [rawAdd, coeff]
    | cons b bs =>
      cases d with
      | zero => simp [rawAdd, coeff]
      | succ d' => simp [rawAdd, coeff, ih]

theorem coeff_rawNeg (p : List Int) (d : Nat) :
    coeff (rawNeg p) d = - coeff p d := by
  induction p generalizing d with
  | nil => simp [rawNeg, coeff]
  | cons a as ih =>
    cases d <;> simp [rawNeg, coeff, ih]

theorem coeff_rawScale (c : Int) (p : List Int) (d : Nat) :
    coeff (rawScale c p) d = c * coeff p d := by
  induction p generalizing d with
  | nil => simp [rawScale, coeff]
  | cons a as ih =>
    cases d <;> simp [rawScale, coeff, ih]

theorem coeff_polyAdd (p q : Poly) (d : Nat) :
    coeff (polyAdd p q) d = coeff p d + coeff q d := by
  rw [polyAdd, coeff_normPoly, coeff_rawAdd]

theorem coeff_polyNeg (p : Poly) (d : Nat) :
    coeff (polyNeg p) d = - coeff p d := by
  rw [polyNeg, coeff_normPoly, coeff_rawNeg]

theorem coeff_rawMul_right_congr (p : List Int) {q₁ q₂ : List Int}
    (hq : ∀ d, coeff q₁ d = coeff q₂ d) :
    ∀ d, coeff (rawMul p q₁) d = coeff (rawMul p q₂) d := by
  induction p with
  | nil => intro _; rfl
  | cons a as ih =>
    intro d
    unfold rawMul
    rw [coeff_rawAdd, coeff_rawAdd, coeff_rawScale, coeff_rawScale, hq d]
    cases d with
    | zero => rfl
    | succ d' =>
      simp only [coeff]
      rw [ih d']

theorem coeff_rawMul_nil_right (p : List Int) (d : Nat) :
    coeff (rawMul p []) d = 0 := by
  induction p generalizing d with
  | nil => rfl
  | cons a as ih =>
    unfold rawMul
    rw [coeff_rawAdd, coeff_rawScale]
    cases d with
    | zero => simp [coeff]
    | succ d' => simp [coeff, ih d']

theorem coeff_rawMul_add_left (p₁ p₂ q : List Int) (d : Nat) :
    coeff (rawMul (rawAdd p₁ p₂) q) d = coeff (rawMul p₁ q) d + coeff (rawMul p₂ q) d := by
  induction p₁ generalizing p₂ d with
  | nil => simp [rawAdd, rawMul, coeff]
  | cons a as ih =>
    cases p₂ with
    | nil => simp [rawAdd, rawMul, coeff]
    | cons b bs =>
      simp only [rawAdd, rawMul, coeff_rawAdd, coeff_rawScale]
      cases d with
      | zero =>
        simp only [coeff, Int.add_mul]
        omega
      | succ d' =>
        simp only [coeff, ih bs d', Int.add_mul]
        omega

theorem coeff_rawMul_add_right (p q₁ q₂ : List Int) (d : Nat) :
    coeff (rawMul p (rawAdd q₁ q₂)) d = coeff (rawMul p q₁) d + coeff (rawMul p q₂) d := by
  induction p generalizing d with
  | nil => simp [rawMul, coeff]
  | cons a as ih =>
    simp only [rawMul, coeff_rawAdd, coeff_rawScale]
    cases d with
    | zero =>
      simp only [coeff, coeff_rawAdd, Int.mul_add]
      omega
    | succ d' =>
      simp only [coeff, coeff_rawAdd, ih d', Int.mul_add]
      omega

theorem coeff_rawMul_scale_left (c : Int) (p q : List Int) (d : Nat) :
    coeff (rawMul (rawScale c p) q) d = c * coeff (rawMul p q) d := by
  induction p generalizing d with
  | nil => simp [rawScale, rawMul, coeff]
  | cons a as ih =>
    simp only [rawScale, rawMul, coeff_rawAdd, coeff_rawScale]
    cases d with
    | zero =>
      simp [coeff, Int.mul_assoc]
    | succ d' =>
      simp [coeff, ih d', Int.mul_add, Int.mul_assoc]

theorem coeff_rawMul_shift_right (p q : List Int) (d : Nat) :
    coeff (rawMul p (0 :: q)) d = coeff (0 :: rawMul p q) d := by
  induction p generalizing d with
  | nil => cases d <;> rfl
  | cons a as ih =>
    simp only [rawMul, coeff_rawAdd, coeff_rawScale]
    cases d with
    | zero => simp [coeff]
    | succ d' =>
      cases d' with
      | zero =>
        simp [coeff, ih 0, coeff_rawAdd, coeff_rawScale]
      | succ d'' =>
        simp [coeff, ih (d'' + 1), coeff_rawAdd, coeff_rawScale]

theorem coeff_rawMul_singleton_right (q : List Int) (a : Int) (d : Nat) :
    coeff (rawScale a q) d = coeff (rawMul q [a]) d := by
  induction q generalizing d with
  | nil => simp [rawScale, rawMul, coeff]
  | cons b bs ihq =>
    simp only [rawScale, rawMul, coeff_rawAdd, coeff_rawScale]
    cases d with
    | zero => simp [coeff, Int.mul_comm]
    | succ d' =>
      have := ihq d'
      simp only [coeff]
      rw [← this]
      simp [coeff]

theorem coeff_rawMul_comm (p q : List Int) :
    ∀ d, coeff (rawMul p q) d = coeff (rawMul q p) d := by
  induction p with
  | nil =>
    intro d
    rw [coeff_rawMul_nil_right]
    rfl
  | cons a as ih =>
    intro d
    have hdecomp : ∀ r, coeff (rawAdd [a] (0 :: as)) r = coeff (a :: as) r := by
      intro r; cases r <;> simp [rawAdd, coeff]
    have hrhs := coeff_rawMul_right_congr q hdecomp d
    rw [← hrhs, coeff_rawMul_add_right, coeff_rawMul_shift_right]
    conv => lhs; unfold rawMul
    rw [coeff_rawAdd, coeff_rawMul_singleton_right]
    cases d with
    | zero => simp [coeff]
    | succ d' =>
      simp only [coeff]
      rw [ih d']

theorem coeff_rawMul_left_congr {p₁ p₂ : List Int} (q : List Int)
    (hp : ∀ d, coeff p₁ d = coeff p₂ d) (d : Nat) :
    coeff (rawMul p₁ q) d = coeff (rawMul p₂ q) d := by
  rw [coeff_rawMul_comm p₁ q d, coeff_rawMul_comm p₂ q d]
  exact coeff_rawMul_right_congr q hp d

theorem coeff_rawMul_assoc (p q r : List Int) :
    ∀ d, coeff (rawMul (rawMul p q) r) d = coeff (rawMul p (rawMul q r)) d := by
  induction p with
  | nil => intro _; rfl
  | cons a as ih =>
    intro d
    simp only [rawMul]
    rw [coeff_rawMul_add_left, coeff_rawMul_scale_left]
    rw [coeff_rawAdd, coeff_rawScale]
    have hshift : coeff (rawMul (0 :: rawMul as q) r) d = coeff (0 :: rawMul (rawMul as q) r) d := by
      simp [rawMul, coeff_rawAdd, coeff_rawScale]
    rw [hshift]
    cases d with
    | zero => simp [coeff]
    | succ d' =>
      simp only [coeff]
      rw [ih d']

/-! #### Algebraic Ring Laws on Canonical `Poly` -/

theorem polyAdd_comm (p q : Poly) : polyAdd p q = polyAdd q p := by
  unfold polyAdd
  exact normPoly_eq_of_coeff_eq fun d => by
    rw [coeff_rawAdd, coeff_rawAdd]; omega

theorem polyAdd_assoc (p q r : Poly) :
    polyAdd (polyAdd p q) r = polyAdd p (polyAdd q r) := by
  unfold polyAdd
  exact normPoly_eq_of_coeff_eq fun d => by
    rw [coeff_rawAdd, coeff_normPoly, coeff_rawAdd,
        coeff_rawAdd, coeff_normPoly, coeff_rawAdd]
    omega

@[simp] theorem polyAdd_zero (p : Poly) : polyAdd p polyZero = normPoly p := by
  unfold polyAdd polyZero
  exact normPoly_eq_of_coeff_eq fun d => by simp [coeff_rawAdd, coeff]

@[simp] theorem zero_polyAdd (p : Poly) : polyAdd polyZero p = normPoly p := by
  rw [polyAdd_comm, polyAdd_zero]

theorem polyNeg_add (p q : Poly) :
    polyNeg (polyAdd p q) = polyAdd (polyNeg p) (polyNeg q) := by
  unfold polyNeg polyAdd
  exact normPoly_eq_of_coeff_eq fun d => by
    rw [coeff_rawNeg, coeff_normPoly, coeff_rawAdd,
        coeff_rawAdd, coeff_normPoly, coeff_rawNeg, coeff_normPoly, coeff_rawNeg]
    omega

theorem polyNeg_neg (p : Poly) : polyNeg (polyNeg p) = normPoly p := by
  unfold polyNeg
  exact normPoly_eq_of_coeff_eq fun d => by
    rw [coeff_rawNeg, coeff_normPoly, coeff_rawNeg]
    omega

@[simp] theorem polyNeg_zero : polyNeg polyZero = polyZero := rfl

theorem polyMul_comm (p q : Poly) : polyMul p q = polyMul q p := by
  unfold polyMul
  exact normPoly_eq_of_coeff_eq (coeff_rawMul_comm p q)

theorem polyMul_assoc (p q r : Poly) :
    polyMul (polyMul p q) r = polyMul p (polyMul q r) := by
  unfold polyMul
  exact normPoly_eq_of_coeff_eq fun d => by
    rw [coeff_rawMul_left_congr r (coeff_normPoly (rawMul p q)) d,
        coeff_rawMul_right_congr p (coeff_normPoly (rawMul q r)) d,
        coeff_rawMul_assoc]

@[simp] theorem polyMul_zero (p : Poly) : polyMul p polyZero = polyZero := by
  unfold polyMul polyZero
  exact normPoly_eq_nil_of_coeff_zero (rawMul p []) (coeff_rawMul_nil_right p)

@[simp] theorem zero_polyMul (p : Poly) : polyMul polyZero p = polyZero := rfl

theorem polyMul_neg_right (p q : Poly) :
    polyMul p (polyNeg q) = polyNeg (polyMul p q) := by
  unfold polyMul polyNeg
  exact normPoly_eq_of_coeff_eq fun d => by
    rw [coeff_rawMul_right_congr p (coeff_normPoly (rawNeg q)) d,
        coeff_rawNeg, coeff_normPoly]
    have hscale : ∀ k, coeff (rawNeg q) k = coeff (rawScale (-1) q) k := by
      intro k; rw [coeff_rawNeg, coeff_rawScale]; omega
    rw [coeff_rawMul_right_congr p hscale d, coeff_rawMul_comm,
        coeff_rawMul_scale_left, coeff_rawMul_comm]
    omega

theorem polyMul_neg_left (p q : Poly) :
    polyMul (polyNeg p) q = polyNeg (polyMul p q) := by
  rw [polyMul_comm, polyMul_neg_right, polyMul_comm]

theorem polyMul_const_one_left (p : Poly) :
    polyMul (polyConst 1) p = normPoly p := by
  unfold polyMul polyConst
  exact normPoly_eq_of_coeff_eq fun d => by
    have hc : ∀ k, coeff (normPoly [1]) k = coeff [1] k := coeff_normPoly [1]
    rw [coeff_rawMul_left_congr p hc d]
    simp only [rawMul, coeff_rawAdd, coeff_rawScale]
    cases d <;> simp [coeff]

theorem polyMul_const_neg_one_left (p : Poly) :
    polyMul (polyConst (-1)) p = polyNeg p := by
  unfold polyMul polyConst polyNeg
  exact normPoly_eq_of_coeff_eq fun d => by
    have hc : ∀ k, coeff (normPoly [-1]) k = coeff [-1] k := coeff_normPoly [-1]
    rw [coeff_rawMul_left_congr p hc d, coeff_rawNeg]
    simp only [rawMul, coeff_rawAdd, coeff_rawScale]
    cases d <;> simp [coeff]

/-! ### Laplace Determinant `detPoly` over `Poly` & Characteristic Polynomial -/

/-- Sum of a list of normalized polynomials (always normalized). -/
def polySum : List Poly → Poly
  | [] => polyZero
  | p :: ps => polyAdd p (polySum ps)

theorem normPoly_polySum (ps : List Poly) : normPoly (polySum ps) = polySum ps := by
  cases ps with
  | nil => rfl
  | cons p ps => simp [polySum, polyAdd]

theorem polyNeg_polySum (ps : List Poly) :
    polyNeg (polySum ps) = polySum (ps.map polyNeg) := by
  induction ps with
  | nil => rfl
  | cons p ps ih =>
    simp only [polySum, List.map, polyNeg_add, ih]

theorem polySum_append (xs ys : List Poly) :
    polySum (xs ++ ys) = polyAdd (polySum xs) (polySum ys) := by
  induction xs with
  | nil =>
    simp [polySum, normPoly_polySum]
  | cons x xs ih =>
    simp only [List.cons_append, polySum, ih, polyAdd_assoc]

theorem polySum_congr {α : Type u} {L : List α} {f g : α → Poly}
    (h : ∀ x ∈ L, f x = g x) :
    polySum (L.map f) = polySum (L.map g) := by
  induction L with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.map, polySum]
    rw [h x (List.mem_cons_self ..), ih (fun y hy => h y (List.mem_cons_of_mem _ hy))]

theorem normPoly_polyMul (p q : Poly) : normPoly (polyMul p q) = polyMul p q := by
  simp [polyMul]

theorem normPoly_polyNeg (p : Poly) : normPoly (polyNeg p) = polyNeg p := by
  simp [polyNeg]

theorem mem_of_mem_removeOne {α : Type u} [DecidableEq α] {a b : α} {L : List α}
    (h : b ∈ removeOne a L) : b ∈ L := by
  induction L with
  | nil => cases h
  | cons x xs ih =>
    unfold removeOne at h
    by_cases hxa : x = a
    · simp only [hxa, ↓reduceIte] at h
      exact List.mem_cons_of_mem _ h
    · simp only [hxa, ↓reduceIte] at h
      rcases List.mem_cons.mp h with rfl | hxs
      · exact List.mem_cons_self ..
      · exact List.mem_cons_of_mem _ (ih hxs)

theorem nodup_removeOne {α : Type u} [DecidableEq α] (a : α) {L : List α}
    (hL : Nodup L) : Nodup (removeOne a L) := by
  induction hL with
  | nil => exact .nil
  | @cons z zs hz hzs ih =>
    unfold removeOne
    by_cases hza : z = a
    · simp only [hza, ↓reduceIte]
      exact hzs
    · simp only [hza, ↓reduceIte]
      refine .cons ?_ ih
      intro hmem
      exact hz (mem_of_mem_removeOne hmem)

theorem not_mem_removeOne_self {α : Type u} [DecidableEq α] {a : α} {L : List α}
    (hL : Nodup L) : a ∉ removeOne a L := by
  induction hL with
  | nil => intro h; cases h
  | @cons z zs hz _ ih =>
    unfold removeOne
    by_cases hza : z = a
    · subst hza
      simp only [↓reduceIte]
      exact hz
    · simp only [hza, ↓reduceIte]
      intro hmem
      rcases List.mem_cons.mp hmem with rfl | hrest
      · exact hza rfl
      · exact ih hrest

theorem polySum_removeOne {α : Type u} [DecidableEq α] {a : α} {L : List α}
    (ha : a ∈ L) (f : α → Poly) (hf : ∀ x ∈ L, normPoly (f x) = f x) :
    polySum (L.map f) = polyAdd (f a) (polySum ((removeOne a L).map f)) := by
  induction L with
  | nil => cases ha
  | cons x xs ih =>
    unfold removeOne
    by_cases hxa : x = a
    · subst hxa
      simp [polySum]
    · simp only [hxa, ↓reduceIte, List.map, polySum]
      rcases List.mem_cons.mp ha with rfl | hxs
      · exact False.elim (hxa rfl)
      · rw [ih hxs (fun y hy => hf y (List.mem_cons_of_mem _ hy))]
        rw [← polyAdd_assoc, polyAdd_comm (f x) (f a), polyAdd_assoc]

/-- Reindexing invariance of `polySum` along a bijection between duplicate-free lists. -/
theorem polySum_bij {α : Type u} {β : Type v} [DecidableEq α] [DecidableEq β]
    {L₁ : List α} {L₂ : List β} (hnd₁ : Nodup L₁) (hnd₂ : Nodup L₂)
    (π : α → β) (π_inv : β → α)
    (h1 : ∀ x ∈ L₁, π x ∈ L₂ ∧ π_inv (π x) = x)
    (h2 : ∀ y ∈ L₂, π_inv y ∈ L₁ ∧ π (π_inv y) = y)
    (f : α → Poly) (g : β → Poly)
    (hfg : ∀ x ∈ L₁, f x = g (π x))
    (hg_norm : ∀ y ∈ L₂, normPoly (g y) = g y) :
    polySum (L₁.map f) = polySum (L₂.map g) := by
  induction hnd₁ generalizing L₂ with
  | nil =>
    cases L₂ with
    | nil => rfl
    | cons y _ =>
      cases (h2 y (List.mem_cons_self ..)).1
  | @cons x xs hx _ ih =>
    have hπx : π x ∈ L₂ := (h1 x (List.mem_cons_self ..)).1
    rw [polySum_removeOne hπx g hg_norm]
    simp only [List.map, polySum]
    rw [hfg x (List.mem_cons_self ..)]
    congr 1
    refine ih (nodup_removeOne (π x) hnd₂) ?_ ?_
      (fun a ha => hfg a (List.mem_cons_of_mem _ ha))
      (fun b hb => hg_norm b (mem_of_mem_removeOne hb))
    · intro a ha
      have ha1 := h1 a (List.mem_cons_of_mem _ ha)
      refine ⟨mem_removeOne_of_ne ?_ ha1.1, ha1.2⟩
      intro heq
      have hax : a = x := by
        rw [← ha1.2, heq, (h1 x (List.mem_cons_self ..)).2]
      exact hx (hax ▸ ha)
    · intro b hb
      have hb2 := h2 b (mem_of_mem_removeOne hb)
      rcases List.mem_cons.mp hb2.1 with heq | hxs
      · have hb_eq : b = π x := by rw [← hb2.2, heq]
        exact False.elim (not_mem_removeOne_self hnd₂ (hb_eq ▸ hb))
      · exact ⟨hxs, hb2.2⟩

/-- Order-preserving injection skipping index `k : Fin (n + 1)`. -/
def deleteIdx {n : Nat} (k : Fin (n + 1)) (i : Fin n) : Fin (n + 1) :=
  if i.val < k.val then ⟨i.val, by omega⟩ else ⟨i.val + 1, by omega⟩

/-- `(n × n)` minor obtained by deleting row `r` and column `c`. -/
def submatrix {n : Nat} (r c : Fin (n + 1))
    (M : Fin (n + 1) → Fin (n + 1) → Poly) : Fin n → Fin n → Poly :=
  fun i j => M (deleteIdx r i) (deleteIdx c j)

/-- Alternating sign `(-1)^j` as a constant polynomial. -/
def signPoly (j : Nat) : Poly :=
  if j % 2 == 0 then polyConst 1 else polyConst (-1)

/-- Textbook Laplace determinant over `ℤ[x]` along the first row. -/
def detPoly : {n : Nat} → (Fin n → Fin n → Poly) → Poly
  | 0, _ => polyConst 1
  | n + 1, M =>
    polySum ((allFin (n + 1)).map (fun j =>
      polyMul (polyMul (signPoly j.val) (M 0 j)) (detPoly (submatrix 0 j M))))

/-- Fast zero-skipping Laplace determinant (mathematically identical to `detPoly`). -/
def fastDetPoly : {n : Nat} → (Fin n → Fin n → Poly) → Poly
  | 0, _ => polyConst 1
  | n + 1, M =>
    polySum ((allFin (n + 1)).map (fun j =>
      if M 0 j == polyZero then polyZero
      else polyMul (polyMul (signPoly j.val) (M 0 j)) (fastDetPoly (submatrix 0 j M))))

theorem detPoly_eq_fastDetPoly :
    ∀ {n : Nat} (M : Fin n → Fin n → Poly), detPoly M = fastDetPoly M
  | 0, _ => rfl
  | n + 1, M => by
    unfold detPoly fastDetPoly
    refine polySum_congr ?_
    intro j _
    by_cases hz : (M 0 j == polyZero) = true
    · have hz' : M 0 j = polyZero := of_decide_eq_true (by simpa using hz)
      simp [hz, hz']
    · have hzf : (M 0 j == polyZero) = false := Bool.eq_false_iff.mpr hz
      simp [hzf, detPoly_eq_fastDetPoly (submatrix 0 j M)]

/-- Characteristic matrix `xI - A_G` of a simple graph `G : SimpleGraphN n`. -/
def charMatrix {n : Nat} (G : SimpleGraphN n) (i j : Fin n) : Poly :=
  if i = j then polyX
  else if G.adj i j then polyConst (-1)
  else polyZero

/-- Exact characteristic polynomial `χ_G(x) = det(xI - A_G) ∈ ℤ[x]`. -/
def charPoly {n : Nat} (G : SimpleGraphN n) : Poly :=
  detPoly (charMatrix G)

/-- Fast evaluator for `charPoly G`, proved equal to `charPoly G` via `detPoly_eq_fastDetPoly`. -/
def fastCharPoly {n : Nat} (G : SimpleGraphN n) : Poly :=
  fastDetPoly (charMatrix G)

theorem charPoly_eq_fastCharPoly {n : Nat} (G : SimpleGraphN n) :
    charPoly G = fastCharPoly G :=
  detPoly_eq_fastDetPoly (charMatrix G)

/-- Two graphs on `n` vertices have the same adjacency spectrum iff their characteristic
    polynomials `det(xI - A_G)` coincide. -/
def SameAdjacencySpectrum {n : Nat} (G₁ G₂ : SimpleGraphN n) : Prop :=
  charPoly G₁ = charPoly G₂

/-! ### Graph Isomorphism Invariance of `charPoly` (`G₁ ≅ G₂ → charPoly G₁ = charPoly G₂`) -/

/-- Adjacent transposition swapping `k` and `k + 1` in `Fin (m + 1)`. -/
def swapAdj {m : Nat} (k : Fin m) (x : Fin (m + 1)) : Fin (m + 1) :=
  if x.val = k.val then ⟨k.val + 1, by omega⟩
  else if x.val = k.val + 1 then ⟨k.val, by omega⟩
  else x

theorem swapAdj_val {m : Nat} (k : Fin m) (x : Fin (m + 1)) :
    (swapAdj k x).val =
      if x.val = k.val then k.val + 1
      else if x.val = k.val + 1 then k.val
      else x.val := by
  unfold swapAdj
  by_cases h1 : x.val = k.val
  · simp [h1]
  · by_cases h2 : x.val = k.val + 1 <;> simp [h1, h2]

theorem deleteIdx_val {n : Nat} (k : Fin (n + 1)) (i : Fin n) :
    (deleteIdx k i).val = if i.val < k.val then i.val else i.val + 1 := by
  unfold deleteIdx
  by_cases h : i.val < k.val <;> simp [h]

theorem swapAdj_invol {m : Nat} (k : Fin m) (x : Fin (m + 1)) :
    swapAdj k (swapAdj k x) = x := by
  apply Fin.ext
  rw [swapAdj_val, swapAdj_val]
  by_cases h1 : x.val = k.val
  · simp [h1]
  · by_cases h2 : x.val = k.val + 1 <;> simp [h1, h2]

theorem signPoly_succ (j : Nat) : signPoly (j + 1) = polyNeg (signPoly j) := by
  unfold signPoly
  by_cases hj : (j % 2 == 0) = true
  · have hj0 : j % 2 = 0 := of_decide_eq_true (by simpa using hj)
    have hj1 : ((j + 1) % 2 == 0) = false := by
      apply Bool.eq_false_iff.mpr
      intro h; have := of_decide_eq_true (by simpa using h); omega
    simp only [hj, hj1, Bool.false_eq_true, ↓reduceIte]
    decide
  · have hjf : (j % 2 == 0) = false := Bool.eq_false_iff.mpr hj
    have hj0 : j % 2 ≠ 0 := fun h => hj (by simpa using decide_eq_true h)
    have hj1 : ((j + 1) % 2 == 0) = true := by
      have : (j + 1) % 2 = 0 := by omega
      simpa using decide_eq_true this
    simp only [hjf, hj1, Bool.false_eq_true, ↓reduceIte]
    decide

theorem signPoly_mul_neg_eq (a b a' b' : Nat)
    (hodd : (a' + b') % 2 ≠ (a + b) % 2) (p : Poly) :
    polyMul (polyMul (signPoly a') (signPoly b')) p =
    polyNeg (polyMul (polyMul (signPoly a) (signPoly b)) p) := by
  have hpar : ∀ x y : Nat,
      polyMul (signPoly x) (signPoly y) =
      (if (x + y) % 2 == 0 then polyConst 1 else polyConst (-1)) := by
    intro x y
    unfold signPoly
    by_cases hx : (x % 2 == 0) = true <;> by_cases hy : (y % 2 == 0) = true
    · have hx' : x % 2 = 0 := of_decide_eq_true (by simpa using hx)
      have hy' : y % 2 = 0 := of_decide_eq_true (by simpa using hy)
      have hxy : ((x + y) % 2 == 0) = true := by
        have : (x + y) % 2 = 0 := by omega
        simpa using decide_eq_true this
      simp only [hx, hy, hxy, ↓reduceIte]; decide
    · have hyf : (y % 2 == 0) = false := Bool.eq_false_iff.mpr hy
      have hx' : x % 2 = 0 := of_decide_eq_true (by simpa using hx)
      have hy' : y % 2 ≠ 0 := fun h => hy (by simpa using decide_eq_true h)
      have hxy : ((x + y) % 2 == 0) = false := by
        apply Bool.eq_false_iff.mpr; intro h
        have := of_decide_eq_true (by simpa using h); omega
      simp only [hx, hyf, hxy, Bool.false_eq_true, ↓reduceIte]; decide
    · have hxf : (x % 2 == 0) = false := Bool.eq_false_iff.mpr hx
      have hx' : x % 2 ≠ 0 := fun h => hx (by simpa using decide_eq_true h)
      have hy' : y % 2 = 0 := of_decide_eq_true (by simpa using hy)
      have hxy : ((x + y) % 2 == 0) = false := by
        apply Bool.eq_false_iff.mpr; intro h
        have := of_decide_eq_true (by simpa using h); omega
      simp only [hxf, hy, hxy, Bool.false_eq_true, ↓reduceIte]; decide
    · have hxf : (x % 2 == 0) = false := Bool.eq_false_iff.mpr hx
      have hyf : (y % 2 == 0) = false := Bool.eq_false_iff.mpr hy
      have hx' : x % 2 ≠ 0 := fun h => hx (by simpa using decide_eq_true h)
      have hy' : y % 2 ≠ 0 := fun h => hy (by simpa using decide_eq_true h)
      have hxy : ((x + y) % 2 == 0) = true := by
        have : (x + y) % 2 = 0 := by omega
        simpa using decide_eq_true this
      simp only [hxf, hyf, hxy, Bool.false_eq_true, ↓reduceIte]; decide
  rw [hpar a' b', hpar a b]
  by_cases hab : ((a + b) % 2 == 0) = true
  · have hab0 : (a + b) % 2 = 0 := of_decide_eq_true (by simpa using hab)
    have hab' : ((a' + b') % 2 == 0) = false := by
      apply Bool.eq_false_iff.mpr; intro h
      have := of_decide_eq_true (by simpa using h); omega
    simp only [hab, hab', Bool.false_eq_true, ↓reduceIte,
      polyMul_const_neg_one_left, polyMul_const_one_left]
    unfold polyNeg
    exact normPoly_eq_of_coeff_eq fun d => by
      rw [coeff_rawNeg, coeff_rawNeg, coeff_normPoly]
  · have habf : ((a + b) % 2 == 0) = false := Bool.eq_false_iff.mpr hab
    have hab0 : (a + b) % 2 ≠ 0 := fun h => hab (by simpa using decide_eq_true h)
    have hab' : ((a' + b') % 2 == 0) = true := by
      have : (a' + b') % 2 = 0 := by omega
      simpa using decide_eq_true this
    simp only [habf, hab', Bool.false_eq_true, ↓reduceIte,
      polyMul_const_neg_one_left, polyMul_const_one_left, polyNeg_neg]

theorem normPoly_detPoly : ∀ {n : Nat} (M : Fin n → Fin n → Poly),
    normPoly (detPoly M) = detPoly M
  | 0, _ => rfl
  | _ + 1, _ => normPoly_polySum _

/-- Swapping two adjacent columns `k` and `k + 1` negates `detPoly`. -/
theorem detPoly_colSwapAdj :
    ∀ {n : Nat} (k : Fin n) (M : Fin (n + 1) → Fin (n + 1) → Poly),
      detPoly (fun i j => M i (swapAdj k j)) = polyNeg (detPoly M)
  | 0, k, _ => k.elim0
  | m + 1, k, M => by
    unfold detPoly
    rw [polyNeg_polySum, List.map_map]
    refine polySum_bij (nodup_allFin (m + 2)) (nodup_allFin (m + 2))
      (swapAdj k) (swapAdj k)
      (fun x _ => ⟨mem_allFin _, swapAdj_invol k x⟩)
      (fun y _ => ⟨mem_allFin _, swapAdj_invol k y⟩)
      _ _ ?_ (fun y _ => normPoly_polyNeg _)
    intro j _
    have hjl := j.isLt
    have hkl := k.isLt
    dsimp only [Function.comp]
    by_cases hjk : j.val = k.val
    · have hswapj : swapAdj k j = ⟨k.val + 1, by omega⟩ := by
        apply Fin.ext; rw [swapAdj_val]; simp [hjk]
      have hmin : submatrix 0 j (fun r c => M r (swapAdj k c)) =
          submatrix 0 ⟨k.val + 1, by omega⟩ M := by
        funext r c
        unfold submatrix
        dsimp only
        congr 1
        apply Fin.ext
        rw [swapAdj_val, deleteIdx_val, deleteIdx_val]
        change (if (if c.val < j.val then c.val else c.val + 1) = k.val then k.val + 1
          else if (if c.val < j.val then c.val else c.val + 1) = k.val + 1 then k.val
          else if c.val < j.val then c.val else c.val + 1) =
          (if c.val < k.val + 1 then c.val else c.val + 1)
        by_cases h1 : c.val < j.val <;> by_cases h2 : c.val < k.val + 1 <;> simp only [h1, h2, ↓reduceIte]
        all_goals (try split) <;> (try split) <;> omega
      have hsign : signPoly (k.val + 1) = polyNeg (signPoly j.val) := by
        rw [hjk, signPoly_succ]
      rw [hswapj, hmin]
      change polyMul (polyMul (signPoly j.val) (M 0 ⟨k.val + 1, _⟩))
          (detPoly (submatrix 0 ⟨k.val + 1, _⟩ M)) =
        polyNeg (polyMul (polyMul (signPoly (k.val + 1)) (M 0 ⟨k.val + 1, _⟩))
          (detPoly (submatrix 0 ⟨k.val + 1, _⟩ M)))
      rw [hsign, polyMul_neg_left, polyMul_neg_left, polyNeg_neg, normPoly_polyMul]
    · by_cases hjk1 : j.val = k.val + 1
      · have hswapj : swapAdj k j = ⟨k.val, by omega⟩ := by
          apply Fin.ext; rw [swapAdj_val]; simp [hjk, hjk1]
        have hmin : submatrix 0 j (fun r c => M r (swapAdj k c)) =
            submatrix 0 ⟨k.val, by omega⟩ M := by
          funext r c
          unfold submatrix
          dsimp only
          congr 1
          apply Fin.ext
          rw [swapAdj_val, deleteIdx_val, deleteIdx_val]
          change (if (if c.val < j.val then c.val else c.val + 1) = k.val then k.val + 1
            else if (if c.val < j.val then c.val else c.val + 1) = k.val + 1 then k.val
            else if c.val < j.val then c.val else c.val + 1) =
            (if c.val < k.val then c.val else c.val + 1)
          by_cases h1 : c.val < j.val <;> by_cases h2 : c.val < k.val <;> simp only [h1, h2, ↓reduceIte]
          all_goals (try split) <;> (try split) <;> omega
        have hsign : signPoly j.val = polyNeg (signPoly k.val) := by
          rw [hjk1, signPoly_succ]
        rw [hswapj, hmin]
        change polyMul (polyMul (signPoly j.val) (M 0 ⟨k.val, _⟩))
            (detPoly (submatrix 0 ⟨k.val, _⟩ M)) =
          polyNeg (polyMul (polyMul (signPoly k.val) (M 0 ⟨k.val, _⟩))
            (detPoly (submatrix 0 ⟨k.val, _⟩ M)))
        rw [hsign, polyMul_neg_left, polyMul_neg_left]
      · have hswapj : swapAdj k j = j := by
          apply Fin.ext; rw [swapAdj_val]; simp [hjk, hjk1]
        let k' : Fin m :=
          if hlt : j.val < k.val then ⟨k.val - 1, by omega⟩ else ⟨k.val, by omega⟩
        have hk'_val : k'.val = if j.val < k.val then k.val - 1 else k.val := by
          unfold k'; split <;> rfl
        have hmin : submatrix 0 j (fun r c => M r (swapAdj k c)) =
            (fun r c => submatrix 0 j M r (swapAdj k' c)) := by
          funext r c
          unfold submatrix
          dsimp only
          congr 1
          apply Fin.ext
          rw [swapAdj_val, deleteIdx_val, deleteIdx_val, swapAdj_val, hk'_val]
          have hcl := c.isLt
          by_cases hlt : j.val < k.val <;> by_cases hc : c.val < j.val <;> simp only [hlt, hc, ↓reduceIte]
          all_goals
            (try split) <;> (try split) <;> (try split) <;> (try split) <;> (try split) <;> omega
        rw [hmin, hswapj, detPoly_colSwapAdj k' (submatrix 0 j M), polyMul_neg_right]

/-- Partner involution on `Fin (m + 2) × Fin (m + 1)` swapping the two deleted column indices. -/
def row01Partner {m : Nat} (p : Fin (m + 2) × Fin (m + 1)) : Fin (m + 2) × Fin (m + 1) :=
  (deleteIdx p.1 p.2,
   if h : p.2.val < p.1.val then ⟨p.1.val - 1, by have := p.1.isLt; omega⟩
   else ⟨p.1.val, by have := p.1.isLt; have := p.2.isLt; omega⟩)

theorem row01Partner_snd_val {m : Nat} (p : Fin (m + 2) × Fin (m + 1)) :
    (row01Partner p).2.val = if p.2.val < p.1.val then p.1.val - 1 else p.1.val := by
  unfold row01Partner
  split <;> rfl

theorem row01Partner_invol {m : Nat} (p : Fin (m + 2) × Fin (m + 1)) :
    row01Partner (row01Partner p) = p := by
  rcases p with ⟨j₀, j₁⟩
  have hj₀ := j₀.isLt
  have hj₁ := j₁.isLt
  ext
  · show (deleteIdx (row01Partner (j₀, j₁)).1 (row01Partner (j₀, j₁)).2).val = j₀.val
    rw [deleteIdx_val, row01Partner_snd_val]
    have h1 : (row01Partner (j₀, j₁)).1.val = if j₁.val < j₀.val then j₁.val else j₁.val + 1 :=
      deleteIdx_val j₀ j₁
    rw [h1]
    by_cases h : j₁.val < j₀.val
    · have h2 : ¬ (j₀.val - 1 < j₁.val) := by omega
      simp [h, h2]; omega
    · have h2 : j₀.val < j₁.val + 1 := by omega
      simp [h, h2]
  · rw [row01Partner_snd_val, row01Partner_snd_val]
    have h1 : (row01Partner (j₀, j₁)).1.val = if j₁.val < j₀.val then j₁.val else j₁.val + 1 :=
      deleteIdx_val j₀ j₁
    rw [h1]
    by_cases h : j₁.val < j₀.val
    · have h2 : ¬ (j₀.val - 1 < j₁.val) := by omega
      simp [h, h2]
    · have h2 : j₀.val < j₁.val + 1 := by omega
      simp [h, h2]

theorem deleteIdx_comm_row01 {m : Nat} (p : Fin (m + 2) × Fin (m + 1)) (c : Fin m) :
    deleteIdx (row01Partner p).1 (deleteIdx (row01Partner p).2 c) =
    deleteIdx p.1 (deleteIdx p.2 c) := by
  rcases p with ⟨j₀, j₁⟩
  apply Fin.ext
  rw [deleteIdx_val, deleteIdx_val, deleteIdx_val, deleteIdx_val, row01Partner_snd_val]
  have h1 : (row01Partner (j₀, j₁)).1.val = if j₁.val < j₀.val then j₁.val else j₁.val + 1 :=
    deleteIdx_val j₀ j₁
  rw [h1]
  by_cases h : j₁.val < j₀.val
  · simp only [h, ↓reduceIte]
    by_cases hc1 : c.val < j₀.val - 1
    · by_cases hc2 : c.val < j₁.val
      · have h3 : c.val < j₀.val := by omega
        simp [hc1, hc2, h3]
      · have h3 : c.val + 1 < j₀.val := by omega
        simp [hc1, hc2, h3]
    · have hc2 : ¬ (c.val < j₁.val) := by omega
      have h3 : ¬ (c.val + 1 < j₁.val) := by omega
      have h4 : ¬ (c.val + 1 < j₀.val) := by omega
      simp [hc1, hc2, h3, h4]
  · simp only [h, ↓reduceIte]
    by_cases hc1 : c.val < j₀.val
    · have hc2 : c.val < j₁.val + 1 := by omega
      have hc3 : c.val < j₁.val := by omega
      simp [hc1, hc2, hc3]
    · by_cases hc2 : c.val + 1 < j₁.val + 1
      · have hc3 : c.val < j₁.val := by omega
        simp [hc1, hc2, hc3]
      · have hc3 : ¬ (c.val < j₁.val) := by omega
        have hc4 : ¬ (c.val + 1 < j₀.val) := by omega
        simp [hc1, hc2, hc3, hc4]

theorem polyMul_polySum_right (a : Poly) (ps : List Poly) :
    polyMul a (polySum ps) = polySum (ps.map (fun p => polyMul a p)) := by
  induction ps with
  | nil => simp [polySum]
  | cons p ps ih =>
    simp only [polySum, List.map]
    rw [← ih]
    unfold polyMul polyAdd
    exact normPoly_eq_of_coeff_eq fun d => by
      rw [coeff_rawMul_right_congr a (coeff_normPoly (rawAdd p (polySum ps))) d,
          coeff_rawMul_add_right, coeff_rawAdd, coeff_normPoly, coeff_normPoly]

theorem polySum_listProd {α : Type u} {β : Type v}
    (xs : List α) (ys : List β) (F : α × β → Poly) :
    polySum ((listProd xs ys).map F) =
    polySum (xs.map (fun x => polySum (ys.map (fun y => F (x, y))))) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [listProd, List.map_append, polySum_append, List.map_map, polySum, ih]
    rfl

theorem polyMul_four_rearrange (s₀ a₀ s₁ a₁ D : Poly) :
    polyMul (polyMul s₀ a₀) (polyMul (polyMul s₁ a₁) D) =
    polyMul (polyMul s₀ s₁) (polyMul (polyMul a₀ a₁) D) := by
  calc
    polyMul (polyMul s₀ a₀) (polyMul (polyMul s₁ a₁) D)
      = polyMul s₀ (polyMul a₀ (polyMul s₁ (polyMul a₁ D))) := by
          rw [polyMul_assoc, polyMul_assoc]
    _ = polyMul s₀ (polyMul (polyMul a₀ s₁) (polyMul a₁ D)) := by
          rw [← polyMul_assoc a₀ s₁]
    _ = polyMul s₀ (polyMul (polyMul s₁ a₀) (polyMul a₁ D)) := by
          rw [polyMul_comm a₀ s₁]
    _ = polyMul s₀ (polyMul s₁ (polyMul a₀ (polyMul a₁ D))) := by
          rw [polyMul_assoc s₁ a₀]
    _ = polyMul (polyMul s₀ s₁) (polyMul (polyMul a₀ a₁) D) := by
          rw [← polyMul_assoc s₀ s₁, ← polyMul_assoc a₀ a₁]

/-- Swapping two adjacent rows `k` and `k + 1` negates `detPoly`. -/
theorem detPoly_rowSwapAdj :
    ∀ {n : Nat} (k : Fin n) (M : Fin (n + 1) → Fin (n + 1) → Poly),
      detPoly (fun i j => M (swapAdj k i) j) = polyNeg (detPoly M)
  | 0, k, _ => k.elim0
  | m + 1, k, M => by
    cases k using Fin.cases with
    | succ k' =>
      unfold detPoly
      rw [polyNeg_polySum, List.map_map]
      refine polySum_congr ?_
      intro j _
      have h0 : swapAdj k'.succ (0 : Fin (m + 2)) = 0 := by
        apply Fin.ext; rw [swapAdj_val]; simp
      have hmin : submatrix 0 j (fun r c => M (swapAdj k'.succ r) c) =
          (fun r c => submatrix 0 j M (swapAdj k' r) c) := by
        funext r c
        unfold submatrix
        dsimp only
        have hrow : swapAdj k'.succ (deleteIdx 0 r) = deleteIdx 0 (swapAdj k' r) := by
          apply Fin.ext
          rw [swapAdj_val, deleteIdx_val, deleteIdx_val, swapAdj_val]
          have hr0 : ¬ (r.val < 0) := by omega
          have hsw0 : ¬ ((if r.val = k'.val then k'.val + 1 else if r.val = k'.val + 1 then k'.val else r.val) < 0) := by omega
          simp only [Fin.val_zero, hr0, hsw0, ↓reduceIte, Fin.val_succ]
          by_cases h1 : r.val = k'.val
          · simp [h1]
          · by_cases h2 : r.val = k'.val + 1
            · have h1' : r.val + 1 ≠ k'.val + 1 := by omega
              simp [h1, h2, h1']
            · have h1' : r.val + 1 ≠ k'.val + 1 := by omega
              have h2' : r.val + 1 ≠ k'.val + 1 + 1 := by omega
              simp [h1, h2, h1', h2']
        rw [hrow]
      dsimp only [Function.comp]
      rw [h0, hmin, detPoly_rowSwapAdj k' (submatrix 0 j M), polyMul_neg_right]
    | zero =>
      let M' : Fin (m + 2) → Fin (m + 2) → Poly := fun i j => M (swapAdj 0 i) j
      have hexpand : ∀ A : Fin (m + 2) → Fin (m + 2) → Poly,
          detPoly A = polySum ((listProd (allFin (m + 2)) (allFin (m + 1))).map (fun p =>
            polyMul (polyMul (signPoly p.1.val) (signPoly p.2.val))
              (polyMul (polyMul (A 0 p.1) (A 1 (deleteIdx p.1 p.2)))
                (detPoly (submatrix 0 p.2 (submatrix 0 p.1 A)))))) := by
        intro A
        conv => lhs; unfold detPoly
        rw [polySum_listProd]
        refine polySum_congr ?_
        intro j₀ _
        conv => lhs; rhs; unfold detPoly
        rw [polyMul_polySum_right, List.map_map]
        refine polySum_congr ?_
        intro j₁ _
        dsimp only [Function.comp]
        have hdel0 : deleteIdx (0 : Fin (m + 2)) (0 : Fin (m + 1)) = (1 : Fin (m + 2)) := rfl
        have hentry : submatrix 0 j₀ A 0 j₁ = A 1 (deleteIdx j₀ j₁) := hdel0 ▸ rfl
        rw [hentry, polyMul_four_rearrange]
      change detPoly M' = polyNeg (detPoly M)
      rw [hexpand M', hexpand M, polyNeg_polySum, List.map_map]
      have hnd := nodup_listProd (nodup_allFin (m + 2)) (nodup_allFin (m + 1))
      refine polySum_bij hnd hnd row01Partner row01Partner
        (fun p _ => ⟨mem_listProd.mpr ⟨mem_allFin _, mem_allFin _⟩, row01Partner_invol p⟩)
        (fun q _ => ⟨mem_listProd.mpr ⟨mem_allFin _, mem_allFin _⟩, row01Partner_invol q⟩)
        _ _ ?_ (fun _ _ => normPoly_polyNeg _)
      intro p _
      dsimp only [Function.comp]
      have hswap0 : swapAdj (0 : Fin (m + 1)) (0 : Fin (m + 2)) = (1 : Fin (m + 2)) := rfl
      have hswap1 : swapAdj (0 : Fin (m + 1)) (1 : Fin (m + 2)) = (0 : Fin (m + 2)) := by
        apply Fin.ext; rw [swapAdj_val]; simp
      have hp1 : M' 0 p.1 = M 1 p.1 := by show M (swapAdj 0 0) p.1 = M 1 p.1; rw [hswap0]
      have hp2 : M' 1 (deleteIdx p.1 p.2) = M 0 (deleteIdx p.1 p.2) := by
        show M (swapAdj 0 1) (deleteIdx p.1 p.2) = M 0 (deleteIdx p.1 p.2); rw [hswap1]
      have hpartner_col : deleteIdx (row01Partner p).1 (row01Partner p).2 = p.1 := by
        have := congrArg Prod.fst (row01Partner_invol p)
        simpa [row01Partner] using this
      have hpartner_row1 : (row01Partner p).1 = deleteIdx p.1 p.2 := rfl
      have hmin : submatrix 0 p.2 (submatrix 0 p.1 M') =
          submatrix 0 (row01Partner p).2 (submatrix 0 (row01Partner p).1 M) := by
        funext r c
        unfold submatrix
        have hrr : swapAdj (0 : Fin (m + 1)) (deleteIdx 0 (deleteIdx 0 r)) =
            deleteIdx 0 (deleteIdx 0 r) := by
          apply Fin.ext
          rw [swapAdj_val, deleteIdx_val, deleteIdx_val]
          have h1 : ¬ (r.val < 0) := by omega
          have h2 : ¬ (r.val + 1 < 0) := by omega
          have h3 : r.val + 1 + 1 ≠ 0 := by omega
          have h4 : r.val + 1 + 1 ≠ 1 := by omega
          simp [h1, h2, h3, h4]
        show M (swapAdj 0 (deleteIdx 0 (deleteIdx 0 r))) (deleteIdx p.1 (deleteIdx p.2 c)) =
          M (deleteIdx 0 (deleteIdx 0 r)) (deleteIdx (row01Partner p).1 (deleteIdx (row01Partner p).2 c))
        rw [hrr, deleteIdx_comm_row01 p c]
      rw [hp1, hp2, hmin, hpartner_col, ← hpartner_row1, polyMul_comm (M 1 p.1) (M 0 (row01Partner p).1)]
      apply signPoly_mul_neg_eq (row01Partner p).1.val (row01Partner p).2.val p.1.val p.2.val
      rcases p with ⟨j₀, j₁⟩
      have hj₀ := j₀.isLt
      have hj₁ := j₁.isLt
      rw [row01Partner_snd_val]
      have h1 : (row01Partner (j₀, j₁)).1.val = if j₁.val < j₀.val then j₁.val else j₁.val + 1 :=
        deleteIdx_val j₀ j₁
      rw [h1]
      by_cases hlt : j₁.val < j₀.val
      · simp only [hlt, ↓reduceIte]; omega
      · simp only [hlt, ↓reduceIte]; omega

/-- Simultaneous adjacent swap of rows AND columns leaves `detPoly` invariant! -/
theorem detPoly_conjSwapAdj {n : Nat} (k : Fin n) (M : Fin (n + 1) → Fin (n + 1) → Poly) :
    detPoly (fun i j => M (swapAdj k i) (swapAdj k j)) = detPoly M := by
  rw [detPoly_rowSwapAdj k (fun i j => M i (swapAdj k j)),
      detPoly_colSwapAdj k M, polyNeg_neg, normPoly_detPoly]

/-! #### Decomposition of Arbitrary Bijections on `Fin n` into Adjacent Swaps -/

/-- Extend a map `f : Fin m → Fin m` to `Fin (m + 1)` by fixing `.last m`. -/
def liftFixLast {m : Nat} (f : Fin m → Fin m) (x : Fin (m + 1)) : Fin (m + 1) :=
  if h : x.val < m then ⟨(f ⟨x.val, h⟩).val, by omega⟩ else ⟨m, by omega⟩

/-- Bubble element `start` up by `steps` positions in `Fin (m + 1)` via adjacent swaps. -/
def bubbleToLast {m : Nat} : (steps : Nat) → (start : Nat) → (start + steps ≤ m) →
    Fin (m + 1) → Fin (m + 1)
  | 0, _, _, x => x
  | s + 1, st, h, x =>
    bubbleToLast s (st + 1) (by omega) (swapAdj ⟨st, by omega⟩ x)

theorem bubbleToLast_at_start {m : Nat} :
    ∀ (steps start : Nat) (h : start + steps ≤ m),
      bubbleToLast (m := m) steps start h ⟨start, by omega⟩ = ⟨start + steps, by omega⟩
  | 0, _, _ => Fin.ext (by simp [bubbleToLast])
  | s + 1, st, h => by
    unfold bubbleToLast
    have hsw : swapAdj (m := m) ⟨st, by omega⟩ ⟨st, by omega⟩ = ⟨st + 1, by omega⟩ := by
      apply Fin.ext; rw [swapAdj_val]; simp
    rw [hsw]
    have ih := bubbleToLast_at_start (m := m) s (st + 1) (by omega)
    rw [ih]
    apply Fin.ext
    simp only
    omega

theorem bubbleToLast_bijective {m : Nat} :
    ∀ (steps start : Nat) (h : start + steps ≤ m),
      ∃ g : Fin (m + 1) → Fin (m + 1),
        (∀ x, g (bubbleToLast (m := m) steps start h x) = x) ∧
        (∀ y, bubbleToLast (m := m) steps start h (g y) = y)
  | 0, _, _ => ⟨id, fun _ => rfl, fun _ => rfl⟩
  | s + 1, st, h => by
    rcases bubbleToLast_bijective (m := m) s (st + 1) (by omega) with ⟨g', hl, hr⟩
    let sw := swapAdj (m := m) ⟨st, by omega⟩
    refine ⟨fun y => sw (g' y), ?_, ?_⟩
    · intro x
      unfold bubbleToLast
      dsimp [sw]
      rw [hl (swapAdj ⟨st, by omega⟩ x), swapAdj_invol]
    · intro y
      unfold bubbleToLast
      dsimp [sw]
      rw [swapAdj_invol, hr y]

/-- Permutations of `Fin n` generated by identity, composition, and adjacent transpositions. -/
inductive GenBySwapAdj : {n : Nat} → (Fin n → Fin n) → Prop where
  | id {n : Nat} : GenBySwapAdj (n := n) id
  | comp {n : Nat} {f g : Fin n → Fin n} :
      GenBySwapAdj f → GenBySwapAdj g → GenBySwapAdj (fun x => f (g x))
  | swap {m : Nat} (k : Fin m) : GenBySwapAdj (swapAdj k)

theorem liftFixLast_val {m : Nat} (f : Fin m → Fin m) (x : Fin (m + 1)) :
    (liftFixLast f x).val = if h : x.val < m then (f ⟨x.val, h⟩).val else m := by
  unfold liftFixLast
  split <;> rfl

theorem genBySwapAdj_liftFixLast :
    ∀ {m : Nat} {f : Fin m → Fin m}, GenBySwapAdj f → GenBySwapAdj (liftFixLast f)
  | m, _, .id => by
    have h : liftFixLast (m := m) id = id := by
      funext x
      apply Fin.ext
      rw [liftFixLast_val]
      have hxl := x.isLt
      by_cases hx : x.val < m
      · simp [hx]
      · simp [hx]; omega
    rw [h]; exact .id
  | m, _, @GenBySwapAdj.comp _ f₁ f₂ h1 h2 => by
    have h : liftFixLast (m := m) (fun x => f₁ (f₂ x)) =
        (fun x => liftFixLast f₁ (liftFixLast f₂ x)) := by
      funext x
      apply Fin.ext
      rw [liftFixLast_val, liftFixLast_val, liftFixLast_val]
      by_cases hx : x.val < m
      · have hfx : (f₂ ⟨x.val, hx⟩).val < m := (f₂ ⟨x.val, hx⟩).isLt
        simp [hx, hfx]
      · have hnot : ¬ (m < m) := by omega
        simp [hx, hnot]
    rw [h]
    exact .comp (genBySwapAdj_liftFixLast h1) (genBySwapAdj_liftFixLast h2)
  | m' + 1, _, .swap k => by
    have h : liftFixLast (m := m' + 1) (swapAdj k) = swapAdj ⟨k.val, by omega⟩ := by
      funext x
      apply Fin.ext
      rw [liftFixLast_val, swapAdj_val]
      have hxl := x.isLt
      have hkl := k.isLt
      by_cases hx : x.val < m' + 1
      · simp only [hx, ↓reduceDIte, swapAdj_val]
      · have hm1 : m' + 1 ≠ k.val := by omega
        have hm2 : m' + 1 ≠ k.val + 1 := by omega
        have hxv : x.val = m' + 1 := by omega
        simp only [hx, ↓reduceDIte]
        simp only [hxv, hm1, hm2, ↓reduceIte]
    rw [h]
    exact .swap ⟨k.val, by omega⟩

theorem genBySwapAdj_bubbleToLast {m : Nat} :
    ∀ (steps start : Nat) (h : start + steps ≤ m),
      GenBySwapAdj (bubbleToLast (m := m) steps start h)
  | 0, _, _ => .id
  | s + 1, st, h => by
    have heta : bubbleToLast (m := m) (s + 1) st h =
        (fun x => bubbleToLast (m := m) s (st + 1) (by omega) (swapAdj ⟨st, by omega⟩ x)) := rfl
    rw [heta]
    exact .comp (genBySwapAdj_bubbleToLast (m := m) s (st + 1) (by omega)) (.swap ⟨st, by omega⟩)

/-- Every bijection `f : Fin n → Fin n` is generated by adjacent transpositions. -/
theorem genBySwapAdj_of_bijective :
    ∀ {n : Nat} (f g : Fin n → Fin n),
      (∀ x, g (f x) = x) → (∀ y, f (g y) = y) → GenBySwapAdj f
  | 0, f, _, _, _ => by
    have : f = id := funext fun x => x.elim0
    rw [this]; exact .id
  | 1, f, _, _, _ => by
    have : f = id := funext fun x => Fin.ext (by omega)
    rw [this]; exact .id
  | m + 2, f, g, hfg, hgf => by
    let lastIdx : Fin (m + 2) := ⟨m + 1, by omega⟩
    let a : Fin (m + 2) := g lastIdx
    have hal := a.isLt
    have hfa : f a = lastIdx := hgf lastIdx
    let steps := (m + 1) - a.val
    have hbound : a.val + steps ≤ m + 1 := by omega
    let B := bubbleToLast (m := m + 1) steps a.val hbound
    rcases bubbleToLast_bijective (m := m + 1) steps a.val hbound with ⟨Binv, hBl, hBr⟩
    have hBa : B a = lastIdx := by
      have h1 := bubbleToLast_at_start (m := m + 1) steps a.val hbound
      exact h1.trans (Fin.ext (by simp [lastIdx, steps]; omega))
    have hBinv_last : Binv lastIdx = a := by
      have h1 : Binv (B a) = a := hBl a
      rw [hBa] at h1
      exact h1
    let f' : Fin (m + 2) → Fin (m + 2) := fun x => f (Binv x)
    let g' : Fin (m + 2) → Fin (m + 2) := fun y => B (g y)
    have hf'g' : ∀ x, g' (f' x) = x := fun x => by
      dsimp [f', g', B]; rw [hfg, hBr]
    have hg'f' : ∀ y, f' (g' y) = y := fun y => by
      dsimp [f', g', B]; rw [hBl, hgf]
    have hf'_last : f' lastIdx = lastIdx := by dsimp [f']; rw [hBinv_last, hfa]
    have hg'_last : g' lastIdx = lastIdx := by dsimp [g']; exact hBa
    have hf'_lt : ∀ u : Fin (m + 1), (f' ⟨u.val, by omega⟩).val < m + 1 := by
      intro u
      have hfl := (f' ⟨u.val, by omega⟩).isLt
      have hne : f' ⟨u.val, by omega⟩ ≠ lastIdx := by
        intro heq
        have := congrArg g' heq
        rw [hf'g', hg'_last] at this
        have : u.val = m + 1 := congrArg Fin.val this
        omega
      have : (f' ⟨u.val, by omega⟩).val ≠ m + 1 := fun h => hne (Fin.ext h)
      omega
    have hg'_lt : ∀ v : Fin (m + 1), (g' ⟨v.val, by omega⟩).val < m + 1 := by
      intro v
      have hgl := (g' ⟨v.val, by omega⟩).isLt
      have hne : g' ⟨v.val, by omega⟩ ≠ lastIdx := by
        intro heq
        have := congrArg f' heq
        rw [hg'f', hf'_last] at this
        have : v.val = m + 1 := congrArg Fin.val this
        omega
      have : (g' ⟨v.val, by omega⟩).val ≠ m + 1 := fun h => hne (Fin.ext h)
      omega
    let f₀ : Fin (m + 1) → Fin (m + 1) := fun u => ⟨(f' ⟨u.val, by omega⟩).val, hf'_lt u⟩
    let g₀ : Fin (m + 1) → Fin (m + 1) := fun v => ⟨(g' ⟨v.val, by omega⟩).val, hg'_lt v⟩
    have hf₀g₀ : ∀ u, g₀ (f₀ u) = u := by
      intro u; apply Fin.ext
      show (g' ⟨(f' ⟨u.val, _⟩).val, _⟩).val = u.val
      have heq : (⟨(f' ⟨u.val, by omega⟩).val, by omega⟩ : Fin (m + 2)) = f' ⟨u.val, by omega⟩ :=
        Fin.ext rfl
      rw [heq]
      exact congrArg Fin.val (hf'g' ⟨u.val, by omega⟩)
    have hg₀f₀ : ∀ v, f₀ (g₀ v) = v := by
      intro v; apply Fin.ext
      show (f' ⟨(g' ⟨v.val, _⟩).val, _⟩).val = v.val
      have heq : (⟨(g' ⟨v.val, by omega⟩).val, by omega⟩ : Fin (m + 2)) = g' ⟨v.val, by omega⟩ :=
        Fin.ext rfl
      rw [heq]
      exact congrArg Fin.val (hg'f' ⟨v.val, by omega⟩)
    have hf_decomp : f = (fun x => liftFixLast f₀ (B x)) := by
      funext x
      have hfx : f x = f' (B x) := by dsimp [f', B]; rw [hBl]
      rw [hfx]
      apply Fin.ext
      rw [liftFixLast_val]
      have hBxl := (B x).isLt
      by_cases hBx : (B x).val < m + 1
      · simp only [hBx, ↓reduceDIte, f₀]
      · simp only [hBx, ↓reduceDIte]
        have hBl' : B x = lastIdx := Fin.ext (by simp [lastIdx]; omega)
        rw [hBl', hf'_last]
    rw [hf_decomp]
    exact .comp (genBySwapAdj_liftFixLast (genBySwapAdj_of_bijective f₀ g₀ hf₀g₀ hg₀f₀))
      (genBySwapAdj_bubbleToLast (m := m + 1) steps a.val hbound)

theorem detPoly_of_genBySwapAdj :
    ∀ {n : Nat} {f : Fin n → Fin n}, GenBySwapAdj f →
      ∀ (M : Fin n → Fin n → Poly), detPoly (fun i j => M (f i) (f j)) = detPoly M
  | _, _, .id, _ => rfl
  | _, _, @GenBySwapAdj.comp _ f₁ f₂ _ _ , M => by
    rename_i h1 h2
    rw [detPoly_of_genBySwapAdj h2 (fun i j => M (f₁ i) (f₁ j)), detPoly_of_genBySwapAdj h1 M]
  | _, _, .swap k, M => detPoly_conjSwapAdj k M

/-- Simultaneous row-and-column permutation by ANY bijection preserves `detPoly`. -/
theorem detPoly_conjPerm {n : Nat} (f g : Fin n → Fin n)
    (hfg : ∀ x, g (f x) = x) (hgf : ∀ y, f (g y) = y)
    (M : Fin n → Fin n → Poly) :
    detPoly (fun i j => M (f i) (f j)) = detPoly M :=
  detPoly_of_genBySwapAdj (genBySwapAdj_of_bijective f g hfg hgf) M

/-- Isomorphic graphs have identical characteristic polynomials `det(xI - A_G)`. -/
theorem IsoWitness.charPoly_eq {n : Nat} {G₁ G₂ : SimpleGraphN n}
    (w : IsoWitness G₁ G₂) : charPoly G₁ = charPoly G₂ := by
  unfold charPoly
  have hmat : charMatrix G₁ = (fun i j => charMatrix G₂ (w.toFun i) (w.toFun j)) := by
    funext i j
    unfold charMatrix
    by_cases hij : i = j
    · subst hij; simp
    · have hwij : w.toFun i ≠ w.toFun j := by
        intro heq
        apply hij
        rw [← w.left_inv i, ← w.left_inv j, heq]
      simp [hij, hwij, w.map_adj i j]
  rw [hmat]
  exact detPoly_conjPerm w.toFun w.invFun w.left_inv w.right_inv (charMatrix G₂)

theorem GraphIso.charPoly_eq {n : Nat} {G₁ G₂ : SimpleGraphN n}
    (h : GraphIso G₁ G₂) : charPoly G₁ = charPoly G₂ :=
  let ⟨w⟩ := h
  w.charPoly_eq

end Conjecture00000003970
