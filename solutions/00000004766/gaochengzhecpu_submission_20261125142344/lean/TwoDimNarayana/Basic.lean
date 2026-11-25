/-
  Conjecture 00000004766 — Two-Dimensional Noncrossing and Narayana Polynomials
  Basic.lean: Univariate and bivariate integer polynomials, Narayana numbers,
  symmetry/palindromicity predicates, and universal root-vanishing / non-polynomiality lemmas.
-/

namespace TwoDimNarayana

/-- Binomial coefficient C(n, k). -/
def binom : Nat → Nat → Nat
  | _, 0 => 1
  | 0, _ + 1 => 0
  | n + 1, k + 1 => binom n k + binom n (k + 1)

/-- Classical 1D Narayana number N(n, k) = (1/n) * C(n, k) * C(n, k-1) for 1 ≤ k ≤ n. -/
def narayana : Nat → Nat → Nat
  | 0, _ => 0
  | _, 0 => 0
  | n, k => (binom n k * binom n (k - 1)) / n

/-- Classical Catalan number C_n = C(2n, n) / (n + 1). -/
def catalan (n : Nat) : Nat :=
  binom (2 * n) n / (n + 1)

/-- Univariate polynomial p(t) = ∑_{k=0}^{m-1} c_k t^k represented by its coefficient list. -/
abbrev Poly1 := List Int

/-- Coefficient of t^k in a univariate polynomial. -/
def coeff1 (p : Poly1) (k : Nat) : Int :=
  p.getD k 0

/-- Classical 1D Narayana polynomial N_n(t) = ∑_{k=1}^n N(n, k) t^k. -/
def narayanaPoly1 (n : Nat) : Poly1 :=
  0 :: (List.range n).map (fun i => (narayana n (i + 1) : Int))

/-- Narayana palindromicity (Kreweras self-duality): coeff(k) = coeff(N + 1 - k) for 1 ≤ k ≤ N. -/
def isPalindromic1 (N : Nat) (p : Poly1) : Bool :=
  (List.range N).all (fun i =>
    let k := i + 1
    coeff1 p k == coeff1 p (N + 1 - k))

/-- Bivariate polynomial P(u, v) = ∑_{i, j} c_{i,j} u^i v^j represented as rows of coefficients in v. -/
abbrev Poly2 := List (List Int)

/-- Coefficient of u^i v^j in P(u, v). -/
def coeff2 (P : Poly2) (i j : Nat) : Int :=
  (P.getD i []).getD j 0

/-- Product of two univariate polynomials as a bivariate polynomial P(u) * Q(v). -/
def outerProdPoly (p q : Poly1) : Poly2 :=
  p.map (fun ci => q.map (fun cj => ci * cj))

/-- Bivariate variable-swap symmetry P(u, v) = P(v, u) up to degree bound B. -/
def isSymmetric2 (B : Nat) (P : Poly2) : Bool :=
  (List.range (B + 1)).all (fun i =>
    (List.range (B + 1)).all (fun j =>
      coeff2 P i j == coeff2 P j i))

/-- Two-dimensional Narayana biduality: coeff(i, j) = coeff(n + 1 - i, n + 1 - j) for 1 ≤ i, j ≤ n. -/
def isBidual2 (n : Nat) (P : Poly2) : Bool :=
  (List.range n).all (fun a =>
    (List.range n).all (fun b =>
      let i := a + 1
      let j := b + 1
      coeff2 P i j == coeff2 P (n + 1 - i) (n + 1 - j)))

/-! ### Exact Evaluation and Universal Vanishing Lemma for Polynomials -/

/-- Evaluate a univariate polynomial ∑ c_k x^k at x : Int. -/
def evalPoly1 : Poly1 → Int → Int
  | [], _ => 0
  | c :: cs, x => c + x * evalPoly1 cs x

/-- Coefficient-wise addition of univariate polynomials. -/
def polyAdd1 : Poly1 → Poly1 → Poly1
  | [], q => q
  | p, [] => p
  | a :: as, b :: bs => (a + b) :: polyAdd1 as bs

/-- Scalar multiplication of a univariate polynomial. -/
def polyScale1 (s : Int) : Poly1 → Poly1
  | [] => []
  | a :: as => (s * a) :: polyScale1 s as

/-- Negation of a univariate polynomial. -/
def polyNeg1 : Poly1 → Poly1
  | [] => []
  | a :: as => (-a) :: polyNeg1 as

/-- Subtraction of univariate polynomials. -/
def polySub1 (p q : Poly1) : Poly1 :=
  polyAdd1 p (polyNeg1 q)

theorem evalPoly1_add (p q : Poly1) (x : Int) :
    evalPoly1 (polyAdd1 p q) x = evalPoly1 p x + evalPoly1 q x := by
  induction p generalizing q with
  | nil => simp [polyAdd1, evalPoly1]
  | cons a as ih =>
    cases q with
    | nil => simp [polyAdd1, evalPoly1]
    | cons b bs =>
      simp only [polyAdd1, evalPoly1, ih, Int.mul_add]
      omega

theorem evalPoly1_scale (s : Int) (p : Poly1) (x : Int) :
    evalPoly1 (polyScale1 s p) x = s * evalPoly1 p x := by
  induction p with
  | nil => simp [polyScale1, evalPoly1]
  | cons a as ih =>
    simp only [polyScale1, evalPoly1, ih, Int.mul_add]
    have hmul : s * (x * evalPoly1 as x) = x * (s * evalPoly1 as x) := by
      rw [← Int.mul_assoc, Int.mul_comm s x, Int.mul_assoc]
    omega

theorem evalPoly1_neg (p : Poly1) (x : Int) :
    evalPoly1 (polyNeg1 p) x = -evalPoly1 p x := by
  induction p with
  | nil => simp [polyNeg1, evalPoly1]
  | cons a as ih =>
    simp only [polyNeg1, evalPoly1, ih, Int.mul_neg]
    omega

theorem evalPoly1_sub_poly (p q : Poly1) (x : Int) :
    evalPoly1 (polySub1 p q) x = evalPoly1 p x - evalPoly1 q x := by
  simp only [polySub1, evalPoly1_add, evalPoly1_neg]
  omega

theorem polyAdd1_length (p q : Poly1) :
    (polyAdd1 p q).length ≤ if p.length ≤ q.length then q.length else p.length := by
  induction p generalizing q with
  | nil => simp [polyAdd1]
  | cons a as ih =>
    cases q with
    | nil => simp [polyAdd1]
    | cons b bs =>
      simp only [polyAdd1, List.length_cons]
      have h := ih bs
      split at h <;> split <;> omega

theorem polyScale1_length (s : Int) (p : Poly1) :
    (polyScale1 s p).length = p.length := by
  induction p with
  | nil => rfl
  | cons _ as ih => simp [polyScale1, ih]

/-- Difference quotient polynomial q(x) satisfying p(x) - p(r) = (x - r) * q(x). -/
def diffQuot : Poly1 → Int → Poly1
  | [], _ => []
  | _ :: cs, r => polyAdd1 cs (polyScale1 r (diffQuot cs r))

theorem diffQuot_length (c : Int) (cs : Poly1) (r : Int) :
    (diffQuot (c :: cs) r).length ≤ cs.length := by
  induction cs generalizing c with
  | nil => simp [diffQuot, polyScale1, polyAdd1]
  | cons c2 cs2 ih =>
    rw [diffQuot]
    have h1 := polyAdd1_length (c2 :: cs2) (polyScale1 r (diffQuot (c2 :: cs2) r))
    rw [polyScale1_length] at h1
    have h2 := ih c2
    simp only [List.length_cons] at h1 h2 ⊢
    split at h1 <;> omega

theorem evalPoly1_sub_eval (p : Poly1) (x r : Int) :
    evalPoly1 p x - evalPoly1 p r = (x - r) * evalPoly1 (diffQuot p r) x := by
  induction p with
  | nil => simp [diffQuot, evalPoly1]
  | cons c cs ih =>
    rw [diffQuot]
    simp only [evalPoly1, evalPoly1_add, evalPoly1_scale]
    have step1 : (c + x * evalPoly1 cs x) - (c + r * evalPoly1 cs r) =
        (x - r) * evalPoly1 cs x + r * (evalPoly1 cs x - evalPoly1 cs r) := by
      rw [Int.sub_mul, Int.mul_sub]
      omega
    rw [step1, ih]
    have step2 : r * ((x - r) * evalPoly1 (diffQuot cs r) x) =
        (x - r) * (r * evalPoly1 (diffQuot cs r) x) := by
      rw [← Int.mul_assoc, Int.mul_comm r (x - r), Int.mul_assoc]
    rw [step2, ← Int.mul_add]

/-- Any univariate polynomial over ℤ that vanishes at all natural numbers n ≥ k vanishes identically. -/
theorem evalPoly1_eq_zero_of_forall_ge :
    ∀ (degBound : Nat) (p : Poly1), p.length ≤ degBound →
      ∀ (k : Nat), (∀ n : Nat, k ≤ n → evalPoly1 p (n : Int) = 0) →
        ∀ x : Int, evalPoly1 p x = 0
  | 0, p, hlen, _, _, x => by
    cases p with
    | nil => rfl
    | cons _ _ => simp at hlen
  | d + 1, [], _, _, _, _ => rfl
  | d + 1, c :: cs, hlen, k, hvan, x => by
    have hk : evalPoly1 (c :: cs) (k : Int) = 0 := hvan k (Nat.le_refl k)
    have hq_len : (diffQuot (c :: cs) (k : Int)).length ≤ d := by
      have h1 := diffQuot_length c cs (k : Int)
      simp only [List.length_cons] at hlen
      omega
    have hq_van : ∀ n : Nat, k + 1 ≤ n → evalPoly1 (diffQuot (c :: cs) (k : Int)) (n : Int) = 0 := by
      intro n hn
      have hn0 : evalPoly1 (c :: cs) (n : Int) = 0 := hvan n (by omega)
      have hsub := evalPoly1_sub_eval (c :: cs) (n : Int) (k : Int)
      rw [hn0, hk] at hsub
      have hmul : ((n : Int) - (k : Int)) * evalPoly1 (diffQuot (c :: cs) (k : Int)) (n : Int) = 0 :=
        hsub.symm
      have hne : (n : Int) - (k : Int) ≠ 0 := by omega
      cases Int.mul_eq_zero.mp hmul with
      | inl hfalse => exact False.elim (hne hfalse)
      | inr hzero => exact hzero
    have hq_all := evalPoly1_eq_zero_of_forall_ge d (diffQuot (c :: cs) (k : Int)) hq_len (k + 1) hq_van x
    have hsub := evalPoly1_sub_eval (c :: cs) x (k : Int)
    rw [hk, hq_all, Int.mul_zero] at hsub
    omega

/-- Evaluate a bivariate polynomial P(x, y) = ∑_{i, j} c_{i,j} x^i y^j at (x, y) ∈ ℤ².
    Notice that for fixed x, y ↦ evalPoly2 P x y is a univariate polynomial in y! -/
def evalPoly2AsPolyY : Poly2 → Int → Poly1
  | [], _ => []
  | row :: rows, x => polyAdd1 row (polyScale1 x (evalPoly2AsPolyY rows x))

def evalPoly2 (P : Poly2) (x y : Int) : Int :=
  evalPoly1 (evalPoly2AsPolyY P x) y

/-- Direct Horner evaluation ∑_i x^i (∑_j c_{i,j} y^j) agrees with `evalPoly2`. -/
def evalPoly2Horner : Poly2 → Int → Int → Int
  | [], _, _ => 0
  | row :: rows, x, y => evalPoly1 row y + x * evalPoly2Horner rows x y

theorem evalPoly2_eq_horner (P : Poly2) (x y : Int) :
    evalPoly2 P x y = evalPoly2Horner P x y := by
  unfold evalPoly2
  induction P with
  | nil => rfl
  | cons row rows ih =>
    simp only [evalPoly2AsPolyY, evalPoly2Horner, evalPoly1_add, evalPoly1_scale, ih]

/-- General algebraic obstruction: no rational bivariate polynomial (1/D) * P(x, y) (with D > 0)
    can take value 2*n + 1 for all (m, n) = (2, n) with n ≥ 2 while taking value 1 at (2, 1). -/
theorem no_biv_poly_grid_slice (D : Nat) (hD : 0 < D) (P : Poly2)
    (h_ge2 : ∀ n : Nat, 2 ≤ n → evalPoly2 P 2 (n : Int) = ((D * (2 * n + 1)) : Int))
    (h_at1 : evalPoly2 P 2 1 = (D : Int)) : False := by
  let g : Poly1 := evalPoly2AsPolyY P 2
  let lin : Poly1 := [(D : Int), (2 * (D : Int))]
  let diff : Poly1 := polySub1 g lin
  have hvan : ∀ n : Nat, 2 ≤ n → evalPoly1 diff (n : Int) = 0 := by
    intro n hn
    have hgn : evalPoly1 g (n : Int) = ((D * (2 * n + 1)) : Int) := h_ge2 n hn
    change evalPoly1 (polySub1 g [(D : Int), (2 * (D : Int))]) (n : Int) = 0
    rw [evalPoly1_sub_poly, hgn]
    simp only [evalPoly1, Int.mul_zero, Int.add_zero]
    have hcast : ((D * (2 * n + 1)) : Int) = (D : Int) * (2 * (n : Int) + 1) := by
      omega
    have hmul : (n : Int) * (2 * (D : Int)) = (D : Int) * (2 * (n : Int)) := by
      calc (n : Int) * (2 * (D : Int))
        _ = ((n : Int) * 2) * (D : Int) := (Int.mul_assoc _ _ _).symm
        _ = (2 * (n : Int)) * (D : Int) := by rw [Int.mul_comm (n : Int) 2]
        _ = (D : Int) * (2 * (n : Int)) := Int.mul_comm _ _
    rw [hmul, Int.mul_add, Int.mul_one] at *
    omega
  have hall := evalPoly1_eq_zero_of_forall_ge diff.length diff (Nat.le_refl _) 2 hvan 1
  have hg1 : evalPoly1 g 1 = (D : Int) := h_at1
  change evalPoly1 (polySub1 g [(D : Int), (2 * (D : Int))]) 1 = 0 at hall
  rw [evalPoly1_sub_poly, hg1] at hall
  simp only [evalPoly1, Int.one_mul, Int.mul_zero, Int.add_zero] at hall
  omega

end TwoDimNarayana
