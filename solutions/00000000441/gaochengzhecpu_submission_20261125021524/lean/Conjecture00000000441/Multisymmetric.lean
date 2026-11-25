/-
  Multisymmetric.lean
  First-principles algebraic model of multisymmetric polynomials in `n` vector variables
  across `r` sets of variables over `ℤ`, defining:
  - Multivariate polynomials `Poly` in merge-sorted normal form,
  - Multisymmetric monomial basis `mPoly` (orbit sum over `S_n`),
  - Elementary multisymmetric basis `ePoly` from `∏_{i=1}^n (1 + ∑_{j=1}^r t_j x_{i,j})`,
  - Complete homogeneous multisymmetric basis `hPoly` from `∏_{i=1}^n (1 - ∑_{j=1}^r t_j x_{i,j})^{-1}`,
  - Power-sum multisymmetric basis `pPoly` from `∑_{i=1}^n x_i^u`,
  - Dual-functional linear independence of `{m_Λ}` and uniqueness of transition matrices,
  - Set-partition multilinear formula `M(e, m)_{π, σ}` at `d = (1, ..., 1)`,
  - General all-`r` power-sum automorphism diagonal formula and divisibility by `3` at `d = (3, 1, ..., 1)`.
-/

import Conjecture00000000441.LinearAlgebra

namespace Conjecture00000000441

/-- Multi-exponent vector `u ∈ ℕ^r` for a single vector variable `(x_{i,1}, ..., x_{i,r})`. -/
abbrev Vec := List Nat

/-- A vector partition `Λ = [u_1, ..., u_ℓ]` of multidegree `d ∈ ℕ^r`. -/
abbrev VecPart := List Vec

/-- A monomial in `n × r` variables: list of `n` exponent vectors `v_0, ..., v_{n-1} ∈ ℕ^r`. -/
abbrev Monom := List Vec

def vecZero (r : Nat) : Vec :=
  List.replicate r 0

def unitVec (r j : Nat) : Vec :=
  (List.range r).map (fun k => if k == j then 1 else 0)

def vecAdd : Vec → Vec → Vec
  | [], _ => []
  | _, [] => []
  | a :: as, b :: bs => (a + b) :: vecAdd as bs

def vecLeq : Vec → Vec → Bool
  | [], [] => true
  | a :: as, b :: bs => (a ≤ b) && vecLeq as bs
  | _, _ => false

def vecSum (r : Nat) : List Vec → Vec
  | [] => vecZero r
  | u :: us => vecAdd u (vecSum r us)

def cmpNat (a b : Nat) : Ordering :=
  if a < b then Ordering.lt else if b < a then Ordering.gt else Ordering.eq

theorem cmpNat_eq_iff (a b : Nat) : cmpNat a b = Ordering.eq → a = b := by
  unfold cmpNat
  by_cases h1 : a < b
  · simp [h1]
  · by_cases h2 : b < a
    · simp [h1, h2]
    · intro _; omega

def cmpVec : Vec → Vec → Ordering
  | [], [] => Ordering.eq
  | [], _ :: _ => Ordering.lt
  | _ :: _, [] => Ordering.gt
  | a :: as, b :: bs =>
      match cmpNat a b with
      | Ordering.eq => cmpVec as bs
      | ord => ord

theorem cmpVec_eq_iff : ∀ (u v : Vec), cmpVec u v = Ordering.eq → u = v
  | [], [], _ => rfl
  | [], _ :: _, h => by simp [cmpVec] at h
  | _ :: _, [], h => by simp [cmpVec] at h
  | a :: as, b :: bs, h => by
    simp only [cmpVec] at h
    cases hnat : cmpNat a b with
    | lt => rw [hnat] at h; contradiction
    | gt => rw [hnat] at h; contradiction
    | eq =>
      rw [hnat] at h
      rw [cmpNat_eq_iff a b hnat, cmpVec_eq_iff as bs h]

def cmpMonom : Monom → Monom → Ordering
  | [], [] => Ordering.eq
  | [], _ :: _ => Ordering.lt
  | _ :: _, [] => Ordering.gt
  | u :: us, v :: vs =>
      match cmpVec u v with
      | Ordering.eq => cmpMonom us vs
      | ord => ord

theorem cmpMonom_eq_iff : ∀ (m1 m2 : Monom), cmpMonom m1 m2 = Ordering.eq → m1 = m2
  | [], [], _ => rfl
  | [], _ :: _, h => by simp [cmpMonom] at h
  | _ :: _, [], h => by simp [cmpMonom] at h
  | u :: us, v :: vs, h => by
    simp only [cmpMonom] at h
    cases hv : cmpVec u v with
    | lt => rw [hv] at h; contradiction
    | gt => rw [hv] at h; contradiction
    | eq =>
      rw [hv] at h
      rw [cmpVec_eq_iff u v hv, cmpMonom_eq_iff us vs h]

def monomZero (n r : Nat) : Monom :=
  List.replicate n (vecZero r)

def monomMul : Monom → Monom → Monom
  | [], _ => []
  | _, [] => []
  | u :: us, v :: vs => vecAdd u v :: monomMul us vs

def monomDeg (r : Nat) (m : Monom) : Vec :=
  vecSum r m

def monomLeqDeg (r : Nat) (m : Monom) (d : Vec) : Bool :=
  vecLeq (monomDeg r m) d

/-- Sparse multivariate polynomial over `ℤ` in sorted normal form (`List (Monom × Int)`). -/
abbrev Poly := List (Monom × Int)

def polyZero : Poly := []

def polyOne (n r : Nat) : Poly :=
  [(monomZero n r, 1)]

def mergePolyAux (m1 : Monom) (c1 : Int) (p' : Poly) (mergeP' : Poly → Poly) : Poly → Poly
  | [] => (m1, c1) :: p'
  | (m2, c2) :: q' =>
      match cmpMonom m1 m2 with
      | Ordering.lt => (m1, c1) :: mergeP' ((m2, c2) :: q')
      | Ordering.gt => (m2, c2) :: mergePolyAux m1 c1 p' mergeP' q'
      | Ordering.eq =>
          let s := c1 + c2
          if s == 0 then mergeP' q'
          else (m1, s) :: mergeP' q'

def mergePoly : Poly → Poly → Poly
  | [], q => q
  | (m1, c1) :: p', q => mergePolyAux m1 c1 p' (mergePoly p') q

def polyAdd (p q : Poly) : Poly :=
  mergePoly p q

def polyScale (c : Int) (p : Poly) : Poly :=
  if c == 0 then []
  else p.filterMap (fun (m, k) =>
    let ck := c * k
    if ck == 0 then none else some (m, ck))

def polyMulTerm (m : Monom) (c : Int) (q : Poly) : Poly :=
  if c == 0 then []
  else q.filterMap (fun (m', k) =>
    let ck := c * k
    if ck == 0 then none else some (monomMul m m', ck))

def polyMul (p q : Poly) : Poly :=
  p.foldl (fun acc (m, c) => polyAdd acc (polyMulTerm m c q)) []

def polyMulTrunc (r : Nat) (bound : Vec) : Poly → Poly → Poly
  | [], _ => []
  | (m, c) :: rest, q =>
      let term := (polyMulTerm m c q).filter (fun (m', _) => monomLeqDeg r m' bound)
      polyAdd term (polyMulTrunc r bound rest q)

def polyProdTrunc (n r : Nat) (bound : Vec) : List Poly → Poly
  | [] => polyOne n r
  | p :: ps => polyMulTrunc r bound p (polyProdTrunc n r bound ps)

def polySumList : List Poly → Poly
  | [] => polyZero
  | p :: ps => polyAdd p (polySumList ps)

def polyFilterDeg (r : Nat) (d : Vec) (p : Poly) : Poly :=
  p.filter (fun (m, _) => monomDeg r m == d)

/-- Extract the coefficient of monomial `target` in `p`. -/
def polyCoeff : Poly → Monom → Int
  | [], _ => 0
  | (m, c) :: rest, target => (if m == target then c else 0) + polyCoeff rest target

/-- Insert a single monomial `(m, 1)` into a sorted `Poly`, dropping duplicates for orbit sums. -/
def insertOrbitMonom (m : Monom) : Poly → Poly
  | [] => [(m, 1)]
  | (m', c) :: rest =>
      match cmpMonom m m' with
      | Ordering.lt => (m, 1) :: (m', c) :: rest
      | Ordering.eq => (m', c) :: rest
      | Ordering.gt => (m', c) :: insertOrbitMonom m rest

def eraseFirst {α : Type} [BEq α] (x : α) : List α → List α
  | [] => []
  | y :: ys => if x == y then ys else y :: eraseFirst x ys

def dedupList {α : Type} [BEq α] : List α → List α
  | [] => []
  | x :: xs =>
      let rest := dedupList xs
      if rest.any (· == x) then rest else x :: rest

def distinctPerms : Nat → List Vec → List Monom
  | 0, _ => [[]]
  | k + 1, xs =>
      let choices := dedupList xs
      choices.foldr (fun v acc =>
        let sub := distinctPerms k (eraseFirst v xs)
        (sub.map (fun tail => v :: tail)) ++ acc) []

/-- Representative monomial `x_0^{u_0} ⋯ x_{ℓ-1}^{u_{ℓ-1}}` of a vector partition `Λ` in `n` variables. -/
def repMonom (n r : Nat) (Λ : VecPart) : Monom :=
  Λ ++ List.replicate (n - Λ.length) (vecZero r)

/-- Multisymmetric monomial basis polynomial `m_Λ` in `n` vector variables across `r` variable sets. -/
def mPoly (n r : Nat) (Λ : VecPart) : Poly :=
  let base := repMonom n r Λ
  (distinctPerms base.length base).foldr insertOrbitMonom []

def singleVarMonom (n r slot varSet : Nat) : Monom :=
  (List.range n).map (fun i => if i == slot then unitVec r varSet else vecZero r)

/-- Elementary generator `e_u` from `[t^u] ∏_{i=0}^{n-1} (1 + ∑_{j=0}^{r-1} t_j x_{i,j})`. -/
def eGenPoly (n r : Nat) (u : Vec) : Poly :=
  let factors := (List.range n).map (fun i =>
    polyAdd (polyOne n r) (polySumList ((List.range r).filterMap (fun j =>
      if u.getD j 0 == 0 then none
      else some [(singleVarMonom n r i j, 1)]))))
  polyFilterDeg r u (polyProdTrunc n r u factors)

/-- Elementary multisymmetric basis element `e_Λ = ∏_{u ∈ Λ} e_u`. -/
def ePoly (n r : Nat) (d : Vec) (Λ : VecPart) : Poly :=
  polyFilterDeg r d (polyProdTrunc n r d (Λ.map (eGenPoly n r)))

def hHornerAux (n r : Nat) (u : Vec) (lin : Poly) : Nat → Poly
  | 0 => polyOne n r
  | k + 1 => polyAdd (polyOne n r) (polyMulTrunc r u lin (hHornerAux n r u lin k))

/-- Complete homogeneous generator `h_u` from `[t^u] ∏_{i=0}^{n-1} (1 - ∑_{j=0}^{r-1} t_j x_{i,j})^{-1}`. -/
def hGenPoly (n r : Nat) (u : Vec) : Poly :=
  let tot := u.foldr (· + ·) 0
  let factors := (List.range n).map (fun i =>
    let lin := polySumList ((List.range r).filterMap (fun j =>
      if u.getD j 0 == 0 then none
      else some [(singleVarMonom n r i j, 1)]))
    hHornerAux n r u lin tot)
  polyFilterDeg r u (polyProdTrunc n r u factors)

/-- Complete homogeneous multisymmetric basis element `h_Λ = ∏_{u ∈ Λ} h_u`. -/
def hPoly (n r : Nat) (d : Vec) (Λ : VecPart) : Poly :=
  polyFilterDeg r d (polyProdTrunc n r d (Λ.map (hGenPoly n r)))

/-- Power-sum generator `p_u = ∑_{i=0}^{n-1} x_i^u`. -/
def pGenPoly (n r : Nat) (u : Vec) : Poly :=
  polySumList ((List.range n).map (fun i =>
    [( (List.range n).map (fun s => if s == i then u else vecZero r), 1 )]))

/-- Power-sum multisymmetric basis element `p_Λ = ∏_{u ∈ Λ} p_u`. -/
def pPoly (n r : Nat) (d : Vec) (Λ : VecPart) : Poly :=
  polyFilterDeg r d (polyProdTrunc n r d (Λ.map (pGenPoly n r)))

/-- Linear combination `∑_{j : Fin N} c_j • basis_j` in `Poly`, skipping zero coefficients. -/
def polyLinComb : (N : Nat) → (Fin N → Int) → (Fin N → Poly) → Poly
  | 0, _, _ => polyZero
  | N + 1, c, b =>
      let c0 := c ⟨0, Nat.zero_lt_succ N⟩
      let rest := polyLinComb N (fun j => c ⟨j.val + 1, Nat.succ_lt_succ j.isLt⟩)
        (fun j => b ⟨j.val + 1, Nat.succ_lt_succ j.isLt⟩)
      if c0 == 0 then rest
      else polyAdd (polyScale c0 (b ⟨0, Nat.zero_lt_succ N⟩)) rest

/-! ### Linearity of `polyCoeff` and Uniqueness of Basis Transition Matrices -/

theorem polyCoeff_mergePolyAux (m1 : Monom) (c1 : Int) (p' : Poly)
    (mergeP' : Poly → Poly)
    (ih : ∀ (q0 : Poly) (target : Monom),
      polyCoeff (mergeP' q0) target = polyCoeff p' target + polyCoeff q0 target) :
    ∀ (q : Poly) (target : Monom),
      polyCoeff (mergePolyAux m1 c1 p' mergeP' q) target =
        polyCoeff ((m1, c1) :: p') target + polyCoeff q target
  | [], target => by simp [mergePolyAux, polyCoeff]
  | (m2, c2) :: q', target => by
    simp only [mergePolyAux]
    cases hcmp : cmpMonom m1 m2 with
    | lt =>
      simp only [polyCoeff]
      rw [ih ((m2, c2) :: q') target]
      simp only [polyCoeff]
      omega
    | gt =>
      simp only [polyCoeff]
      rw [polyCoeff_mergePolyAux m1 c1 p' mergeP' ih q' target]
      simp only [polyCoeff]
      omega
    | eq =>
      have hm_eq : m1 = m2 := cmpMonom_eq_iff m1 m2 hcmp
      subst hm_eq
      dsimp only
      cases hs : c1 + c2 == 0 with
      | true =>
        simp only [↓reduceIte, polyCoeff]
        rw [ih q' target]
        have hs0 : c1 + c2 = 0 := beq_iff_eq.mp hs
        cases m1 == target <;> simp <;> omega
      | false =>
        have hite : (false = true) ↔ False := by decide
        simp only [hite, ↓reduceIte, polyCoeff]
        rw [ih q' target]
        cases m1 == target <;> simp <;> omega

theorem polyCoeff_mergePoly :
    ∀ (p q : Poly) (target : Monom),
      polyCoeff (mergePoly p q) target = polyCoeff p target + polyCoeff q target
  | [], q, target => by simp [mergePoly, polyCoeff]
  | (m1, c1) :: p', q, target =>
      polyCoeff_mergePolyAux m1 c1 p' (mergePoly p') (polyCoeff_mergePoly p') q target

theorem polyCoeff_add (p q : Poly) (target : Monom) :
    polyCoeff (polyAdd p q) target = polyCoeff p target + polyCoeff q target :=
  polyCoeff_mergePoly p q target

theorem polyCoeff_filterMap_scale (c : Int) :
    ∀ (p : Poly) (target : Monom),
      polyCoeff (p.filterMap (fun (m, k) =>
        let ck := c * k
        if ck == 0 then none else some (m, ck))) target = c * polyCoeff p target
  | [], _ => by simp [polyCoeff]
  | (m, k) :: rest, target => by
    simp only [List.filterMap, polyCoeff]
    cases hck : c * k == 0 with
    | true =>
      simp only [↓reduceIte]
      rw [polyCoeff_filterMap_scale c rest target, Int.mul_add]
      have h0 : c * k = 0 := beq_iff_eq.mp hck
      cases m == target with
      | true => simp [h0]
      | false => simp
    | false =>
      have hite : (false = true) ↔ False := by decide
      simp only [hite, ↓reduceIte, polyCoeff]
      rw [polyCoeff_filterMap_scale c rest target, Int.mul_add]
      cases m == target <;> simp

theorem polyCoeff_scale (c : Int) (p : Poly) (target : Monom) :
    polyCoeff (polyScale c p) target = c * polyCoeff p target := by
  unfold polyScale
  cases hc : c == 0 with
  | true =>
    have hc0 : c = 0 := beq_iff_eq.mp hc
    subst hc0
    simp [polyCoeff]
  | false =>
    have hite : (false = true) ↔ False := by decide
    simp only [hite, ↓reduceIte]
    exact polyCoeff_filterMap_scale c p target

theorem polyCoeff_linComb :
    ∀ (N : Nat) (c : Fin N → Int) (b : Fin N → Poly) (target : Monom),
      polyCoeff (polyLinComb N c b) target = finSum N (fun j => c j * polyCoeff (b j) target)
  | 0, _, _, _ => rfl
  | N + 1, c, b, target => by
    simp only [polyLinComb]
    cases hc0 : c ⟨0, Nat.zero_lt_succ N⟩ == 0 with
    | true =>
      simp only [↓reduceIte, polyCoeff_linComb N, finSum_succ]
      have hz : c ⟨0, Nat.zero_lt_succ N⟩ = 0 := beq_iff_eq.mp hc0
      rw [hz, Int.zero_mul, Int.zero_add]
    | false =>
      have hite : (false = true) ↔ False := by decide
      simp only [hite, ↓reduceIte, polyCoeff_add, polyCoeff_scale, polyCoeff_linComb N, finSum_succ]

theorem finSum_delta :
    ∀ {N : Nat} (c : Fin N → Int) (k : Fin N),
      finSum N (fun j => c j * (if j = k then 1 else 0)) = c k
  | 0, _, k => Fin.elim0 k
  | N + 1, c, ⟨0, _⟩ => by
    rw [finSum_succ]
    simp only [↓reduceIte, Int.mul_one]
    have htail : ∀ i : Fin N,
        c ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩ *
          (if (⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩ : Fin (N + 1)) =
            ⟨0, Nat.zero_lt_succ N⟩ then 1 else 0) = 0 := by
      intro i
      have hne : (⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩ : Fin (N + 1)) ≠ ⟨0, Nat.zero_lt_succ N⟩ := by
        intro heq; have hv := congrArg Fin.val heq; dsimp at hv; omega
      simp [hne]
    rw [finSum_congr htail, finSum_zero, Int.add_zero]
  | N + 1, c, ⟨k + 1, hk⟩ => by
    rw [finSum_succ]
    have h0ne : (⟨0, Nat.zero_lt_succ N⟩ : Fin (N + 1)) ≠ ⟨k + 1, hk⟩ := by
      intro heq; have hv := congrArg Fin.val heq; dsimp at hv; omega
    simp only [h0ne, ↓reduceIte, Int.mul_zero, Int.zero_add]
    have htail : ∀ i : Fin N,
        c ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩ *
          (if (⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩ : Fin (N + 1)) = ⟨k + 1, hk⟩ then 1 else 0) =
        c ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩ *
          (if i = ⟨k, Nat.lt_of_succ_lt_succ hk⟩ then 1 else 0) := by
      intro i
      by_cases hik : i.val = k
      · have h1 : (⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩ : Fin (N + 1)) = ⟨k + 1, hk⟩ :=
          Fin.ext (congrArg (· + 1) hik)
        have h2 : i = ⟨k, Nat.lt_of_succ_lt_succ hk⟩ := Fin.ext hik
        simp [h1, h2]
      · have h1 : (⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩ : Fin (N + 1)) ≠ ⟨k + 1, hk⟩ := by
          intro heq; have hv := congrArg Fin.val heq; dsimp at hv; omega
        have h2 : i ≠ ⟨k, Nat.lt_of_succ_lt_succ hk⟩ := fun heq => hik (congrArg Fin.val heq)
        simp [h1, h2]
    rw [finSum_congr htail]
    exact finSum_delta (fun i => c ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩)
      ⟨k, Nat.lt_of_succ_lt_succ hk⟩

/-- Predicate asserting that `M` is a valid polynomial basis transition matrix from `srcBasis`
    to the multisymmetric monomial basis `{mPoly n r (parts j)}`. -/
def IsBasisTransition {N : Nat} (n r : Nat) (parts : Fin N → VecPart)
    (srcBasis : Fin N → Poly) (M : Mat N) : Prop :=
  (∀ j k : Fin N,
    polyCoeff (mPoly n r (parts j)) (repMonom n r (parts k)) = if j = k then 1 else 0) ∧
  (∀ i : Fin N,
    srcBasis i = polyLinComb N (fun j => M i j) (fun j => mPoly n r (parts j)))

/-- Uniqueness theorem: because `{m_Λ}` is dual to representative-monomial extraction,
    any matrix satisfying `IsBasisTransition` is uniquely determined! -/
theorem basisTransition_unique {N : Nat} {n r : Nat} {parts : Fin N → VecPart}
    {srcBasis : Fin N → Poly} {M1 M2 : Mat N}
    (h1 : IsBasisTransition n r parts srcBasis M1)
    (h2 : IsBasisTransition n r parts srcBasis M2) :
    M1 = M2 := by
  funext i k
  have heq_poly : polyLinComb N (fun j => M1 i j) (fun j => mPoly n r (parts j)) =
      polyLinComb N (fun j => M2 i j) (fun j => mPoly n r (parts j)) := by
    rw [← h1.2 i, ← h2.2 i]
  have heq_coeff := congrArg (fun p => polyCoeff p (repMonom n r (parts k))) heq_poly
  dsimp only at heq_coeff
  rw [polyCoeff_linComb, polyCoeff_linComb] at heq_coeff
  have h1_eval : finSum N (fun j => M1 i j *
      polyCoeff (mPoly n r (parts j)) (repMonom n r (parts k))) = M1 i k := by
    rw [finSum_congr (fun j => by rw [h1.1 j k])]
    exact finSum_delta (fun j => M1 i j) k
  have h2_eval : finSum N (fun j => M2 i j *
      polyCoeff (mPoly n r (parts j)) (repMonom n r (parts k))) = M2 i k := by
    rw [finSum_congr (fun j => by rw [h1.1 j k])]
    exact finSum_delta (fun j => M2 i j) k
  rw [h1_eval, h2_eval] at heq_coeff
  exact heq_coeff

/-- Boolean checker for `IsBasisTransition`, caching `mPoly` evaluations in a list once. -/
def checkBasisTransitionBool (N n r : Nat) (parts : List VecPart)
    (srcFn : VecPart → Poly) (rows : List (List Int)) : Bool :=
  let mList := (List.range N).map (fun j => mPoly n r (parts.getD j []))
  let dualOk := (List.range N).all (fun j =>
    (List.range N).all (fun k =>
      polyCoeff (mList.getD j []) (repMonom n r (parts.getD k [])) ==
        (if j == k then 1 else 0)))
  let expOk := (List.range N).all (fun i =>
    srcFn (parts.getD i []) ==
      polyLinComb N (fun j => (rows.getD i []).getD j.val 0) (fun j => mList.getD j.val []))
  dualOk && expOk

theorem checkBasisTransitionBool_sound (N n r : Nat) (parts : List VecPart)
    (srcFn : VecPart → Poly) (rows : List (List Int))
    (h : checkBasisTransitionBool N n r parts srcFn rows = true) :
    IsBasisTransition n r (fun j : Fin N => parts.getD j.val [])
      (fun i : Fin N => srcFn (parts.getD i.val [])) (matOfRows N rows) := by
  unfold checkBasisTransitionBool at h
  dsimp only at h
  rcases (Bool.and_eq_true _ _).mp h with ⟨hd, hexp⟩
  let mList := (List.range N).map (fun j => mPoly n r (parts.getD j []))
  have hm_eq : ∀ j : Fin N, mList.getD j.val [] = mPoly n r (parts.getD j.val []) := by
    intro j
    exact getD_map_range N (fun k => mPoly n r (parts.getD k [])) [] j.val j.isLt
  rw [list_all_range_iff] at hd hexp
  constructor
  · intro j k
    have hjk := hd j.val j.isLt
    rw [list_all_range_iff] at hjk
    have hk := beq_iff_eq.mp (hjk k.val k.isLt)
    change polyCoeff (mList.getD j.val []) (repMonom n r (parts.getD k.val [])) = _ at hk
    rw [hm_eq j] at hk
    rw [hk]
    by_cases heq : j = k
    · subst heq; simp
    · have hval : (j.val == k.val) = false := by
        cases hb : j.val == k.val with
        | false => rfl
        | true => exfalso; exact heq (Fin.ext (beq_iff_eq.mp hb))
      simp [heq, hval]
  · intro i
    dsimp only
    have hi := beq_iff_eq.mp (hexp i.val i.isLt)
    change srcFn (parts.getD i.val []) =
      polyLinComb N (fun j => (rows.getD i.val []).getD j.val 0)
        (fun j => mList.getD j.val []) at hi
    rw [hi]
    have hfn : (fun j : Fin N => mList.getD j.val []) =
        (fun j : Fin N => mPoly n r (parts.getD j.val [])) := by
      funext j; exact hm_eq j
    rw [hfn]
    rfl

/-! ### Multilinear Set-Partition Formula (`d = (1, ..., 1)`) -/

/-- Two `0-1` blocks `u, v ∈ {0,1}^r` share at most one element (`∑_k u_k v_k ≤ 1`). -/
def blocksAtMostOneOverlap (u v : Vec) : Bool :=
  let dot := (List.zipWith (· * ·) u v).foldl (· + ·) 0
  dot ≤ 1

/-- In multilinear degree `d = (1, ..., 1)`, `[m_σ] e_π = 1` iff `π ∧ σ = 0̂` in `Π_r`,
    i.e., every block of `π` intersects every block of `σ` in at most `1` element; else `0`. -/
def multilinearElemEntry (π σ : VecPart) : Int :=
  if π.all (fun u => σ.all (fun v => blocksAtMostOneOverlap u v)) then 1 else 0

/-! ### General All-`r` Power-Sum Automorphism Formula and Divisibility by `3` -/

def factNat : Nat → Nat
  | 0 => 1
  | k + 1 => (k + 1) * factNat k

def countVec (u : Vec) (Λ : VecPart) : Nat :=
  (Λ.filter (· == u)).length

/-- Automorphism order `aut(Λ) = ∏_{u ∈ dedup(Λ)} m_Λ(u)!` (diagonal entry of `M(p, m)` and `M(m̃, m)`). -/
def autOrder (Λ : VecPart) : Int :=
  Int.ofNat ((dedupList Λ).foldr (fun u acc => factNat (countVec u Λ) * acc) 1)

/-- For every `r ≥ 1`, the canonical strictly positive multidegree `d'_r = (3, 1, ..., 1) ∈ ℕ^r`
    contains the vector partition `starPart r = [e_0, e_0, e_0, e_1, ..., e_{r-1}]`. -/
def starPart (r : Nat) : VecPart :=
  [unitVec r 0, unitVec r 0, unitVec r 0] ++
    (List.range (r - 1)).map (fun j => unitVec r (j + 1))

theorem unitVec_succ_ne_unitVec_zero (r j : Nat) (hr : 1 ≤ r) :
    (unitVec r (j + 1) == unitVec r 0) = false := by
  cases r with
  | zero => omega
  | succ m =>
    unfold unitVec
    rw [List.range_succ_eq_map]
    simp

theorem filter_unitVec_zero_tail (r : Nat) (hr : 1 ≤ r) :
    ∀ (xs : List Nat),
      ((xs.map (fun j => unitVec r (j + 1))).filter (· == unitVec r 0)) = []
  | [] => rfl
  | j :: js => by
    simp only [List.map, List.filter, unitVec_succ_ne_unitVec_zero r j hr,
      filter_unitVec_zero_tail r hr js]

theorem countVec_unitVec0_starPart (r : Nat) (hr : 1 ≤ r) :
    countVec (unitVec r 0) (starPart r) = 3 := by
  unfold countVec starPart
  rw [List.filter_append, filter_unitVec_zero_tail r hr (List.range (r - 1))]
  simp

theorem mem_dedupList_of_head {α : Type} [BEq α] [LawfulBEq α] (x : α) (xs : List α) :
    x ∈ dedupList (x :: xs) := by
  simp only [dedupList]
  cases h : (dedupList xs).any (· == x) with
  | true =>
    obtain ⟨y, hy_mem, hy_eq⟩ := List.any_eq_true.mp h
    have hyx : y = x := beq_iff_eq.mp hy_eq
    subst hyx
    exact hy_mem
  | false =>
    have hite : (false = true) ↔ False := by decide
    simp [hite]

theorem foldr_dvd_of_mem (Λ : VecPart) (w : Vec) :
    ∀ (us : List Vec), w ∈ us →
      factNat (countVec w Λ) ∣ us.foldr (fun u acc => factNat (countVec u Λ) * acc) 1
  | [], hmem => by cases hmem
  | u :: us, hmem => by
    simp only [List.foldr]
    cases List.mem_cons.mp hmem with
    | inl hwu =>
      subst hwu
      exact ⟨us.foldr (fun v acc => factNat (countVec v Λ) * acc) 1, rfl⟩
    | inr htail =>
      obtain ⟨q, hq⟩ := foldr_dvd_of_mem Λ w us htail
      refine ⟨factNat (countVec u Λ) * q, ?_⟩
      rw [hq, ← Nat.mul_assoc, Nat.mul_comm _ (factNat (countVec w Λ)), Nat.mul_assoc]

theorem six_dvd_autOrder_starPart (r : Nat) (hr : 1 ≤ r) :
    (6 : Int) ∣ autOrder (starPart r) := by
  have hmem : unitVec r 0 ∈ dedupList (starPart r) := by
    unfold starPart
    exact mem_dedupList_of_head (unitVec r 0) _
  have hdvd_nat := foldr_dvd_of_mem (starPart r) (unitVec r 0) (dedupList (starPart r)) hmem
  rw [countVec_unitVec0_starPart r hr] at hdvd_nat
  have hf3 : factNat 3 = 6 := rfl
  rw [hf3] at hdvd_nat
  obtain ⟨q, hq⟩ := hdvd_nat
  refine ⟨Int.ofNat q, ?_⟩
  unfold autOrder
  rw [hq]
  rfl

/-- **Universal All-`r` Power-Sum / Augmented-Monomial Theorem:**
    For EVERY number of variable sets `r ≥ 1`, on any multidegree whose vector-partition basis
    `parts : Fin N → VecPart` contains `starPart r` (in particular the strictly positive multidegree
    `d'_r = (3, 1, ..., 1) ∈ ℕ^r`), any lower-triangular transition matrix `M : Mat N` with diagonal
    entries `M i i = autOrder (parts i)` (which holds identically for `M(p, m)` and `M(m̃, m)`)
    has `6 ∣ det M`, hence `3 ∣ det M`, and therefore `det M` is NEVER a power of two (even up to sign)! -/
theorem powerSum_all_r_not_power_of_two (r : Nat) (hr : 1 ≤ r)
    {N : Nat} (parts : Fin N → VecPart) (M : Mat N)
    (hlo : IsLowerTri M)
    (hdiag : ∀ i : Fin N, M i i = autOrder (parts i))
    (hstar : ∃ k : Fin N, parts k = starPart r) :
    (3 : Int) ∣ det M ∧ ¬IsPowerOfTwoUpToSign (det M) := by
  obtain ⟨k, hk⟩ := hstar
  have hdet : det M = diagProd M := det_lowerTri M hlo
  have hkk_dvd : M k k ∣ det M := by
    rw [hdet]
    exact diag_dvd_diagProd M k
  rw [hdiag k, hk] at hkk_dvd
  have h6 : (6 : Int) ∣ autOrder (starPart r) := six_dvd_autOrder_starPart r hr
  obtain ⟨a, ha⟩ := h6
  obtain ⟨b, hb⟩ := hkk_dvd
  have h3 : (3 : Int) ∣ det M := by
    refine ⟨2 * (a * b), ?_⟩
    rw [hb, ha]
    have h63 : (6 : Int) = 3 * 2 := rfl
    rw [h63, Int.mul_assoc 3 2 a, Int.mul_assoc 3 (2 * a) b, Int.mul_assoc 2 a b]
  exact ⟨h3, not_isPowerOfTwoUpToSign_of_dvd_three h3⟩

end Conjecture00000000441
