/-
  Conjecture 00000007617 — Metric-Free Poincaré/Hodge Duality, Grassmann–Cayley
  Regressive Product ("Meet"), Sign-Correction Laws, and General-Dimension
  Basis-Blade Transverse Intersection & Non-Transverse Vanishing
  Core Lean 4.19.0 only (zero external dependencies).
-/

import Conjecture00000007617.Exterior

namespace Conjecture00000007617
namespace Cl

section PoincareAndMeet
variable {R : Type} [CRing R]

/-- Right Poincaré / basis-complement star `⋆ : Λ^k(R^n) → Λ^{n-k}(R^n)`
    characterized by `[x ∧ ⋆y]_{ω_n} = ⟨x, y⟩_euclid`. -/
def pStar : (n : Nat) → Cl R n → Cl R n
  | 0, a => a
  | n + 1, x => (invol n (pStar n x.2), pStar n x.1)

/-- Exact two-sided inverse `⋆⁻¹ : Λ^{n-k}(R^n) → Λ^k(R^n)` of `pStar`. -/
def pStarInv : (n : Nat) → Cl R n → Cl R n
  | 0, a => a
  | n + 1, u => (pStarInv n u.2, pStarInv n (invol n u.1))

/-- Canonical Grassmann–Cayley / Plücker regressive product ("meet")
    `A ∨ B := ⋆⁻¹(⋆A ∧ ⋆B) ∈ Λ^{r+s-n}(R^n)` with respect to volume form `ω_n`. -/
def regressive (n : Nat) (A B : Cl R n) : Cl R n :=
  pStarInv n (wedge n (pStar n A) (pStar n B))

/-- Forward-star regressive product convention `A ∨_fwd B := ⋆(⋆A ∧ ⋆B)`. -/
def regressiveFwd (n : Nat) (A B : Cl R n) : Cl R n :=
  pStar n (wedge n (pStar n A) (pStar n B))

/-- Reversed-dual regressive product convention `A ∨_rev B := ⋆⁻¹(⋆B ∧ ⋆A)`. -/
def regressiveRev (n : Nat) (A B : Cl R n) : Cl R n :=
  pStarInv n (wedge n (pStar n B) (pStar n A))

/-- Bracket-rescaled regressive product `A ∨_{c} B := c • (A ∨ B)` corresponding
    to rescaling the dual volume bracket `[·]_ω ↦ c [·]_ω`. -/
def regressiveScaled (n : Nat) (c : R) (A B : Cl R n) : Cl R n :=
  smul n c (regressive n A B)

/-! ### Exact Bijectivity and Linearity of `pStar` and `pStarInv` -/

theorem pStar_zero (n : Nat) : pStar n (zero (R := R) n) = zero n := by
  induction n with
  | zero => rfl
  | succ n ih => exact Prod.ext (by simp [pStar, zero, ih, invol_zero]) (by simp [pStar, zero, ih])

theorem pStar_add (n : Nat) (x y : Cl R n) :
    pStar n (add n x y) = add n (pStar n x) (pStar n y) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      exact Prod.ext (by simp [pStar, add, ih, invol_add]) (by simp [pStar, add, ih])

theorem pStar_neg (n : Nat) (x : Cl R n) :
    pStar n (neg n x) = neg n (pStar n x) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      exact Prod.ext (by simp [pStar, neg, ih, invol_neg]) (by simp [pStar, neg, ih])

theorem pStar_smul (n : Nat) (r : R) (x : Cl R n) :
    pStar n (smul n r x) = smul n r (pStar n x) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      exact Prod.ext (by simp [pStar, smul, ih, invol_smul]) (by simp [pStar, smul, ih])

theorem pStar_signCl (n m : Nat) (x : Cl R n) :
    pStar n (signCl n m x) = signCl n m (pStar n x) := by
  induction m with
  | zero => rfl
  | succ m ih => simp [signCl, pStar_neg, ih]

theorem pStarInv_zero (n : Nat) : pStarInv n (zero (R := R) n) = zero n := by
  induction n with
  | zero => rfl
  | succ n ih => exact Prod.ext (by simp [pStarInv, zero, ih]) (by simp [pStarInv, zero, invol_zero, ih])

theorem pStarInv_add (n : Nat) (x y : Cl R n) :
    pStarInv n (add n x y) = add n (pStarInv n x) (pStarInv n y) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      exact Prod.ext (by simp [pStarInv, add, ih]) (by simp [pStarInv, add, invol_add, ih])

theorem pStarInv_neg (n : Nat) (x : Cl R n) :
    pStarInv n (neg n x) = neg n (pStarInv n x) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      exact Prod.ext (by simp [pStarInv, neg, ih]) (by simp [pStarInv, neg, invol_neg, ih])

theorem pStarInv_smul (n : Nat) (r : R) (x : Cl R n) :
    pStarInv n (smul n r x) = smul n r (pStarInv n x) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      exact Prod.ext (by simp [pStarInv, smul, ih]) (by simp [pStarInv, smul, invol_smul, ih])

theorem pStarInv_signCl (n m : Nat) (x : Cl R n) :
    pStarInv n (signCl n m x) = signCl n m (pStarInv n x) := by
  induction m with
  | zero => rfl
  | succ m ih => simp [signCl, pStarInv_neg, ih]

theorem pStarInv_pStar (n : Nat) (x : Cl R n) :
    pStarInv n (pStar n x) = x := by
  induction n with
  | zero => rfl
  | succ n ih =>
      exact Prod.ext (ih x.1) (by simp [pStar, pStarInv, invol_invol, ih])

theorem pStar_pStarInv (n : Nat) (u : Cl R n) :
    pStar n (pStarInv n u) = u := by
  induction n with
  | zero => rfl
  | succ n ih =>
      exact Prod.ext (by simp [pStar, pStarInv, ih, invol_invol]) (ih u.2)

/-! ### Non-Tautological Exterior Hodge Star Equation `[x ∧ ⋆y]_{ω_n} = ⟨x, y⟩` -/

theorem topCoeff_add (n : Nat) (x y : Cl R n) :
    topCoeff n (add n x y) = CRing.add (topCoeff n x) (topCoeff n y) := by
  induction n with
  | zero => rfl
  | succ n ih => exact ih x.2 y.2

theorem topCoeff_wedge_pStar (n : Nat) (x y : Cl R n) :
    topCoeff n (wedge n x (pStar n y)) = inner (euclidMetric (R := R) n) x y := by
  induction n with
  | zero => rfl
  | succ n ih =>
      have hi : initMetric (euclidMetric (R := R) (n + 1)) = euclidMetric (R := R) n := rfl
      have hl : lastMetric (euclidMetric (R := R) (n + 1)) = CRing.one := rfl
      rw [wedge_eq]
      change topCoeff n (add n (wedge n x.1 (pStar n y.1))
        (wedge n x.2 (invol n (invol n (pStar n y.2))))) =
        CRing.add (inner (initMetric (euclidMetric (n + 1))) x.1 y.1)
          (CRing.mul (lastMetric (euclidMetric (n + 1)))
            (inner (initMetric (euclidMetric (n + 1))) x.2 y.2))
      rw [invol_invol, topCoeff_add, ih x.1 y.1, ih x.2 y.2, hi, hl, CRing.one_mul]

/-! ### Bilinearity of `regressive` -/

theorem regressive_zero_left (n : Nat) (B : Cl R n) :
    regressive n (zero n) B = zero n := by
  unfold regressive wedge
  rw [pStar_zero, zero_mul, pStarInv_zero]

theorem regressive_zero_right (n : Nat) (A : Cl R n) :
    regressive n A (zero n) = zero n := by
  unfold regressive wedge
  rw [pStar_zero, mul_zero, pStarInv_zero]

theorem regressive_add_left (n : Nat) (A1 A2 B : Cl R n) :
    regressive n (add n A1 A2) B = add n (regressive n A1 B) (regressive n A2 B) := by
  unfold regressive wedge
  rw [pStar_add, right_distrib, pStarInv_add]

theorem regressive_add_right (n : Nat) (A B1 B2 : Cl R n) :
    regressive n A (add n B1 B2) = add n (regressive n A B1) (regressive n A B2) := by
  unfold regressive wedge
  rw [pStar_add, left_distrib, pStarInv_add]

theorem regressive_smul_left (n : Nat) (r : R) (A B : Cl R n) :
    regressive n (smul n r A) B = smul n r (regressive n A B) := by
  unfold regressive wedge
  rw [pStar_smul, smul_mul, pStarInv_smul]

theorem regressive_smul_right (n : Nat) (r : R) (A B : Cl R n) :
    regressive n A (smul n r B) = smul n r (regressive n A B) := by
  unfold regressive wedge
  rw [pStar_smul, mul_smul, pStarInv_smul]

/-! ### Grading of `pStar`, `pStarInv`, and `regressive`, plus Sign-Correction Theorems -/

theorem pStar_hasGrade {n k : Nat} {x : Cl R n}
    (hk : k ≤ n) (hx : HasGrade n k x) :
    HasGrade n (n - k) (pStar n x) := by
  induction n generalizing k with
  | zero =>
      have hk0 : k = 0 := by omega
      subst hk0
      trivial
  | succ n ih =>
      cases k with
      | zero =>
          simp only [Nat.sub_zero]
          refine ⟨?_, ?_⟩
          · change HasGrade n (n + 1) (invol n (pStar n x.2))
            rw [hx.2, pStar_zero, invol_zero]
            exact hasGrade_zero n (n + 1)
          · change HasGrade n n (pStar n x.1)
            have hp1 : HasGrade n (n - 0) (pStar n x.1) := ih (Nat.zero_le n) hx.1
            simp only [Nat.sub_zero] at hp1
            exact hp1
      | succ j =>
          have hj : j ≤ n := by omega
          by_cases hjn : j = n
          · subst hjn
            simp only [Nat.sub_self]
            have hx1 : x.1 = zero j := hasGrade_gt_eq_zero (Nat.lt_succ_self j) hx.1
            refine ⟨?_, ?_⟩
            · change HasGrade j 0 (invol j (pStar j x.2))
              have hp2 : HasGrade j (j - j) (pStar j x.2) := ih (Nat.le_refl j) hx.2
              simp only [Nat.sub_self] at hp2
              rw [invol_on_grade hp2]
              exact hp2
            · change pStar j x.1 = zero j
              rw [hx1, pStar_zero]
          · have hjlt : j < n := by omega
            have hsub : (n + 1) - (j + 1) = (n - 1 - j) + 1 := by omega
            rw [hsub]
            refine ⟨?_, ?_⟩
            · change HasGrade n ((n - 1 - j) + 1) (invol n (pStar n x.2))
              have hp2 : HasGrade n (n - j) (pStar n x.2) := ih hj hx.2
              have he1 : n - j = (n - 1 - j) + 1 := by omega
              rw [he1] at hp2
              rw [invol_on_grade hp2]
              exact hasGrade_signCl _ hp2
            · change HasGrade n (n - 1 - j) (pStar n x.1)
              have hp1 : HasGrade n (n - (j + 1)) (pStar n x.1) := ih hjlt hx.1
              have he2 : n - (j + 1) = n - 1 - j := by omega
              rw [he2] at hp1
              exact hp1

theorem pStarInv_hasGrade {n d : Nat} {u : Cl R n}
    (hd : d ≤ n) (hu : HasGrade n (n - d) u) :
    HasGrade n d (pStarInv n u) := by
  induction n generalizing d with
  | zero =>
      have hd0 : d = 0 := by omega
      subst hd0
      trivial
  | succ n ih =>
      cases d with
      | zero =>
          simp only [Nat.sub_zero] at hu
          have hu1 : u.1 = zero n := hasGrade_gt_eq_zero (Nat.lt_succ_self n) hu.1
          refine ⟨?_, ?_⟩
          · change HasGrade n 0 (pStarInv n u.2)
            have hn0 : n - 0 = n := Nat.sub_zero n
            exact ih (Nat.zero_le n) (by rw [hn0]; exact hu.2)
          · change pStarInv n (invol n u.1) = zero n
            rw [hu1, invol_zero, pStarInv_zero]
      | succ j =>
          have hj : j ≤ n := by omega
          by_cases hjn : j = n
          · subst hjn
            simp only [Nat.sub_self] at hu
            refine ⟨?_, ?_⟩
            · change HasGrade j (j + 1) (pStarInv j u.2)
              rw [hu.2, pStarInv_zero]
              exact hasGrade_zero j (j + 1)
            · change HasGrade j j (pStarInv j (invol j u.1))
              have hi1 : HasGrade j (j - j) (invol j u.1) := by
                simp only [Nat.sub_self]
                rw [invol_on_grade hu.1]
                exact hu.1
              exact ih (Nat.le_refl j) hi1
          · have hjlt : j < n := by omega
            have hsub : (n + 1) - (j + 1) = (n - 1 - j) + 1 := by omega
            rw [hsub] at hu
            refine ⟨?_, ?_⟩
            · change HasGrade n (j + 1) (pStarInv n u.2)
              have he2 : n - (j + 1) = n - 1 - j := by omega
              exact ih hjlt (by rw [he2]; exact hu.2)
            · change HasGrade n j (pStarInv n (invol n u.1))
              have hi1 : HasGrade n (n - j) (invol n u.1) := by
                have he1 : n - j = (n - 1 - j) + 1 := by omega
                rw [he1, invol_on_grade hu.1]
                exact hasGrade_signCl _ hu.1
              exact ih hj hi1

theorem pStar_pStar_grade {n k : Nat} {x : Cl R n}
    (hk : k ≤ n) (hx : HasGrade n k x) :
    pStar n (pStar n x) = signCl n (k * (n - k)) x := by
  induction n generalizing k with
  | zero =>
      have hk0 : k = 0 := by omega
      subst hk0
      rfl
  | succ n ih =>
      rw [signCl_pair]
      cases k with
      | zero =>
          simp only [Nat.zero_mul, signCl]
          refine Prod.ext ?_ ?_
          · change invol n (pStar n (pStar n x.1)) = x.1
            rw [ih (Nat.zero_le n) hx.1]
            simp only [Nat.zero_mul, signCl]
            rw [invol_on_grade hx.1]
            rfl
          · change pStar n (invol n (pStar n x.2)) = x.2
            rw [hx.2, pStar_zero, invol_zero, pStar_zero]
      | succ j =>
          have hj : j ≤ n := by omega
          by_cases hjn : j = n
          · subst hjn
            simp only [Nat.sub_self, Nat.mul_zero, signCl]
            have hx1 : x.1 = zero j := hasGrade_gt_eq_zero (Nat.lt_succ_self j) hx.1
            refine Prod.ext ?_ ?_
            · change invol j (pStar j (pStar j x.1)) = x.1
              rw [hx1, pStar_zero, pStar_zero, invol_zero]
            · change pStar j (invol j (pStar j x.2)) = x.2
              have hp2 : HasGrade j 0 (pStar j x.2) := by
                have h := pStar_hasGrade (Nat.le_refl j) hx.2
                simp only [Nat.sub_self] at h
                exact h
              rw [invol_on_grade hp2]
              simp only [signCl]
              rw [ih (Nat.le_refl j) hx.2]
              simp only [Nat.sub_self, Nat.mul_zero, signCl]
          · have hjlt : j < n := by omega
            refine Prod.ext ?_ ?_
            · change invol n (pStar n (pStar n x.1)) = signCl n ((j + 1) * (n + 1 - (j + 1))) x.1
              rw [ih hjlt hx.1, invol_signCl, invol_on_grade hx.1, ← signCl_add_exp]
              have hexp : (j + 1) * (n - (j + 1)) + (j + 1) = (j + 1) * (n + 1 - (j + 1)) := by
                have h1 : n + 1 - (j + 1) = (n - (j + 1)) + 1 := by omega
                rw [h1, Nat.mul_add, Nat.mul_one]
              rw [hexp]
            · change pStar n (invol n (pStar n x.2)) = signCl n ((j + 1) * (n + 1 - (j + 1))) x.2
              have hp2 : HasGrade n (n - j) (pStar n x.2) := pStar_hasGrade hj hx.2
              rw [invol_on_grade hp2, pStar_signCl, ih hj hx.2, ← signCl_add_exp]
              have hexp : (n - j) + j * (n - j) = (j + 1) * (n + 1 - (j + 1)) := by
                have h1 : n + 1 - (j + 1) = n - j := by omega
                rw [h1, Nat.add_mul, Nat.one_mul, Nat.add_comm]
              rw [hexp]

theorem regressive_hasGrade {n r s : Nat} {A B : Cl R n}
    (hr : r ≤ n) (hs : s ≤ n) (hrs : n ≤ r + s)
    (hA : HasGrade n r A) (hB : HasGrade n s B) :
    HasGrade n (r + s - n) (regressive n A B) := by
  unfold regressive
  have hpA : HasGrade n (n - r) (pStar n A) := pStar_hasGrade hr hA
  have hpB : HasGrade n (n - s) (pStar n B) := pStar_hasGrade hs hB
  have hW : HasGrade n ((n - r) + (n - s)) (wedge n (pStar n A) (pStar n B)) :=
    wedge_hasGrade hpA hpB
  have hd_le : r + s - n ≤ n := by omega
  have heq : (n - r) + (n - s) = n - (r + s - n) := by omega
  rw [heq] at hW
  exact pStarInv_hasGrade hd_le hW

/-- Exact grade-dependent sign correction between forward-star and inverse-star meet:
    `A ∨_fwd B = (-1)^{d(n - d)} (A ∨ B)` where `d = r + s - n`. -/
theorem regressiveFwd_eq_sign_regressive {n r s : Nat} {A B : Cl R n}
    (hr : r ≤ n) (hs : s ≤ n) (hrs : n ≤ r + s)
    (hA : HasGrade n r A) (hB : HasGrade n s B) :
    regressiveFwd n A B = signCl n ((r + s - n) * (n - (r + s - n))) (regressive n A B) := by
  have hM : HasGrade n (r + s - n) (regressive n A B) :=
    regressive_hasGrade hr hs hrs hA hB
  have hd_le : r + s - n ≤ n := by omega
  unfold regressiveFwd
  have hW : wedge n (pStar n A) (pStar n B) = pStar n (regressive n A B) :=
    Eq.symm (pStar_pStarInv n _)
  rw [hW]
  exact pStar_pStar_grade hd_le hM

/-- Exact grade-dependent Koszul sign between reversed-dual / swapped meet and canonical meet:
    `B ∨ A = A ∨_rev B = (-1)^{(n - r)(n - s)} (A ∨ B)`. -/
theorem regressive_comm_sign {n r s : Nat} {A B : Cl R n}
    (hr : r ≤ n) (hs : s ≤ n)
    (hA : HasGrade n r A) (hB : HasGrade n s B) :
    regressive n B A = signCl n ((n - r) * (n - s)) (regressive n A B) := by
  unfold regressive
  have hpA : HasGrade n (n - r) (pStar n A) := pStar_hasGrade hr hA
  have hpB : HasGrade n (n - s) (pStar n B) := pStar_hasGrade hs hB
  rw [wedge_grade_comm hpA hpB, pStarInv_signCl]

theorem regressiveRev_eq_sign_regressive {n r s : Nat} {A B : Cl R n}
    (hr : r ≤ n) (hs : s ≤ n)
    (hA : HasGrade n r A) (hB : HasGrade n s B) :
    regressiveRev n A B = signCl n ((n - r) * (n - s)) (regressive n A B) :=
  regressive_comm_sign hr hs hA hB

/-! ### General-Dimension Basis-Blade Transverse Intersection & Non-Transverse Vanishing -/

def initMask {n : Nat} (I : Fin (n + 1) → Bool) : Fin n → Bool :=
  fun i => I ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩

def lastMask {n : Nat} (I : Fin (n + 1) → Bool) : Bool :=
  I ⟨n, Nat.lt_succ_self n⟩

def complMask {n : Nat} (I : Fin n → Bool) : Fin n → Bool :=
  fun i => !(I i)

def orMask {n : Nat} (I J : Fin n → Bool) : Fin n → Bool :=
  fun i => I i || J i

def andMask {n : Nat} (I J : Fin n → Bool) : Fin n → Bool :=
  fun i => I i && J i

def maskCard : {n : Nat} → (Fin n → Bool) → Nat
  | 0, _ => 0
  | _ + 1, I => maskCard (initMask I) + (if lastMask I then 1 else 0)

def disjointMasks : {n : Nat} → (Fin n → Bool) → (Fin n → Bool) → Bool
  | 0, _, _ => true
  | _ + 1, I, J => disjointMasks (initMask I) (initMask J) && !(lastMask I && lastMask J)

def coversAll : {n : Nat} → (Fin n → Bool) → (Fin n → Bool) → Bool
  | 0, _, _ => true
  | _ + 1, I, J => coversAll (initMask I) (initMask J) && (lastMask I || lastMask J)

def starSignExp : {n : Nat} → (Fin n → Bool) → Nat
  | 0, _ => 0
  | n + 1, I =>
      if lastMask I then
        starSignExp (initMask I) + (n - maskCard (initMask I))
      else
        starSignExp (initMask I)

def wedgeSignExp : {n : Nat} → (Fin n → Bool) → (Fin n → Bool) → Nat
  | 0, _, _ => 0
  | _ + 1, I, J =>
      wedgeSignExp (initMask I) (initMask J) +
        (if lastMask I && !(lastMask J) then maskCard (initMask J) else 0)

def meetSignExp {n : Nat} (I J : Fin n → Bool) : Nat :=
  let cI := complMask I
  let cJ := complMask J
  starSignExp I + starSignExp J + wedgeSignExp cI cJ + starSignExp (andMask I J)

theorem maskCard_le : {n : Nat} → (I : Fin n → Bool) → maskCard I ≤ n
  | 0, _ => Nat.le_refl 0
  | n + 1, I => by
      have ih := maskCard_le (initMask I)
      unfold maskCard
      cases lastMask I <;> simp <;> omega

theorem basisBlade_hasGrade : {n : Nat} → (I : Fin n → Bool) →
    HasGrade n (maskCard I) (basisBlade (R := R) n I)
  | 0, _ => trivial
  | n + 1, I => by
      have ih := basisBlade_hasGrade (initMask I)
      have hbb : basisBlade (R := R) (n + 1) I =
          (if lastMask I then (zero n, basisBlade n (initMask I))
           else (basisBlade n (initMask I), zero n)) := rfl
      have hmc : maskCard I = maskCard (initMask I) + (if lastMask I then 1 else 0) := rfl
      rw [hbb, hmc]
      cases lastMask I
      · change HasGrade (n + 1) (maskCard (initMask I)) (basisBlade n (initMask I), zero n)
        cases hc : maskCard (initMask I) with
        | zero =>
            rw [hc] at ih
            exact ⟨ih, rfl⟩
        | succ k =>
            rw [hc] at ih
            exact ⟨ih, hasGrade_zero n k⟩
      · exact ⟨hasGrade_zero n _, ih⟩

theorem maskCard_compl : {n : Nat} → (I : Fin n → Bool) →
    maskCard (complMask I) = n - maskCard I
  | 0, _ => rfl
  | n + 1, I => by
      have ih := maskCard_compl (initMask I)
      have hle := maskCard_le (initMask I)
      have hinit : initMask (complMask I) = complMask (initMask I) := rfl
      have hlast : lastMask (complMask I) = !(lastMask I) := rfl
      unfold maskCard
      rw [hinit, hlast, ih]
      cases lastMask I <;> simp <;> omega

theorem pStar_basisBlade : {n : Nat} → (I : Fin n → Bool) →
    pStar n (basisBlade (R := R) n I) =
      signCl n (starSignExp I) (basisBlade n (complMask I))
  | 0, _ => rfl
  | n + 1, I => by
      have ih := pStar_basisBlade (initMask I)
      have hbb : basisBlade (R := R) (n + 1) I =
          (if lastMask I then (zero n, basisBlade n (initMask I))
           else (basisBlade n (initMask I), zero n)) := rfl
      have hbbc : basisBlade (R := R) (n + 1) (complMask I) =
          (if lastMask (complMask I) then (zero n, basisBlade n (complMask (initMask I)))
           else (basisBlade n (complMask (initMask I)), zero n)) := rfl
      have hsse : starSignExp I =
          (if lastMask I then starSignExp (initMask I) + (n - maskCard (initMask I))
           else starSignExp (initMask I)) := rfl
      have hl_c : lastMask (complMask I) = !(lastMask I) := rfl
      rw [hbb, hbbc, hsse, hl_c]
      cases lastMask I
      · change pStar (n + 1) (basisBlade n (initMask I), zero n) =
          signCl (n + 1) (starSignExp (initMask I)) (zero n, basisBlade n (complMask (initMask I)))
        unfold pStar
        rw [signCl_pair]
        refine Prod.ext ?_ ?_
        · change invol n (pStar n (zero n)) = signCl n (starSignExp (initMask I)) (zero n)
          rw [pStar_zero, invol_zero, signCl_zero_elem]
        · exact ih
      · change pStar (n + 1) (zero n, basisBlade n (initMask I)) =
          signCl (n + 1) (starSignExp (initMask I) + (n - maskCard (initMask I)))
            (basisBlade n (complMask (initMask I)), zero n)
        unfold pStar
        rw [signCl_pair]
        refine Prod.ext ?_ ?_
        · change invol n (pStar n (basisBlade n (initMask I))) =
            signCl n (starSignExp (initMask I) + (n - maskCard (initMask I)))
              (basisBlade n (complMask (initMask I)))
          rw [ih, invol_signCl]
          have hg := basisBlade_hasGrade (R := R) (complMask (initMask I))
          rw [invol_on_grade hg, ← signCl_add_exp, maskCard_compl, Nat.add_comm]
        · change pStar n (zero n) = signCl n _ (zero n)
          rw [pStar_zero, signCl_zero_elem]

theorem pStarInv_basisBlade {n : Nat} (K : Fin n → Bool) :
    pStarInv n (basisBlade (R := R) n K) =
      signCl n (starSignExp (complMask K)) (basisBlade n (complMask K)) := by
  have hcc : complMask (complMask K) = K := by
    funext i
    unfold complMask
    cases K i <;> rfl
  have hp := pStar_basisBlade (R := R) (complMask K)
  rw [hcc] at hp
  have h1 : pStarInv n (pStar n (basisBlade (R := R) n (complMask K))) =
      pStarInv n (signCl n (starSignExp (complMask K)) (basisBlade n K)) :=
    congrArg (pStarInv n) hp
  rw [pStarInv_pStar, pStarInv_signCl] at h1
  have h2 := congrArg (signCl n (starSignExp (complMask K))) h1
  rw [signCl_self_cancel] at h2
  exact Eq.symm h2

theorem wedge_basisBlade : {n : Nat} → (A B : Fin n → Bool) →
    wedge n (basisBlade (R := R) n A) (basisBlade n B) =
      if disjointMasks A B then
        signCl n (wedgeSignExp A B) (basisBlade n (orMask A B))
      else
        zero n
  | 0, _, _ => by
      simp [disjointMasks, wedgeSignExp, signCl, basisBlade, wedge, mul, CRing.one_mul]
  | n + 1, A, B => by
      have ih := wedge_basisBlade (initMask A) (initMask B)
      have hbbA : basisBlade (R := R) (n + 1) A =
          (if lastMask A then (zero n, basisBlade n (initMask A))
           else (basisBlade n (initMask A), zero n)) := rfl
      have hbbB : basisBlade (R := R) (n + 1) B =
          (if lastMask B then (zero n, basisBlade n (initMask B))
           else (basisBlade n (initMask B), zero n)) := rfl
      have hbbOR : basisBlade (R := R) (n + 1) (orMask A B) =
          (if lastMask A || lastMask B then (zero n, basisBlade n (orMask (initMask A) (initMask B)))
           else (basisBlade n (orMask (initMask A) (initMask B)), zero n)) := rfl
      have hdm : disjointMasks A B =
          (disjointMasks (initMask A) (initMask B) && !(lastMask A && lastMask B)) := rfl
      have hwse : wedgeSignExp A B =
          wedgeSignExp (initMask A) (initMask B) +
            (if lastMask A && !(lastMask B) then maskCard (initMask B) else 0) := rfl
      rw [hbbA, hbbB, hbbOR, hdm, hwse]
      cases lastMask A <;> cases lastMask B
      · change wedge (n + 1) (basisBlade n (initMask A), zero n) (basisBlade n (initMask B), zero n) =
          if (disjointMasks (initMask A) (initMask B) && true) = true then
            signCl (n + 1) (wedgeSignExp (initMask A) (initMask B))
              (basisBlade n (orMask (initMask A) (initMask B)), zero n)
          else zero (n + 1)
        rw [Bool.and_true, wedge_eq]
        cases hdisj : disjointMasks (initMask A) (initMask B)
        · rw [hdisj] at ih
          have ih' : wedge n (basisBlade n (initMask A)) (basisBlade n (initMask B)) = zero n := ih
          refine Prod.ext ih' ?_
          change add n (wedge n (basisBlade n (initMask A)) (zero n))
            (wedge n (zero n) (invol n (basisBlade n (initMask B)))) = zero n
          unfold wedge; rw [mul_zero, zero_mul, add_zero]
        · rw [hdisj] at ih
          have ih' : wedge n (basisBlade n (initMask A)) (basisBlade n (initMask B)) =
              signCl n (wedgeSignExp (initMask A) (initMask B))
                (basisBlade n (orMask (initMask A) (initMask B))) := ih
          change (wedge n (basisBlade n (initMask A)) (basisBlade n (initMask B)),
              add n (wedge n (basisBlade n (initMask A)) (zero n))
                (wedge n (zero n) (invol n (basisBlade n (initMask B))))) =
            signCl (n + 1) (wedgeSignExp (initMask A) (initMask B))
              (basisBlade n (orMask (initMask A) (initMask B)), zero n)
          rw [signCl_pair]
          refine Prod.ext ih' ?_
          change add n (wedge n (basisBlade n (initMask A)) (zero n))
            (wedge n (zero n) (invol n (basisBlade n (initMask B)))) =
            signCl n (wedgeSignExp (initMask A) (initMask B)) (zero n)
          unfold wedge; rw [mul_zero, zero_mul, add_zero, signCl_zero_elem]
      · change wedge (n + 1) (basisBlade n (initMask A), zero n) (zero n, basisBlade n (initMask B)) =
          if (disjointMasks (initMask A) (initMask B) && true) = true then
            signCl (n + 1) (wedgeSignExp (initMask A) (initMask B))
              (zero n, basisBlade n (orMask (initMask A) (initMask B)))
          else zero (n + 1)
        rw [Bool.and_true, wedge_eq]
        cases hdisj : disjointMasks (initMask A) (initMask B)
        · rw [hdisj] at ih
          have ih' : wedge n (basisBlade n (initMask A)) (basisBlade n (initMask B)) = zero n := ih
          refine Prod.ext ?_ ?_
          · change wedge n (basisBlade n (initMask A)) (zero n) = zero n
            unfold wedge; rw [mul_zero]
          · change add n (wedge n (basisBlade n (initMask A)) (basisBlade n (initMask B)))
              (wedge n (zero n) (invol n (zero n))) = zero n
            rw [ih']; unfold wedge; rw [zero_mul, add_zero]
        · rw [hdisj] at ih
          have ih' : wedge n (basisBlade n (initMask A)) (basisBlade n (initMask B)) =
              signCl n (wedgeSignExp (initMask A) (initMask B))
                (basisBlade n (orMask (initMask A) (initMask B))) := ih
          change (wedge n (basisBlade n (initMask A)) (zero n),
              add n (wedge n (basisBlade n (initMask A)) (basisBlade n (initMask B)))
                (wedge n (zero n) (invol n (zero n)))) =
            signCl (n + 1) (wedgeSignExp (initMask A) (initMask B))
              (zero n, basisBlade n (orMask (initMask A) (initMask B)))
          rw [signCl_pair]
          refine Prod.ext ?_ ?_
          · change wedge n (basisBlade n (initMask A)) (zero n) =
              signCl n (wedgeSignExp (initMask A) (initMask B)) (zero n)
            unfold wedge; rw [mul_zero, signCl_zero_elem]
          · change add n (wedge n (basisBlade n (initMask A)) (basisBlade n (initMask B)))
              (wedge n (zero n) (invol n (zero n))) =
              signCl n (wedgeSignExp (initMask A) (initMask B)) (basisBlade n (orMask (initMask A) (initMask B)))
            rw [ih']; unfold wedge; rw [zero_mul, add_zero]
      · change wedge (n + 1) (zero n, basisBlade n (initMask A)) (basisBlade n (initMask B), zero n) =
          if (disjointMasks (initMask A) (initMask B) && true) = true then
            signCl (n + 1) (wedgeSignExp (initMask A) (initMask B) + maskCard (initMask B))
              (zero n, basisBlade n (orMask (initMask A) (initMask B)))
          else zero (n + 1)
        rw [Bool.and_true, wedge_eq]
        cases hdisj : disjointMasks (initMask A) (initMask B)
        · rw [hdisj] at ih
          have ih' : wedge n (basisBlade n (initMask A)) (basisBlade n (initMask B)) = zero n := ih
          refine Prod.ext ?_ ?_
          · change wedge n (zero n) (basisBlade n (initMask B)) = zero n
            unfold wedge; rw [zero_mul]
          · change add n (wedge n (zero n) (zero n))
              (wedge n (basisBlade n (initMask A)) (invol n (basisBlade n (initMask B)))) = zero n
            have hgB := basisBlade_hasGrade (R := R) (initMask B)
            rw [invol_on_grade hgB]
            unfold wedge at ih' ⊢
            rw [zero_mul, zero_add, mul_signCl, ih', signCl_zero_elem]
        · rw [hdisj] at ih
          have ih' : wedge n (basisBlade n (initMask A)) (basisBlade n (initMask B)) =
              signCl n (wedgeSignExp (initMask A) (initMask B))
                (basisBlade n (orMask (initMask A) (initMask B))) := ih
          change (wedge n (zero n) (basisBlade n (initMask B)),
              add n (wedge n (zero n) (zero n))
                (wedge n (basisBlade n (initMask A)) (invol n (basisBlade n (initMask B))))) =
            signCl (n + 1) (wedgeSignExp (initMask A) (initMask B) + maskCard (initMask B))
              (zero n, basisBlade n (orMask (initMask A) (initMask B)))
          rw [signCl_pair]
          refine Prod.ext ?_ ?_
          · change wedge n (zero n) (basisBlade n (initMask B)) = signCl n _ (zero n)
            unfold wedge; rw [zero_mul, signCl_zero_elem]
          · change add n (wedge n (zero n) (zero n))
              (wedge n (basisBlade n (initMask A)) (invol n (basisBlade n (initMask B)))) = _
            have hgB := basisBlade_hasGrade (R := R) (initMask B)
            rw [invol_on_grade hgB]
            unfold wedge at ih' ⊢
            rw [zero_mul, zero_add, mul_signCl, ih', ← signCl_add_exp, Nat.add_comm]
      · change wedge (n + 1) (zero n, basisBlade n (initMask A)) (zero n, basisBlade n (initMask B)) =
          if (disjointMasks (initMask A) (initMask B) && false) = true then _ else zero (n + 1)
        rw [Bool.and_false]
        change wedge (n + 1) (zero n, basisBlade n (initMask A)) (zero n, basisBlade n (initMask B)) = zero (n + 1)
        rw [wedge_eq]
        refine Prod.ext ?_ ?_
        · change wedge n (zero n) (zero n) = zero n
          unfold wedge; rw [zero_mul]
        · change add n (wedge n (zero n) (basisBlade n (initMask B)))
            (wedge n (basisBlade n (initMask A)) (invol n (zero n))) = zero n
          unfold wedge; rw [zero_mul, invol_zero, mul_zero, add_zero]

theorem disjoint_compl_eq_coversAll : {n : Nat} → (I J : Fin n → Bool) →
    disjointMasks (complMask I) (complMask J) = coversAll I J
  | 0, _, _ => rfl
  | n + 1, I, J => by
      have ih := disjoint_compl_eq_coversAll (initMask I) (initMask J)
      have hiI : initMask (complMask I) = complMask (initMask I) := rfl
      have hiJ : initMask (complMask J) = complMask (initMask J) := rfl
      have hlI : lastMask (complMask I) = !(lastMask I) := rfl
      have hlJ : lastMask (complMask J) = !(lastMask J) := rfl
      unfold disjointMasks coversAll
      rw [hiI, hiJ, hlI, hlJ, ih]
      cases lastMask I <;> cases lastMask J <;> rfl

theorem compl_or_compl_eq_and {n : Nat} (I J : Fin n → Bool) :
    complMask (orMask (complMask I) (complMask J)) = andMask I J := by
  funext i
  change (!((!(I i)) || (!(J i)))) = (I i && J i)
  cases I i <;> cases J i <;> rfl

/-- Master General-Dimension Basis-Blade Regressive Product Formula:
    * When `coversAll I J = true` (`U_I + U_J = R^n`, transverse coordinate subspaces),
      `e_I ∨ e_J = (-1)^{meetSignExp I J} e_{I ∩ J}` represents `U_I ∩ U_J`.
    * When `coversAll I J = false` (`U_I + U_J ⊊ R^n`, non-transverse subspaces),
      `e_I ∨ e_J = 0` vanishes identically! -/
theorem regressive_basisBlade {n : Nat} (I J : Fin n → Bool) :
    regressive n (basisBlade (R := R) n I) (basisBlade n J) =
      if coversAll I J then
        signCl n (meetSignExp I J) (basisBlade n (andMask I J))
      else
        zero n := by
  unfold regressive
  rw [pStar_basisBlade, pStar_basisBlade]
  unfold wedge
  rw [signCl_mul, mul_signCl]
  change pStarInv n (signCl n (starSignExp I) (signCl n (starSignExp J)
      (wedge n (basisBlade n (complMask I)) (basisBlade n (complMask J))))) = _
  rw [wedge_basisBlade, disjoint_compl_eq_coversAll]
  cases coversAll I J
  · change pStarInv n (signCl n (starSignExp I) (signCl n (starSignExp J) (zero n))) = zero n
    rw [signCl_zero_elem, signCl_zero_elem, pStarInv_zero]
  · change pStarInv n (signCl n (starSignExp I) (signCl n (starSignExp J)
        (signCl n (wedgeSignExp (complMask I) (complMask J))
          (basisBlade n (orMask (complMask I) (complMask J)))))) =
      signCl n (meetSignExp I J) (basisBlade n (andMask I J))
    rw [pStarInv_signCl, pStarInv_signCl, pStarInv_signCl, pStarInv_basisBlade, compl_or_compl_eq_and,
        ← signCl_add_exp, ← signCl_add_exp, ← signCl_add_exp]
    rfl

theorem signCl_ne_zero {n : Nat} (m : Nat) {x : Cl R n} (hx : x ≠ zero n) :
    signCl n m x ≠ zero n := by
  intro hz
  have h1 := congrArg (signCl n m) hz
  rw [signCl_self_cancel, signCl_zero_elem] at h1
  exact hx h1

end PoincareAndMeet

theorem basisBlade_ne_zero {R : Type} [IDomain R] : {n : Nat} → (I : Fin n → Bool) →
    basisBlade (R := R) n I ≠ zero n
  | 0, _ => IDomain.one_ne_zero
  | n + 1, I => by
      have ih := basisBlade_ne_zero (R := R) (initMask I)
      have hbb : basisBlade (R := R) (n + 1) I =
          (if lastMask I then (zero n, basisBlade n (initMask I))
           else (basisBlade n (initMask I), zero n)) := rfl
      rw [hbb]
      cases lastMask I
      · intro h
        exact ih (congrArg Prod.fst h)
      · intro h
        exact ih (congrArg Prod.snd h)

end Cl
end Conjecture00000007617
