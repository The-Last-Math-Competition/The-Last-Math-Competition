/-
  Conjecture 00000007616 — Authentic Exterior Hodge Star & Universal Chevalley–Hodge Realization
  Core Lean 4.19.0 only (zero external dependencies).

  Defines the Hodge star operator purely by its classical exterior-algebraic specification:
    star : Λ^k(R^n) → Λ^{n-k}(R^n),   α ∧ star(β) = ⟨α, β⟩_q ν   (∀ α, β ∈ Λ^k)
  without building Clifford multiplication into the definition.
  Then proves constructively by induction on dimension `n`:
    1. Poincaré duality nondegeneracy of the exterior wedge pairing `Λ^k × Λ^{n-k} → Λ^n`;
    2. Universal Chevalley–Hodge theorem: `x ↦ rev(x) · ν` satisfies `IsHodgeStar q ν`
       for ALL dimensions `n`, ALL commutative rings `R`, ALL metrics `q` (including
       indefinite, non-unimodular, and degenerate), and ALL `ν = c · ω_n`;
    3. Uniqueness of the Hodge star operator across all of `Cl R n` from `IsHodgeStar`;
    4. Exact norm identity `rev(c · ω_n) · (c · ω_n) = (c² ∏ q_i) · 1` and
       `⟨c · ω_n, c · ω_n⟩_q = c² ∏ q_i`.
-/

import Conjecture00000007616.Clifford

namespace Conjecture00000007616
namespace Cl

section HodgeTheory
variable {R : Type} [CRing R]

/-- Classical exterior-duality specification of the Hodge star operator `⋆_ν`
    associated to quadratic form `q : Fin n → R` and top-degree element `ν ∈ Λ^n`:
    1. `star` is additive on `Λ(R^n)`;
    2. `star` maps `Λ^k` into `Λ^{n-k}` for every `0 ≤ k ≤ n`;
    3. `α ∧ star(β) = ⟨α, β⟩_q · ν` for all `α, β ∈ Λ^k`. -/
def IsHodgeStar {n : Nat} (q : Fin n → R) (nu : Cl R n) (star : Cl R n → Cl R n) : Prop :=
  (∀ x y, star (add n x y) = add n (star x) (star y)) ∧
  (∀ k, k ≤ n → ∀ β, HasGrade n k β → HasGrade n (n - k) (star β)) ∧
  (∀ k, k ≤ n → ∀ α β, HasGrade n k α → HasGrade n k β →
    wedge n α (star β) = smul n (inner q α β) nu)

/-- Dual left-wedge convention `(⋆_ν^L β) ∧ α = ⟨β, α⟩_q · ν`. -/
def IsLeftHodgeStar {n : Nat} (q : Fin n → R) (nu : Cl R n) (star : Cl R n → Cl R n) : Prop :=
  (∀ x y, star (add n x y) = add n (star x) (star y)) ∧
  (∀ k, k ≤ n → ∀ β, HasGrade n k β → HasGrade n (n - k) (star β)) ∧
  (∀ k, k ≤ n → ∀ α β, HasGrade n k α → HasGrade n k β →
    wedge n (star β) α = smul n (inner q β α) nu)

/-- Reverted right Clifford realization `x ↦ x̃ · ν`. -/
def cliffordRightStar {n : Nat} (q : Fin n → R) (nu : Cl R n) (x : Cl R n) : Cl R n :=
  mul q (rev n x) nu

/-- Reverted left Clifford realization `x ↦ ν · x̃`. -/
def cliffordLeftStar {n : Nat} (q : Fin n → R) (nu : Cl R n) (x : Cl R n) : Cl R n :=
  mul q nu (rev n x)

/-! ### Inner Product Helper Lemmas -/

theorem inner_zero_left : ∀ {n : Nat} (q : Fin n → R) (y : Cl R n),
    inner q (zero n) y = CRing.zero
  | 0, _, y => CRing.zero_mul y
  | _ + 1, q, (c, d) => by
      show CRing.add (inner (initMetric q) (zero _) c)
        (CRing.mul (lastMetric q) (inner (initMetric q) (zero _) d)) = CRing.zero
      rw [inner_zero_left, inner_zero_left, CRing.mul_zero, CRing.zero_add]

theorem inner_zero_right : ∀ {n : Nat} (q : Fin n → R) (x : Cl R n),
    inner q x (zero n) = CRing.zero
  | 0, _, x => CRing.mul_zero x
  | _ + 1, q, (a, b) => by
      show CRing.add (inner (initMetric q) a (zero _))
        (CRing.mul (lastMetric q) (inner (initMetric q) b (zero _))) = CRing.zero
      rw [inner_zero_right, inner_zero_right, CRing.mul_zero, CRing.zero_add]

theorem inner_neg_neg : ∀ {n : Nat} (q : Fin n → R) (x y : Cl R n),
    inner q (neg n x) (neg n y) = inner q x y
  | 0, _, x, y => CRing.neg_mul_neg x y
  | _ + 1, q, (a, b), (c, d) => by
      show CRing.add (inner (initMetric q) (neg _ a) (neg _ c))
        (CRing.mul (lastMetric q) (inner (initMetric q) (neg _ b) (neg _ d))) =
        CRing.add (inner (initMetric q) a c)
          (CRing.mul (lastMetric q) (inner (initMetric q) b d))
      rw [inner_neg_neg, inner_neg_neg]

theorem inner_invol : ∀ {n : Nat} (q : Fin n → R) (x y : Cl R n),
    inner q (invol n x) (invol n y) = inner q x y
  | 0, _, _, _ => rfl
  | _ + 1, q, (a, b), (c, d) => by
      show CRing.add (inner (initMetric q) (invol _ a) (invol _ c))
        (CRing.mul (lastMetric q) (inner (initMetric q) (neg _ (invol _ b)) (neg _ (invol _ d)))) =
        CRing.add (inner (initMetric q) a c)
          (CRing.mul (lastMetric q) (inner (initMetric q) b d))
      rw [inner_neg_neg, inner_invol, inner_invol]

theorem inner_smul_left : ∀ {n : Nat} (q : Fin n → R) (r : R) (x y : Cl R n),
    inner q (smul n r x) y = CRing.mul r (inner q x y)
  | 0, _, r, x, y => CRing.mul_assoc r x y
  | _ + 1, q, r, (a, b), (c, d) => by
      show CRing.add (inner (initMetric q) (smul _ r a) c)
        (CRing.mul (lastMetric q) (inner (initMetric q) (smul _ r b) d)) =
        CRing.mul r (CRing.add (inner (initMetric q) a c)
          (CRing.mul (lastMetric q) (inner (initMetric q) b d)))
      rw [inner_smul_left, inner_smul_left, CRing.left_distrib,
          ← CRing.mul_assoc, ← CRing.mul_assoc, CRing.mul_comm (lastMetric q) r]

theorem inner_smul_right : ∀ {n : Nat} (q : Fin n → R) (r : R) (x y : Cl R n),
    inner q x (smul n r y) = CRing.mul r (inner q x y)
  | 0, _, r, x, y => by
      show CRing.mul x (CRing.mul r y) = CRing.mul r (CRing.mul x y)
      rw [← CRing.mul_assoc, CRing.mul_comm x r, CRing.mul_assoc]
  | _ + 1, q, r, (a, b), (c, d) => by
      show CRing.add (inner (initMetric q) a (smul _ r c))
        (CRing.mul (lastMetric q) (inner (initMetric q) b (smul _ r d))) =
        CRing.mul r (CRing.add (inner (initMetric q) a c)
          (CRing.mul (lastMetric q) (inner (initMetric q) b d)))
      rw [inner_smul_right, inner_smul_right, CRing.left_distrib,
          ← CRing.mul_assoc, ← CRing.mul_assoc, CRing.mul_comm (lastMetric q) r]

/-! ### Step 1: Poincaré Duality Nondegeneracy of Exterior Wedge -/

/-- Exact Poincaré duality on `Λ(R^n)`: if `δ ∈ Λ^{n-k}` satisfies `α ∧ δ = 0` for all
    `α ∈ Λ^k`, then `δ = 0` (valid over any commutative ring `R`, independent of `q`). -/
theorem poincare_wedge_nondeg :
    ∀ (n k : Nat), k ≤ n → ∀ (δ : Cl R n),
      HasGrade n (n - k) δ →
      (∀ α : Cl R n, HasGrade n k α → wedge n α δ = zero n) →
      δ = zero n
  | 0, 0, _, δ, _, hwedge => by
      have h1 := hwedge (one 0) trivial
      show δ = CRing.zero
      have hmul : CRing.mul CRing.one δ = CRing.zero := h1
      rw [CRing.one_mul] at hmul
      exact hmul
  | 0, _ + 1, hle, _, _, _ => absurd hle (Nat.not_succ_le_zero _)
  | n + 1, 0, _, (x, y), hδ, hwedge => by
      have hsub : (n + 1) - 0 = n + 1 := rfl
      rw [hsub] at hδ
      rcases hδ with ⟨hx_gt, hy_n⟩
      have hx0 : x = zero n := hasGrade_gt_zero n (n + 1) x (Nat.lt_succ_self n) hx_gt
      have h1 := hwedge (one (n + 1)) (hasGrade_one (n + 1))
      have hone : wedge (n + 1) (one (n + 1)) (x, y) = (x, y) := one_mul (zeroMetric (n + 1)) (x, y)
      rw [hone] at h1
      have _ := hy_n
      have _ := hx0
      exact h1
  | n + 1, m + 1, hle, (x, y), hδ, hwedge => by
      have hm_le : m ≤ n := Nat.le_of_succ_le_succ hle
      have hsub : (n + 1) - (m + 1) = n - m := Nat.succ_sub_succ n m
      rw [hsub] at hδ
      by_cases hmn : m = n
      · subst hmn
        rw [Nat.sub_self m] at hδ
        rcases hδ with ⟨hx0_grade, hy0⟩
        -- Test with `α = (0, α')` where `α' ∈ Λ^n(R^n)`
        have hhat0 : invol m x = zero m := by
          apply poincare_wedge_nondeg m m (Nat.le_refl m) (invol m x)
          · rw [Nat.sub_self m]
            exact hasGrade_invol m 0 hx0_grade
          · intro α' hα'
            have hstep := hwedge (zero m, α') ⟨hasGrade_zero m (m + 1), hα'⟩
            rw [wedge_step, zero_wedge, zero_wedge, zero_add] at hstep
            exact congrArg Prod.snd hstep
        have hx0 : x = zero m := by
          rw [← invol_invol m x, hhat0, invol_zero]
        exact Prod.ext hx0 hy0
      · have hm_lt : m < n := Nat.lt_of_le_of_ne hm_le hmn
        have hnm_eq : n - m = (n - (m + 1)) + 1 := by omega
        rw [hnm_eq] at hδ
        rcases hδ with ⟨hx_grade, hy_grade⟩
        -- First deduce `y = 0` by testing `α = (a, 0)` with `a ∈ Λ^{m+1}(R^n)`
        have hy0 : y = zero n := by
          apply poincare_wedge_nondeg n (m + 1) hm_lt y hy_grade
          intro a ha
          have hstep := hwedge (a, zero n) ⟨ha, hasGrade_zero n m⟩
          rw [wedge_step, zero_wedge, add_zero] at hstep
          exact congrArg Prod.snd hstep
        -- Next deduce `invol x = 0` (hence `x = 0`) by testing `α = (0, b)` with `b ∈ Λ^m(R^n)`
        have hhat0 : invol n x = zero n := by
          apply poincare_wedge_nondeg n m hm_le (invol n x)
          · rw [hnm_eq]
            exact hasGrade_invol n ((n - (m + 1)) + 1) hx_grade
          · intro b hb
            have hstep := hwedge (zero n, b) ⟨hasGrade_zero n (m + 1), hb⟩
            rw [wedge_step, zero_wedge, zero_wedge, zero_add] at hstep
            exact congrArg Prod.snd hstep
        have hx0 : x = zero n := by
          rw [← invol_invol n x, hhat0, invol_zero]
        exact Prod.ext hx0 hy0

/-! ### Step 2: Universal Chevalley–Hodge Realization Theorem -/

theorem cliffordRightStar_add {n : Nat} (q : Fin n → R) (nu : Cl R n) (x y : Cl R n) :
    cliffordRightStar q nu (add n x y) = add n (cliffordRightStar q nu x) (cliffordRightStar q nu y) := by
  unfold cliffordRightStar
  rw [rev_add, right_distrib]

theorem cliffordRightStar_zero {n : Nat} (q : Fin n → R) (nu : Cl R n) :
    cliffordRightStar q nu (zero n) = zero n := by
  unfold cliffordRightStar
  rw [rev_zero, zero_mul]

theorem cliffordRightStar_omega_step {n : Nat} (q : Fin (n + 1) → R) (c d : Cl R n) :
    cliffordRightStar q (omega (n + 1)) (c, d) =
      ( smul n (lastMetric q) (invol n (cliffordRightStar (initMetric q) (omega n) d)),
        cliffordRightStar (initMetric q) (omega n) c ) := by
  let q' := initMetric q
  let qn := lastMetric q
  show ( add n (mul q' (rev n c) (zero n))
               (smul n qn (mul q' (invol n (rev n d)) (invol n (omega n)))),
         add n (mul q' (rev n c) (omega n))
               (mul q' (invol n (rev n d)) (invol n (zero n))) ) =
       ( smul n qn (invol n (mul q' (rev n d) (omega n))),
         mul q' (rev n c) (omega n) )
  apply Prod.ext
  · dsimp only
    rw [mul_zero, zero_add, ← invol_mul q' (rev n d) (omega n)]
  · dsimp only
    rw [invol_zero, mul_zero, add_zero]

theorem cliffordRightStar_omega_hasGrade :
    ∀ {n : Nat} (q : Fin n → R) (k : Nat), k ≤ n → ∀ (β : Cl R n),
      HasGrade n k β → HasGrade n (n - k) (cliffordRightStar q (omega n) β)
  | 0, _, 0, _, _, _ => trivial
  | 0, _, _ + 1, hle, _, _ => absurd hle (Nat.not_succ_le_zero _)
  | n + 1, q, 0, _, (c, d), ⟨hc, hd⟩ => by
      rw [cliffordRightStar_omega_step, hd, cliffordRightStar_zero, invol_zero, smul_zero]
      exact ⟨hasGrade_zero n (n + 1),
             cliffordRightStar_omega_hasGrade (initMetric q) 0 (Nat.zero_le n) c hc⟩
  | n + 1, q, m + 1, hle, (c, d), ⟨hc, hd⟩ => by
      have hm_le : m ≤ n := Nat.le_of_succ_le_succ hle
      have hsub : (n + 1) - (m + 1) = n - m := Nat.succ_sub_succ n m
      rw [hsub, cliffordRightStar_omega_step]
      by_cases hmn : m = n
      · subst hmn
        rw [Nat.sub_self m]
        have hc0 : c = zero m := hasGrade_gt_zero m (m + 1) c (Nat.lt_succ_self m) hc
        rw [hc0, cliffordRightStar_zero]
        have hd_star := cliffordRightStar_omega_hasGrade (initMetric q) m (Nat.le_refl m) d hd
        rw [Nat.sub_self m] at hd_star
        exact ⟨hasGrade_smul m 0 (lastMetric q) (hasGrade_invol m 0 hd_star), rfl⟩
      · have hm_lt : m < n := Nat.lt_of_le_of_ne hm_le hmn
        have hnm_eq : n - m = (n - (m + 1)) + 1 := by omega
        rw [hnm_eq]
        have hd_star := cliffordRightStar_omega_hasGrade (initMetric q) m hm_le d hd
        rw [hnm_eq] at hd_star
        have hc_star := cliffordRightStar_omega_hasGrade (initMetric q) (m + 1) hm_lt c hc
        exact ⟨hasGrade_smul n ((n - (m + 1)) + 1) (lastMetric q)
                (hasGrade_invol n ((n - (m + 1)) + 1) hd_star),
               hc_star⟩

theorem wedge_cliffordRightStar_omega :
    ∀ {n : Nat} (q : Fin n → R) (k : Nat), k ≤ n → ∀ (α β : Cl R n),
      HasGrade n k α → HasGrade n k β →
      wedge n α (cliffordRightStar q (omega n) β) = smul n (inner q α β) (omega n)
  | 0, _, 0, _, α, β, _, _ => by
      show CRing.mul α (CRing.mul β CRing.one) = CRing.mul (CRing.mul α β) CRing.one
      rw [CRing.mul_assoc]
  | 0, _, _ + 1, hle, _, _, _, _ => absurd hle (Nat.not_succ_le_zero _)
  | n + 1, q, 0, _, (a, b), (c, d), ⟨ha, hb⟩, ⟨hc, hd⟩ => by
      rw [cliffordRightStar_omega_step, hb, hd, cliffordRightStar_zero, invol_zero, smul_zero,
          wedge_step, wedge_zero, zero_wedge, add_zero]
      have ih := wedge_cliffordRightStar_omega (initMetric q) 0 (Nat.zero_le n) a c ha hc
      rw [ih]
      show (zero n, smul n (inner (initMetric q) a c) (omega n)) =
        ( smul n (CRing.add (inner (initMetric q) a c)
            (CRing.mul (lastMetric q) (inner (initMetric q) (zero n) (zero n)))) (zero n),
          smul n (CRing.add (inner (initMetric q) a c)
            (CRing.mul (lastMetric q) (inner (initMetric q) (zero n) (zero n)))) (omega n) )
      rw [smul_zero, inner_zero_left, CRing.mul_zero, CRing.add_zero]
  | n + 1, q, m + 1, hle, (a, b), (c, d), ⟨ha, hb⟩, ⟨hc, hd⟩ => by
      have hm_le : m ≤ n := Nat.le_of_succ_le_succ hle
      rw [cliffordRightStar_omega_step, wedge_step]
      let q' := initMetric q
      let qn := lastMetric q
      -- First component vanishes because its grade is `(m + 1) + (n - m) = n + 1 > n`
      have h1st : wedge n a (smul n qn (invol n (cliffordRightStar q' (omega n) d))) = zero n := by
        have hd_gr := cliffordRightStar_omega_hasGrade q' m hm_le d hd
        have hrhs_gr := hasGrade_smul n (n - m) qn (hasGrade_invol n (n - m) hd_gr)
        have hw_gr := hasGrade_wedge n (m + 1) (n - m) ha hrhs_gr
        have hsum : (m + 1) + (n - m) = n + 1 := by omega
        rw [hsum] at hw_gr
        exact hasGrade_gt_zero n (n + 1) _ (Nat.lt_succ_self n) hw_gr
      -- Simplify `invol (smul qn (invol z)) = smul qn z` in second component
      have hinvol_cancel :
          invol n (smul n qn (invol n (cliffordRightStar q' (omega n) d))) =
            smul n qn (cliffordRightStar q' (omega n) d) := by
        rw [invol_smul, invol_invol]
      rw [h1st, hinvol_cancel]
      have hw_smul :
          wedge n b (smul n qn (cliffordRightStar q' (omega n) d)) =
            smul n qn (wedge n b (cliffordRightStar q' (omega n) d)) :=
        mul_smul (zeroMetric n) qn b _
      rw [hw_smul]
      by_cases hmn : m = n
      · subst hmn
        have ha0 : a = zero m := hasGrade_gt_zero m (m + 1) a (Nat.lt_succ_self m) ha
        have hc0 : c = zero m := hasGrade_gt_zero m (m + 1) c (Nat.lt_succ_self m) hc
        rw [ha0, hc0, zero_wedge, zero_add]
        have ih_bd := wedge_cliffordRightStar_omega q' m (Nat.le_refl m) b d hb hd
        rw [ih_bd, smul_smul]
        show (zero m, smul m (CRing.mul qn (inner q' b d)) (omega m)) =
          ( smul m (CRing.add (inner q' (zero m) (zero m)) (CRing.mul qn (inner q' b d))) (zero m),
            smul m (CRing.add (inner q' (zero m) (zero m)) (CRing.mul qn (inner q' b d))) (omega m) )
        rw [smul_zero, inner_zero_left, CRing.zero_add]
      · have hm_lt : m < n := Nat.lt_of_le_of_ne hm_le hmn
        have ih_ac := wedge_cliffordRightStar_omega q' (m + 1) hm_lt a c ha hc
        have ih_bd := wedge_cliffordRightStar_omega q' m hm_le b d hb hd
        rw [ih_ac, ih_bd, smul_smul, ← add_smul]
        show (zero n, smul n (CRing.add (inner q' a c) (CRing.mul qn (inner q' b d))) (omega n)) =
          ( smul n (CRing.add (inner q' a c) (CRing.mul qn (inner q' b d))) (zero n),
            smul n (CRing.add (inner q' a c) (CRing.mul qn (inner q' b d))) (omega n) )
        rw [smul_zero]

/-- **Theorem (Universal Chevalley–Hodge Realization):**
    For every dimension `n`, every commutative ring `R`, every orthogonal metric `q`
    (positive-definite, indefinite, non-unimodular, or degenerate), and every top-degree
    element `ν = r · ω_n`, the reverted Clifford right product `x ↦ rev(x) · ν`
    satisfies the exterior Hodge star specification `IsHodgeStar q ν`. -/
theorem rev_mul_isHodgeStar {n : Nat} (q : Fin n → R) (r : R) :
    IsHodgeStar q (smul n r (omega n)) (cliffordRightStar q (smul n r (omega n))) := by
  refine ⟨cliffordRightStar_add q _, ?_, ?_⟩
  · intro k hk β hβ
    unfold cliffordRightStar
    rw [mul_smul]
    exact hasGrade_smul n (n - k) r (cliffordRightStar_omega_hasGrade q k hk β hβ)
  · intro k hk α β hα hβ
    have hcr : cliffordRightStar q (smul n r (omega n)) β =
        smul n r (cliffordRightStar q (omega n) β) :=
      mul_smul q r (rev n β) (omega n)
    rw [hcr, wedge_smul r α _,
        wedge_cliffordRightStar_omega q k hk α β hα hβ,
        smul_smul, smul_smul, CRing.mul_comm r (inner q α β)]

/-! ### Step 3: Uniqueness of the Hodge Star Operator -/

/-- Any two operators satisfying `IsHodgeStar q ν` agree identically on all of `Cl R n`. -/
theorem hodgeStar_unique_pair {n : Nat} (q : Fin n → R) (nu : Cl R n)
    (star₁ star₂ : Cl R n → Cl R n)
    (h₁ : IsHodgeStar q nu star₁) (h₂ : IsHodgeStar q nu star₂) :
    ∀ z : Cl R n, star₁ z = star₂ z := by
  rcases h₁ with ⟨hadd₁, hgr₁, hw₁⟩
  rcases h₂ with ⟨hadd₂, hgr₂, hw₂⟩
  apply eq_of_eq_on_grades n n star₁ star₂ hadd₁ hadd₂
  intro k hk β hβ
  rw [← sub_eq_zero]
  apply poincare_wedge_nondeg n k hk (sub n (star₁ β) (star₂ β))
  · exact hasGrade_add n (n - k) (hgr₁ k hk β hβ) (hasGrade_neg n (n - k) (hgr₂ k hk β hβ))
  · intro α hα
    unfold sub
    rw [wedge_left_distrib, wedge_neg,
        hw₁ k hk α β hα hβ, hw₂ k hk α β hα hβ, add_right_neg]

/-- **Corollary (Canonical Formula for Any Hodge Star):**
    Every operator `star` satisfying `IsHodgeStar q (r · ω_n) star` equals
    `cliffordRightStar q (r · ω_n)` (`x ↦ rev(x) · (r · ω_n)`) on all of `Cl R n`. -/
theorem hodgeStar_eq_cliffordRightStar {n : Nat} (q : Fin n → R) (r : R)
    (star : Cl R n → Cl R n)
    (hstar : IsHodgeStar q (smul n r (omega n)) star) :
    ∀ z : Cl R n, star z = cliffordRightStar q (smul n r (omega n)) z :=
  hodgeStar_unique_pair q (smul n r (omega n)) star
    (cliffordRightStar q (smul n r (omega n))) hstar (rev_mul_isHodgeStar q r)

/-! ### Step 4: Exact Reversion Norm & Exterior Norm of Volume Realizations -/

theorem inner_omega_self : ∀ {n : Nat} (q : Fin n → R),
    inner q (omega n) (omega n) = prodMetric q
  | 0, _ => CRing.one_mul CRing.one
  | _ + 1, q => by
      show CRing.add (inner (initMetric q) (zero _) (zero _))
        (CRing.mul (lastMetric q) (inner (initMetric q) (omega _) (omega _))) =
        CRing.mul (prodMetric (initMetric q)) (lastMetric q)
      rw [inner_zero_left, CRing.zero_add, inner_omega_self (initMetric q), CRing.mul_comm]

theorem inner_smul_omega_self {n : Nat} (q : Fin n → R) (r : R) :
    inner q (smul n r (omega n)) (smul n r (omega n)) =
      CRing.mul (CRing.mul r r) (prodMetric q) := by
  rw [inner_smul_left, inner_smul_right, inner_omega_self, CRing.mul_assoc]

theorem rev_omega_mul_omega : ∀ {n : Nat} (q : Fin n → R),
    mul q (rev n (omega n)) (omega n) = smul n (prodMetric q) (one n)
  | 0, _ => by
      show CRing.mul CRing.one CRing.one = CRing.mul CRing.one CRing.one
      rfl
  | n + 1, q => by
      let q' := initMetric q
      let qn := lastMetric q
      show ( add n (mul q' (rev n (zero n)) (zero n))
                   (smul n qn (mul q' (invol n (rev n (omega n))) (invol n (omega n)))),
             add n (mul q' (rev n (zero n)) (omega n))
                   (mul q' (invol n (rev n (omega n))) (invol n (zero n))) ) =
           (smul n (CRing.mul (prodMetric q') qn) (one n), smul n (CRing.mul (prodMetric q') qn) (zero n))
      apply Prod.ext
      · dsimp only
        rw [rev_zero, zero_mul, zero_add, ← invol_mul q' (rev n (omega n)) (omega n),
            rev_omega_mul_omega q', invol_smul, invol_one, smul_smul, CRing.mul_comm qn (prodMetric q')]
      · dsimp only
        rw [rev_zero, zero_mul, invol_zero, mul_zero, add_zero, smul_zero]

/-- **Exact Clifford Reversion Norm Law:**
    For any scalar `r ∈ R` and `Ω = r · ω_n`,
    `rev(Ω) · Ω = (r² · ∏_{i=0}^{n-1} q_i) · 1`. -/
theorem rev_smul_omega_mul_self {n : Nat} (q : Fin n → R) (r : R) :
    mul q (rev n (smul n r (omega n))) (smul n r (omega n)) =
      smul n (CRing.mul (CRing.mul r r) (prodMetric q)) (one n) := by
  rw [rev_smul, smul_mul, mul_smul, rev_omega_mul_omega, smul_smul, smul_smul]

end HodgeTheory

end Cl
end Conjecture00000007616
