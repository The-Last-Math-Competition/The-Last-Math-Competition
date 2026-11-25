/-
  Conjecture 00000007618 — Authentic Hodge–Poincaré Star, Grassmann–Cayley Regressive Meet,
  Contraction Dualities, and Exact Sign-Correction Laws
  Core Lean 4.19.0 only (zero external dependencies).

  Establishes constructively over any commutative ring `CRing R` and all dimensions `n`:
    1. Classical exterior Hodge star specification `IsHodgeStar`, Poincaré nondegeneracy,
       universal Chevalley–Hodge realization `rev_mul_isHodgeStar`, and uniqueness;
    2. Master arbitrary-metric double-star identity
         `⋆_{q,ω_n}(⋆_{q,ω_n} x) = (-1)^{k(n-k)} (∏ q_i) · x`
       and Plücker–Poincaré specialization `⋆(⋆x) = (-1)^{k(n-k)} · x`;
    3. Exact two-sided inverse `pStarInv` (`⋆⁻¹`) on all of `Cl R n`, canonical
       Grassmann–Cayley regressive (meet / intersection) product `vee` (`A ∨ B`),
       associativity, top-blade unit laws, grading, and left–right star invariance;
    4. Exact graded commutation sign law `B ∨ A = (-1)^{(n-r)(n-s)} (A ∨ B)`;
    5. Exact forward three-star sign-correction law
         `A ∨ B = (-1)^{k(n-k)} ⋆((⋆A) ∧ (⋆B)) = (-1)^{(r+s)(n-1)} ⋆((⋆A) ∧ (⋆B))`;
    6. Authentic Cartan and Dorst interior contractions (`cartanLeft`, `dorstLeft`)
       characterized by metric adjointness, with exact De Morgan meet sign laws;
    7. Unreverted Clifford pseudoscalar meet operator `veeUnrevertedClifford`.
-/

import Conjecture00000007618.ExteriorClifford

namespace Conjecture00000007618
namespace Cl

section ProjectiveMeetTheory
variable {R : Type} [CRing R]

/-- Classical exterior-duality specification of the Hodge star operator `⋆_{q,ν}`:
    additive, maps `Λ^k → Λ^{n-k}` for `0 ≤ k ≤ n`, and satisfies `α ∧ ⋆β = ⟨α, β⟩_q · ν`. -/
def IsHodgeStar {n : Nat} (q : Fin n → R) (nu : Cl R n) (star : Cl R n → Cl R n) : Prop :=
  (∀ x y, star (add n x y) = add n (star x) (star y)) ∧
  (∀ k, k ≤ n → ∀ β, HasGrade n k β → HasGrade n (n - k) (star β)) ∧
  (∀ k, k ≤ n → ∀ α β, HasGrade n k α → HasGrade n k β →
    wedge n α (star β) = smul n (inner q α β) nu)

/-- Reverted right Clifford realization `x ↦ x̃ ·_q ν`. -/
def cliffordRightStar {n : Nat} (q : Fin n → R) (nu : Cl R n) (x : Cl R n) : Cl R n :=
  mul q (rev n x) nu

/-- Reverted left Clifford realization `x ↦ ν ·_q x̃`. -/
def cliffordLeftStar {n : Nat} (q : Fin n → R) (nu : Cl R n) (x : Cl R n) : Cl R n :=
  mul q nu (rev n x)

/-! ### Inner Product & Discriminant Lemmas -/

theorem prodMetric_euclMetric : ∀ (n : Nat), prodMetric (euclMetric (R := R) n) = CRing.one
  | 0 => rfl
  | n + 1 => by
      show CRing.mul (prodMetric (euclMetric n)) CRing.one = CRing.one
      rw [prodMetric_euclMetric n, CRing.mul_one]

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

theorem inner_add_left : ∀ {n : Nat} (q : Fin n → R) (x y z : Cl R n),
    inner q (add n x y) z = CRing.add (inner q x z) (inner q y z)
  | 0, _, x, y, z => CRing.right_distrib x y z
  | _ + 1, q, (a1, a2), (b1, b2), (c1, c2) => by
      show CRing.add (inner (initMetric q) (add _ a1 b1) c1)
             (CRing.mul (lastMetric q) (inner (initMetric q) (add _ a2 b2) c2)) =
           CRing.add (CRing.add (inner (initMetric q) a1 c1)
                                (CRing.mul (lastMetric q) (inner (initMetric q) a2 c2)))
                     (CRing.add (inner (initMetric q) b1 c1)
                                (CRing.mul (lastMetric q) (inner (initMetric q) b2 c2)))
      rw [inner_add_left, inner_add_left, CRing.left_distrib,
          CRing.add_assoc, CRing.add_assoc,
          ← CRing.add_assoc (inner (initMetric q) b1 c1) _ _,
          CRing.add_comm (inner (initMetric q) b1 c1)
                         (CRing.mul (lastMetric q) (inner (initMetric q) a2 c2)),
          CRing.add_assoc (CRing.mul (lastMetric q) (inner (initMetric q) a2 c2)) _ _]

theorem inner_add_right : ∀ {n : Nat} (q : Fin n → R) (x y z : Cl R n),
    inner q x (add n y z) = CRing.add (inner q x y) (inner q x z)
  | 0, _, x, y, z => CRing.left_distrib x y z
  | _ + 1, q, (a1, a2), (b1, b2), (c1, c2) => by
      show CRing.add (inner (initMetric q) a1 (add _ b1 c1))
             (CRing.mul (lastMetric q) (inner (initMetric q) a2 (add _ b2 c2))) =
           CRing.add (CRing.add (inner (initMetric q) a1 b1)
                                (CRing.mul (lastMetric q) (inner (initMetric q) a2 b2)))
                     (CRing.add (inner (initMetric q) a1 c1)
                                (CRing.mul (lastMetric q) (inner (initMetric q) a2 c2)))
      rw [inner_add_right, inner_add_right, CRing.left_distrib,
          CRing.add_assoc, CRing.add_assoc,
          ← CRing.add_assoc (inner (initMetric q) a1 c1) _ _,
          CRing.add_comm (inner (initMetric q) a1 c1)
                         (CRing.mul (lastMetric q) (inner (initMetric q) a2 b2)),
          CRing.add_assoc (CRing.mul (lastMetric q) (inner (initMetric q) a2 b2)) _ _]

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

/-! ### Poincaré Duality & Universal Chevalley–Hodge Realization -/

/-- Exact Poincaré duality on `Λ(R^n)`: if `δ ∈ Λ^{n-k}` satisfies `α ∧ δ = 0` for all
    `α ∈ Λ^k`, then `δ = 0`. -/
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
  | n + 1, 0, _, (x, y), _, hwedge => by
      have h1 := hwedge (one (n + 1)) (hasGrade_one (n + 1))
      rw [one_wedge] at h1
      exact h1
  | n + 1, m + 1, hle, (x, y), hδ, hwedge => by
      have hm_le : m ≤ n := Nat.le_of_succ_le_succ hle
      have hsub : (n + 1) - (m + 1) = n - m := Nat.succ_sub_succ n m
      rw [hsub] at hδ
      by_cases hmn : m = n
      · subst hmn
        rw [Nat.sub_self m] at hδ
        rcases hδ with ⟨hx0_grade, hy0⟩
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
        have hy0 : y = zero n := by
          apply poincare_wedge_nondeg n (m + 1) hm_lt y hy_grade
          intro a ha
          have hstep := hwedge (a, zero n) ⟨ha, hasGrade_zero n m⟩
          rw [wedge_step, zero_wedge, add_zero] at hstep
          exact congrArg Prod.snd hstep
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

theorem cliffordRightStar_add {n : Nat} (q : Fin n → R) (nu : Cl R n) (x y : Cl R n) :
    cliffordRightStar q nu (add n x y) = add n (cliffordRightStar q nu x) (cliffordRightStar q nu y) := by
  unfold cliffordRightStar
  rw [rev_add, right_distrib]

theorem cliffordRightStar_smul {n : Nat} (q : Fin n → R) (nu : Cl R n) (r : R) (x : Cl R n) :
    cliffordRightStar q nu (smul n r x) = smul n r (cliffordRightStar q nu x) := by
  unfold cliffordRightStar
  rw [rev_smul, smul_mul]

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
        have hc0 : c = zero m := hasGrade_gt_zero m (m + 1) (Nat.lt_succ_self m) c hc
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
      rw [CRing.mul_one, CRing.mul_one]
  | 0, _, _ + 1, hle, _, _, _, _ => absurd hle (Nat.not_succ_le_zero _)
  | n + 1, q, 0, _, (a, b), (c, d), ⟨ha, hb⟩, ⟨hc, hd⟩ => by
      rw [cliffordRightStar_omega_step, hb, hd, cliffordRightStar_zero, invol_zero, smul_zero,
          wedge_step, wedge_zero, zero_wedge, add_zero]
      show (zero n, wedge n a (cliffordRightStar (initMetric q) (omega n) c)) =
           (smul n _ (zero n),
            smul n (CRing.add (inner (initMetric q) a c)
                              (CRing.mul (lastMetric q) (inner (initMetric q) (zero n) (zero n))))
                   (omega n))
      rw [smul_zero, inner_zero_left, CRing.mul_zero, CRing.add_zero,
          wedge_cliffordRightStar_omega (initMetric q) 0 (Nat.zero_le n) a c ha hc]
  | n + 1, q, m + 1, hle, (a, b), (c, d), ⟨ha, hb⟩, ⟨hc, hd⟩ => by
      have hm_le : m ≤ n := Nat.le_of_succ_le_succ hle
      let q' := initMetric q
      let qn := lastMetric q
      rw [cliffordRightStar_omega_step, wedge_step]
      have hfirst0 : wedge n a (smul n qn (invol n (cliffordRightStar q' (omega n) d))) = zero n := by
        have hd_star := cliffordRightStar_omega_hasGrade q' m hm_le d hd
        have h_rhs_grade : HasGrade n (n - m) (smul n qn (invol n (cliffordRightStar q' (omega n) d))) :=
          hasGrade_smul n (n - m) qn (hasGrade_invol n (n - m) hd_star)
        have hw_grade := wedge_hasGrade n (m + 1) (n - m) ha h_rhs_grade
        have hgt : n < (m + 1) + (n - m) := by omega
        exact hasGrade_gt_zero n ((m + 1) + (n - m)) hgt _ hw_grade
      have hsecond_b :
          wedge n b (invol n (smul n qn (invol n (cliffordRightStar q' (omega n) d)))) =
            smul n (CRing.mul qn (inner q' b d)) (omega n) := by
        rw [invol_smul, invol_invol, wedge_smul,
            wedge_cliffordRightStar_omega q' m hm_le b d hb hd, smul_smul]
      have hsecond_a :
          wedge n a (cliffordRightStar q' (omega n) c) = smul n (inner q' a c) (omega n) := by
        by_cases hmn : m = n
        · subst hmn
          have ha0 : a = zero m := hasGrade_gt_zero m (m + 1) (Nat.lt_succ_self m) a ha
          rw [ha0, zero_wedge, inner_zero_left, zero_smul]
        · have hm_lt : m < n := Nat.lt_of_le_of_ne hm_le hmn
          exact wedge_cliffordRightStar_omega q' (m + 1) hm_lt a c ha hc
      apply Prod.ext
      · show wedge n a (smul n qn (invol n (cliffordRightStar q' (omega n) d))) =
             smul n _ (zero n)
        rw [hfirst0, smul_zero]
      · show add n (wedge n a (cliffordRightStar q' (omega n) c))
                   (wedge n b (invol n (smul n qn (invol n (cliffordRightStar q' (omega n) d))))) =
             smul n (CRing.add (inner q' a c) (CRing.mul qn (inner q' b d))) (omega n)
        rw [hsecond_a, hsecond_b, add_smul]

/-- Universal Chevalley–Hodge Theorem: `x ↦ x̃ ·_q ω_n` satisfies `IsHodgeStar q ω_n`
    across all dimensions `n`, all commutative rings `R`, and all metrics `q`. -/
theorem rev_mul_isHodgeStar {n : Nat} (q : Fin n → R) :
    IsHodgeStar q (omega n) (cliffordRightStar q (omega n)) :=
  ⟨cliffordRightStar_add q (omega n),
   cliffordRightStar_omega_hasGrade q,
   wedge_cliffordRightStar_omega q⟩

/-- Uniqueness of the exterior Hodge star on every homogeneous grade `k ≤ n`. -/
theorem hodgeStar_unique_on_grade {n : Nat} (q : Fin n → R) (nu : Cl R n)
    (star1 star2 : Cl R n → Cl R n)
    (h1 : IsHodgeStar q nu star1) (h2 : IsHodgeStar q nu star2)
    {k : Nat} (hk : k ≤ n) {β : Cl R n} (hβ : HasGrade n k β) :
    star1 β = star2 β := by
  rcases h1 with ⟨_, hgrade1, hwedge1⟩
  rcases h2 with ⟨_, hgrade2, hwedge2⟩
  apply (sub_eq_zero (n := n)).mp
  apply poincare_wedge_nondeg n k hk (sub n (star1 β) (star2 β))
  · exact hasGrade_add n (n - k) (hgrade1 k hk β hβ) (hasGrade_neg n (n - k) (hgrade2 k hk β hβ))
  · intro α hα
    unfold sub
    rw [wedge_add_right, ← neg_one_smul n (star2 β), wedge_smul, neg_one_smul,
        hwedge1 k hk α β hα hβ, hwedge2 k hk α β hα hβ, add_right_neg]

/-! ### Master Arbitrary-Metric Double-Star Sign Theorem -/

/-- Master Double-Star Sign Law for Arbitrary Orthogonal Metrics `q : Fin n → R`:
    For every `0 ≤ k ≤ n` and `x ∈ Λ^k(R^n)`,
      `⋆_{q,ω_n}(⋆_{q,ω_n}(x)) = (-1)^{k(n-k)} · (∏_{i=0}^{n-1} q_i) · x`. -/
theorem cliffordRightStar_double :
    ∀ {n : Nat} (q : Fin n → R) (k : Nat), k ≤ n → ∀ (x : Cl R n),
      HasGrade n k x →
      cliffordRightStar q (omega n) (cliffordRightStar q (omega n) x) =
        smul n (CRing.mul (CRing.ringParitySign (k * (n - k))) (prodMetric q)) x
  | 0, _, 0, _, x, _ => by
      have h0 : (0 * (0 - 0)) % 2 = 0 := rfl
      rw [CRing.ringParitySign_even h0]
      show CRing.mul (CRing.mul x CRing.one) CRing.one = CRing.mul (CRing.mul CRing.one CRing.one) x
      rw [CRing.mul_one, CRing.mul_one, CRing.one_mul, CRing.one_mul]
  | 0, _, _ + 1, hle, _, _ => absurd hle (Nat.not_succ_le_zero _)
  | n + 1, q, 0, _, (c, d), ⟨hc, hd⟩ => by
      let q' := initMetric q
      let qn := lastMetric q
      have h0 : (0 * ((n + 1) - 0)) % 2 = 0 := by simp
      have h0' : (0 * (n - 0)) % 2 = 0 := by simp
      rw [CRing.ringParitySign_even h0, CRing.one_mul, hd]
      have hstep1 := cliffordRightStar_omega_step q c (zero n)
      rw [cliffordRightStar_zero, invol_zero, smul_zero] at hstep1
      rw [hstep1, cliffordRightStar_omega_step, cliffordRightStar_zero]
      apply Prod.ext
      · show smul n qn (invol n (cliffordRightStar q' (omega n) (cliffordRightStar q' (omega n) c))) =
             smul n (CRing.mul (prodMetric q') qn) c
        rw [cliffordRightStar_double q' 0 (Nat.zero_le n) c hc,
            CRing.ringParitySign_even h0', CRing.one_mul,
            invol_smul, invol_on_grade n 0 hc, CRing.ringParitySign_even rfl, one_smul,
            smul_smul, CRing.mul_comm qn (prodMetric q')]
      · exact (smul_zero n _).symm
  | n + 1, q, m + 1, hle, (c, d), ⟨hc, hd⟩ => by
      have hm_le : m ≤ n := Nat.le_of_succ_le_succ hle
      have hsub : (n + 1) - (m + 1) = n - m := Nat.succ_sub_succ n m
      let q' := initMetric q
      let qn := lastMetric q
      have hstep1 := cliffordRightStar_omega_step q c d
      rw [hsub, hstep1, cliffordRightStar_omega_step]
      apply Prod.ext
      · show smul n qn (invol n (cliffordRightStar q' (omega n) (cliffordRightStar q' (omega n) c))) =
             smul n (CRing.mul (CRing.ringParitySign ((m + 1) * (n - m))) (CRing.mul (prodMetric q') qn)) c
        by_cases hmn : m = n
        · subst hmn
          have hc0 : c = zero m := hasGrade_gt_zero m (m + 1) (Nat.lt_succ_self m) c hc
          rw [hc0, cliffordRightStar_zero, cliffordRightStar_zero, invol_zero, smul_zero, smul_zero]
        · have hm_lt : m < n := Nat.lt_of_le_of_ne hm_le hmn
          rw [cliffordRightStar_double q' (m + 1) hm_lt c hc, invol_smul,
              invol_on_grade n (m + 1) hc, smul_smul, smul_smul]
          have hexp : (m + 1) * (n - (m + 1)) + (m + 1) = (m + 1) * (n - m) := by
            have hnm : n - m = (n - (m + 1)) + 1 := by omega
            rw [hnm, Nat.mul_succ]
          have hscalar :
              CRing.mul (CRing.mul qn (CRing.mul (CRing.ringParitySign ((m + 1) * (n - (m + 1))))
                                                 (prodMetric q')))
                        (CRing.ringParitySign (m + 1)) =
                CRing.mul (CRing.ringParitySign ((m + 1) * (n - m))) (CRing.mul (prodMetric q') qn) := by
            rw [CRing.mul_assoc qn _ _,
                CRing.mul_assoc (CRing.ringParitySign ((m + 1) * (n - (m + 1)))) (prodMetric q') _,
                CRing.mul_comm (prodMetric q') (CRing.ringParitySign (m + 1)),
                ← CRing.mul_assoc (CRing.ringParitySign ((m + 1) * (n - (m + 1)))) _ _,
                ← CRing.ringParitySign_add, hexp,
                ← CRing.mul_assoc qn _ _, CRing.mul_comm qn _, CRing.mul_assoc,
                CRing.mul_comm qn (prodMetric q')]
          rw [hscalar]
      · show cliffordRightStar q' (omega n)
               (smul n qn (invol n (cliffordRightStar q' (omega n) d))) =
             smul n (CRing.mul (CRing.ringParitySign ((m + 1) * (n - m))) (CRing.mul (prodMetric q') qn)) d
        have hd_star := cliffordRightStar_omega_hasGrade q' m hm_le d hd
        rw [cliffordRightStar_smul, invol_on_grade n (n - m) hd_star,
            cliffordRightStar_smul, cliffordRightStar_double q' m hm_le d hd,
            smul_smul, smul_smul]
        have hexp : (n - m) + m * (n - m) = (m + 1) * (n - m) := by
          rw [Nat.succ_mul, Nat.add_comm]
        have hscalar :
            CRing.mul (CRing.mul qn (CRing.ringParitySign (n - m)))
                      (CRing.mul (CRing.ringParitySign (m * (n - m))) (prodMetric q')) =
              CRing.mul (CRing.ringParitySign ((m + 1) * (n - m))) (CRing.mul (prodMetric q') qn) := by
          rw [CRing.mul_assoc qn _ _,
              ← CRing.mul_assoc (CRing.ringParitySign (n - m)) _ _,
              ← CRing.ringParitySign_add, hexp,
              ← CRing.mul_assoc qn _ _, CRing.mul_comm qn _, CRing.mul_assoc,
              CRing.mul_comm qn (prodMetric q')]
        rw [hscalar]

/-! ### Canonical Plücker–Poincaré Star `pStar` and Exact Two-Sided Inverse `pStarInv` -/

/-- Canonical Plücker–Poincaré right star `⋆ : Λ^k(R^n) → Λ^{n-k}(R^n)`. -/
def pStar (n : Nat) (x : Cl R n) : Cl R n :=
  cliffordRightStar (euclMetric n) (omega n) x

/-- Exact two-sided inverse `⋆⁻¹ : Λ^{n-k}(R^n) → Λ^k(R^n)` defined across all `Cl R n`. -/
def pStarInv : (n : Nat) → Cl R n → Cl R n
  | 0, a => a
  | n + 1, (u, v) => (pStarInv n v, pStarInv n (invol n u))

theorem pStar_step (n : Nat) (c d : Cl R n) :
    pStar (n + 1) (c, d) = (invol n (pStar n d), pStar n c) := by
  unfold pStar
  rw [cliffordRightStar_omega_step]
  have hqn : lastMetric (euclMetric (R := R) (n + 1)) = CRing.one := rfl
  have hq' : initMetric (euclMetric (R := R) (n + 1)) = euclMetric n := rfl
  rw [hqn, hq', one_smul]

theorem pStar_add (n : Nat) (x y : Cl R n) :
    pStar n (add n x y) = add n (pStar n x) (pStar n y) :=
  cliffordRightStar_add (euclMetric n) (omega n) x y

theorem pStar_smul (n : Nat) (r : R) (x : Cl R n) :
    pStar n (smul n r x) = smul n r (pStar n x) :=
  cliffordRightStar_smul (euclMetric n) (omega n) r x

theorem pStar_zero (n : Nat) : pStar n (zero (R := R) n) = zero n :=
  cliffordRightStar_zero (euclMetric n) (omega n)

theorem pStar_hasGrade {n k : Nat} (hk : k ≤ n) {x : Cl R n} (hx : HasGrade n k x) :
    HasGrade n (n - k) (pStar n x) :=
  cliffordRightStar_omega_hasGrade (euclMetric n) k hk x hx

theorem pStar_isHodgeStar (n : Nat) : IsHodgeStar (euclMetric (R := R) n) (omega n) (pStar n) :=
  rev_mul_isHodgeStar (euclMetric n)

theorem pStarInv_pStar : ∀ (n : Nat) (x : Cl R n), pStarInv n (pStar n x) = x
  | 0, x => by
      show CRing.mul x CRing.one = x
      exact CRing.mul_one x
  | n + 1, (c, d) => by
      rw [pStar_step]
      show (pStarInv n (pStar n c), pStarInv n (invol n (invol n (pStar n d)))) = (c, d)
      rw [invol_invol, pStarInv_pStar n c, pStarInv_pStar n d]

theorem pStar_pStarInv : ∀ (n : Nat) (y : Cl R n), pStar n (pStarInv n y) = y
  | 0, y => by
      show CRing.mul y CRing.one = y
      exact CRing.mul_one y
  | n + 1, (u, v) => by
      show pStar (n + 1) (pStarInv n v, pStarInv n (invol n u)) = (u, v)
      rw [pStar_step, pStar_pStarInv n v, pStar_pStarInv n (invol n u), invol_invol]

theorem pStarInv_zero : ∀ (n : Nat), pStarInv n (zero (R := R) n) = zero n
  | 0 => rfl
  | n + 1 => by
      show (pStarInv n (zero n), pStarInv n (invol n (zero n))) = (zero n, zero n)
      rw [invol_zero, pStarInv_zero n]

theorem pStarInv_add : ∀ (n : Nat) (x y : Cl R n),
    pStarInv n (add n x y) = add n (pStarInv n x) (pStarInv n y)
  | 0, _, _ => rfl
  | n + 1, (a, b), (c, d) => by
      show (pStarInv n (add n b d), pStarInv n (invol n (add n a c))) =
           (add n (pStarInv n b) (pStarInv n d),
            add n (pStarInv n (invol n a)) (pStarInv n (invol n c)))
      rw [invol_add, pStarInv_add n, pStarInv_add n]

theorem pStarInv_smul : ∀ (n : Nat) (r : R) (x : Cl R n),
    pStarInv n (smul n r x) = smul n r (pStarInv n x)
  | 0, _, _ => rfl
  | n + 1, r, (a, b) => by
      show (pStarInv n (smul n r b), pStarInv n (invol n (smul n r a))) =
           (smul n r (pStarInv n b), smul n r (pStarInv n (invol n a)))
      rw [invol_smul, pStarInv_smul n, pStarInv_smul n]

theorem pStarInv_hasGrade :
    ∀ {n m : Nat}, m ≤ n → ∀ {y : Cl R n}, HasGrade n m y → HasGrade n (n - m) (pStarInv n y)
  | 0, 0, _, _, _ => trivial
  | 0, _ + 1, hle, _, _ => absurd hle (Nat.not_succ_le_zero _)
  | n + 1, 0, _, (u, v), ⟨hu, hv⟩ => by
      show HasGrade (n + 1) (n + 1) (pStarInv n v, pStarInv n (invol n u))
      rw [hv, pStarInv_zero]
      exact ⟨hasGrade_zero n (n + 1), pStarInv_hasGrade (Nat.zero_le n) (hasGrade_invol n 0 hu)⟩
  | n + 1, k + 1, hle, (u, v), ⟨hu, hv⟩ => by
      have hk_le : k ≤ n := Nat.le_of_succ_le_succ hle
      have hsub : (n + 1) - (k + 1) = n - k := Nat.succ_sub_succ n k
      rw [hsub]
      by_cases hkn : k = n
      · subst hkn
        rw [Nat.sub_self k]
        have hu0 : u = zero k := hasGrade_gt_zero k (k + 1) (Nat.lt_succ_self k) u hu
        show HasGrade k 0 (pStarInv k v) ∧ pStarInv k (invol k u) = zero k
        rw [hu0, invol_zero, pStarInv_zero]
        have hv_inv := pStarInv_hasGrade (Nat.le_refl k) hv
        rw [Nat.sub_self k] at hv_inv
        exact ⟨hv_inv, rfl⟩
      · have hk_lt : k < n := Nat.lt_of_le_of_ne hk_le hkn
        have hnk : n - k = (n - (k + 1)) + 1 := by omega
        rw [hnk]
        have hv_inv := pStarInv_hasGrade hk_le hv
        rw [hnk] at hv_inv
        have hu_inv := pStarInv_hasGrade hk_lt (hasGrade_invol n (k + 1) hu)
        exact ⟨hv_inv, hu_inv⟩

/-- Plücker–Poincaré Double-Star Sign Law: `⋆(⋆x) = (-1)^{k(n-k)} · x` for `x ∈ Λ^k(R^n)`. -/
theorem pStar_double {n k : Nat} (hk : k ≤ n) {x : Cl R n} (hx : HasGrade n k x) :
    pStar n (pStar n x) = smul n (CRing.ringParitySign (k * (n - k))) x := by
  unfold pStar
  rw [cliffordRightStar_double (euclMetric n) k hk x hx,
      prodMetric_euclMetric n, CRing.mul_one]

/-- Conversion between forward `pStar` and inverse `pStarInv` on homogeneous grade `m ≤ n`:
      `⋆y = (-1)^{m(n-m)} · ⋆⁻¹y`. -/
theorem pStar_eq_sign_pStarInv {n m : Nat} (hm : m ≤ n) {y : Cl R n} (hy : HasGrade n m y) :
    pStar n y = smul n (CRing.ringParitySign (m * (n - m))) (pStarInv n y) := by
  have hx_grade : HasGrade n (n - m) (pStarInv n y) := pStarInv_hasGrade hm hy
  have hle : n - m ≤ n := by omega
  have hdouble := pStar_double hle hx_grade
  rw [pStar_pStarInv] at hdouble
  have hexp : (n - m) * (n - (n - m)) = m * (n - m) := by
    have hsub : n - (n - m) = m := by omega
    rw [hsub, Nat.mul_comm]
  rw [hexp] at hdouble
  exact hdouble

theorem pStar_omega : ∀ (n : Nat), pStar n (omega (R := R) n) = one n
  | 0 => by show CRing.mul CRing.one CRing.one = CRing.one; exact CRing.one_mul CRing.one
  | n + 1 => by
      show pStar (n + 1) (zero n, omega n) = (one n, zero n)
      rw [pStar_step, pStar_omega n, invol_one, pStar_zero]

/-! ### Canonical Grassmann–Cayley Regressive (Meet / Intersection) Product -/

/-- Canonical Grassmann–Cayley regressive (intersection / meet) product `A ∨ B = ⋆⁻¹((⋆A) ∧ (⋆B))`. -/
def vee (n : Nat) (A B : Cl R n) : Cl R n :=
  pStarInv n (wedge n (pStar n A) (pStar n B))

/-- Uncorrected forward three-star projective intersection operator `⋆((⋆A) ∧ (⋆B))`. -/
def veeForward3Star (n : Nat) (A B : Cl R n) : Cl R n :=
  pStar n (wedge n (pStar n A) (pStar n B))

/-- Defining Poincaré–De Morgan duality of the regressive product: `⋆(A ∨ B) = (⋆A) ∧ (⋆B)`. -/
theorem pStar_vee (n : Nat) (A B : Cl R n) :
    pStar n (vee n A B) = wedge n (pStar n A) (pStar n B) :=
  pStar_pStarInv n _

/-- Uniqueness of the regressive product: `M = A ∨ B` iff `⋆M = (⋆A) ∧ (⋆B)`. -/
theorem vee_unique {n : Nat} {A B M : Cl R n}
    (h : pStar n M = wedge n (pStar n A) (pStar n B)) :
    M = vee n A B := by
  unfold vee
  rw [← h, pStarInv_pStar]

/-- Associativity of the Grassmann–Cayley regressive product across all dimensions `n`. -/
theorem vee_assoc (n : Nat) (A B C : Cl R n) :
    vee n (vee n A B) C = vee n A (vee n B C) := by
  apply vee_unique
  rw [pStar_vee, pStar_vee, pStar_vee, wedge_assoc]

/-- Left unit law of the ambient space volume blade `ω_n`: `ω_n ∨ B = B`. -/
theorem omega_vee (n : Nat) (B : Cl R n) : vee n (omega n) B = B := by
  unfold vee
  rw [pStar_omega, one_wedge, pStarInv_pStar]

/-- Right unit law of the ambient space volume blade `ω_n`: `A ∨ ω_n = A`. -/
theorem vee_omega (n : Nat) (A : Cl R n) : vee n A (omega n) = A := by
  unfold vee
  rw [pStar_omega, wedge_one, pStarInv_pStar]

/-- Exact grading of the regressive product: for `A ∈ Λ^r`, `B ∈ Λ^s` with `r, s ≤ n` and `n ≤ r + s`,
      `A ∨ B ∈ Λ^{r + s - n}`. -/
theorem vee_hasGrade {n r s : Nat} (hr : r ≤ n) (hs : s ≤ n) (hrs : n ≤ r + s)
    {A B : Cl R n} (hA : HasGrade n r A) (hB : HasGrade n s B) :
    HasGrade n (r + s - n) (vee n A B) := by
  unfold vee
  have hw := wedge_hasGrade n (n - r) (n - s) (pStar_hasGrade hr hA) (pStar_hasGrade hs hB)
  have hm_le : (n - r) + (n - s) ≤ n := by omega
  have hinv := pStarInv_hasGrade hm_le hw
  have hgrade_eq : n - ((n - r) + (n - s)) = r + s - n := by omega
  rw [hgrade_eq] at hinv
  exact hinv

/-- Non-spanning subspaces (`r + s < n`) have zero transverse regressive product. -/
theorem vee_eq_zero_of_lt {n r s : Nat} (hr : r ≤ n) (hs : s ≤ n) (hlt : r + s < n)
    {A B : Cl R n} (hA : HasGrade n r A) (hB : HasGrade n s B) :
    vee n A B = zero n := by
  unfold vee
  have hw := wedge_hasGrade n (n - r) (n - s) (pStar_hasGrade hr hA) (pStar_hasGrade hs hB)
  have hgt : n < (n - r) + (n - s) := by omega
  rw [hasGrade_gt_zero n ((n - r) + (n - s)) hgt _ hw, pStarInv_zero]

/-! ### Exact Graded Commutation Law of the Regressive Product -/

/-- Exact Graded Commutation Law of the Grassmann–Cayley Regressive Product:
    For all `r ≤ n`, `s ≤ n` and `A ∈ Λ^r(R^n)`, `B ∈ Λ^s(R^n)`,
      `B ∨ A = (-1)^{(n - r)(n - s)} · (A ∨ B)`.
    The exponent is the PRODUCT OF CODIMENSIONS `(n - r)(n - s)`, NOT the dimension sum `r + s`. -/
theorem vee_graded_comm {n r s : Nat} (hr : r ≤ n) (hs : s ≤ n)
    {A B : Cl R n} (hA : HasGrade n r A) (hB : HasGrade n s B) :
    vee n B A = smul n (CRing.ringParitySign ((n - r) * (n - s))) (vee n A B) := by
  unfold vee
  have hcomm := wedge_graded_comm n (n - r) (n - s) (pStar_hasGrade hr hA) (pStar_hasGrade hs hB)
  rw [hcomm, pStarInv_smul]

/-! ### Exact Forward Three-Star Intersection Sign-Correction Law -/

/-- Exact Forward Three-Star Intersection Law:
    For `A ∈ Λ^r(R^n)`, `B ∈ Λ^s(R^n)` with `r, s ≤ n`, `n ≤ r + s`, and `k = r + s - n`:
      `⋆((⋆A) ∧ (⋆B)) = (-1)^{k(n-k)} · (A ∨ B)`. -/
theorem veeForward3Star_eq_sign_vee {n r s : Nat}
    (hr : r ≤ n) (hs : s ≤ n) (hrs : n ≤ r + s)
    {A B : Cl R n} (hA : HasGrade n r A) (hB : HasGrade n s B) :
    veeForward3Star n A B =
      smul n (CRing.ringParitySign ((r + s - n) * (n - (r + s - n)))) (vee n A B) := by
  unfold veeForward3Star vee
  have hw := wedge_hasGrade n (n - r) (n - s) (pStar_hasGrade hr hA) (pStar_hasGrade hs hB)
  have hm_le : (n - r) + (n - s) ≤ n := by omega
  rw [pStar_eq_sign_pStarInv hm_le hw]
  have hexp : ((n - r) + (n - s)) * (n - ((n - r) + (n - s))) =
              (r + s - n) * (n - (r + s - n)) := by
    have h1 : (n - r) + (n - s) = n - (r + s - n) := by omega
    have h2 : n - (n - (r + s - n)) = r + s - n := by omega
    rw [h1, h2, Nat.mul_comm]
  rw [hexp]

/-- Inverse form of the Forward Three-Star Intersection Law:
      `A ∨ B = (-1)^{k(n-k)} · ⋆((⋆A) ∧ (⋆B))`. -/
theorem vee_eq_sign_veeForward3Star {n r s : Nat}
    (hr : r ≤ n) (hs : s ≤ n) (hrs : n ≤ r + s)
    {A B : Cl R n} (hA : HasGrade n r A) (hB : HasGrade n s B) :
    vee n A B =
      smul n (CRing.ringParitySign ((r + s - n) * (n - (r + s - n)))) (veeForward3Star n A B) := by
  rw [veeForward3Star_eq_sign_vee hr hs hrs hA hB, smul_smul,
      CRing.ringParitySign_sq, one_smul]

/-- Master Parity-Reduced Forward Three-Star Intersection Law:
      `A ∨ B = (-1)^{(r + s)(n - 1)} · ⋆((⋆A) ∧ (⋆B))`. -/
theorem vee_eq_dimSum_factor_veeForward3Star {n r s : Nat}
    (hr : r ≤ n) (hs : s ≤ n) (hrs : n ≤ r + s)
    {A B : Cl R n} (hA : HasGrade n r A) (hB : HasGrade n s B) :
    vee n A B =
      smul n (CRing.ringParitySign ((r + s) * (n - 1))) (veeForward3Star n A B) := by
  rw [vee_eq_sign_veeForward3Star hr hs hrs hA hB,
      CRing.ringParitySign_of_mod_eq (intersection_double_star_mod_two hr hs hrs)]

/-! ### Left-Star Duality Invariance of the Regressive Product -/

/-- Plücker–Poincaré left star `⋆_L : x ↦ ω_n · x̃` and its exact two-sided inverse `⋆_L⁻¹`. -/
def pStarLeft (n : Nat) (x : Cl R n) : Cl R n :=
  cliffordLeftStar (euclMetric n) (omega n) x

def pStarLeftInv : (n : Nat) → Cl R n → Cl R n
  | 0, a => a
  | n + 1, (u, v) => (invol n (pStarLeftInv n v), pStarLeftInv n u)

theorem pStarLeft_step (n : Nat) (c d : Cl R n) :
    pStarLeft (n + 1) (c, d) = (pStarLeft n d, pStarLeft n (invol n c)) := by
  unfold pStarLeft cliffordLeftStar
  let q' := euclMetric (R := R) n
  show (add n (mul q' (zero n) (rev n c))
              (smul n CRing.one (mul q' (omega n) (invol n (invol n (rev n d))))),
        add n (mul q' (zero n) (invol n (rev n d)))
              (mul q' (omega n) (invol n (rev n c)))) =
       (mul q' (omega n) (rev n d), mul q' (omega n) (rev n (invol n c)))
  rw [zero_mul, zero_mul, zero_add, zero_add, one_smul, invol_invol, rev_invol]

theorem pStarLeft_on_grade :
    ∀ {n k : Nat}, k ≤ n → ∀ {x : Cl R n}, HasGrade n k x →
      pStarLeft n x = smul n (CRing.ringParitySign (k * (n - k))) (pStar n x)
  | 0, 0, _, x, _ => by
      have h0 : (0 * (0 - 0)) % 2 = 0 := rfl
      rw [CRing.ringParitySign_even h0, one_smul]
      show CRing.mul CRing.one x = CRing.mul x CRing.one
      rw [CRing.one_mul, CRing.mul_one]
  | 0, _ + 1, hle, _, _ => absurd hle (Nat.not_succ_le_zero _)
  | n + 1, 0, _, (c, d), ⟨hc, hd⟩ => by
      have h0 : (0 * ((n + 1) - 0)) % 2 = 0 := by simp
      have h0' : (0 * (n - 0)) % 2 = 0 := by simp
      rw [CRing.ringParitySign_even h0, one_smul, hd, pStarLeft_step, pStar_step,
          pStar_zero, invol_zero]
      have hinv : invol n c = c := by
        rw [invol_on_grade n 0 hc, CRing.ringParitySign_even rfl, one_smul]
      have hd0 : pStarLeft n (zero (R := R) n) = zero n := by
        unfold pStarLeft cliffordLeftStar
        rw [rev_zero, mul_zero]
      rw [hd0, hinv, pStarLeft_on_grade (Nat.zero_le n) hc,
          CRing.ringParitySign_even h0', one_smul]
  | n + 1, m + 1, hle, (c, d), ⟨hc, hd⟩ => by
      have hm_le : m ≤ n := Nat.le_of_succ_le_succ hle
      have hsub : (n + 1) - (m + 1) = n - m := Nat.succ_sub_succ n m
      rw [hsub, pStarLeft_step, pStar_step]
      apply Prod.ext
      · show pStarLeft n d =
             smul n (CRing.ringParitySign ((m + 1) * (n - m))) (invol n (pStar n d))
        rw [pStarLeft_on_grade hm_le hd,
            invol_on_grade n (n - m) (pStar_hasGrade hm_le hd),
            smul_smul, ← CRing.ringParitySign_add]
        have hmod : (m * (n - m)) % 2 = ((m + 1) * (n - m) + (n - m)) % 2 := by
          have heq : (m + 1) * (n - m) + (n - m) = m * (n - m) + 2 * (n - m) := by
            rw [Nat.succ_mul, Nat.add_assoc, ← Nat.two_mul]
          rw [heq]
          omega
        rw [CRing.ringParitySign_of_mod_eq hmod]
      · show pStarLeft n (invol n c) =
             smul n (CRing.ringParitySign ((m + 1) * (n - m))) (pStar n c)
        by_cases hmn : m = n
        · subst hmn
          have hc0 : c = zero m := hasGrade_gt_zero m (m + 1) (Nat.lt_succ_self m) c hc
          have hl0 : pStarLeft m (zero (R := R) m) = zero m := by
            unfold pStarLeft cliffordLeftStar; rw [rev_zero, mul_zero]
          rw [hc0, invol_zero, hl0, pStar_zero, smul_zero]
        · have hm_lt : m < n := Nat.lt_of_le_of_ne hm_le hmn
          have hl_smul : ∀ (r : R) (z : Cl R n), pStarLeft n (smul n r z) = smul n r (pStarLeft n z) := by
            intro r z; unfold pStarLeft cliffordLeftStar; rw [rev_smul, mul_smul]
          rw [invol_on_grade n (m + 1) hc, hl_smul,
              pStarLeft_on_grade hm_lt hc, smul_smul, ← CRing.ringParitySign_add]
          have hexp : (m + 1) + (m + 1) * (n - (m + 1)) = (m + 1) * (n - m) := by
            have hnm : n - m = (n - (m + 1)) + 1 := by omega
            rw [hnm, Nat.mul_succ, Nat.add_comm]
          rw [hexp]

theorem pStarLeft_pStarLeftInv : ∀ (n : Nat) (y : Cl R n), pStarLeft n (pStarLeftInv n y) = y
  | 0, y => by show CRing.mul CRing.one y = y; exact CRing.one_mul y
  | n + 1, (u, v) => by
      show pStarLeft (n + 1) (invol n (pStarLeftInv n v), pStarLeftInv n u) = (u, v)
      rw [pStarLeft_step, invol_invol, pStarLeft_pStarLeftInv n u, pStarLeft_pStarLeftInv n v]

theorem pStarLeftInv_on_grade {n m : Nat} (hm : m ≤ n) {y : Cl R n} (hy : HasGrade n m y) :
    pStarLeftInv n y = smul n (CRing.ringParitySign (m * (n - m))) (pStarInv n y) := by
  have h_apply : ∀ {a b : Cl R n}, pStarLeft n a = pStarLeft n b → a = b := by
    intro a b hab
    have hinv : ∀ (d : Nat) (z : Cl R d), pStarLeftInv d (pStarLeft d z) = z := by
      intro d
      induction d with
      | zero => intro z; show CRing.mul CRing.one z = z; exact CRing.one_mul z
      | succ d ih =>
          intro (z1, z2)
          rw [pStarLeft_step]
          show (invol d (pStarLeftInv d (pStarLeft d (invol d z1))),
                pStarLeftInv d (pStarLeft d z2)) = (z1, z2)
          rw [ih, ih, invol_invol]
    rw [← hinv n a, ← hinv n b, hab]
  apply h_apply
  have hl_smul : ∀ (r : R) (z : Cl R n), pStarLeft n (smul n r z) = smul n r (pStarLeft n z) := by
    intro r z; unfold pStarLeft cliffordLeftStar; rw [rev_smul, mul_smul]
  rw [pStarLeft_pStarLeftInv, hl_smul]
  have hx_grade := pStarInv_hasGrade hm hy
  have hle : n - m ≤ n := by omega
  rw [pStarLeft_on_grade hle hx_grade, pStar_pStarInv, smul_smul]
  have hexp : (n - m) * (n - (n - m)) = m * (n - m) := by
    have hsub : n - (n - m) = m := by omega
    rw [hsub, Nat.mul_comm]
  rw [hexp, CRing.ringParitySign_sq, one_smul]

theorem pStarLeftInv_smul : ∀ (n : Nat) (c : R) (z : Cl R n),
    pStarLeftInv n (smul n c z) = smul n c (pStarLeftInv n z)
  | 0, _, _ => rfl
  | n + 1, c, (z1, z2) => by
      show (invol n (pStarLeftInv n (smul n c z2)), pStarLeftInv n (smul n c z1)) =
           (smul n c (invol n (pStarLeftInv n z2)), smul n c (pStarLeftInv n z1))
      rw [pStarLeftInv_smul n, pStarLeftInv_smul n, invol_smul]

/-- Universal Left–Right Star Duality Invariance of the Regressive Product:
      `⋆_L⁻¹((⋆_L A) ∧ (⋆_L B)) = A ∨ B` identically (with sign `+1`) for all `n, r, s`! -/
theorem vee_eq_leftStar_meet {n r s : Nat}
    (hr : r ≤ n) (hs : s ≤ n) (hrs : n ≤ r + s)
    {A B : Cl R n} (hA : HasGrade n r A) (hB : HasGrade n s B) :
    pStarLeftInv n (wedge n (pStarLeft n A) (pStarLeft n B)) = vee n A B := by
  rw [pStarLeft_on_grade hr hA, pStarLeft_on_grade hs hB, smul_wedge, wedge_smul]
  have hw := wedge_hasGrade n (n - r) (n - s) (pStar_hasGrade hr hA) (pStar_hasGrade hs hB)
  have hm_le : (n - r) + (n - s) ≤ n := by omega
  rw [pStarLeftInv_smul, pStarLeftInv_smul, pStarLeftInv_on_grade hm_le hw, smul_smul, smul_smul]
  have hr_mod := k_mul_n_sub_k_mod_two hr
  have hs_mod := k_mul_n_sub_k_mod_two hs
  have hw_mod := k_mul_n_sub_k_mod_two hm_le
  by_cases hn0 : n = 0
  · subst hn0
    have hr0 : r = 0 := by omega
    have hs0 : s = 0 := by omega
    subst hr0; subst hs0
    have h0 : (0 : Nat) % 2 = 0 := rfl
    show smul 0 (CRing.mul (CRing.mul (CRing.ringParitySign 0) (CRing.ringParitySign 0))
                           (CRing.ringParitySign 0)) _ = _
    rw [CRing.ringParitySign_even h0, CRing.one_mul, CRing.one_mul, one_smul]
    rfl
  · have hn2 : n % 2 = 0 ∨ n % 2 = 1 := by omega
    rcases hn2 with hneven | hnodd
    · have hn1_odd : (n - 1) % 2 = 1 := by omega
      have h1 : (r * (n - r)) % 2 = r % 2 := by rw [hr_mod, nat_mul_mod_two, hn1_odd]; omega
      have h2 : (s * (n - s)) % 2 = s % 2 := by rw [hs_mod, nat_mul_mod_two, hn1_odd]; omega
      have h3 : (((n - r) + (n - s)) * (n - ((n - r) + (n - s)))) % 2 =
                ((n - r) + (n - s)) % 2 := by rw [hw_mod, nat_mul_mod_two, hn1_odd]; omega
      rw [CRing.ringParitySign_of_mod_eq h1, CRing.ringParitySign_of_mod_eq h2,
          CRing.ringParitySign_of_mod_eq h3, ← CRing.ringParitySign_add, ← CRing.ringParitySign_add]
      have htot : (r + s + ((n - r) + (n - s))) % 2 = 0 := by omega
      rw [CRing.ringParitySign_even htot, one_smul]
      rfl
    · have hn1_even : (n - 1) % 2 = 0 := by omega
      have h1 : (r * (n - r)) % 2 = 0 := by rw [hr_mod, nat_mul_mod_two, hn1_even]; simp
      have h2 : (s * (n - s)) % 2 = 0 := by rw [hs_mod, nat_mul_mod_two, hn1_even]; simp
      have h3 : (((n - r) + (n - s)) * (n - ((n - r) + (n - s)))) % 2 = 0 := by
        rw [hw_mod, nat_mul_mod_two, hn1_even]; simp
      rw [CRing.ringParitySign_even h1, CRing.ringParitySign_even h2,
          CRing.ringParitySign_even h3, CRing.one_mul, CRing.one_mul, one_smul]
      rfl

/-! ### Authentic Cartan & Dorst Interior Contractions & De Morgan Meet Sign Laws -/

/-- Cartan left interior contraction `α ⌟_C β`, characterized by metric adjointness
      `⟨γ, α ⌟_C β⟩ = ⟨α ∧ γ, β⟩` across all of `Cl R n`. -/
def cartanLeft : (n : Nat) → Cl R n → Cl R n → Cl R n
  | 0, a, b => CRing.mul a b
  | n + 1, (a1, a2), (b1, b2) =>
      (add n (cartanLeft n a1 b1) (invol n (cartanLeft n a2 b2)),
       cartanLeft n a1 b2)

/-- Dorst/Hestenes left contraction `α ⌋ β`, characterized by `⟨γ, α ⌋ β⟩ = ⟨α̃ ∧ γ, β⟩`. -/
def dorstLeft (n : Nat) (a b : Cl R n) : Cl R n :=
  cartanLeft n (rev n a) b

/-- Authentic metric adjointness of `cartanLeft`: `⟨γ, α ⌟_C β⟩ = ⟨α ∧ γ, β⟩` for all `α, β, γ`. -/
theorem inner_cartanLeft : ∀ (n : Nat) (a b g : Cl R n),
    inner (euclMetric n) g (cartanLeft n a b) = inner (euclMetric n) (wedge n a g) b
  | 0, a, b, g => by
      show CRing.mul g (CRing.mul a b) = CRing.mul (CRing.mul a g) b
      rw [← CRing.mul_assoc, CRing.mul_comm g a]
  | n + 1, (a1, a2), (b1, b2), (g1, g2) => by
      rw [wedge_step]
      show CRing.add (inner (euclMetric n) g1 (add n (cartanLeft n a1 b1) (invol n (cartanLeft n a2 b2))))
                     (CRing.mul CRing.one (inner (euclMetric n) g2 (cartanLeft n a1 b2))) =
           CRing.add (inner (euclMetric n) (wedge n a1 g1) b1)
                     (CRing.mul CRing.one (inner (euclMetric n)
                       (add n (wedge n a1 g2) (wedge n a2 (invol n g1))) b2))
      rw [CRing.one_mul, CRing.one_mul, inner_add_right, inner_add_left,
          inner_cartanLeft n a1 b1 g1, inner_cartanLeft n a1 b2 g2]
      have hinv : inner (euclMetric n) g1 (invol n (cartanLeft n a2 b2)) =
                  inner (euclMetric n) (wedge n a2 (invol n g1)) b2 := by
        rw [← inner_invol (euclMetric n) g1 (invol n (cartanLeft n a2 b2)),
            invol_invol, inner_cartanLeft n a2 b2 (invol n g1)]
      rw [hinv, CRing.add_assoc, CRing.add_comm (inner (euclMetric n) (wedge n a2 (invol n g1)) b2) _]

/-- Authentic metric adjointness of `dorstLeft`: `⟨γ, α ⌋ β⟩ = ⟨α̃ ∧ γ, β⟩` for all `α, β, γ`. -/
theorem inner_dorstLeft (n : Nat) (a b g : Cl R n) :
    inner (euclMetric n) g (dorstLeft n a b) = inner (euclMetric n) (wedge n (rev n a) g) b :=
  inner_cartanLeft n (rev n a) b g

theorem cartanLeft_zero_left : ∀ (n : Nat) (b : Cl R n), cartanLeft n (zero n) b = zero n
  | 0, b => CRing.zero_mul b
  | n + 1, (b1, b2) => by
      show (add n (cartanLeft n (zero n) b1) (invol n (cartanLeft n (zero n) b2)),
            cartanLeft n (zero n) b2) = (zero n, zero n)
      rw [cartanLeft_zero_left n, cartanLeft_zero_left n, invol_zero, add_zero]

theorem cartanLeft_zero_right : ∀ (n : Nat) (a : Cl R n), cartanLeft n a (zero n) = zero n
  | 0, a => CRing.mul_zero a
  | n + 1, (a1, a2) => by
      show (add n (cartanLeft n a1 (zero n)) (invol n (cartanLeft n a2 (zero n))),
            cartanLeft n a1 (zero n)) = (zero n, zero n)
      rw [cartanLeft_zero_right n, cartanLeft_zero_right n, invol_zero, add_zero]

theorem cartanLeft_smul_left : ∀ (n : Nat) (r : R) (a b : Cl R n),
    cartanLeft n (smul n r a) b = smul n r (cartanLeft n a b)
  | 0, r, a, b => CRing.mul_assoc r a b
  | n + 1, r, (a1, a2), (b1, b2) => by
      show (add n (cartanLeft n (smul n r a1) b1) (invol n (cartanLeft n (smul n r a2) b2)),
            cartanLeft n (smul n r a1) b2) =
           (smul n r (add n (cartanLeft n a1 b1) (invol n (cartanLeft n a2 b2))),
            smul n r (cartanLeft n a1 b2))
      rw [cartanLeft_smul_left n, cartanLeft_smul_left n, cartanLeft_smul_left n, invol_smul, smul_add]

theorem cartanLeft_gt_zero :
    ∀ {n a b : Nat}, b < a → ∀ {α β : Cl R n},
      HasGrade n a α → HasGrade n b β → cartanLeft n α β = zero n
  | 0, 0, _, hlt, _, _, _, _ => absurd hlt (Nat.not_lt_zero _)
  | 0, _ + 1, _, _, α, β, hα, _ => by
      show CRing.mul α β = CRing.zero
      rw [hα, CRing.zero_mul]
  | _ + 1, 0, _, hlt, _, _, _, _ => absurd hlt (Nat.not_lt_zero _)
  | n + 1, j + 1, 0, _, (a1, a2), (b1, b2), ⟨ha1, _⟩, ⟨hb1, hb2⟩ => by
      show (add n (cartanLeft n a1 b1) (invol n (cartanLeft n a2 b2)),
            cartanLeft n a1 b2) = (zero n, zero n)
      rw [hb2, cartanLeft_zero_right, cartanLeft_zero_right, invol_zero, add_zero,
          cartanLeft_gt_zero (Nat.zero_lt_succ j) ha1 hb1]
  | n + 1, j + 1, k + 1, hlt, (a1, a2), (b1, b2), ⟨ha1, ha2⟩, ⟨hb1, hb2⟩ => by
      have hkj : k < j := Nat.lt_of_succ_lt_succ hlt
      have hkj1 : k < j + 1 := Nat.lt_succ_of_lt hkj
      show (add n (cartanLeft n a1 b1) (invol n (cartanLeft n a2 b2)),
            cartanLeft n a1 b2) = (zero n, zero n)
      rw [cartanLeft_gt_zero hlt ha1 hb1, cartanLeft_gt_zero hkj ha2 hb2,
          cartanLeft_gt_zero hkj1 ha1 hb2, invol_zero, add_zero]

theorem cartanLeft_hasGrade :
    ∀ {n a b : Nat}, a ≤ b → b ≤ n → ∀ {α β : Cl R n},
      HasGrade n a α → HasGrade n b β → HasGrade n (b - a) (cartanLeft n α β)
  | 0, 0, 0, _, _, _, _, _, _ => trivial
  | 0, _, _ + 1, _, hbn, _, _, _, _ => absurd hbn (Nat.not_succ_le_zero _)
  | 0, _ + 1, 0, hab, _, _, _, _, _ => absurd hab (Nat.not_succ_le_zero _)
  | n + 1, 0, 0, _, _, (a1, a2), (b1, b2), ⟨ha1, ha2⟩, ⟨hb1, hb2⟩ => by
      show HasGrade n 0 (add n (cartanLeft n a1 b1) (invol n (cartanLeft n a2 b2))) ∧
           cartanLeft n a1 b2 = zero n
      rw [ha2, hb2, cartanLeft_zero_left, cartanLeft_zero_right, invol_zero, add_zero]
      exact ⟨cartanLeft_hasGrade (Nat.le_refl 0) (Nat.zero_le n) ha1 hb1, rfl⟩
  | n + 1, 0, k + 1, _, hbn, (a1, a2), (b1, b2), ⟨ha1, ha2⟩, ⟨hb1, hb2⟩ => by
      have hk_le : k ≤ n := Nat.le_of_succ_le_succ hbn
      show HasGrade n (k + 1) (add n (cartanLeft n a1 b1) (invol n (cartanLeft n a2 b2))) ∧
           HasGrade n k (cartanLeft n a1 b2)
      rw [ha2, cartanLeft_zero_left, invol_zero, add_zero]
      by_cases hkn : k = n
      · subst hkn
        have hb1_0 : b1 = zero k := hasGrade_gt_zero k (k + 1) (Nat.lt_succ_self k) b1 hb1
        rw [hb1_0, cartanLeft_zero_right]
        have h2 := cartanLeft_hasGrade (Nat.zero_le k) (Nat.le_refl k) ha1 hb2
        rw [Nat.sub_zero] at h2
        exact ⟨hasGrade_zero k (k + 1), h2⟩
      · have hk_lt : k < n := Nat.lt_of_le_of_ne hk_le hkn
        have h1 := cartanLeft_hasGrade (Nat.zero_le (k + 1)) hk_lt ha1 hb1
        have h2 := cartanLeft_hasGrade (Nat.zero_le k) hk_le ha1 hb2
        rw [Nat.sub_zero] at h1 h2
        exact ⟨h1, h2⟩
  | n + 1, _ + 1, 0, hab, _, _, _, _, _ => absurd hab (Nat.not_succ_le_zero _)
  | n + 1, j + 1, k + 1, hab, hbn, (a1, a2), (b1, b2), ⟨ha1, ha2⟩, ⟨hb1, hb2⟩ => by
      have hjk : j ≤ k := Nat.le_of_succ_le_succ hab
      have hk_le : k ≤ n := Nat.le_of_succ_le_succ hbn
      have hsub : (k + 1) - (j + 1) = k - j := Nat.succ_sub_succ k j
      rw [hsub]
      by_cases hj_eq_k : j = k
      · subst hj_eq_k
        rw [Nat.sub_self j]
        show HasGrade n 0 (add n (cartanLeft n a1 b1) (invol n (cartanLeft n a2 b2))) ∧
             cartanLeft n a1 b2 = zero n
        by_cases hjn : j = n
        · subst hjn
          have ha1_0 : a1 = zero j := hasGrade_gt_zero j (j + 1) (Nat.lt_succ_self j) a1 ha1
          rw [ha1_0, cartanLeft_zero_left, cartanLeft_zero_left, zero_add]
          have h2 := cartanLeft_hasGrade (Nat.le_refl j) (Nat.le_refl j) ha2 hb2
          rw [Nat.sub_self j] at h2
          exact ⟨hasGrade_invol j 0 h2, rfl⟩
        · have hj_lt : j < n := Nat.lt_of_le_of_ne hk_le hjn
          have h1 := cartanLeft_hasGrade (Nat.le_refl (j + 1)) hj_lt ha1 hb1
          have h2 := cartanLeft_hasGrade (Nat.le_refl j) hk_le ha2 hb2
          rw [Nat.sub_self (j + 1)] at h1
          rw [Nat.sub_self j] at h2
          exact ⟨hasGrade_add n 0 h1 (hasGrade_invol n 0 h2),
                 cartanLeft_gt_zero (Nat.lt_succ_self j) ha1 hb2⟩
      · have hj_lt_k : j < k := Nat.lt_of_le_of_ne hjk hj_eq_k
        have hkj_eq : k - j = (k - (j + 1)) + 1 := by omega
        rw [hkj_eq]
        show HasGrade n ((k - (j + 1)) + 1)
               (add n (cartanLeft n a1 b1) (invol n (cartanLeft n a2 b2))) ∧
             HasGrade n (k - (j + 1)) (cartanLeft n a1 b2)
        have h_snd := cartanLeft_hasGrade hj_lt_k hk_le ha1 hb2
        have h_a2b2 := cartanLeft_hasGrade hjk hk_le ha2 hb2
        rw [hkj_eq] at h_a2b2
        by_cases hkn : k = n
        · subst hkn
          have hb1_0 : b1 = zero k := hasGrade_gt_zero k (k + 1) (Nat.lt_succ_self k) b1 hb1
          rw [hb1_0, cartanLeft_zero_right, zero_add]
          exact ⟨hasGrade_invol k ((k - (j + 1)) + 1) h_a2b2, h_snd⟩
        · have hk_lt_n : k < n := Nat.lt_of_le_of_ne hk_le hkn
          have h_a1b1 := cartanLeft_hasGrade hab hk_lt_n ha1 hb1
          rw [hsub, hkj_eq] at h_a1b1
          exact ⟨hasGrade_add n ((k - (j + 1)) + 1) h_a1b1
                   (hasGrade_invol n ((k - (j + 1)) + 1) h_a2b2),
                 h_snd⟩

/-- Exact De Morgan / Cartan Contraction Meet Sign Law:
    For `A ∈ Λ^r(R^n)`, `B ∈ Λ^s(R^n)` with `r, s ≤ n`, `n ≤ r + s`, and `k = r + s - n`:
      `(⋆A) ⌟_C B = (-1)^{k(n - r)} · (A ∨ B)`. -/
theorem cartanLeft_pStar_eq_sign_vee {n r s : Nat}
    (hr : r ≤ n) (hs : s ≤ n) (hrs : n ≤ r + s)
    {A B : Cl R n} (hA : HasGrade n r A) (hB : HasGrade n s B) :
    cartanLeft n (pStar n A) B =
      smul n (CRing.ringParitySign ((r + s - n) * (n - r))) (vee n A B) := by
  let k := r + s - n
  have hk_le : k ≤ n := by omega
  have hnr_le_s : n - r ≤ s := by omega
  have hstA : HasGrade n (n - r) (pStar n A) := pStar_hasGrade hr hA
  have hLHS_grade : HasGrade n k (cartanLeft n (pStar n A) B) := by
    have hcg := cartanLeft_hasGrade hnr_le_s hs hstA hB
    have hsub : s - (n - r) = k := by omega
    rw [hsub] at hcg
    exact hcg
  have hRHS_grade : HasGrade n k
      (smul n (CRing.ringParitySign (k * (n - r))) (vee n A B)) :=
    hasGrade_smul n k _ (vee_hasGrade hr hs hrs hA hB)
  have hstar_eq :
      pStar n (cartanLeft n (pStar n A) B) =
        pStar n (smul n (CRing.ringParitySign (k * (n - r))) (vee n A B)) := by
    apply (sub_eq_zero (n := n)).mp
    apply poincare_wedge_nondeg n k hk_le
    · exact hasGrade_add n (n - k) (pStar_hasGrade hk_le hLHS_grade)
        (hasGrade_neg n (n - k) (pStar_hasGrade hk_le hRHS_grade))
    · intro γ hγ
      unfold sub
      rw [wedge_add_right, ← neg_one_smul n (pStar n _), wedge_smul, neg_one_smul]
      have hw1 : wedge n γ (pStar n (cartanLeft n (pStar n A) B)) =
                 smul n (inner (euclMetric n) γ (cartanLeft n (pStar n A) B)) (omega n) :=
        wedge_cliffordRightStar_omega (euclMetric n) k hk_le γ _ hγ hLHS_grade
      rw [inner_cartanLeft] at hw1
      have hw_ag_grade : HasGrade n s (wedge n (pStar n A) γ) := by
        have hg := wedge_hasGrade n (n - r) k hstA hγ
        have hsum : (n - r) + k = s := by omega
        rw [hsum] at hg
        exact hg
      have hw2 : smul n (inner (euclMetric n) (wedge n (pStar n A) γ) B) (omega n) =
                 wedge n (wedge n (pStar n A) γ) (pStar n B) :=
        (wedge_cliffordRightStar_omega (euclMetric n) s hs _ B hw_ag_grade hB).symm
      rw [hw1, hw2, wedge_graded_comm n k (n - r) hγ hstA, smul_wedge, wedge_assoc,
          pStar_smul, pStar_vee, wedge_smul, add_right_neg]
  have hinj := congrArg (pStarInv n) hstar_eq
  rw [pStarInv_pStar, pStarInv_pStar] at hinj
  exact hinj

/-- Exact Dorst/Hestenes Left-Contraction Meet Sign Law:
    For `A ∈ Λ^r(R^n)`, `B ∈ Λ^s(R^n)` with `r, s ≤ n`, `n ≤ r + s`, and `k = r + s - n`:
      `(⋆A) ⌋ B = (-1)^{k(n - r) + (n - r)(n - r - 1)/2} · (A ∨ B)`. -/
theorem dorstLeft_pStar_eq_sign_vee {n r s : Nat}
    (hr : r ≤ n) (hs : s ≤ n) (hrs : n ≤ r + s)
    {A B : Cl R n} (hA : HasGrade n r A) (hB : HasGrade n s B) :
    dorstLeft n (pStar n A) B =
      smul n (CRing.ringParitySign ((r + s - n) * (n - r) + (n - r) * (n - r - 1) / 2))
             (vee n A B) := by
  unfold dorstLeft
  have hstA : HasGrade n (n - r) (pStar n A) := pStar_hasGrade hr hA
  rw [rev_on_grade n (n - r) hstA, cartanLeft_smul_left,
      cartanLeft_pStar_eq_sign_vee hr hs hrs hA hB, smul_smul,
      ← CRing.ringParitySign_add, Nat.add_comm ((n - r) * (n - r - 1) / 2) _]

/-- Unreverted Clifford pseudoscalar meet formula `((A · ω_n⁻¹) ∧ (B · ω_n⁻¹)) · ω_n`
    in Euclidean `Cl_{n,0}` (where `ω_n⁻¹ = ω̃_n`). -/
def veeUnrevertedClifford (n : Nat) (A B : Cl R n) : Cl R n :=
  let q := euclMetric (R := R) n
  let omInv := rev n (omega (R := R) n)
  mul q (wedge n (mul q A omInv) (mul q B omInv)) (omega n)

theorem mul_omega_eq_sign_pStar {n m : Nat} {X : Cl R n} (hX : HasGrade n m X) :
    mul (euclMetric n) X (omega n) =
      smul n (CRing.ringParitySign (m * (m - 1) / 2)) (pStar n X) := by
  unfold pStar cliffordRightStar
  rw [rev_on_grade n m hX, smul_mul, smul_smul, CRing.ringParitySign_sq, one_smul]

/-- Exact Universal Sign Law for the Unreverted Clifford Pseudoscalar Meet:
    For `A ∈ Λ^r(R^n)`, `B ∈ Λ^s(R^n)` with `r, s ≤ n`, `n ≤ r + s`, and `k = r + s - n`:
      `((A · ω_n⁻¹) ∧ (B · ω_n⁻¹)) · ω_n =
         (-1)^{r(r-1)/2 + s(s-1)/2 + (n-k)(n-k-1)/2 + k(n-k)} · (A ∨ B)`. -/
theorem veeUnrevertedClifford_eq_sign_vee {n r s : Nat}
    (hr : r ≤ n) (hs : s ≤ n) (hrs : n ≤ r + s)
    {A B : Cl R n} (hA : HasGrade n r A) (hB : HasGrade n s B) :
    veeUnrevertedClifford n A B =
      smul n (CRing.ringParitySign
        (r * (r - 1) / 2 + s * (s - 1) / 2 +
         (n - (r + s - n)) * ((n - (r + s - n)) - 1) / 2 +
         (r + s - n) * (n - (r + s - n))))
        (vee n A B) := by
  unfold veeUnrevertedClifford
  dsimp only
  rw [rev_on_grade n n (hasGrade_omega n), mul_smul, mul_smul,
      mul_omega_eq_sign_pStar hA, mul_omega_eq_sign_pStar hB,
      smul_smul, smul_smul, smul_wedge, wedge_smul, smul_smul, smul_mul]
  have hcancel :
      CRing.mul (CRing.mul (CRing.ringParitySign (R := R) (n * (n - 1) / 2))
                           (CRing.ringParitySign (R := R) (r * (r - 1) / 2)))
                (CRing.mul (CRing.ringParitySign (R := R) (n * (n - 1) / 2))
                           (CRing.ringParitySign (R := R) (s * (s - 1) / 2))) =
        CRing.ringParitySign (R := R) (r * (r - 1) / 2 + s * (s - 1) / 2) := by
    rw [CRing.mul_assoc (CRing.ringParitySign (n * (n - 1) / 2)) _ _,
        ← CRing.mul_assoc (CRing.ringParitySign (r * (r - 1) / 2)) _ _,
        CRing.mul_comm (CRing.ringParitySign (r * (r - 1) / 2))
                       (CRing.ringParitySign (n * (n - 1) / 2)),
        CRing.mul_assoc (CRing.ringParitySign (n * (n - 1) / 2)) _ _,
        ← CRing.mul_assoc (CRing.ringParitySign (n * (n - 1) / 2))
                          (CRing.ringParitySign (n * (n - 1) / 2)) _,
        CRing.ringParitySign_sq, CRing.one_mul, ← CRing.ringParitySign_add]
  rw [hcancel]
  have hw := wedge_hasGrade n (n - r) (n - s) (pStar_hasGrade hr hA) (pStar_hasGrade hs hB)
  have hm_eq : (n - r) + (n - s) = n - (r + s - n) := by omega
  rw [hm_eq] at hw
  rw [mul_omega_eq_sign_pStar hw]
  change smul n _ (smul n _ (veeForward3Star n A B)) = _
  rw [veeForward3Star_eq_sign_vee hr hs hrs hA hB, smul_smul, smul_smul,
      ← CRing.ringParitySign_add, ← CRing.ringParitySign_add]

end ProjectiveMeetTheory

end Cl
end Conjecture00000007618
