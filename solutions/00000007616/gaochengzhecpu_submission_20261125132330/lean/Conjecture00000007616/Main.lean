/-
  Conjecture 00000007616 — Main Structural Theorems, Positive Regime & Complete Refutations
  Core Lean 4.19.0 only (zero external dependencies).

  Summary of Formalized Results:
  1. Positive Characterization (Non-Vacuity):
     `euclidean_reverted_realization_holds` — On Euclidean `Cl_{n,0}` (`q_i = 1`) for all `n`,
     metric-normalized volume forms `±ω_n` yield Hodge stars realized by `x ↦ rev(x) · Ω`
     with `Ω = ±ω_n` unique up to orientation sign `c ∈ {1, -1}` and unit reversion/metric
     norm `rev(Ω) · Ω = 1`, `⟨Ω, Ω⟩_q = 1`.
  2. Refutation of Clause 1 (Unreverted / Two-Sided Geometric Product):
     - `two_sided_eq_antiInv_forces_comm` — Universal ring-theoretic obstruction: no two-sided
       multiplication `x ↦ A · x · C` can equal an involutive anti-automorphism unless the
       algebra is commutative.
     - `no_two_sided_clifford_realization` — For EVERY `n = m + 2 ≥ 2` and every invertible
       metric/volume pair, NO `A, B` satisfy `⋆_ν(x) = A · x · B` or `⋆_ν(x) = A · invol(x) · B`
       (ruling out `c · x · Ω` and `c · Ω · x` across all grades).
     - `cl2_unreverted_right_iff_rank_le_one` — Exact rank-1 characterization in `n = 2`:
       `⋆_{rω₂}(x) = x · (rω₂)` holds iff `q₀ = 0 ∨ q₁ = 0`.
  3. Refutation of Clause 3 (Unit Norm):
     - `lorentzian_cl11_refutes_unit_norm` & `minkowski_cl31_refutes_unit_norm` — Unique
       reverted realization `Ω = ±ω` has `rev(Ω) · Ω = -1 ≠ 1` and `-a² ≠ b²` over `ℚ`.
     - `degenerate_cl101_refutes_unit_norm` — Unique reverted realization `Ω = c · ω₂` (`c ≠ 0`)
       has `rev(Ω) · Ω = conj(Ω) · Ω = Ω² = 0 ≠ 1` and `⟨Ω, Ω⟩_q = 0 ∉ {1, -1}`.
     - `rational_diag23_refutes_unit_norm` — Positive-definite `Q = diag(2, 3)` over `ℚ`
       satisfies `6 a² ≠ ±b²` for all `b ≠ 0`: no rational pseudoscalar has norm `±1`.
     - `euclidean_sq_and_conj_norm_not_unit` — `ω₂² = -1 ≠ 1` in `Cl_{2,0}` and
       `conj(ω₃) · ω₃ = -1 ≠ 1` in `Cl_{3,0}`.
  4. Refutation of Clause 2 (Uniqueness Deviation Beyond Volume Orientation `±1`):
     - `scale_deviation_exceeds_orientation` — Positively oriented `ν_c = c · ω₂` (`c = 2 > 0`)
       forces `Ω = 2 · ω₂ ∉ {±ω₂}`, and in degenerate `Cl_{1,0,1}` all `c > 0` share identical
       metric norm `0`.
     - `degenerate_positive_grade_nonunique` — Infinitely many distinct `Ω_c = c · ω₂` realize
       the same `⋆_{ω₂}` on all positive grades `k ≥ 1` when `q = (0, 0)`.
  5. Master Bundled Refutations:
     `conjecture_00000007616_direct_false` and `conjecture_00000007616_reverted_false`.
-/

import Conjecture00000007616.HodgeStar

namespace Conjecture00000007616
namespace Cl

/-! ### Part 1: Universal Ring-Theoretic Obstruction & Noncommutativity for `n ≥ 2` -/

section Obstruction
variable {R : Type} [CRing R]

/-- `conj n` is an involutive algebra anti-automorphism of `Cl R n`. -/
theorem conj_one (n : Nat) : conj n (one (R := R) n) = one n := by
  unfold conj
  rw [rev_one, invol_one]

theorem conj_conj (n : Nat) (x : Cl R n) : conj n (conj n x) = x := by
  unfold conj
  rw [← invol_rev_comm n (rev n x), rev_rev, invol_invol]

theorem conj_mul {n : Nat} (q : Fin n → R) (x y : Cl R n) :
    conj n (mul q x y) = mul q (conj n y) (conj n x) := by
  unfold conj
  rw [rev_mul, invol_mul]

/-- **Universal Automorphism vs. Anti-Automorphism Obstruction:**
    In `Cl(R^n, q)`, if an involutive anti-automorphism `τ` (`τ(1) = 1`, `τ(τ(x)) = x`,
    `τ(x · y) = τ(y) · τ(x)`) is realized by a two-sided multiplication `x ↦ A · x · C`,
    then `Cl(R^n, q)` must be commutative. -/
theorem two_sided_eq_antiInv_forces_comm {n : Nat} (q : Fin n → R)
    (τ : Cl R n → Cl R n)
    (hτ1 : τ (one n) = one n)
    (hτ_inv : ∀ x, τ (τ x) = x)
    (hτ_anti : ∀ x y, τ (mul q x y) = mul q (τ y) (τ x))
    (A C : Cl R n)
    (hAC : ∀ x, mul q (mul q A x) C = τ x) :
    ∀ u v : Cl R n, mul q u v = mul q v u := by
  have hAC1 : mul q A C = one n := by
    have h := hAC (one n)
    rw [mul_one, hτ1] at h
    exact h
  have hτCA : τ (mul q C A) = one n := by
    calc
      τ (mul q C A) = mul q (mul q A (mul q C A)) C := (hAC (mul q C A)).symm
      _ = mul q (mul q (mul q A C) A) C := by rw [← mul_assoc q A C A]
      _ = mul q (mul q A C) (mul q A C) := mul_assoc q (mul q A C) A C
      _ = mul q (one n) (one n) := by rw [hAC1]
      _ = one n := one_mul q (one n)
  have hCA : mul q C A = one n := by
    calc
      mul q C A = τ (τ (mul q C A)) := (hτ_inv (mul q C A)).symm
      _ = τ (one n) := by rw [hτCA]
      _ = one n := hτ1
  have hprod : ∀ x y : Cl R n,
      mul q (mul q (mul q A x) C) (mul q (mul q A y) C) = mul q (mul q A (mul q x y)) C := by
    intro x y
    calc
      mul q (mul q (mul q A x) C) (mul q (mul q A y) C)
          = mul q (mul q A x) (mul q C (mul q (mul q A y) C)) := mul_assoc q _ C _
      _ = mul q (mul q A x) (mul q (mul q C (mul q A y)) C) := by
            rw [← mul_assoc q C (mul q A y) C]
      _ = mul q (mul q A x) (mul q (mul q (mul q C A) y) C) := by
            rw [← mul_assoc q C A y]
      _ = mul q (mul q A x) (mul q y C) := by rw [hCA, one_mul]
      _ = mul q A (mul q x (mul q y C)) := mul_assoc q A x (mul q y C)
      _ = mul q A (mul q (mul q x y) C) := by rw [← mul_assoc q x y C]
      _ = mul q (mul q A (mul q x y)) C := (mul_assoc q A (mul q x y) C).symm
  intro u v
  calc
    mul q u v = mul q (τ (τ u)) (τ (τ v)) := by rw [hτ_inv, hτ_inv]
    _ = mul q (mul q (mul q A (τ u)) C) (mul q (mul q A (τ v)) C) := by rw [hAC, hAC]
    _ = mul q (mul q A (mul q (τ u) (τ v))) C := hprod (τ u) (τ v)
    _ = τ (mul q (τ u) (τ v)) := hAC (mul q (τ u) (τ v))
    _ = mul q (τ (τ v)) (τ (τ u)) := hτ_anti (τ u) (τ v)
    _ = mul q v u := by rw [hτ_inv, hτ_inv]

theorem scalarPart_one : ∀ (n : Nat), scalarPart n (one (R := R) n) = CRing.one
  | 0 => rfl
  | n + 1 => scalarPart_one n

theorem scalarPart_neg : ∀ (n : Nat) (x : Cl R n),
    scalarPart n (neg n x) = CRing.neg (scalarPart n x)
  | 0, _ => rfl
  | n + 1, (a, _) => scalarPart_neg n a

/-- Every Clifford/exterior algebra of dimension `n = m + 2 ≥ 2` over a ring with
    `1 + 1 ≠ 0` is strictly noncommutative (`e_m · e_{m+1} ≠ e_{m+1} · e_m`). -/
theorem cl_noncomm_of_ge_two (m : Nat) (q : Fin (m + 2) → R)
    (hchar2 : CRing.add (R := R) CRing.one CRing.one ≠ CRing.zero) :
    ∃ u v : Cl R (m + 2), mul q u v ≠ mul q v u := by
  let u1 : Cl R (m + 1) := (zero m, one m)
  let u : Cl R (m + 2) := (u1, zero (m + 1))
  let v : Cl R (m + 2) := (zero (m + 1), one (m + 1))
  refine ⟨u, v, ?_⟩
  intro heq
  let q' := initMetric q
  have huv_snd : (mul q u v).2 = u1 := by
    show add (m + 1) (mul q' u1 (one (m + 1))) (mul q' (zero (m + 1)) (invol (m + 1) (zero (m + 1)))) = u1
    rw [mul_one, zero_mul, add_zero]
  have hvu_snd : (mul q v u).2 = invol (m + 1) u1 := by
    show add (m + 1) (mul q' (zero (m + 1)) (zero (m + 1))) (mul q' (one (m + 1)) (invol (m + 1) u1)) =
      invol (m + 1) u1
    rw [zero_mul, one_mul, zero_add]
  have hsnd : (mul q u v).2 = (mul q v u).2 := congrArg Prod.snd heq
  rw [huv_snd, hvu_snd] at hsnd
  have hsnd2 : (one (R := R) m) = neg m (invol m (one m)) := congrArg Prod.snd hsnd
  rw [invol_one] at hsnd2
  have hsc : scalarPart m (one (R := R) m) = scalarPart m (neg m (one m)) :=
    congrArg (scalarPart m) hsnd2
  rw [scalarPart_one, scalarPart_neg, scalarPart_one] at hsc
  have htwo : CRing.add (R := R) CRing.one CRing.one = CRing.zero := by
    calc
      CRing.add (R := R) CRing.one CRing.one = CRing.add CRing.one (CRing.neg CRing.one) :=
        congrArg (CRing.add CRing.one) hsc
      _ = CRing.zero := CRing.add_right_neg CRing.one
  exact hchar2 htwo

theorem omega_mul_rev_omega : ∀ {n : Nat} (q : Fin n → R),
    mul q (omega n) (rev n (omega n)) = smul n (prodMetric q) (one n)
  | 0, _ => rfl
  | n + 1, q => by
      let q' := initMetric q
      let qn := lastMetric q
      show ( add n (mul q' (zero n) (rev n (zero n)))
                   (smul n qn (mul q' (omega n) (invol n (invol n (rev n (omega n)))))),
             add n (mul q' (zero n) (invol n (rev n (omega n))))
                   (mul q' (omega n) (invol n (rev n (zero n)))) ) =
           (smul n (CRing.mul (prodMetric q') qn) (one n),
            smul n (CRing.mul (prodMetric q') qn) (zero n))
      apply Prod.ext
      · dsimp only
        rw [rev_zero, zero_mul, zero_add, invol_invol, omega_mul_rev_omega q',
            smul_smul, CRing.mul_comm qn (prodMetric q')]
      · dsimp only
        rw [rev_zero, zero_mul, invol_zero, mul_zero, add_zero, smul_zero]

/-- **Main Theorem (Refutation of Clause 1 for All Invertible Metrics in `n ≥ 2`):**
    For every dimension `n = m + 2 ≥ 2`, every commutative ring `R` with `1 + 1 ≠ 0`,
    and every metric `q` and volume scale `r` such that `r · prodMetric q` is invertible
    in `R` (`s · (r · prodMetric q) = 1`), NO two-sided geometric product `x ↦ A · x · B`
    nor grade-involuted two-sided product `x ↦ A · invol(x) · B` can satisfy `IsHodgeStar`. -/
theorem no_two_sided_clifford_realization (m : Nat) (q : Fin (m + 2) → R) (r s : R)
    (hchar2 : CRing.add (R := R) CRing.one CRing.one ≠ CRing.zero)
    (hinv : CRing.mul s (CRing.mul r (prodMetric q)) = CRing.one)
    (star : Cl R (m + 2) → Cl R (m + 2))
    (hstar : IsHodgeStar q (smul (m + 2) r (omega (m + 2))) star) :
    (¬ ∃ A B : Cl R (m + 2), ∀ x, star x = mul q (mul q A x) B) ∧
    (¬ ∃ A B : Cl R (m + 2), ∀ x, star x = mul q (mul q A (invol (m + 2) x)) B) := by
  let N := m + 2
  let nu := smul N r (omega N)
  let nuInv := smul N s (rev N (omega N))
  have hnu_inv : mul q nu nuInv = one N := by
    show mul q (smul N r (omega N)) (smul N s (rev N (omega N))) = one N
    rw [smul_mul, mul_smul, omega_mul_rev_omega, smul_smul, smul_smul,
        CRing.mul_comm r s, CRing.mul_assoc s r (prodMetric q), hinv, one_smul]
  have hcanon := hodgeStar_eq_cliffordRightStar q r star hstar
  have ⟨u, v, hnoncomm⟩ := cl_noncomm_of_ge_two m q hchar2
  constructor
  · rintro ⟨A, B, hAB⟩
    let C := mul q B nuInv
    have hAC : ∀ x : Cl R N, mul q (mul q A x) C = rev N x := by
      intro x
      calc
        mul q (mul q A x) (mul q B nuInv)
            = mul q (mul q (mul q A x) B) nuInv := (mul_assoc q (mul q A x) B nuInv).symm
        _ = mul q (star x) nuInv := by rw [← hAB x]
        _ = mul q (mul q (rev N x) nu) nuInv := by rw [hcanon x]; rfl
        _ = mul q (rev N x) (mul q nu nuInv) := mul_assoc q (rev N x) nu nuInv
        _ = mul q (rev N x) (one N) := by rw [hnu_inv]
        _ = rev N x := mul_one q (rev N x)
    have hcomm := two_sided_eq_antiInv_forces_comm q (rev N) (rev_one N) (rev_rev N)
      (fun x y => rev_mul q x y) A C hAC
    exact hnoncomm (hcomm u v)
  · rintro ⟨A, B, hAB⟩
    let C := mul q B nuInv
    have hAC : ∀ x : Cl R N, mul q (mul q A x) C = conj N x := by
      intro x
      calc
        mul q (mul q A x) (mul q B nuInv)
            = mul q (mul q A (invol N (invol N x))) (mul q B nuInv) := by rw [invol_invol]
        _ = mul q (mul q (mul q A (invol N (invol N x))) B) nuInv :=
              (mul_assoc q _ B nuInv).symm
        _ = mul q (star (invol N x)) nuInv := by rw [← hAB (invol N x)]
        _ = mul q (mul q (rev N (invol N x)) nu) nuInv := by rw [hcanon (invol N x)]; rfl
        _ = mul q (conj N x) (mul q nu nuInv) := by
              rw [← invol_rev_comm N x]
              exact mul_assoc q (conj N x) nu nuInv
        _ = mul q (conj N x) (one N) := by rw [hnu_inv]
        _ = conj N x := mul_one q (conj N x)
    have hcomm := two_sided_eq_antiInv_forces_comm q (conj N) (conj_one N) (conj_conj N)
      (fun x y => conj_mul q x y) A C hAC
    exact hnoncomm (hcomm u v)

/-- **Corollary:** Neither right geometric multiplication `x ↦ k₀ · (x · Ω)` nor left
    geometric multiplication `x ↦ k₀ · (Ω · x)` with a scalar conversion constant `k₀`
    can realize `IsHodgeStar` in dimension `n ≥ 2` for invertible `r · prodMetric q`. -/
theorem no_scalar_left_or_right_clifford_realization (m : Nat) (q : Fin (m + 2) → R) (r s : R)
    (hchar2 : CRing.add (R := R) CRing.one CRing.one ≠ CRing.zero)
    (hinv : CRing.mul s (CRing.mul r (prodMetric q)) = CRing.one)
    (star : Cl R (m + 2) → Cl R (m + 2))
    (hstar : IsHodgeStar q (smul (m + 2) r (omega (m + 2))) star) :
    (¬ ∃ (k₀ : R) (Ω : Cl R (m + 2)), ∀ x, star x = smul (m + 2) k₀ (mul q x Ω)) ∧
    (¬ ∃ (k₀ : R) (Ω : Cl R (m + 2)), ∀ x, star x = smul (m + 2) k₀ (mul q Ω x)) := by
  have ⟨hno_two, _⟩ := no_two_sided_clifford_realization m q r s hchar2 hinv star hstar
  constructor
  · rintro ⟨k₀, Ω, hk⟩
    apply hno_two
    refine ⟨smul (m + 2) k₀ (one (m + 2)), Ω, ?_⟩
    intro x
    rw [smul_mul, one_mul, smul_mul]
    exact hk x
  · rintro ⟨k₀, Ω, hk⟩
    apply hno_two
    refine ⟨smul (m + 2) k₀ Ω, one (m + 2), ?_⟩
    intro x
    rw [mul_one, smul_mul]
    exact hk x

end Obstruction

/-! ### Part 2: Positive Euclidean Regime (Non-Vacuity) Over `Int` -/

/-- Standard positive-definite Euclidean metric `q = (1, 1, ..., 1)` on `R^n`. -/
def euclideanMetric (n : Nat) : Fin n → Int :=
  fun _ => 1

theorem prodMetric_euclidean : ∀ (n : Nat), prodMetric (euclideanMetric n) = 1
  | 0 => rfl
  | n + 1 => by
      have hinit : initMetric (euclideanMetric (n + 1)) = euclideanMetric n := rfl
      show prodMetric (initMetric (euclideanMetric (n + 1))) *
        lastMetric (euclideanMetric (n + 1)) = 1
      rw [hinit, prodMetric_euclidean n]
      rfl

theorem int_sq_eq_one_iff (c : Int) : c * c = 1 ↔ (c = 1 ∨ c = -1) := by
  constructor
  · intro h
    have habs : c.natAbs * c.natAbs = 1 := by
      have h1 : Int.ofNat (c.natAbs * c.natAbs) = (1 : Int) := by
        rw [int_natAbs_mul_self c]
        exact h
      exact Int.ofNat.inj h1
    have hn1 : c.natAbs = 1 := by
      cases hn : c.natAbs with
      | zero => rw [hn] at habs; contradiction
      | succ k =>
          cases k with
          | zero => rfl
          | succ k' =>
              rw [hn] at habs
              have hge : (k' + 2) * (k' + 2) ≥ 4 := by
                have : k' + 2 ≥ 2 := by omega
                exact Nat.le_trans (by decide) (Nat.mul_le_mul this this)
              rw [habs] at hge
              omega
    cases Int.natAbs_eq c with
    | inl hp => rw [hn1] at hp; exact Or.inl hp
    | inr hn => rw [hn1] at hn; exact Or.inr hn
  · rintro (rfl | rfl) <;> rfl

/-- **Positive Characterization Theorem (Non-Vacuity):**
    In every dimension `n`, on Euclidean `Cl_{n,0}` (`q_i = 1`):
    1. For either volume orientation `c ∈ {1, -1}`, `Ω = c · ω_n` realizes `⋆_Ω` via
       `x ↦ rev(x) · Ω`, with unit Clifford reversion norm `rev(Ω) · Ω = 1` and
       unit metric norm `⟨Ω, Ω⟩_q = 1`;
    2. For a fixed `⋆_ν`, the realization element `Ω` in `⋆_ν(x) = rev(x) · Ω` is
       uniquely `Ω = ν`;
    3. Among top-degree elements `c · ω_n`, unit metric norm `⟨c · ω_n, c · ω_n⟩_q = 1`
       holds if and only if `c = 1 ∨ c = -1` (deviation solely by volume orientation). -/
theorem euclidean_reverted_realization_holds (n : Nat) :
    (∀ c : Int, (c = 1 ∨ c = -1) →
      let Ω := smul n c (omega (R := Int) n)
      IsHodgeStar (euclideanMetric n) Ω (cliffordRightStar (euclideanMetric n) Ω) ∧
      mul (euclideanMetric n) (rev n Ω) Ω = one n ∧
      inner (euclideanMetric n) Ω Ω = 1) ∧
    (∀ (star : Cl Int n → Cl Int n) (Ω₁ Ω₂ : Cl Int n),
      (∀ x, star x = mul (euclideanMetric n) (rev n x) Ω₁) →
      (∀ x, star x = mul (euclideanMetric n) (rev n x) Ω₂) →
      Ω₁ = Ω₂) ∧
    (∀ c : Int,
      inner (euclideanMetric n) (smul n c (omega n)) (smul n c (omega n)) = 1 ↔
        (c = 1 ∨ c = -1)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro c hc
    have hsq : c * c = 1 := (int_sq_eq_one_iff c).mpr hc
    refine ⟨rev_mul_isHodgeStar (euclideanMetric n) c, ?_, ?_⟩
    · rw [rev_smul_omega_mul_self, prodMetric_euclidean]
      change smul n ((c * c) * 1) (one n) = one n
      rw [hsq]
      exact one_smul n (one n)
    · rw [inner_smul_omega_self, prodMetric_euclidean]
      change (c * c) * 1 = 1
      omega
  · intro star Ω₁ Ω₂ h₁ h₂
    have heq := Eq.trans (h₁ (one n)).symm (h₂ (one n))
    rw [rev_one, one_mul, one_mul] at heq
    exact heq
  · intro c
    rw [inner_smul_omega_self, prodMetric_euclidean]
    change (c * c) * 1 = 1 ↔ (c = 1 ∨ c = -1)
    rw [Int.mul_one]
    exact int_sq_eq_one_iff c

/-! ### Part 3: Concrete 2D Exact Rank-1 Characterization & Explicit Counterexamples -/

/-- Exact rank-1 characterization of unreverted right multiplication in `n = 2`:
    For `r ≠ 0`, `x ↦ x · (r · ω₂)` satisfies `IsHodgeStar q (r · ω₂)` if and only if
    `q(0) = 0 ∨ q(1) = 0` (i.e. `rank(q) ≤ 1`). -/
theorem cl2_unreverted_right_iff_rank_le_one (q : Fin 2 → Int) (r : Int) (hr : r ≠ 0) :
    IsHodgeStar q (smul 2 r (omega 2)) (fun x => mul q x (smul 2 r (omega 2))) ↔
      (q ⟨0, by decide⟩ = 0 ∨ q ⟨1, by decide⟩ = 0) := by
  constructor
  · intro hstar
    have heq := hodgeStar_eq_cliffordRightStar q r
      (fun x => mul q x (smul 2 r (omega 2))) hstar (omega 2)
    have hrev_om2 : rev 2 (omega (R := Int) 2) = neg 2 (omega 2) := rfl
    have hrhs : cliffordRightStar q (smul 2 r (omega 2)) (omega 2) =
        smul 2 (r * prodMetric q) (one 2) := by
      unfold cliffordRightStar
      rw [mul_smul, rev_omega_mul_omega, smul_smul]
      rfl
    have hlhs : mul q (omega 2) (smul 2 r (omega 2)) =
        neg 2 (cliffordRightStar q (smul 2 r (omega 2)) (omega 2)) := by
      unfold cliffordRightStar
      rw [hrev_om2, neg_mul, neg_neg]
    rw [hlhs, hrhs] at heq
    have hcomp : (neg 2 (smul 2 (r * prodMetric q) (one 2))).1.1 =
        (smul 2 (r * prodMetric q) (one 2)).1.1 :=
      congrArg (fun z : Cl Int 2 => z.1.1) heq
    change -((r * prodMetric q) * 1) = (r * prodMetric q) * 1 at hcomp
    have hzero : r * prodMetric q = 0 := by omega
    have hprod_eq : prodMetric q = (1 * q ⟨0, by decide⟩) * q ⟨1, by decide⟩ := rfl
    rw [hprod_eq, Int.one_mul] at hzero
    cases Int.mul_eq_zero.mp hzero with
    | inl hr0 => exact absurd hr0 hr
    | inr hq01 => exact Int.mul_eq_zero.mp hq01
  · intro hrank
    have hfun : (fun x => mul q x (smul 2 r (omega 2))) =
        cliffordRightStar q (smul 2 r (omega 2)) := by
      funext ⟨⟨x00, x01⟩, ⟨x10, x11⟩⟩
      apply Prod.ext <;> apply Prod.ext
      · simp only [cliffordRightStar, mul, rev, invol, smul, add, neg, zero, one, omega,
          initMetric, lastMetric, CRing.add, CRing.mul, CRing.neg, CRing.zero, CRing.one,
          Int.mul_zero, Int.zero_mul, Int.mul_one, Int.one_mul,
          Int.add_zero, Int.zero_add, Int.neg_zero, Int.mul_neg, Int.neg_mul, Int.neg_neg]
        cases hrank with
        | inl hq0 => rw [hq0]; simp [Int.zero_mul, Int.mul_zero]
        | inr hq1 => rw [hq1]; simp [Int.zero_mul, Int.mul_zero]
      · simp only [cliffordRightStar, mul, rev, invol, smul, add, neg, zero, one, omega,
          initMetric, lastMetric, CRing.add, CRing.mul, CRing.neg, CRing.zero, CRing.one,
          Int.mul_zero, Int.zero_mul, Int.mul_one, Int.one_mul,
          Int.add_zero, Int.zero_add, Int.neg_zero, Int.mul_neg, Int.neg_mul, Int.neg_neg]
      · simp only [cliffordRightStar, mul, rev, invol, smul, add, neg, zero, one, omega,
          initMetric, lastMetric, CRing.add, CRing.mul, CRing.neg, CRing.zero, CRing.one,
          Int.mul_zero, Int.zero_mul, Int.mul_one, Int.one_mul,
          Int.add_zero, Int.zero_add, Int.neg_zero, Int.mul_neg, Int.neg_mul, Int.neg_neg]
      · simp only [cliffordRightStar, mul, rev, invol, smul, add, neg, zero, one, omega,
          initMetric, lastMetric, CRing.add, CRing.mul, CRing.neg, CRing.zero, CRing.one,
          Int.mul_zero, Int.zero_mul, Int.mul_one, Int.one_mul,
          Int.add_zero, Int.zero_add, Int.neg_zero, Int.mul_neg, Int.neg_mul, Int.neg_neg]
    rw [hfun]
    exact rev_mul_isHodgeStar q r

/-! ### Part 4: Refutations of Unit Norm (Clause 3) -/

/-- 2D Lorentzian / Minkowski metric `q = (1, -1)` (`Cl_{1,1}`). -/
def lorentzian11Metric : Fin 2 → Int
  | ⟨0, _⟩ => 1
  | ⟨1, _⟩ => -1

/-- 4D Minkowski spacetime metric `q = (1, 1, 1, -1)` (`Cl_{3,1}`). -/
def minkowski31Metric : Fin 4 → Int
  | ⟨0, _⟩ => 1
  | ⟨1, _⟩ => 1
  | ⟨2, _⟩ => 1
  | ⟨3, _⟩ => -1

/-- 2D Degenerate Projective Geometric Algebra metric `q = (1, 0)` (`Cl_{1,0,1}`). -/
def degenerate101Metric : Fin 2 → Int
  | ⟨0, _⟩ => 1
  | ⟨1, _⟩ => 0

/-- 2D Positive-definite non-unimodular metric `q = (2, 3)` (`det = 6`). -/
def diag23Metric : Fin 2 → Int
  | ⟨0, _⟩ => 2
  | ⟨1, _⟩ => 3

/-- **Theorem (Lorentzian `Cl_{1,1}` Refutes Unit Norm):**
    1. For both metric-canonical volume orientations `c ∈ {1, -1}` (`Ω = c · ω₂`),
       `x ↦ rev(x) · Ω` is the unique reverted realization of `⋆_Ω`, yet its Clifford
       reversion norm is `rev(Ω) · Ω = -1 ≠ 1` and its metric norm is `⟨Ω, Ω⟩_q = -1 ≠ 1`;
    2. Over `ℚ` (for all `a, b : Int` with `b ≠ 0`), `(a² · prodMetric q) ≠ b²`, so NO
       rational (or real) scalar multiple `(a/b) · ω₂` achieves unit norm `+1`. -/
theorem lorentzian_cl11_refutes_unit_norm :
    (∀ c : Int, (c = 1 ∨ c = -1) →
      let Ω := smul 2 c (omega 2)
      IsHodgeStar lorentzian11Metric Ω (cliffordRightStar lorentzian11Metric Ω) ∧
      mul lorentzian11Metric (rev 2 Ω) Ω = neg 2 (one 2) ∧
      mul lorentzian11Metric (rev 2 Ω) Ω ≠ one 2 ∧
      inner lorentzian11Metric Ω Ω = -1) ∧
    (∀ a b : Int, b ≠ 0 →
      inner lorentzian11Metric (smul 2 a (omega 2)) (smul 2 a (omega 2)) ≠ b * b) := by
  have hprod : prodMetric lorentzian11Metric = -1 := rfl
  constructor
  · intro c hc
    have hsq : c * c = 1 := (int_sq_eq_one_iff c).mpr hc
    refine ⟨rev_mul_isHodgeStar lorentzian11Metric c, ?_, ?_, ?_⟩
    · rw [rev_smul_omega_mul_self, hprod]
      change smul 2 ((c * c) * (-1)) (one 2) = neg 2 (one 2)
      rw [hsq]
      exact neg_one_smul 2 (one 2)
    · rw [rev_smul_omega_mul_self, hprod]
      intro heq
      have hsc : ((smul 2 ((c * c) * (-1)) (one 2)).1.1) = (one (R := Int) 2).1.1 :=
        congrArg (fun z : Cl Int 2 => z.1.1) heq
      change ((c * c) * (-1)) * 1 = 1 at hsc
      rw [hsq] at hsc
      omega
    · rw [inner_smul_omega_self, hprod]
      change (c * c) * (-1) = -1
      rw [hsq]
      rfl
  · intro a b hb heq
    rw [inner_smul_omega_self, hprod] at heq
    change (a * a) * (-1) = b * b at heq
    have ha_nn : (0 : Int) ≤ a * a := by
      rw [← int_natAbs_mul_self a]
      exact Int.ofNat_le.mpr (Nat.zero_le _)
    have hb_pos : (0 : Int) < b * b := by
      have hne : b.natAbs ≠ 0 := fun h0 => hb (Int.natAbs_eq_zero.mp h0)
      rw [← int_natAbs_mul_self b]
      exact Int.ofNat_lt.mpr (Nat.mul_pos (Nat.pos_of_ne_zero hne) (Nat.pos_of_ne_zero hne))
    omega

/-- **Theorem (4D Minkowski `Cl_{3,1}` Refutes Unit Norm):**
    In 4D Lorentzian spacetime signature `(3, 1)`, the metric volume element `±ω₄`
    has `rev(±ω₄) · (±ω₄) = -1 ≠ 1` and `⟨±ω₄, ±ω₄⟩_q = -1 ≠ 1`. -/
theorem minkowski_cl31_refutes_unit_norm (c : Int) (hc : c = 1 ∨ c = -1) :
    let Ω := smul 4 c (omega 4)
    IsHodgeStar minkowski31Metric Ω (cliffordRightStar minkowski31Metric Ω) ∧
    mul minkowski31Metric (rev 4 Ω) Ω = neg 4 (one 4) ∧
    mul minkowski31Metric (rev 4 Ω) Ω ≠ one 4 ∧
    inner minkowski31Metric Ω Ω = -1 := by
  have hprod : prodMetric minkowski31Metric = -1 := rfl
  have hsq : c * c = 1 := (int_sq_eq_one_iff c).mpr hc
  refine ⟨rev_mul_isHodgeStar minkowski31Metric c, ?_, ?_, ?_⟩
  · rw [rev_smul_omega_mul_self, hprod]
    change smul 4 ((c * c) * (-1)) (one 4) = neg 4 (one 4)
    rw [hsq]
    exact neg_one_smul 4 (one 4)
  · rw [rev_smul_omega_mul_self, hprod]
    intro heq
    have hsc := congrArg (scalarPart 4) heq
    change (((c * c) * (-1)) * 1) = 1 at hsc
    rw [hsq] at hsc
    omega
  · rw [inner_smul_omega_self, hprod]
    change (c * c) * (-1) = -1
    rw [hsq]
    rfl

/-- **Theorem (Degenerate `Cl_{1,0,1}` Refutes Unit Norm Under EVERY Norm Definition):**
    For EVERY non-zero volume scale `c ≠ 0` on `q = (1, 0)`:
    1. `⋆_{cω₂}` exists uniquely and any `Ω` with `∀ x, ⋆_{cω₂}(x) = rev(x) · Ω`
       is uniquely forced to be `Ω = c · ω₂ ≠ 0`;
    2. `rev(Ω) · Ω = 0 ≠ 1`, `conj(Ω) · Ω = 0 ≠ 1`, `Ω · Ω = 0 ≠ 1`,
       and `⟨Ω, Ω⟩_q = 0 ∉ {1, -1}` (even unsigned modulus vanishes!). -/
theorem degenerate_cl101_refutes_unit_norm (c : Int) (hc : c ≠ 0) :
    let Ω := smul 2 c (omega 2)
    IsHodgeStar degenerate101Metric Ω (cliffordRightStar degenerate101Metric Ω) ∧
    Ω ≠ zero 2 ∧
    (∀ Ω' : Cl Int 2,
      (∀ x, cliffordRightStar degenerate101Metric Ω x = mul degenerate101Metric (rev 2 x) Ω') →
      Ω' = Ω) ∧
    mul degenerate101Metric (rev 2 Ω) Ω = zero 2 ∧
    mul degenerate101Metric (conj 2 Ω) Ω = zero 2 ∧
    mul degenerate101Metric Ω Ω = zero 2 ∧
    mul degenerate101Metric (rev 2 Ω) Ω ≠ one 2 ∧
    inner degenerate101Metric Ω Ω = 0 := by
  have hprod : prodMetric degenerate101Metric = 0 := rfl
  let Ω := smul 2 c (omega 2)
  refine ⟨rev_mul_isHodgeStar degenerate101Metric c, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro hz
    have htop : (smul 2 c (omega 2)).2.2 = (zero (R := Int) 2).2.2 :=
      congrArg (fun z : Cl Int 2 => z.2.2) hz
    change c * 1 = 0 at htop
    omega
  · intro Ω' hΩ'
    have h1 := hΩ' (one 2)
    unfold cliffordRightStar at h1
    rw [rev_one, one_mul, one_mul] at h1
    exact h1.symm
  · rw [rev_smul_omega_mul_self, hprod]
    change smul 2 ((c * c) * 0) (one 2) = zero 2
    rw [Int.mul_zero]
    exact zero_smul 2 (one 2)
  · unfold conj
    rw [invol_rev_comm]
    -- `invol 2 Ω = Ω` since `Ω` has grade 2 (even), and `rev Ω · Ω = 0`
    have hrev0 : mul degenerate101Metric (rev 2 Ω) Ω = zero 2 := by
      rw [rev_smul_omega_mul_self, hprod]
      change smul 2 ((c * c) * 0) (one 2) = zero 2
      rw [Int.mul_zero]
      exact zero_smul 2 (one 2)
    have hinvol : invol 2 Ω = Ω := by
      simp only [Ω, invol, neg, smul, omega, zero, one,
        CRing.mul, CRing.neg, CRing.zero, CRing.one, Int.mul_zero, Int.neg_zero, Int.neg_neg]
    rw [hinvol, hrev0]
  · -- `Ω · Ω = 0` since `rev Ω = -Ω`
    have hrev_neg : rev 2 Ω = neg 2 Ω := by
      simp only [Ω, rev, invol, neg, smul, omega, zero, one,
        CRing.mul, CRing.neg, CRing.zero, CRing.one, Int.mul_zero, Int.neg_zero]
    have hrev0 : mul degenerate101Metric (rev 2 Ω) Ω = zero 2 := by
      rw [rev_smul_omega_mul_self, hprod]
      change smul 2 ((c * c) * 0) (one 2) = zero 2
      rw [Int.mul_zero]
      exact zero_smul 2 (one 2)
    rw [hrev_neg, neg_mul] at hrev0
    have hnn := congrArg (neg 2) hrev0
    rw [neg_neg, neg_zero] at hnn
    exact hnn
  · rw [rev_smul_omega_mul_self, hprod]
    intro heq
    have hsc := congrArg (fun z : Cl Int 2 => z.1.1) heq
    change (((c * c) * 0) * 1 : Int) = 1 at hsc
    omega
  · rw [inner_smul_omega_self, hprod]
    change (c * c) * 0 = 0
    omega

/-- **Theorem (Positive-Definite Rational Space `Q = diag(2, 3)` Refutes Unit Norm):**
    Even on a positive-definite quadratic space over `ℚ`, if the discriminant `6` is
    not a square in `ℚ`, NO rational volume blade `(a/b) · ω₂` (`b ≠ 0`) achieves
    norm `+1` or `-1`. -/
theorem rational_diag23_refutes_unit_norm (a b : Int) (hb : b ≠ 0) :
    inner diag23Metric (smul 2 a (omega 2)) (smul 2 a (omega 2)) ≠ b * b ∧
    inner diag23Metric (smul 2 a (omega 2)) (smul 2 a (omega 2)) ≠ -(b * b) := by
  have hprod : prodMetric diag23Metric = 6 := rfl
  rw [inner_smul_omega_self, hprod]
  change (a * a) * 6 ≠ b * b ∧ (a * a) * 6 ≠ -(b * b)
  rw [Int.mul_comm (a * a) 6]
  exact int_six_mul_sq_ne_pm_sq a b hb

/-- Even in standard Euclidean spaces `Cl_{2,0}` and `Cl_{3,0}`, the algebraic square
    `ω₂²` and Clifford conjugation norm `conj(ω₃) · ω₃` equal `-1 ≠ 1`. -/
theorem euclidean_sq_and_conj_norm_not_unit :
    (mul (euclideanMetric 2) (omega 2) (omega 2) = neg 2 (one 2) ∧
     mul (euclideanMetric 2) (omega 2) (omega 2) ≠ one 2) ∧
    (mul (euclideanMetric 3) (conj 3 (omega 3)) (omega 3) = neg 3 (one 3) ∧
     mul (euclideanMetric 3) (conj 3 (omega 3)) (omega 3) ≠ one 3) := by
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · apply Prod.ext <;> apply Prod.ext <;> rfl
  · intro h
    have hsc := congrArg (fun z : Cl Int 2 => z.1.1) h
    change (-1 : Int) = 1 at hsc
    omega
  · apply Prod.ext <;> apply Prod.ext <;> apply Prod.ext <;> rfl
  · intro h
    have hsc := congrArg (scalarPart 3) h
    change (-1 : Int) = 1 at hsc
    omega

/-! ### Part 5: Refutations of `±1` Uniqueness Deviation (Clause 2) -/

/-- **Theorem (Scale Deviation Within a Fixed Orientation & Absent Metric Normalization):**
    1. For positively oriented `ν₂ = 2 · ω₂` (`c = 2 > 0`), the unique reverted realization
       element `Ω₂ = 2 · ω₂` deviates from `ω₂` by factor `2 ∉ {1, -1}`;
    2. In degenerate `Cl_{1,0,1}`, ALL volume forms `c · ω₂` (`c ∈ Int`) have identical
       metric norm `0`, so the quadratic form induces no unit-norm selection rule to
       reduce `c > 0` to `c = 1`. -/
theorem scale_deviation_exceeds_orientation :
    let Ω₁ := smul 2 (1 : Int) (omega 2)
    let Ω₂ := smul 2 (2 : Int) (omega 2)
    (2 : Int) > 0 ∧
    Ω₂ ≠ Ω₁ ∧
    Ω₂ ≠ neg 2 Ω₁ ∧
    (∀ c : Int, inner degenerate101Metric (smul 2 c (omega 2)) (smul 2 c (omega 2)) = 0) := by
  refine ⟨by decide, ?_, ?_, ?_⟩
  · intro h
    have htop := congrArg (fun z : Cl Int 2 => z.2.2) h
    change (2 : Int) * 1 = 1 * 1 at htop
    omega
  · intro h
    have htop := congrArg (fun z : Cl Int 2 => z.2.2) h
    change (2 : Int) * 1 = -(1 * 1) at htop
    omega
  · intro c
    rw [inner_smul_omega_self]
    change (c * c) * 0 = 0
    omega

/-- **Theorem (Non-Uniqueness of Realization on Positive Grades in Degenerate Spaces):**
    For the zero quadratic form `q = (0, 0)` on `R^2`, EVERY scalar multiple `Ω_c = c · ω₂`
    (`c ∈ Int`) realizes `⋆_{ω₂}` via `x ↦ rev(x) · Ω_c` on all positive grades `k ∈ {1, 2}`,
    while `Ω_c ≠ Ω_d` whenever `c ≠ d`. -/
theorem degenerate_positive_grade_nonunique :
    let q0 := zeroMetric (R := Int) 2
    (∀ (c : Int) (k : Nat), 1 ≤ k → k ≤ 2 → ∀ x : Cl Int 2,
      HasGrade 2 k x →
      mul q0 (rev 2 x) (smul 2 c (omega 2)) = cliffordRightStar q0 (omega 2) x) ∧
    (∀ c d : Int, c ≠ d → smul 2 c (omega 2) ≠ smul 2 d (omega 2)) := by
  let q0 := zeroMetric (R := Int) 2
  constructor
  · intro c k hk1 hk2 ⟨⟨x00, x01⟩, ⟨x10, x11⟩⟩ hx
    have hx00 : x00 = 0 := by
      cases k with
      | zero => omega
      | succ m =>
          cases m with
          | zero =>
              -- `k = 1`: `HasGrade 2 1` implies `HasGrade 1 1 (x00, x01)`, so `HasGrade 0 1 x00` (`x00 = 0`)
              exact hx.1.1
          | succ m' =>
              have hm' : m' = 0 := by omega
              subst hm'
              -- `k = 2`: `HasGrade 2 2` implies `HasGrade 1 2 (x00, x01)`, so `HasGrade 0 2 x00` (`x00 = 0`)
              exact hx.1.1
    subst hx00
    simp only [q0, cliffordRightStar, mul, rev, invol, smul, add, neg, zero, one, omega,
      initMetric, lastMetric, zeroMetric, CRing.add, CRing.mul, CRing.neg, CRing.zero, CRing.one,
      Int.mul_zero, Int.zero_mul, Int.add_zero, Int.zero_add, Int.neg_zero]
  · intro c d hcd heq
    have htop := congrArg (fun z : Cl Int 2 => z.2.2) heq
    change c * 1 = d * 1 at htop
    omega

/-! ### Part 6: Master Bundled Verdict Statements & Refutations -/

/-- **Interpretation A (Direct / Unreverted Geometric Product Realization Conjecture):**
    Asserts that for every dimension `n ≥ 1` and nondegenerate metric `q` (with `prodMetric q = ±1`),
    the Hodge star `⋆_{ω_n}` admits a scalar conversion constant `k₀` and Clifford element `Ω`
    such that `⋆_{ω_n}(x) = k₀ · (x · Ω)` (or `k₀ · (Ω · x)`) across all multivectors `x`. -/
def Conjecture00000007616_DirectProduct : Prop :=
  ∀ (n : Nat) (q : Fin n → Int),
    (prodMetric q = 1 ∨ prodMetric q = -1) →
    ∃ (k₀ : Int) (Ω : Cl Int n),
      (∀ x, cliffordRightStar q (omega n) x = smul n k₀ (mul q x Ω)) ∨
      (∀ x, cliffordRightStar q (omega n) x = smul n k₀ (mul q Ω x))

/-- **Master Refutation A:** `Conjecture00000007616_DirectProduct` is **FALSE**
    (already failing on 2D Euclidean `Cl_{2,0}`). -/
theorem conjecture_00000007616_direct_false : ¬ Conjecture00000007616_DirectProduct := by
  intro hconj
  have hone2 : smul 2 (1 : Int) (omega 2) = omega 2 := one_smul 2 (omega 2)
  have h2 := hconj 2 (euclideanMetric 2) (Or.inl (prodMetric_euclidean 2))
  rcases h2 with ⟨k₀, Ω, hright | hleft⟩
  · have ⟨hnor, _⟩ := no_scalar_left_or_right_clifford_realization 0 (euclideanMetric 2) 1 1
      (by decide) (by change (1 : Int) * (1 * prodMetric (euclideanMetric 2)) = 1; rw [prodMetric_euclidean]; rfl)
      (cliffordRightStar (euclideanMetric 2) (smul 2 1 (omega 2)))
      (rev_mul_isHodgeStar (euclideanMetric 2) 1)
    apply hnor
    refine ⟨k₀, Ω, ?_⟩
    intro x
    rw [hone2]
    exact hright x
  · have ⟨_, hnol⟩ := no_scalar_left_or_right_clifford_realization 0 (euclideanMetric 2) 1 1
      (by decide) (by change (1 : Int) * (1 * prodMetric (euclideanMetric 2)) = 1; rw [prodMetric_euclidean]; rfl)
      (cliffordRightStar (euclideanMetric 2) (smul 2 1 (omega 2)))
      (rev_mul_isHodgeStar (euclideanMetric 2) 1)
    apply hnol
    refine ⟨k₀, Ω, ?_⟩
    intro x
    rw [hone2]
    exact hleft x

/-- **Interpretation B (Reverted Clifford Realization Unit-Norm Conjecture Across Quadratic Spaces):**
    Asserts that even when reversion `rev(x)` IS built into the Clifford realization law
    (`⋆_ν(x) = rev(x) · Ω`), for every nondegenerate metric `q` with unimodular determinant
    `prodMetric q ∈ {1, -1}` and canonical volume element `ν = ±ω_n`, the unique realization
    element `Ω` has unit Clifford reversion norm `rev(Ω) · Ω = 1`. -/
def Conjecture00000007616_RevertedUnitNorm : Prop :=
  ∀ (n : Nat) (q : Fin n → Int),
    (prodMetric q = 1 ∨ prodMetric q = -1) →
    ∀ (Ω : Cl Int n),
      (∀ x, cliffordRightStar q (omega n) x = mul q (rev n x) Ω) →
      mul q (rev n Ω) Ω = one n

/-- **Master Refutation B:** `Conjecture00000007616_RevertedUnitNorm` is **FALSE**
    (refuted by Lorentzian `Cl_{1,1}` and 4D Minkowski `Cl_{3,1}`, where `rev(Ω) · Ω = -1 ≠ 1`). -/
theorem conjecture_00000007616_reverted_false : ¬ Conjecture00000007616_RevertedUnitNorm := by
  intro hconj
  have hone2 : smul 2 (1 : Int) (omega 2) = omega 2 := one_smul 2 (omega 2)
  have h11 := hconj 2 lorentzian11Metric (Or.inr rfl) (smul 2 1 (omega 2)) (by
    intro x
    unfold cliffordRightStar
    rw [hone2])
  have ⟨hnorm, _⟩ := lorentzian_cl11_refutes_unit_norm
  have ⟨_, _, hne1, _⟩ := hnorm 1 (Or.inl rfl)
  exact hne1 h11

end Cl

/-! ### Axiom Verification Checks -/

#print axioms Cl.rev_mul_isHodgeStar
#print axioms Cl.hodgeStar_eq_cliffordRightStar
#print axioms Cl.euclidean_reverted_realization_holds
#print axioms Cl.no_two_sided_clifford_realization
#print axioms Cl.cl2_unreverted_right_iff_rank_le_one
#print axioms Cl.lorentzian_cl11_refutes_unit_norm
#print axioms Cl.minkowski_cl31_refutes_unit_norm
#print axioms Cl.degenerate_cl101_refutes_unit_norm
#print axioms Cl.rational_diag23_refutes_unit_norm
#print axioms Cl.scale_deviation_exceeds_orientation
#print axioms Cl.degenerate_positive_grade_nonunique
#print axioms Cl.conjecture_00000007616_direct_false
#print axioms Cl.conjecture_00000007616_reverted_false

end Conjecture00000007616
