/-
Copyright (c) 2026. All rights reserved.
 Formalization of Conjecture 00000000593:
 Sharpness, boundary witnesses, and complete classification of alternative readings:
 1. Minimum chain length `r ≥ n` (`(1 - t)^n` never divides shorter chains).
 2. Klein `SL₂(5)` witness: reduced denominator divides a chain of `(1 - t^d)` factors
    but is NOT equal to any product `∏ (1 - t^{d_i})`.
 3. Modular `(𝔽₄, +) ≅ C₂ × C₂` witness: reduced denominator divides `(1 - t^{|G|})^2`
    but NOT `(1 - t^{exp(G)})^2`.
 4. Refutation of hyper-literal index-rationality `m ↦ a_m ∈ ℚ(m)` on `k[x]^{±1}`.
 5. Positive non-vacuity witnesses (`S₃` and Bertin's modular non-Cohen-Macaulay `𝔽₂[V]^{C₄}`).
-/
import Conjecture00000000593.ModularPeriodic

namespace Conjecture00000000593

/-! ### 1. Exact Cancellation of `(1 - t)` and Minimum Chain Length `r ≥ n` -/

theorem cancel_oneMinusT {A B : ZPoly}
    (h : PolyEq (mul (oneMinusTPow 1) A) (mul (oneMinusTPow 1) B)) :
    PolyEq A B := by
  have hser : ∀ m : Nat,
      shiftSub 1 (mulPolySeries A unitSeries) m =
        shiftSub 1 (mulPolySeries B unitSeries) m := by
    intro m
    rw [← mulPolySeries_oneMinusTPow (by omega : 1 ≤ 1)]
    rw [← mulPolySeries_oneMinusTPow (by omega : 1 ≤ 1)]
    rw [← mulPolySeries_mul, ← mulPolySeries_mul]
    rw [mulPolySeries_unit, mulPolySeries_unit]
    exact h m
  intro m
  induction m with
  | zero =>
    have h0 := hser 0
    unfold shiftSub at h0
    simp only [Nat.zero_lt_one, ↓reduceIte, mulPolySeries_unit] at h0
    exact h0
  | succ m' ih =>
    have hm := hser (m' + 1)
    unfold shiftSub at hm
    have hlt : ¬ (m' + 1 < 1) := by omega
    have hsub : m' + 1 - 1 = m' := by omega
    simp only [hlt, ↓reduceIte, hsub, mulPolySeries_unit] at hm
    omega

theorem cancel_replicate_oneMinusT :
    ∀ (k : Nat) {A B : ZPoly},
      PolyEq (mul (chainProd (List.replicate k 1)) A)
             (mul (chainProd (List.replicate k 1)) B) →
      PolyEq A B
  | 0, A, B, h => by
      intro m
      rw [← mulPolySeries_unit A m, ← mulPolySeries_unit B m]
      have hA : mulPolySeries (mul [1] A) unitSeries m = mulPolySeries A unitSeries m := by
        rw [mulPolySeries_mul, mulPolySeries_one_poly]
      have hB : mulPolySeries (mul [1] B) unitSeries m = mulPolySeries B unitSeries m := by
        rw [mulPolySeries_mul, mulPolySeries_one_poly]
      rw [← hA, ← hB, mulPolySeries_unit, mulPolySeries_unit]
      exact h m
  | k + 1, A, B, h => by
      simp only [List.replicate_succ, chainProd] at h
      have hassocA := mul_assoc_polyEq (oneMinusTPow 1) (chainProd (List.replicate k 1)) A
      have hassocB := mul_assoc_polyEq (oneMinusTPow 1) (chainProd (List.replicate k 1)) B
      have h' : PolyEq
          (mul (oneMinusTPow 1) (mul (chainProd (List.replicate k 1)) A))
          (mul (oneMinusTPow 1) (mul (chainProd (List.replicate k 1)) B)) :=
        polyEq_trans (polyEq_symm hassocA) (polyEq_trans h hassocB)
      exact cancel_replicate_oneMinusT k (cancel_oneMinusT h')

/-- Product of geometric factors `∏_{d ∈ ds} (1 + t + ... + t^{d-1})`. -/
def geomChainProd : List Nat → ZPoly
  | [] => [1]
  | d :: ds => mul (geomSum 1 d) (geomChainProd ds)

theorem eval_geomChainProd_one :
    ∀ {ds : List Nat}, (∀ d ∈ ds, 1 ≤ d) →
      eval (geomChainProd ds) 1 = ds.foldr (fun d acc => Int.ofNat d * acc) 1
  | [], _ => rfl
  | d :: ds, h => by
      have hds : ∀ x ∈ ds, 1 ≤ x := fun x hx => h x (List.mem_cons_of_mem d hx)
      simp only [geomChainProd, List.foldr_cons]
      rw [eval_mul, eval_geomSum_one, eval_geomChainProd_one hds]

theorem eval_geomChainProd_one_pos :
    ∀ {ds : List Nat}, (∀ d ∈ ds, 1 ≤ d) → 1 ≤ eval (geomChainProd ds) 1
  | [], _ => by decide
  | d :: ds, h => by
      have hd : 1 ≤ d := h d (List.mem_cons_self ..)
      have hds : ∀ x ∈ ds, 1 ≤ x := fun x hx => h x (List.mem_cons_of_mem d hx)
      simp only [geomChainProd]
      rw [eval_mul, eval_geomSum_one]
      have ih := eval_geomChainProd_one_pos hds
      simp only [Int.ofNat_eq_coe]
      have hd_int : (1 : Int) ≤ (d : Int) := by omega
      have hprod : 1 * 1 ≤ (d : Int) * eval (geomChainProd ds) 1 :=
        Int.mul_le_mul hd_int ih (by omega) (by omega)
      omega

theorem chainProd_eq_pow_mul_geomChainProd :
    ∀ {ds : List Nat}, (∀ d ∈ ds, 1 ≤ d) →
      PolyEq (chainProd ds) (mul (chainProd (List.replicate ds.length 1)) (geomChainProd ds))
  | [], _ => by
      intro m
      simp only [List.length_nil, List.replicate, chainProd, geomChainProd]
      cases m <;> rfl
  | d :: ds, h => by
      have hd : 1 ≤ d := h d (List.mem_cons_self ..)
      have hds : ∀ x ∈ ds, 1 ≤ x := fun x hx => h x (List.mem_cons_of_mem d hx)
      simp only [List.length_cons, List.replicate_succ, chainProd, geomChainProd]
      have h1 : PolyEq (oneMinusTPow d) (mul (oneMinusTPow 1) (geomSum 1 d)) := by
        have hg := mul_oneMinusTPow_geomSum (by omega : 1 ≤ 1) d
        rw [Nat.one_mul] at hg
        exact polyEq_symm hg
      have ih := chainProd_eq_pow_mul_geomChainProd hds
      let P1 := oneMinusTPow 1
      let Gd := geomSum 1 d
      let Pk := chainProd (List.replicate ds.length 1)
      let Gds := geomChainProd ds
      have step1 : PolyEq (mul (oneMinusTPow d) (chainProd ds)) (mul (mul P1 Gd) (mul Pk Gds)) :=
        mul_congr h1 ih
      have step2 : PolyEq (mul (mul P1 Gd) (mul Pk Gds)) (mul P1 (mul Gd (mul Pk Gds))) :=
        mul_assoc_polyEq P1 Gd (mul Pk Gds)
      have step3 : PolyEq (mul Gd (mul Pk Gds)) (mul Pk (mul Gd Gds)) := by
        exact polyEq_trans (polyEq_symm (mul_assoc_polyEq Gd Pk Gds))
          (polyEq_trans (mul_congr (mul_comm_polyEq Gd Pk) (polyEq_refl Gds))
            (mul_assoc_polyEq Pk Gd Gds))
      have step4 : PolyEq (mul P1 (mul Gd (mul Pk Gds))) (mul P1 (mul Pk (mul Gd Gds))) :=
        mul_congr (polyEq_refl P1) step3
      have step5 : PolyEq (mul P1 (mul Pk (mul Gd Gds))) (mul (mul P1 Pk) (mul Gd Gds)) :=
        polyEq_symm (mul_assoc_polyEq P1 Pk (mul Gd Gds))
      exact polyEq_trans step1 (polyEq_trans step2 (polyEq_trans step4 step5))

theorem replicate_add_eq {α : Type} (a b : Nat) (x : α) :
    List.replicate (a + b) x = List.replicate a x ++ List.replicate b x := by
  induction a with
  | zero =>
    rw [Nat.zero_add]
    rfl
  | succ a' ih =>
    rw [Nat.succ_add]
    change x :: List.replicate (a' + b) x = x :: (List.replicate a' x ++ List.replicate b x)
    rw [ih]

theorem int_sq_nonneg (z : Int) : 0 ≤ z * z := by
  by_cases hz : 0 ≤ z
  · exact Int.mul_nonneg hz hz
  · have hneg : 0 ≤ -z := by omega
    have hp : 0 ≤ (-z) * (-z) := Int.mul_nonneg hneg hneg
    rw [Int.neg_mul_neg] at hp
    exact hp

/-- **Minimum Chain Length Theorem (`r ≥ n`):**
If `(1 - t)^n` divides `∏_{d ∈ ds} (1 - t^d)` (`∀ d ∈ ds, 1 ≤ d`), then `n ≤ ds.length`.
In particular, for `n ≥ 2`, `(1 - t)^n` never divides a single factor `1 - t^d`. -/
theorem chain_length_ge_vars {n : Nat} {ds : List Nat}
    (hds : ∀ d ∈ ds, 1 ≤ d)
    (hdvd : PolyDvd (chainProd (List.replicate n 1)) (chainProd ds)) :
    n ≤ ds.length := by
  apply Decidable.byContradiction
  intro hlt
  have hgt : ds.length < n := by omega
  rcases hdvd with ⟨R, hR⟩
  have hsplit : n = ds.length + (n - ds.length) := by omega
  have hrem_pos : ∃ k : Nat, n - ds.length = k + 1 := ⟨n - ds.length - 1, by omega⟩
  rcases hrem_pos with ⟨k, hk⟩
  have hrep : List.replicate n 1 = List.replicate ds.length 1 ++ List.replicate (k + 1) 1 := by
    rw [hsplit, hk, replicate_add_eq]
  have hchain_app : ∀ (a b : Nat),
      PolyEq (chainProd (List.replicate a 1 ++ List.replicate b 1))
             (mul (chainProd (List.replicate a 1)) (chainProd (List.replicate b 1))) := by
    intro a b
    induction a with
    | zero =>
      simp only [List.replicate, List.nil_append, chainProd]
      intro m
      rw [← mulPolySeries_unit _ m, ← mulPolySeries_unit _ m, mulPolySeries_mul, mulPolySeries_one_poly]
    | succ a' iha =>
      simp only [List.replicate_succ, List.cons_append, chainProd]
      exact polyEq_trans (mul_congr (polyEq_refl (oneMinusTPow 1)) iha)
        (polyEq_symm (mul_assoc_polyEq (oneMinusTPow 1) (chainProd (List.replicate a' 1)) _))
  have hR2 : PolyEq
      (mul (chainProd (List.replicate ds.length 1)) (geomChainProd ds))
      (mul (chainProd (List.replicate ds.length 1)) (mul (chainProd (List.replicate (k + 1) 1)) R)) := by
    apply polyEq_trans (polyEq_symm (chainProd_eq_pow_mul_geomChainProd hds))
    apply polyEq_trans hR
    rw [hrep]
    exact polyEq_trans (mul_congr (hchain_app ds.length (k + 1)) (polyEq_refl R))
      (mul_assoc_polyEq (chainProd (List.replicate ds.length 1)) _ R)
  have hcanc := cancel_replicate_oneMinusT ds.length hR2
  have hev := eval_eq_of_polyEq hcanc 1
  simp only [List.replicate_succ, chainProd] at hev
  rw [eval_mul, eval_mul, eval_oneMinusTPow_one] at hev
  have hpos := eval_geomChainProd_one_pos hds
  omega

theorem not_dvd_single_factor {n d : Nat} (hn : 2 ≤ n) (hd : 1 ≤ d) :
    ¬ PolyDvd (chainProd (List.replicate n 1)) (oneMinusTPow d) := by
  intro hdvd
  have h1 : PolyDvd (oneMinusTPow d) (chainProd [d]) := by
    refine ⟨[1], ?_⟩
    simp only [chainProd]
    exact polyEq_refl (mul (oneMinusTPow d) [1])
  have hdvd' : PolyDvd (chainProd (List.replicate n 1)) (chainProd [d]) :=
    polyDvd_trans hdvd h1
  have hle := chain_length_ge_vars (fun x hx => by rcases List.mem_singleton.mp hx with rfl; exact hd) hdvd'
  simp at hle
  omega

/-! ### 2. Klein `SL₂(5)` Witness: "Dividing" Cannot Be Strengthened to "Equal To" -/

/-- Reduced numerator `P_ico(t)` of `H(ℂ[x,y]^{SL₂(5)}, t) = (1 + t^30) / ((1 - t^12)(1 - t^20))`. -/
def P_ico : ZPoly :=
  [1, 0, 1, 0, 0, 0, -1, 0, -1, 0, -1, 0, 0, 0, 1, 0, 1]

/-- Reduced denominator `Q_ico(t)` of `H(ℂ[x,y]^{SL₂(5)}, t)` (degree 18). -/
def Q_ico : ZPoly :=
  [1, 0, 1, 0, 0, 0, -1, 0, -1, 0, -1, 0, -1, 0, 0, 0, 1, 0, 1]

/-- Bézout cofactors certifying `U_ico * P_ico + V_ico * Q_ico = 1` in `ℤ[t]`. -/
def U_ico : ZPoly := [1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, -1]
def V_ico : ZPoly := [0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 1]

/-- Cofactor `C_ico = Φ₄ Φ₁₂ Φ₂₀` such that `Q_ico * C_ico = (1 - t^12)(1 - t^20)`. -/
def C_ico : ZPoly := [1, 0, -1, 0, 1, 0, 0, 0, 0, 0, 1, 0, -1, 0, 1]

/-- Quotient `G_ico(t) = Q_ico(t) / (1 - t)^2` (`G_ico(1) = 120 = |SL₂(5)|`). -/
def G_ico : ZPoly := [1, 2, 4, 6, 8, 10, 11, 12, 12, 12, 11, 10, 8, 6, 4, 2, 1]

theorem klein_coprime_bezout : add (mul U_ico P_ico) (mul V_ico Q_ico) = [1] ++ List.replicate 28 0 := by
  decide

theorem klein_coprime_polyEq : PolyEq (add (mul U_ico P_ico) (mul V_ico Q_ico)) [1] := by
  intro m
  rw [klein_coprime_bezout]
  cases m with
  | zero => rfl
  | succ m' =>
    simp only [List.singleton_append, coeff]
    have hzero : ∀ (k n : Nat), coeff (List.replicate k 0) n = 0 := by
      intro k
      induction k with
      | zero => intro _; rfl
      | succ k' ih =>
        intro n
        cases n with
        | zero => rfl
        | succ n' => exact ih n'
    exact hzero 28 m'

theorem klein_divides_12_20 : PolyDvd Q_ico (chainProd [12, 20]) := by
  refine ⟨C_ico, ?_⟩
  have heq : chainProd [12, 20] = mul Q_ico C_ico := by decide
  exact polyEq_of_eq heq

theorem klein_divides_strict_chain_12_60 :
    IsDivChain [12, 60] ∧ IsStrictIncPos [12, 60] ∧ PolyDvd Q_ico (chainProd [12, 60]) := by
  refine ⟨IsDivChain.cons ⟨5, by decide⟩ (IsDivChain.single 60),
          IsStrictIncPos.cons (by decide) (by decide) (IsStrictIncPos.single (by decide)),
          ?_⟩
  have hpwd : PointwiseDvd [12, 20] [12, 60] :=
    PointwiseDvd.cons (by decide) ⟨1, by decide⟩
      (PointwiseDvd.cons (by decide) ⟨3, by decide⟩ PointwiseDvd.nil)
  exact polyDvd_trans klein_divides_12_20 (chainProd_dvd_of_pointwiseDvd hpwd)

theorem klein_factor_oneMinusT_sq : Q_ico = mul (chainProd [1, 1]) G_ico := by
  decide

theorem coeff_chainProd_two_top {d₁ d₂ : Nat} (h₁ : 1 ≤ d₁) (h₂ : 1 ≤ d₂) :
    coeff (chainProd [d₁, d₂]) (d₁ + d₂) = 1 := by
  rw [← mulPolySeries_unit (chainProd [d₁, d₂]) (d₁ + d₂)]
  have hpos : ∀ d ∈ [d₁, d₂], 1 ≤ d := by
    intro d hd
    rcases List.mem_cons.mp hd with rfl | htail
    · exact h₁
    · rcases List.mem_singleton.mp htail with rfl
      exact h₂
  rw [mulPolySeries_chainProd hpos unitSeries]
  simp only [List.foldr, shiftSub, unitSeries]
  have hnot1 : ¬ (d₁ + d₂ < d₁) := by omega
  have hsub1 : d₁ + d₂ - d₁ = d₂ := by omega
  have hnot2 : ¬ (d₁ + d₂ < d₂) := by omega
  have hsub2 : d₁ + d₂ - d₂ = d₁ := by omega
  have hsub3 : d₂ - d₂ = 0 := by omega
  have hnot3 : ¬ (d₂ < d₂) := by omega
  have hnz_sum : d₁ + d₂ ≠ 0 := by omega
  have hnz1 : d₁ ≠ 0 := by omega
  have hnz2 : d₂ ≠ 0 := by omega
  simp [hnot1, hsub1, hnot2, hsub2, hsub3, hnot3, hnz_sum, hnz1, hnz2]

/-- **Sharpness of "Dividing" (Klein `SL₂(5)` Theorem):**
The reduced Molien denominator `Q_ico(t)` is NOT equal in `ℤ[t]` to ANY product
`∏_{d ∈ ds} (1 - t^d)` (`∀ d ∈ ds, 1 ≤ d`), even though it divides `(1 - t^12)(1 - t^60)`. -/
theorem klein_not_equal_any_chain :
    ∀ (ds : List Nat), (∀ d ∈ ds, 1 ≤ d) → ¬ PolyEq Q_ico (chainProd ds) := by
  intro ds hds heq
  have hQ_fac : PolyEq Q_ico (mul (chainProd [1, 1]) G_ico) :=
    polyEq_of_eq klein_factor_oneMinusT_sq
  have hG1 : eval G_ico 1 = 120 := by decide
  cases ds with
  | nil =>
    have hev := eval_eq_of_polyEq heq 1
    have hQ1 : eval Q_ico 1 = 0 := by decide
    have h1 : eval (chainProd []) 1 = 1 := rfl
    omega
  | cons d₁ tail₁ =>
    cases tail₁ with
    | nil =>
      -- ds = [d₁]: cancel one `(1 - t)` and evaluate at `t = 1`
      have hd₁ : 1 ≤ d₁ := hds d₁ (List.mem_cons_self ..)
      have hds_fac := chainProd_eq_pow_mul_geomChainProd hds
      simp only [List.length_singleton, List.replicate] at hds_fac
      have hcomb : PolyEq
          (mul (oneMinusTPow 1) (mul (chainProd [1]) G_ico))
          (mul (oneMinusTPow 1) (mul [1] (geomChainProd [d₁]))) := by
        have hL : PolyEq (mul (chainProd [1, 1]) G_ico)
            (mul (oneMinusTPow 1) (mul (chainProd [1]) G_ico)) :=
          mul_assoc_polyEq (oneMinusTPow 1) (chainProd [1]) G_ico
        have hR : PolyEq (mul (chainProd [1]) (geomChainProd [d₁]))
            (mul (oneMinusTPow 1) (mul [1] (geomChainProd [d₁]))) :=
          mul_assoc_polyEq (oneMinusTPow 1) [1] (geomChainProd [d₁])
        exact polyEq_trans (polyEq_symm hL)
          (polyEq_trans (polyEq_symm hQ_fac) (polyEq_trans heq (polyEq_trans hds_fac hR)))
      have hc := cancel_oneMinusT hcomb
      have hev := eval_eq_of_polyEq hc 1
      simp only [chainProd, geomChainProd] at hev
      rw [eval_mul, eval_mul, eval_oneMinusTPow_one, eval_mul, eval_mul, eval_geomSum_one] at hev
      simp only [eval, Int.ofNat_eq_coe] at hev
      omega
    | cons d₂ tail₂ =>
      cases tail₂ with
      | nil =>
        -- ds = [d₁, d₂]: `d₁ * d₂ = 120` from `G_ico(1) = 120`, while `d₁ + d₂ ≤ 18` from degree!
        have hd₁ : 1 ≤ d₁ := hds d₁ (List.mem_cons_self ..)
        have hd₂ : 1 ≤ d₂ := hds d₂ (List.mem_cons_of_mem d₁ (List.mem_cons_self ..))
        have hds_fac := chainProd_eq_pow_mul_geomChainProd hds
        have hlen2 : [d₁, d₂].length = 2 := rfl
        rw [hlen2] at hds_fac
        have hcomb : PolyEq
            (mul (chainProd (List.replicate 2 1)) G_ico)
            (mul (chainProd (List.replicate 2 1)) (geomChainProd [d₁, d₂])) :=
          polyEq_trans (polyEq_symm hQ_fac) (polyEq_trans heq hds_fac)
        have hc := cancel_replicate_oneMinusT 2 hcomb
        have hev := eval_eq_of_polyEq hc 1
        rw [hG1, eval_geomChainProd_one hds] at hev
        simp only [List.foldr, Int.mul_one, Int.ofNat_eq_coe] at hev
        -- Degree bound: `coeff (chainProd [d₁, d₂]) (d₁ + d₂) = 1`, while `Q_ico.length = 19`
        have htop := heq (d₁ + d₂)
        rw [coeff_chainProd_two_top hd₁ hd₂] at htop
        have hsum_le : d₁ + d₂ ≤ 18 := by
          apply Decidable.byContradiction
          intro hgt
          have hge19 : Q_ico.length ≤ d₁ + d₂ := by
            have hQL : Q_ico.length = 19 := rfl
            omega
          have hz := coeff_gt_length Q_ico (d₁ + d₂) hge19
          omega
        -- Arithmetic contradiction: `d₁ + d₂ ≤ 18` implies `d₁ * d₂ ≤ 81 < 120`
        have hsq_nonneg : 0 ≤ ((d₁ : Int) - (d₂ : Int)) * ((d₁ : Int) - (d₂ : Int)) :=
          int_sq_nonneg ((d₁ : Int) - (d₂ : Int))
        have hsum_int : (d₁ : Int) + (d₂ : Int) ≤ 18 := by omega
        have hsum_sq : ((d₁ : Int) + (d₂ : Int)) * ((d₁ : Int) + (d₂ : Int)) ≤ 18 * 18 :=
          Int.mul_le_mul hsum_int hsum_int (by omega) (by omega)
        have hid : ((d₁ : Int) + (d₂ : Int)) * ((d₁ : Int) + (d₂ : Int)) -
            ((d₁ : Int) - (d₂ : Int)) * ((d₁ : Int) - (d₂ : Int)) =
            4 * ((d₁ : Int) * (d₂ : Int)) := by
          rw [Int.add_mul, Int.mul_add, Int.mul_add, Int.sub_mul, Int.mul_sub, Int.mul_sub]
          rw [Int.mul_comm (d₂ : Int) (d₁ : Int)]
          omega
        omega
      | cons d₃ rest =>
        -- Length ≥ 3: `(1 - t)^3 ∣ chainProd ds = Q_ico`, cancel `(1 - t)^2` and evaluate at `t = 1`
        have hdvd3 : PolyDvd (chainProd (List.replicate 3 1)) (chainProd (d₁ :: d₂ :: d₃ :: rest)) := by
          have hds_fac := chainProd_eq_pow_mul_geomChainProd hds
          have hlen : (d₁ :: d₂ :: d₃ :: rest).length = 3 + rest.length := by simp; omega
          rw [hlen, replicate_add_eq] at hds_fac
          have happ : PolyEq
              (chainProd (List.replicate 3 1 ++ List.replicate rest.length 1))
              (mul (chainProd (List.replicate 3 1)) (chainProd (List.replicate rest.length 1))) := by
            simp only [List.replicate_succ, List.cons_append, List.nil_append, chainProd]
            -- Associate the 3 leading factors of `oneMinusTPow 1`:
            let P1 := oneMinusTPow 1
            let Pr := chainProd (List.replicate rest.length 1)
            have s1 := polyEq_symm (mul_assoc_polyEq P1 [1] Pr)
            have u1 : PolyEq (mul [1] Pr) Pr := by
              intro m
              rw [← mulPolySeries_unit _ m, ← mulPolySeries_unit _ m, mulPolySeries_mul, mulPolySeries_one_poly]
            have s2 : PolyEq (mul P1 Pr) (mul (mul P1 [1]) Pr) :=
              polyEq_trans (mul_congr (polyEq_refl P1) (polyEq_symm u1)) s1
            have s3 : PolyEq (mul P1 (mul P1 Pr)) (mul (mul P1 (mul P1 [1])) Pr) :=
              polyEq_trans (mul_congr (polyEq_refl P1) s2) (polyEq_symm (mul_assoc_polyEq P1 (mul P1 [1]) Pr))
            exact polyEq_trans (mul_congr (polyEq_refl P1) s3)
              (polyEq_symm (mul_assoc_polyEq P1 (mul P1 (mul P1 [1])) Pr))
          exact ⟨mul (chainProd (List.replicate rest.length 1)) (geomChainProd (d₁ :: d₂ :: d₃ :: rest)),
            polyEq_trans hds_fac (polyEq_trans (mul_congr happ (polyEq_refl _))
              (mul_assoc_polyEq (chainProd (List.replicate 3 1)) _ _))⟩
        rcases hdvd3 with ⟨R, hR⟩
        have hcomb : PolyEq
            (mul (chainProd (List.replicate 2 1)) G_ico)
            (mul (chainProd (List.replicate 2 1)) (mul (oneMinusTPow 1) R)) := by
          have h3 : PolyEq (mul (chainProd (List.replicate 3 1)) R)
              (mul (chainProd (List.replicate 2 1)) (mul (oneMinusTPow 1) R)) := by
            let P1 := oneMinusTPow 1
            -- `chainProd [1, 1, 1] = P1 * (P1 * (P1 * [1]))` and `chainProd [1, 1] = P1 * (P1 * [1])`
            have h111 : PolyEq (chainProd (List.replicate 3 1))
                (mul (chainProd (List.replicate 2 1)) P1) :=
              polyEq_of_eq (by decide)
            exact polyEq_trans (mul_congr h111 (polyEq_refl R))
              (mul_assoc_polyEq (chainProd (List.replicate 2 1)) P1 R)
          exact polyEq_trans (polyEq_symm hQ_fac) (polyEq_trans heq (polyEq_trans hR h3))
        have hc := cancel_replicate_oneMinusT 2 hcomb
        have hev := eval_eq_of_polyEq hc 1
        rw [hG1, eval_mul, eval_oneMinusTPow_one] at hev
        omega

/-! ### 3. Modular `(𝔽₄, +) ≅ C₂ × C₂` Witness: `exp(G)` Fails While `|G|` Succeeds -/

/-- Denominator `Q_mod(t) = (1 - t)(1 - t^4)` of `𝔽₄[x, y]^{(𝔽₄, +)}` (`|G| = 4`, `exp(G) = 2`). -/
def Q_mod : ZPoly := chainProd [1, 4]

theorem top_nonzero_degree_le {P R : ZPoly} {dp : Nat}
    (hdp : coeff P dp ≠ 0) (hp_hi : ∀ m : Nat, dp < m → coeff P m = 0)
    (hprod_zero : ∃ n₀ : Nat, coeff (mul P R) n₀ ≠ 0) :
    ∃ top : Nat, dp ≤ top ∧ coeff (mul P R) top ≠ 0 := by
  -- Find the largest nonzero index `kr` of `R` (bounded by `R.length`):
  have hex_R : ∃ kr : Nat, coeff R kr ≠ 0 ∧ ∀ m : Nat, kr < m → coeff R m = 0 := by
    induction R with
    | nil =>
      rcases hprod_zero with ⟨n₀, hn₀⟩
      have hz := mul_nil_right P n₀
      rw [hz] at hn₀
      contradiction
    | cons r rs _ =>
      by_cases hrs_all : ∀ m : Nat, coeff rs m = 0
      · by_cases hr0 : r = 0
        · exfalso
          rcases hprod_zero with ⟨n₀, hn₀⟩
          have hall0 : ∀ m : Nat, coeff (r :: rs) m = 0 := by
            intro m
            cases m with
            | zero => exact hr0
            | succ m' => exact hrs_all m'
          have hmul0 : mulPolySeries (mul P (r :: rs)) unitSeries n₀ = 0 := by
            rw [mulPolySeries_mul]
            have hR0 : mulPolySeries (r :: rs) unitSeries = fun _ => 0 := by
              funext k
              rw [mulPolySeries_unit, hall0 k]
            rw [hR0]
            have hzero_ser : ∀ (Q : ZPoly) (k : Nat), mulPolySeries Q (fun _ => 0) k = 0 := by
              intro Q
              induction Q with
              | nil => intro _; rfl
              | cons q qs ihq =>
                intro k
                cases k with
                | zero => simp [mulPolySeries]
                | succ k' => simp [mulPolySeries, ihq k']
            exact hzero_ser P n₀
          rw [mulPolySeries_unit] at hmul0
          exact hn₀ hmul0
        · refine ⟨0, hr0, ?_⟩
          intro m hm
          cases m with
          | zero => omega
          | succ m' => exact hrs_all m'
      · -- `rs` has a nonzero coefficient!
        -- Prove `∃ k < rs.length, coeff rs k ≠ 0` and pick the maximum via induction on `rs.length`:
        have h_max : ∀ (L : ZPoly), (¬ ∀ m : Nat, coeff L m = 0) →
            ∃ k : Nat, coeff L k ≠ 0 ∧ ∀ m : Nat, k < m → coeff L m = 0 := by
          intro L
          induction L with
          | nil =>
            intro hne
            exact False.elim (hne (fun _ => rfl))
          | cons a as ihas =>
            intro hne
            by_cases has0 : ∀ m : Nat, coeff as m = 0
            · refine ⟨0, ?_, ?_⟩
              · intro ha0
                apply hne
                intro m
                cases m with
                | zero => exact ha0
                | succ m' => exact has0 m'
              · intro m hm
                cases m with
                | zero => omega
                | succ m' => exact has0 m'
            · rcases ihas has0 with ⟨k', hk', hmax'⟩
              refine ⟨k' + 1, hk', ?_⟩
              intro m hm
              cases m with
              | zero => omega
              | succ m' => exact hmax' m' (by omega)
        rcases h_max rs hrs_all with ⟨k', hk', hmax'⟩
        refine ⟨k' + 1, hk', ?_⟩
        intro m hm
        cases m with
        | zero => omega
        | succ m' => exact hmax' m' (by omega)
  rcases hex_R with ⟨kr, hkr, hr_hi⟩
  refine ⟨dp + kr, by omega, ?_⟩
  -- Prove `coeff (mul P R) (dp + kr) = coeff P dp * coeff R kr ≠ 0`:
  have htop_prod : ∀ (A : ZPoly) (da : Nat),
      (∀ m : Nat, da < m → coeff A m = 0) →
      coeff (mul A R) (da + kr) = coeff A da * coeff R kr := by
    intro A
    induction A with
    | nil =>
      intro da _
      simp [mul, coeff]
    | cons a as ihas =>
      intro da hda
      cases da with
      | zero =>
        simp only [Nat.zero_add, mul]
        rw [coeff_add, coeff_scale]
        have h_as0 : ∀ m : Nat, coeff as m = 0 := fun m => hda (m + 1) (by omega)
        have h_mul0 : coeff (0 :: mul as R) kr = 0 := by
          cases kr with
          | zero => rfl
          | succ kr' =>
            simp only [coeff]
            rw [← mulPolySeries_unit (mul as R) kr', mulPolySeries_mul]
            exact mulPolySeries_eq_zero_of_all_zero as h_as0 (mulPolySeries R unitSeries) kr'
        rw [h_mul0, Int.add_zero]
        rfl
      | succ da' =>
        simp only [Nat.succ_add, mul]
        rw [coeff_add, coeff_scale]
        have hr_gt : coeff R (da' + kr + 1) = 0 := hr_hi (da' + kr + 1) (by omega)
        rw [hr_gt, Int.mul_zero, Int.zero_add]
        have h_ih := ihas da' (fun m hm => hda (m + 1) (by omega))
        exact h_ih
  rw [htop_prod P dp hp_hi]
  intro hz
  rcases Int.mul_eq_zero.mp hz with h1 | h2
  · exact hdp h1
  · exact hkr h2

/-- **Modular Exponent Failure Theorem:**
`Q_mod(t) = (1 - t)(1 - t^4)` does NOT divide `(1 - t^{exp(G)})^2 = (1 - t^2)^2` in `ℤ[t]`,
whereas it DOES divide `(1 - t^{|G|})^2 = (1 - t^4)^2` and `(1 - t^4)(1 - t^8)`. -/
theorem modular_F4_witness :
    ¬ PolyDvd Q_mod (chainProd [2, 2]) ∧
    PolyDvd Q_mod (chainProd [4, 4]) ∧
    PolyDvd Q_mod (chainProd [4, 8]) := by
  refine ⟨?_, ?_, ?_⟩
  · intro ⟨R, hR⟩
    have hc5 : coeff Q_mod 5 ≠ 0 := by decide
    have hhi : ∀ m : Nat, 5 < m → coeff Q_mod m = 0 := by
      intro m hm
      have hlen : Q_mod.length ≤ m := by
        have hL : Q_mod.length = 6 := rfl
        omega
      exact coeff_gt_length Q_mod m hlen
    have h0_nz : coeff (mul Q_mod R) 0 ≠ 0 := by
      rw [← hR 0]
      decide
    rcases top_nonzero_degree_le hc5 hhi ⟨0, h0_nz⟩ with ⟨top, htop_ge, htop_nz⟩
    rw [← hR top] at htop_nz
    have hlen22 : (chainProd [2, 2]).length ≤ top := by
      have hL : (chainProd [2, 2]).length = 5 := rfl
      omega
    exact htop_nz (coeff_gt_length (chainProd [2, 2]) top hlen22)
  · exact chainProd_dvd_of_pointwiseDvd
      (PointwiseDvd.cons (by decide) ⟨4, by decide⟩
        (PointwiseDvd.cons (by decide) ⟨1, by decide⟩ PointwiseDvd.nil))
  · exact chainProd_dvd_of_pointwiseDvd
      (PointwiseDvd.cons (by decide) ⟨4, by decide⟩
        (PointwiseDvd.cons (by decide) ⟨2, by decide⟩ PointwiseDvd.nil))

/-! ### 4. Refutation of Hyper-Literal Index-Rationality `m ↦ a_m ∈ ℚ(m)` -/

/-- Dimension sequence `a_m = dim_k(k[x]_m^{±1})` (`1` for even `m`, `0` for odd `m`). -/
def paritySeq : Series :=
  fun m => if m % 2 = 0 then 1 else 0

theorem paritySeq_has_chain_denom : HasDenominatorDividing (chainProd [2]) paritySeq := by
  refine ⟨by decide, 1, ?_⟩
  intro m hm
  have hpos : ∀ d ∈ [2], 1 ≤ d := by
    intro d hd
    rcases List.mem_singleton.mp hd with rfl
    decide
  rw [mulPolySeries_chainProd hpos paritySeq]
  simp only [List.foldr, shiftSub, paritySeq]
  by_cases hlt : m < 2
  · have hm1 : m = 1 := by omega
    subst hm1
    decide
  · have hmod : (m - 2) % 2 = m % 2 := by omega
    simp [hlt, hmod]

/-- Constructive factor-division identity `U(x) - U(r) = (x - r) * Q(x)` with `Q.length < U.length`. -/
theorem poly_sub_eval_factor :
    ∀ (U : ZPoly) (r : Int), U ≠ [] →
      ∃ Q : ZPoly, Q.length < U.length ∧ ∀ x : Int, eval U x - eval U r = (x - r) * eval Q x
  | [], _, hne => False.elim (hne rfl)
  | c :: cs, r, _ => by
      cases cs with
      | nil =>
        refine ⟨[], by simp, ?_⟩
        intro x
        simp [eval]
      | cons c₂ cs' =>
        rcases poly_sub_eval_factor (c₂ :: cs') r (by simp) with ⟨Q', hlen', hQ'⟩
        refine ⟨eval (c₂ :: cs') r :: Q', by simp at hlen' ⊢; omega, ?_⟩
        intro x
        simp only [eval]
        have hstep2 : (c + x * (c₂ + x * eval cs' x)) - (c + r * (c₂ + r * eval cs' r)) =
            (x - r) * (c₂ + r * eval cs' r) + x * ((c₂ + x * eval cs' x) - (c₂ + r * eval cs' r)) := by
          rw [Int.sub_mul, Int.mul_sub]
          omega
        rw [hstep2]
        have hQ'_exp : (c₂ + x * eval cs' x) - (c₂ + r * eval cs' r) = (x - r) * eval Q' x := hQ' x
        rw [hQ'_exp, Int.mul_left_comm x (x - r) (eval Q' x), ← Int.mul_add]

theorem poly_zero_of_odd_roots_from :
    ∀ (n : Nat) (U : ZPoly) (q₀ : Nat), U.length ≤ n →
      (∀ q : Nat, q₀ ≤ q → eval U (Int.ofNat (2 * q + 1)) = 0) →
      ∀ x : Int, eval U x = 0
  | 0, U, _, hlen, _, _ => by
      cases U with
      | nil => rfl
      | cons _ _ => simp at hlen
  | n + 1, U, q₀, hlen, hroots, x => by
      cases U with
      | nil => rfl
      | cons c cs =>
        let r₀ : Int := Int.ofNat (2 * q₀ + 1)
        rcases poly_sub_eval_factor (c :: cs) r₀ (by simp) with ⟨Q, hQlen, hQfac⟩
        have hr₀ : eval (c :: cs) r₀ = 0 := hroots q₀ (Nat.le_refl q₀)
        have hQroots : ∀ q : Nat, q₀ + 1 ≤ q → eval Q (Int.ofNat (2 * q + 1)) = 0 := by
          intro q hq
          have hfac := hQfac (Int.ofNat (2 * q + 1))
          rw [hroots q (by omega), hr₀] at hfac
          have hzero : (Int.ofNat (2 * q + 1) - r₀) * eval Q (Int.ofNat (2 * q + 1)) = 0 :=
            hfac.symm.trans (by simp)
          rcases Int.mul_eq_zero.mp hzero with hneq | hQz
          · exfalso
            have : Int.ofNat (2 * q + 1) ≠ r₀ := by
              dsimp [r₀]
              omega
            omega
          · exact hQz
        have hQ0 : eval Q x = 0 :=
          poly_zero_of_odd_roots_from n Q (q₀ + 1) (by omega) hQroots x
        have hfac_x := hQfac x
        rw [hr₀, hQ0, Int.mul_zero] at hfac_x
        omega

/-- **Refutation of Hyper-Literal Index-Rationality (`m ↦ a_m ∈ ℚ(m)`):**
Even for `n = 1` and `G = {±1}` acting on `k[x]` (`char(k) ≠ 2`), whose Molien series
`1 / (1 - t^2)` has `a_m = 1` (`m` even), `0` (`m` odd), there do NOT exist integer
polynomials `U(X), V(X) ∈ ℤ[X]` with `V(0) ≠ 0` such that `a_m · V(m) = U(m)` for all `m ∈ ℕ`. -/
theorem paritySeq_not_rational_in_index (U V : ZPoly) (hV0 : eval V 0 ≠ 0) :
    ¬ (∀ m : Nat, paritySeq m * eval V (Int.ofNat m) = eval U (Int.ofNat m)) := by
  intro hall
  have hodd : ∀ q : Nat, 0 ≤ q → eval U (Int.ofNat (2 * q + 1)) = 0 := by
    intro q _
    have hq := hall (2 * q + 1)
    unfold paritySeq at hq
    have hmod : (2 * q + 1) % 2 ≠ 0 := by omega
    simp [hmod] at hq
    exact hq.symm
  have hU0 : eval U 0 = 0 := poly_zero_of_odd_roots_from U.length U 0 (Nat.le_refl _) hodd 0
  have hev0 := hall 0
  unfold paritySeq at hev0
  simp only [Nat.zero_mod, ↓reduceIte, Int.one_mul, Int.ofNat_eq_coe] at hev0
  exact hV0 (hev0.trans hU0)

/-! ### 5. Positive Non-Vacuity Witnesses (`S₃` and Bertin's Modular `𝔽₂[x₁,x₂,x₃,x₄]^{C₄}`) -/

/-- For `S₃` on `k[x₁, x₂, x₃]`, the fundamental degrees `[1, 2, 3]` are NOT themselves a
divisibility chain (`2 ∤ 3`), yet `(1 - t)(1 - t^2)(1 - t^3)` divides the explicit strict
divisibility chain `(1 - t)(1 - t^2)(1 - t^6)`. -/
theorem sym3_nonvacuity_witness :
    ¬ IsDivChain [1, 2, 3] ∧
    IsDivChain [1, 2, 6] ∧
    IsStrictIncPos [1, 2, 6] ∧
    PolyDvd (chainProd [1, 2, 3]) (chainProd [1, 2, 6]) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro h
    cases h with
    | cons _ h23 =>
      cases h23 with
      | cons hdvd _ =>
        rcases hdvd with ⟨k, hk⟩
        omega
  · exact IsDivChain.cons ⟨2, by decide⟩ (IsDivChain.cons ⟨3, by decide⟩ (IsDivChain.single 6))
  · exact IsStrictIncPos.cons (by decide) (by decide)
      (IsStrictIncPos.cons (by decide) (by decide) (IsStrictIncPos.single (by decide)))
  · exact chainProd_dvd_of_pointwiseDvd
      (PointwiseDvd.cons (by decide) ⟨1, by decide⟩
        (PointwiseDvd.cons (by decide) ⟨1, by decide⟩
          (PointwiseDvd.cons (by decide) ⟨2, by decide⟩ PointwiseDvd.nil)))

/-- Exact quasi-polynomial dimension sequence `a_m = dim_{𝔽₂}(𝔽₂[x₁,x₂,x₃,x₄]_m^{C₄})`
of Marie-José Bertin's modular non-Cohen-Macaulay invariant ring (`char(k) = 2 ∣ |C₄| = 4`),
expressed on each residue class `c = m % 4` with `q = m / 4`:
- `c = 0`: `1 + 9 C(q,1) + 24 C(q,2) + 16 C(q,3)`
- `c = 1`: `1 + 13 C(q,1) + 28 C(q,2) + 16 C(q,3)`
- `c = 2`: `3 + 19 C(q,1) + 32 C(q,2) + 16 C(q,3)`
- `c = 3`: `5 + 25 C(q,1) + 36 C(q,2) + 16 C(q,3)`. -/
def bertinSeq (m : Nat) : Int :=
  let q := m / 4
  let c := m % 4
  if c = 0 then
    1 + 9 * binom q 1 + 24 * binom q 2 + 16 * binom q 3
  else if c = 1 then
    1 + 13 * binom q 1 + 28 * binom q 2 + 16 * binom q 3
  else if c = 2 then
    3 + 19 * binom q 1 + 32 * binom q 2 + 16 * binom q 3
  else
    5 + 25 * binom q 1 + 36 * binom q 2 + 16 * binom q 3

theorem iterFwdDiff4_cubic_binom (c₀ c₁ c₂ c₃ : Int) :
    ∀ q : Nat, iterFwdDiff 4 (fun r => c₀ + c₁ * binom r 1 + c₂ * binom r 2 + c₃ * binom r 3) q = 0 := by
  intro q
  have h1 : fwdDiff (fun r => c₀ + c₁ * binom r 1 + c₂ * binom r 2 + c₃ * binom r 3) =
      fun r => c₁ * binom r 0 + c₂ * binom r 1 + c₃ * binom r 2 := by
    funext r
    unfold fwdDiff
    dsimp only
    have b1 : binom (r + 1) 1 = binom r 0 + binom r 1 := rfl
    have b2 : binom (r + 1) 2 = binom r 1 + binom r 2 := rfl
    have b3 : binom (r + 1) 3 = binom r 2 + binom r 3 := rfl
    rw [b1, b2, b3, Int.mul_add, Int.mul_add, Int.mul_add]
    omega
  have h2 : fwdDiff (fun r => c₁ * binom r 0 + c₂ * binom r 1 + c₃ * binom r 2) =
      fun r => c₂ * binom r 0 + c₃ * binom r 1 := by
    funext r
    unfold fwdDiff
    dsimp only
    have b0 : binom (r + 1) 0 = 1 := rfl
    have b0' : binom r 0 = 1 := by cases r <;> rfl
    have b1 : binom (r + 1) 1 = binom r 0 + binom r 1 := rfl
    have b2 : binom (r + 1) 2 = binom r 1 + binom r 2 := rfl
    rw [b1, b2, b0, b0', Int.mul_add, Int.mul_add]
    omega
  have h3 : fwdDiff (fun r => c₂ * binom r 0 + c₃ * binom r 1) =
      fun r => c₃ * binom r 0 := by
    funext r
    unfold fwdDiff
    dsimp only
    have b0 : binom (r + 1) 0 = 1 := rfl
    have b0' : binom r 0 = 1 := by cases r <;> rfl
    have b1 : binom (r + 1) 1 = binom r 0 + binom r 1 := rfl
    rw [b1, b0, b0', Int.mul_add]
    omega
  have h4 : fwdDiff (fun r => c₃ * binom r 0) = fun _ => 0 := by
    funext r
    unfold fwdDiff
    dsimp only
    have b0 : binom (r + 1) 0 = 1 := rfl
    have b0' : binom r 0 = 1 := by cases r <;> rfl
    rw [b0, b0']
    omega
  simp only [iterFwdDiff, h1, h2, h3, h4]

/-- **Bertin Modular Non-Cohen-Macaulay Witness Theorem:**
`bertinSeq` satisfies `(Δ_4^4 bertinSeq)_m = 0` for all `m ≥ 0`, hence has rational generating
series with denominator dividing `(1 - t^4)^4` AND the strict length-4 divisibility chain
`(1 - t^4)(1 - t^8)(1 - t^16)(1 - t^32)`. -/
theorem bertin_modular_witness :
    (∀ m : Nat, iterModDiff 4 4 bertinSeq m = 0) ∧
    HasDenominatorDividing (chainProd [4, 4, 4, 4]) bertinSeq ∧
    HasDenominatorDividing (chainProd (uniformStrictChain 4 4)) bertinSeq := by
  have hmod0 : ∀ m : Nat, iterModDiff 4 4 bertinSeq m = 0 := by
    intro m
    have hdiv : (m / 4) * 4 + m % 4 = m := by
      have h1 := Nat.div_add_mod m 4
      rw [Nat.mul_comm] at h1
      exact h1
    rw [← hdiv, iterModDiff_residue_class 4 4 bertinSeq (m % 4) (m / 4)]
    have hres_eq : (fun q' => bertinSeq (q' * 4 + m % 4)) =
        if m % 4 = 0 then fun r => 1 + 9 * binom r 1 + 24 * binom r 2 + 16 * binom r 3
        else if m % 4 = 1 then fun r => 1 + 13 * binom r 1 + 28 * binom r 2 + 16 * binom r 3
        else if m % 4 = 2 then fun r => 3 + 19 * binom r 1 + 32 * binom r 2 + 16 * binom r 3
        else fun r => 5 + 25 * binom r 1 + 36 * binom r 2 + 16 * binom r 3 := by
      funext r
      unfold bertinSeq
      have hq : (r * 4 + m % 4) / 4 = r := by omega
      have hrm : (r * 4 + m % 4) % 4 = m % 4 := by omega
      rw [hq, hrm]
      by_cases h0 : m % 4 = 0
      · simp [h0]
      · by_cases h1 : m % 4 = 1
        · simp [h0, h1]
        · by_cases h2 : m % 4 = 2
          · simp [h0, h1, h2]
          · simp [h0, h1, h2]
    rw [hres_eq]
    by_cases h0 : m % 4 = 0
    · simp [h0, iterFwdDiff4_cubic_binom]
    · by_cases h1 : m % 4 = 1
      · simp [h0, h1, iterFwdDiff4_cubic_binom]
      · by_cases h2 : m % 4 = 2
        · simp [h0, h1, h2, iterFwdDiff4_cubic_binom]
        · simp [h0, h1, h2, iterFwdDiff4_cubic_binom]
  have hpoly : IsPolyBelow (4 * 4) (mulPolySeries (chainProd (List.replicate 4 4)) bertinSeq) :=
    (modular_periodic_iff (by decide : 1 ≤ 4) 4 bertinSeq).1.mpr hmod0
  have hunif : HasDenominatorDividing (chainProd (List.replicate 4 4)) bertinSeq :=
    ⟨by decide, 4 * 4, hpoly⟩
  rcases invariant_ring_strict_chain_of_uniform (by decide : 1 ≤ 4) hunif with ⟨_, _, _, hstrict⟩
  exact ⟨hmod0, hunif, hstrict⟩

end Conjecture00000000593

