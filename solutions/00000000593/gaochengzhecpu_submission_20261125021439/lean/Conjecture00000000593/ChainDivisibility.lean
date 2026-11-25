/-
Copyright (c) 2026. All rights reserved.
 Formalization of Conjecture 00000000593:
 Cyclotomic factor divisibility, explicit strict divisibility-chain upgrading,
 and graded Hilbert-Serre / Molien denominator theorems.
-/
import Conjecture00000000593.PolySeries

namespace Conjecture00000000593

/-- Geometric sum polynomial `1 + t^e + t^{2e} + ... + t^{(k-1)e}` in `ℤ[t]`. -/
def geomSum (e : Nat) : Nat → ZPoly
  | 0 => []
  | k + 1 => add [1] (mul (tPow e) (geomSum e k))

theorem eval_geomSum_one (e : Nat) : ∀ k : Nat, eval (geomSum e k) 1 = Int.ofNat k
  | 0 => rfl
  | k + 1 => by
    simp only [geomSum]
    rw [eval_add, eval_mul, eval_tPow_one, eval_geomSum_one e k]
    simp [eval]
    omega

/-- Fundamental cyclotomic telescoping identity:
`(1 - t^e) * (1 + t^e + ... + t^{(k-1)e}) = 1 - t^{e * k}` in `ℤ[t]`. -/
theorem mul_oneMinusTPow_geomSum {e : Nat} (he : 1 ≤ e) :
    ∀ k : Nat, PolyEq (mul (oneMinusTPow e) (geomSum e k)) (oneMinusTPow (e * k))
  | 0 => by
    intro m
    have h1 := mul_nil_right (oneMinusTPow e) m
    simp only [geomSum]
    rw [h1]
    simp only [Nat.mul_zero, oneMinusTPow, tPow, scale, add]
    cases m <;> rfl
  | k + 1 => by
    intro m
    rw [← mulPolySeries_unit (mul (oneMinusTPow e) (geomSum e (k + 1))) m]
    rw [← mulPolySeries_unit (oneMinusTPow (e * (k + 1))) m]
    rw [mulPolySeries_mul, mulPolySeries_oneMinusTPow he]
    unfold shiftSub
    simp only [geomSum]
    rw [mulPolySeries_add, mulPolySeries_mul, mulPolySeries_tPow]
    have ih_ser : ∀ n : Nat,
        shiftSub e (mulPolySeries (geomSum e k) unitSeries) n =
          mulPolySeries (oneMinusTPow (e * k)) unitSeries n := by
      intro n
      rw [← mulPolySeries_oneMinusTPow he, ← mulPolySeries_mul]
      rw [mulPolySeries_unit, mulPolySeries_unit]
      exact mul_oneMinusTPow_geomSum he k n
    have h_u1 : ∀ n : Nat, mulPolySeries [1] unitSeries n = if n = 0 then 1 else 0 := by
      intro n
      cases n <;> simp [mulPolySeries, unitSeries]
    by_cases hm : m < e
    · have hm2 : m < e * (k + 1) := by
        have hk : 1 ≤ k + 1 := by omega
        have := Nat.mul_le_mul_left e hk
        omega
      simp only [hm, ↓reduceIte, h_u1 m]
      have hne : m ≠ e * (k + 1) := by omega
      unfold oneMinusTPow
      rw [mulPolySeries_unit, coeff_add, coeff_scale, coeff_tPow]
      cases m with
      | zero => simp [coeff, hne]
      | succ m' => simp [coeff, hne]
    · simp only [hm, ↓reduceIte, h_u1 m]
      have hm0 : m ≠ 0 := by omega
      simp only [hm0, ↓reduceIte]
      rw [mulPolySeries_add, mulPolySeries_mul, mulPolySeries_tPow]
      have h_step :
          (0 + mulPolySeries (geomSum e k) unitSeries (m - e)) -
            (mulPolySeries [1] unitSeries (m - e) +
              if m - e < e then 0 else mulPolySeries (geomSum e k) unitSeries (m - e - e)) =
            shiftSub e (mulPolySeries (geomSum e k) unitSeries) (m - e) -
              mulPolySeries [1] unitSeries (m - e) := by
        unfold shiftSub
        by_cases hme2 : m - e < e <;> simp [hme2] <;> omega
      rw [h_step, ih_ser (m - e), h_u1 (m - e)]
      rw [mulPolySeries_unit, mulPolySeries_unit]
      unfold oneMinusTPow
      rw [coeff_add, coeff_add, coeff_scale, coeff_scale, coeff_tPow, coeff_tPow]
      have h_ek : e * (k + 1) = e * k + e := Nat.mul_succ e k
      have hc2 : coeff [1] m = 0 := by
        cases m with
        | zero => omega
        | succ _ => rfl
      rw [hc2]
      by_cases hme : m = e
      · subst hme
        have hsub0 : m - m = 0 := Nat.sub_self m
        rw [hsub0]
        simp only [↓reduceIte, coeff]
        by_cases hk0 : k = 0
        · subst hk0
          simp
        · have hpos : 0 ≠ m * k := by
            intro hz
            rcases Nat.mul_eq_zero.mp hz.symm with hm_z | hk_z <;> omega
          have hne2 : m ≠ m * (k + 1) := by omega
          simp [hpos, hne2]
      · have hsub_pos : m - e ≠ 0 := by omega
        have hc1 : coeff [1] (m - e) = 0 := by
          cases h_eq : m - e with
          | zero => omega
          | succ _ => rfl
        rw [hc1]
        simp only [hsub_pos, ↓reduceIte]
        by_cases h_match : m - e = e * k
        · have h_match2 : m = e * (k + 1) := by omega
          simp [h_match, h_match2]
          omega
        · have h_match2 : m ≠ e * (k + 1) := by omega
          simp [h_match, h_match2]

/-- If `e ∣ d` (`1 ≤ e`), then `(1 - t^e) ∣ (1 - t^d)` in `ℤ[t]`. -/
theorem oneMinusTPow_dvd_of_dvd {e d : Nat} (he : 1 ≤ e) (hdvd : e ∣ d) :
    PolyDvd (oneMinusTPow e) (oneMinusTPow d) := by
  rcases hdvd with ⟨k, rfl⟩
  exact ⟨geomSum e k, polyEq_symm (mul_oneMinusTPow_geomSum he k)⟩

/-- Pointwise divisibility relation between two exponent lists of equal length. -/
inductive PointwiseDvd : List Nat → List Nat → Prop
  | nil : PointwiseDvd [] []
  | cons {e d : Nat} {es ds : List Nat} :
      1 ≤ e → e ∣ d → PointwiseDvd es ds → PointwiseDvd (e :: es) (d :: ds)

theorem chainProd_dvd_of_pointwiseDvd {es ds : List Nat} (h : PointwiseDvd es ds) :
    PolyDvd (chainProd es) (chainProd ds) := by
  induction h with
  | nil => exact polyDvd_refl [1]
  | cons he hdvd _ ih =>
    simp only [chainProd]
    exact polyDvd_mul (oneMinusTPow_dvd_of_dvd he hdvd) ih

/-- Predicate that `ds = [d₁, d₂, ..., d_r]` is a divisibility chain `d₁ ∣ d₂ ∣ ... ∣ d_r`. -/
inductive IsDivChain : List Nat → Prop
  | nil : IsDivChain []
  | single (d : Nat) : IsDivChain [d]
  | cons {a b : Nat} {rest : List Nat} :
      a ∣ b → IsDivChain (b :: rest) → IsDivChain (a :: b :: rest)

/-- Predicate that `ds = [d₁, d₂, ..., d_r]` is strictly increasing and positive
(`0 < d₁ < d₂ < ... < d_r`), ensuring all factors `(1 - t^{d_i})` are pairwise distinct. -/
inductive IsStrictIncPos : List Nat → Prop
  | nil : IsStrictIncPos []
  | single {d : Nat} : 1 ≤ d → IsStrictIncPos [d]
  | cons {a b : Nat} {rest : List Nat} :
      1 ≤ a → a < b → IsStrictIncPos (b :: rest) → IsStrictIncPos (a :: b :: rest)

theorem isStrictIncPos_pos {ds : List Nat} (h : IsStrictIncPos ds) : ∀ d ∈ ds, 1 ≤ d := by
  induction h with
  | nil => intro _ hm; cases hm
  | single hd =>
    intro d hm
    rcases List.mem_singleton.mp hm with rfl
    exact hd
  | cons ha hab hrest ih =>
    intro d hm
    rcases List.mem_cons.mp hm with rfl | htail
    · exact ha
    · exact ih d htail

/-- Explicit strict chain auxiliary constructor: given previous chain term `prev ≥ 1`
and remaining exponents `es`, produces `d₁ = 2 * prev * e₁`, `d₂ = 2 * d₁ * e₂`, ... -/
def strictChainAux (prev : Nat) : List Nat → List Nat
  | [] => []
  | e :: es =>
      let cur := 2 * prev * e
      cur :: strictChainAux cur es

/-- Upgrade any list of positive exponents `es = [e₁, ..., e_r]` into an explicit
strictly increasing divisibility chain `ds = [d₁, ..., d_r]` of the same length
with `e_i ∣ d_i` for every `i`. -/
def strictChain : List Nat → List Nat
  | [] => []
  | e :: es => e :: strictChainAux e es

theorem strictChainAux_props :
    ∀ {es : List Nat} {prev : Nat}, 1 ≤ prev → (∀ e ∈ es, 1 ≤ e) →
      (strictChainAux prev es).length = es.length ∧
      PointwiseDvd es (strictChainAux prev es) ∧
      IsDivChain (prev :: strictChainAux prev es) ∧
      IsStrictIncPos (prev :: strictChainAux prev es)
  | [], prev, hprev, _ =>
      ⟨rfl, PointwiseDvd.nil, IsDivChain.single prev, IsStrictIncPos.single hprev⟩
  | e :: es, prev, hprev, hes => by
      have he : 1 ≤ e := hes e (List.mem_cons_self ..)
      have hrest : ∀ x ∈ es, 1 ≤ x := fun x hx => hes x (List.mem_cons_of_mem e hx)
      let cur := 2 * prev * e
      have hcur_gt : prev < cur := by
        have h1 : prev * 1 ≤ prev * e := Nat.mul_le_mul_left prev he
        have h2 : 2 * prev * e = 2 * (prev * e) := Nat.mul_assoc 2 prev e
        omega
      have hcur_pos : 1 ≤ cur := by omega
      have hprev_dvd : prev ∣ cur := ⟨2 * e, by
        dsimp [cur]
        rw [Nat.mul_assoc, Nat.mul_comm 2 (prev * e), Nat.mul_assoc, Nat.mul_comm e 2]⟩
      have he_dvd : e ∣ cur := ⟨2 * prev, Nat.mul_comm (2 * prev) e⟩
      rcases strictChainAux_props hcur_pos hrest with ⟨hlen, hpwd, hdiv, hinc⟩
      refine ⟨by simp only [strictChainAux, List.length_cons]; dsimp [cur] at hlen; omega, ?_, ?_, ?_⟩
      · exact PointwiseDvd.cons he he_dvd hpwd
      · exact IsDivChain.cons hprev_dvd hdiv
      · exact IsStrictIncPos.cons hprev hcur_gt hinc

/-- **Universal Chain-Upgrading Theorem:**
Every list of positive exponents `es` admits an explicit strictly increasing divisibility
chain `ds = strictChain es` (`d₁ ∣ d₂ ∣ ... ∣ d_r`, `0 < d₁ < d₂ < ... < d_r`) of equal length
such that `∏_{e ∈ es} (1 - t^e) ∣ ∏_{d ∈ ds} (1 - t^d)` in `ℤ[t]`. -/
theorem strictDivChain_upgrade {es : List Nat} (hes : ∀ e ∈ es, 1 ≤ e) :
    (strictChain es).length = es.length ∧
    IsDivChain (strictChain es) ∧
    IsStrictIncPos (strictChain es) ∧
    PolyDvd (chainProd es) (chainProd (strictChain es)) := by
  cases es with
  | nil =>
    exact ⟨rfl, IsDivChain.nil, IsStrictIncPos.nil, polyDvd_refl [1]⟩
  | cons e rest =>
    have he : 1 ≤ e := hes e (List.mem_cons_self ..)
    have hrest : ∀ x ∈ rest, 1 ≤ x := fun x hx => hes x (List.mem_cons_of_mem e hx)
    rcases strictChainAux_props he hrest with ⟨hlen, hpwd, hdiv, hinc⟩
    have hpwd_all : PointwiseDvd (e :: rest) (e :: strictChainAux e rest) :=
      PointwiseDvd.cons he (Nat.dvd_refl e) hpwd
    exact ⟨by simp [strictChain, hlen], hdiv, hinc, chainProd_dvd_of_pointwiseDvd hpwd_all⟩

/-- Explicit tight length-`n` strict divisibility chain `[G_ord, 2 * G_ord, ..., 2^{n-1} * G_ord]`
associated to a finite group of order `G_ord ≥ 1` acting on `n` variables. -/
def uniformStrictChainAux (cur : Nat) : Nat → List Nat
  | 0 => []
  | n + 1 => cur :: uniformStrictChainAux (2 * cur) n

def uniformStrictChain (G_ord n : Nat) : List Nat :=
  uniformStrictChainAux G_ord n

theorem uniformStrictChainAux_props {G_ord cur : Nat} (hG : 1 ≤ G_ord) (hcur : 1 ≤ cur)
    (hdvd : G_ord ∣ cur) :
    ∀ n : Nat,
      (uniformStrictChainAux cur n).length = n ∧
      PointwiseDvd (List.replicate n G_ord) (uniformStrictChainAux cur n) ∧
      (∀ rest_hd : Nat, cur = 2 * rest_hd → IsDivChain (rest_hd :: uniformStrictChainAux cur n)) ∧
      IsDivChain (uniformStrictChainAux cur n) ∧
      IsStrictIncPos (uniformStrictChainAux cur n)
  | 0 => by
      refine ⟨rfl, PointwiseDvd.nil, ?_, IsDivChain.nil, IsStrictIncPos.nil⟩
      intro rest_hd _
      exact IsDivChain.single rest_hd
  | n + 1 => by
      have hcur2_pos : 1 ≤ 2 * cur := by omega
      have hdvd2 : G_ord ∣ 2 * cur := by
        rcases hdvd with ⟨k, rfl⟩
        exact ⟨2 * k, by rw [Nat.mul_left_comm]⟩
      rcases uniformStrictChainAux_props hG hcur2_pos hdvd2 n with ⟨hlen, hpwd, hlink, _, hinc⟩
      refine ⟨by simp [uniformStrictChainAux, hlen],
              PointwiseDvd.cons hG hdvd hpwd,
              ?_, ?_, ?_⟩
      · intro rest_hd heq
        have hrdvd : rest_hd ∣ cur := ⟨2, by rw [heq, Nat.mul_comm]⟩
        exact IsDivChain.cons hrdvd (hlink cur rfl)
      · exact hlink cur rfl
      · simp only [uniformStrictChainAux]
        cases h_next : uniformStrictChainAux (2 * cur) n with
        | nil => exact IsStrictIncPos.single hcur
        | cons b bs =>
          have hb_eq : b = 2 * cur := by
            cases n with
            | zero => simp [uniformStrictChainAux] at h_next
            | succ n' =>
              simp [uniformStrictChainAux] at h_next
              exact h_next.1.symm
          rw [h_next] at hinc
          exact IsStrictIncPos.cons hcur (by omega) hinc

/-- **Sharp Uniform-Order Chain Theorem:**
For every group order `G_ord ≥ 1` and variable count `n`, `(1 - t^{G_ord})^n` divides
the explicit length-`n` strict divisibility chain `∏_{i=0}^{n-1} (1 - t^{2^i G_ord})`. -/
theorem uniformPower_dvd_uniformStrictChain {G_ord : Nat} (hG : 1 ≤ G_ord) (n : Nat) :
    (uniformStrictChain G_ord n).length = n ∧
    IsDivChain (uniformStrictChain G_ord n) ∧
    IsStrictIncPos (uniformStrictChain G_ord n) ∧
    PolyDvd (chainProd (List.replicate n G_ord)) (chainProd (uniformStrictChain G_ord n)) := by
  rcases uniformStrictChainAux_props hG hG (Nat.dvd_refl G_ord) n with
    ⟨hlen, hpwd, _, hdiv, hinc⟩
  exact ⟨hlen, hdiv, hinc, chainProd_dvd_of_pointwiseDvd hpwd⟩

/-- Inductive witness of a graded Hilbert-Serre exact-sequence tower over homogeneous
algebra generators of positive degrees `es = [e₁, ..., e_r]` (as produced constructively
by Noether's orbit polynomials in degrees `1, ..., |G|` or Dade's hsop in degree `|G|`). -/
inductive HilbertSerreTower : List Nat → Series → Prop
  | base {a : Series} : IsPolynomialSeries a → HilbertSerreTower [] a
  | step {d : Nat} {ds : List Nat} {a dimK dimC : Series} :
      1 ≤ d →
      HilbertSerreTower ds dimK →
      HilbertSerreTower ds dimC →
      (∀ m : Nat, shiftSub d a m = dimC m - (if m < d then 0 else dimK (m - d))) →
      HilbertSerreTower (d :: ds) a

theorem shift_series_comm (d e : Nat) (f : Series) :
    shiftSub e (fun m => if m < d then 0 else f (m - d)) =
      fun m => if m < d then 0 else shiftSub e f (m - d) := by
  funext m
  unfold shiftSub
  by_cases hm : m < d
  · have hme : ¬ (d ≤ m - e) := by omega
    by_cases h1 : m < e
    · simp [hm, h1]
    · have h2 : m - e < d := by omega
      simp [hm, h1, h2]
  · by_cases h1 : m < e
    · have h2 : m - d < e := by omega
      simp [hm, h1, h2]
    · by_cases h2 : m - e < d
      · have h3 : m - d < e := by omega
        simp [hm, h1, h2, h3]
      · have h3 : ¬ (m - d < e) := by omega
        have h4 : m - e - d = m - d - e := by omega
        simp [hm, h1, h2, h3, h4]

theorem foldr_shiftSub_sub (ds : List Nat) (f g : Series) :
    ds.foldr shiftSub (fun m => f m - g m) =
      fun m => ds.foldr shiftSub f m - ds.foldr shiftSub g m := by
  induction ds with
  | nil => rfl
  | cons e es ih =>
    simp only [List.foldr_cons, ih]
    funext m
    unfold shiftSub
    by_cases hm : m < e
    · simp [hm]
    · simp [hm]
      omega

theorem foldr_shiftSub_delayed (ds : List Nat) (d : Nat) (f : Series) :
    ds.foldr shiftSub (fun m => if m < d then 0 else f (m - d)) =
      fun m => if m < d then 0 else ds.foldr shiftSub f (m - d) := by
  induction ds with
  | nil => rfl
  | cons e es ih =>
    simp only [List.foldr_cons, ih]
    exact shift_series_comm d e (es.foldr shiftSub f)

/-- **Graded Hilbert-Serre Denominator Theorem:**
Every graded module admitting a Hilbert-Serre exact-sequence tower over generators of
degrees `es` has rational Hilbert-Poincaré series with denominator dividing `∏_{e ∈ es} (1 - t^e)`. -/
theorem hilbert_serre_denominator {es : List Nat} {a : Series}
    (htower : HilbertSerreTower es a) :
    (∀ e ∈ es, 1 ≤ e) ∧ HasDenominatorDividing (chainProd es) a := by
  induction htower with
  | base hpoly =>
    refine ⟨(fun _ hm => nomatch hm), rfl, ?_⟩
    simp only [chainProd, mulPolySeries_one_poly]
    exact hpoly
  | @step d ds a dimK dimC hd _ _ hexact ihK ihC =>
    rcases ihK with ⟨hds, _, ⟨BK, hBK⟩⟩
    rcases ihC with ⟨_, _, ⟨BC, hBC⟩⟩
    have hall : ∀ e ∈ d :: ds, 1 ≤ e := by
      intro e hm
      rcases List.mem_cons.mp hm with rfl | htail
      · exact hd
      · exact hds e htail
    refine ⟨hall, coeff_chainProd_zero hall, ?_⟩
    rw [mulPolySeries_chainProd hall a]
    simp only [List.foldr_cons]
    have hcomm_fold : ∀ (x : Nat) (xs : List Nat) (f : Series),
        shiftSub x (xs.foldr shiftSub f) = xs.foldr shiftSub (shiftSub x f) := by
      intro x xs f
      induction xs with
      | nil => rfl
      | cons y ys ihy =>
        simp only [List.foldr_cons, ← ihy]
        funext m
        unfold shiftSub
        by_cases hmx : m < x <;> by_cases hmy : m < y
        · simp [hmx, hmy]
        · have h1 : m - y < x := by omega
          simp [hmx, hmy, h1]
        · have h1 : m - x < y := by omega
          simp [hmx, hmy, h1]
        · by_cases h1 : m - y < x <;> by_cases h2 : m - x < y
          · simp [hmx, hmy, h1, h2]
            omega
          · omega
          · omega
          · have h3 : m - y - x = m - x - y := by omega
            simp [hmx, hmy, h1, h2, h3]
            omega
    rw [hcomm_fold d ds a]
    have hexact_fn : shiftSub d a = fun m => dimC m - (if m < d then 0 else dimK (m - d)) :=
      funext hexact
    rw [hexact_fn, foldr_shiftSub_sub, foldr_shiftSub_delayed]
    rw [mulPolySeries_chainProd hds dimK] at hBK
    rw [mulPolySeries_chainProd hds dimC] at hBC
    refine ⟨BC + BK + d, ?_⟩
    intro m hm
    have hC0 : ds.foldr shiftSub dimC m = 0 := hBC m (by omega)
    have hlt : ¬ (m < d) := by omega
    have hK0 : ds.foldr shiftSub dimK (m - d) = 0 := hBK (m - d) (by omega)
    simp [hC0, hlt, hK0]

/-- **Constructive Hilbert-Serre Strict Chain Corollary:**
Every Hilbert-Serre tower over positive generator degrees `es` has rational generating series
whose denominator divides an explicit strictly increasing divisibility chain `d₁ ∣ d₂ ∣ ... ∣ d_r`. -/
theorem hilbert_serre_strict_chain {es : List Nat} {a : Series}
    (htower : HilbertSerreTower es a) :
    ∃ ds : List Nat,
      ds.length = es.length ∧
      IsDivChain ds ∧
      IsStrictIncPos ds ∧
      HasDenominatorDividing (chainProd ds) a := by
  rcases hilbert_serre_denominator htower with ⟨hes, hden⟩
  rcases strictDivChain_upgrade hes with ⟨hlen, hdiv, hinc, hdvd⟩
  have hpos_ds : ∀ d ∈ strictChain es, 1 ≤ d := isStrictIncPos_pos hinc
  exact ⟨strictChain es, hlen, hdiv, hinc,
         hasDenominatorDividing_mono hdvd (coeff_chainProd_zero hpos_ds) hden⟩

/-- **Invariant-Ring Uniform HSOP Denominator Theorem:**
Whenever an invariant ring `k[x₁,...,x_n]^G` (`|G| = G_ord ≥ 1`) satisfies
`HasDenominatorDividing (chainProd (List.replicate n G_ord)) a` (via Molien's matrix formula
in non-modular characteristic or Dade's hsop + Hilbert's syzygy theorem in arbitrary/modular
characteristic), its dimension sequence `a` has denominator dividing the explicit length-`n`
strict divisibility chain `∏_{i=0}^{n-1} (1 - t^{2^i |G|})`. -/
theorem invariant_ring_strict_chain_of_uniform {G_ord n : Nat} {a : Series}
    (hG : 1 ≤ G_ord)
    (hunif : HasDenominatorDividing (chainProd (List.replicate n G_ord)) a) :
    (uniformStrictChain G_ord n).length = n ∧
    IsDivChain (uniformStrictChain G_ord n) ∧
    IsStrictIncPos (uniformStrictChain G_ord n) ∧
    HasDenominatorDividing (chainProd (uniformStrictChain G_ord n)) a := by
  rcases uniformPower_dvd_uniformStrictChain hG n with ⟨hlen, hdiv, hinc, hdvd⟩
  have hpos : ∀ d ∈ uniformStrictChain G_ord n, 1 ≤ d := isStrictIncPos_pos hinc
  exact ⟨hlen, hdiv, hinc,
         hasDenominatorDividing_mono hdvd (coeff_chainProd_zero hpos) hunif⟩

end Conjecture00000000593
