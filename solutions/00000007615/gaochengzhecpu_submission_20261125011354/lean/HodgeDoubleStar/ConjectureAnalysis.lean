/-
  HodgeDoubleStar/ConjectureAnalysis.lean
  Complete formal analysis of Conjecture 00000007615:
  1. Middle-dimension self-duality characterization (`exists_nonzero_selfDual_iff`),
     split exact subspace decomposition over `ℤ`, and subspace codimension formulas;
  2. Explicit positive non-vacuity witnesses (4D Riemannian Yang–Mills self-dual 2-form,
     2D Lorentzian self-dual 1-form, and 6D Lorentzian self-dual 3-form);
  3. Formal refutations of every false clause across both Riemannian and pseudo-Riemannian
     metrics and complete disproofs of the bundled conjecture under all readings.
-/
import HodgeDoubleStar.ExteriorHodge

namespace HodgeDoubleStar

/-! ## 1. Middle-Dimension Self-Duality Characterization -/

/-- A form `ω` is **self-dual** with respect to metric signature `eta` if `⋆ω = ω`. -/
def IsSelfDual {n : Nat} (eta : MetricSig n) (ω : ExtForm n) : Prop :=
  hodgeStar eta ω = ω

/-- When `(m * m + s) % 2 = 1`, `⋆(⋆ω) = -ω` on `Λ^m(ℝ^{r,s})`, forcing every self-dual `m`-form to be `0`. -/
theorem no_nonzero_selfDual_of_odd {m : Nat} (eta : MetricSig (2 * m))
    (hodd : (m * m + negIndex eta) % 2 = 1)
    {ω : ExtForm (2 * m)} (hω : IsHomogeneous m ω) (hsd : IsSelfDual eta ω) :
    ω = 0 := by
  have hdd := hodgeStar_hodgeStar eta hω
  rw [IsSelfDual] at hsd
  rw [hsd, hsd] at hdd
  have hsub : 2 * m - m = m := by omega
  rw [hsub] at hdd
  have hsign : signPow (m * m + negIndex eta) = -1 :=
    (signPow_eq_neg_one_iff _).mpr hodd
  rw [hsign] at hdd
  funext I
  have hi := congrFun hdd I
  simp only [smulForm_apply, zeroForm_apply] at hi ⊢
  omega

/-- When `1 ≤ m` and `(m * m + s) % 2 = 0`, `e_{I_0} + ⋆e_{I_0}` is a non-zero self-dual `m`-form. -/
theorem exists_nonzero_selfDual_of_even {m : Nat} (hm : 1 ≤ m) (eta : MetricSig (2 * m))
    (heven : (m * m + negIndex eta) % 2 = 0) :
    ∃ ω : ExtForm (2 * m), IsHomogeneous m ω ∧ ω ≠ 0 ∧ IsSelfDual eta ω := by
  obtain ⟨I₀, hI₀⟩ := exists_mask_of_deg (2 * m) m (by omega)
  let e₀ : ExtForm (2 * m) := basisForm I₀
  let ω : ExtForm (2 * m) := e₀ + hodgeStar eta e₀
  have he₀ : IsHomogeneous m e₀ := by
    have hb := isHomogeneous_basisForm I₀
    rw [hI₀] at hb
    exact hb
  have hstar_e₀ : IsHomogeneous m (hodgeStar eta e₀) := by
    have hs := he₀.hodgeStar eta (by omega)
    have hsub : 2 * m - m = m := by omega
    rw [hsub] at hs
    exact hs
  refine ⟨ω, he₀.add hstar_e₀, ?_, ?_⟩
  · intro hzero
    have heval := congrFun hzero I₀
    have hne : compMask I₀ ≠ I₀ := compMask_ne_self (by omega) I₀
    simp only [ω, e₀, addForm_apply, basisForm, ↓reduceIte, hodgeStar, hne,
      Int.mul_zero, Int.add_zero, zeroForm_apply] at heval
    omega
  · unfold IsSelfDual
    dsimp only [ω]
    rw [hodgeStar_add, hodgeStar_hodgeStar eta he₀]
    have hsub : 2 * m - m = m := by omega
    rw [hsub]
    have hsign : signPow (m * m + negIndex eta) = 1 :=
      (signPow_eq_one_iff _).mpr heven
    rw [hsign]
    funext K
    simp only [addForm_apply, smulForm_apply, Int.one_mul]
    omega

/--
  **Exact Middle-Dimension Self-Duality Criterion (`n = 2m`, `m ≥ 1`):**
  A non-zero self-dual `m`-form exists in `Λ^m(ℝ^{r,s})` (`r + s = 2m`)
  if and only if `(m^2 + s) % 2 = 0` (equivalently `(m + s) % 2 = 0`).
-/
theorem exists_nonzero_selfDual_iff {m : Nat} (hm : 1 ≤ m) (eta : MetricSig (2 * m)) :
    (∃ ω : ExtForm (2 * m), IsHomogeneous m ω ∧ ω ≠ 0 ∧ IsSelfDual eta ω) ↔
      (m * m + negIndex eta) % 2 = 0 := by
  constructor
  · rintro ⟨ω, hω, hne, hsd⟩
    have hmod : (m * m + negIndex eta) % 2 = 0 ∨ (m * m + negIndex eta) % 2 = 1 := by omega
    rcases hmod with heven | hodd
    · exact heven
    · exact absurd (no_nonzero_selfDual_of_odd eta hodd hω hsd) hne
  · exact exists_nonzero_selfDual_of_even hm eta

/--
  **Riemannian Middle-Dimension Self-Duality Theorem (`s = 0`):**
  In positive-definite signature `(2m, 0)` with `m ≥ 1`, a non-zero self-dual `m`-form
  exists if and only if `m` is **even** (`n = 4k`).
-/
theorem riemannian_selfDual_iff_even {m : Nat} (hm : 1 ≤ m) :
    (∃ ω : ExtForm (2 * m), IsHomogeneous m ω ∧ ω ≠ 0 ∧ IsSelfDual (riemSig (2 * m)) ω) ↔
      m % 2 = 0 := by
  rw [exists_nonzero_selfDual_iff hm (riemSig (2 * m)), negIndex_riemSig, Nat.add_zero, sq_mod_two]

/--
  **Lorentzian Middle-Dimension Self-Duality Theorem (`s = 1`):**
  In Lorentzian signature `(2m - 1, 1)` with `m ≥ 1`, a non-zero self-dual `m`-form
  exists if and only if `m` is **odd** (`m = 1, 3, 5, ...`, i.e. `n = 2, 6, 10, ...`).
-/
theorem lorentzian_selfDual_iff_odd {m : Nat} (hm : 1 ≤ m) :
    (∃ ω : ExtForm (2 * m),
      IsHomogeneous m ω ∧ ω ≠ 0 ∧ IsSelfDual (sigOfRS (2 * m) (2 * m - 1)) ω) ↔
      m % 2 = 1 := by
  rw [exists_nonzero_selfDual_iff hm (sigOfRS (2 * m) (2 * m - 1))]
  have hs : negIndex (sigOfRS (2 * m) (2 * m - 1)) = 1 :=
    negIndex_sigOfRS (2 * m) (2 * m - 1) 1 (by omega)
  rw [hs]
  have hsq := sq_mod_two m
  omega

/-! ## 2. Exact Split Direct-Sum & Subspace Codimension of Self-Duality -/

/-- Complementary-half basis index set `M_- = {J ∈ Mask (2m) : |J| = m ∧ J(0) = false}`. -/
def NegHalfMask (m : Nat) (hm : 1 ≤ m) : Type :=
  { J : Mask (2 * m) // degMask J = m ∧ J ⟨0, by omega⟩ = false }

/-- Linear self-duality defect operator `sdDefect(ω)(J) = ω(J) - (⋆ω)(J)` for `J ∈ M_-`. -/
def sdDefect {m : Nat} (hm : 1 ≤ m) (eta : MetricSig (2 * m)) (ω : ExtForm (2 * m)) :
    NegHalfMask m hm → Int :=
  fun J => ω J.val - hodgeStar eta ω J.val

/-- Canonical right-inverse section `σ : ℤ^{M_-} → Λ^m` of `sdDefect`. -/
def sdSection {m : Nat} (hm : 1 ≤ m) (d : NegHalfMask m hm → Int) : ExtForm (2 * m) :=
  fun K =>
    if h : degMask K = m ∧ K ⟨0, by omega⟩ = false then
      d ⟨K, h⟩
    else
      0

theorem sdSection_homogeneous {m : Nat} (hm : 1 ≤ m) (d : NegHalfMask m hm → Int) :
    IsHomogeneous m (sdSection hm d) := by
  intro K hK
  simp [sdSection, hK]

/-- `sdSection` is a right inverse to `sdDefect`, proving `Λ^m / Λ^m_+ ≅ ℤ^{M_-}` when `(m^2 + s) % 2 = 0`. -/
theorem sdDefect_sdSection {m : Nat} (hm : 1 ≤ m) (eta : MetricSig (2 * m))
    (d : NegHalfMask m hm → Int) :
    sdDefect hm eta (sdSection hm d) = d := by
  funext ⟨J, hJdeg, hJ0⟩
  unfold sdDefect
  dsimp only
  have hsecJ : sdSection hm d J = d ⟨J, ⟨hJdeg, hJ0⟩⟩ := by
    simp [sdSection, hJdeg, hJ0]
  have hcomp0 : (compMask J) ⟨0, by omega⟩ = true := by
    simp [compMask, hJ0]
  have hsecComp : sdSection hm d (compMask J) = 0 := by
    simp [sdSection, hcomp0]
  simp [hodgeStar, hsecJ, hsecComp]

/-- When `(m^2 + s) % 2 = 0`, a homogeneous `m`-form `ω` is self-dual iff `sdDefect ω = 0` on `M_-`. -/
theorem isSelfDual_iff_sdDefect_zero {m : Nat} (hm : 1 ≤ m) (eta : MetricSig (2 * m))
    (heven : (m * m + negIndex eta) % 2 = 0)
    {ω : ExtForm (2 * m)} (hω : IsHomogeneous m ω) :
    IsSelfDual eta ω ↔ sdDefect hm eta ω = fun _ => 0 := by
  constructor
  · intro hsd
    funext ⟨J, _⟩
    unfold sdDefect
    rw [IsSelfDual] at hsd
    rw [hsd]
    simp
  · intro hdef
    unfold IsSelfDual
    funext K
    by_cases hdegK : degMask K = m
    · cases hK0 : K ⟨0, by omega⟩
      · have hJ := congrFun hdef ⟨K, ⟨hdegK, hK0⟩⟩
        unfold sdDefect at hJ
        dsimp only at hJ
        omega
      · let J := compMask K
        have hdegJ : degMask J = m := by
          have hs := degMask_add_degMask_comp K
          dsimp [J]
          omega
        have hJ0 : J ⟨0, by omega⟩ = false := by
          simp [J, compMask, hK0]
        have hJ := congrFun hdef ⟨J, ⟨hdegJ, hJ0⟩⟩
        unfold sdDefect at hJ
        dsimp only [J] at hJ
        have heqComp : ω (compMask K) = hodgeStar eta ω (compMask K) := by omega
        have hdd := congrFun (hodgeStar_hodgeStar eta hω) K
        have hsub : 2 * m - m = m := by omega
        have hsign : signPow (m * m + negIndex eta) = 1 :=
          (signPow_eq_one_iff _).mpr heven
        rw [hsub, hsign] at hdd
        simp only [smulForm_apply, Int.one_mul] at hdd
        calc
          hodgeStar eta ω K
            = etaSign eta (compMask K) * signPow (invCount (compMask K) K) * ω (compMask K) := rfl
          _ = etaSign eta (compMask K) * signPow (invCount (compMask K) K) *
                hodgeStar eta ω (compMask K) := by rw [heqComp]
          _ = hodgeStar eta (hodgeStar eta ω) K := rfl
          _ = ω K := hdd
    · have hstar : IsHomogeneous m (hodgeStar eta ω) := by
        have hs := hω.hodgeStar eta (by omega)
        have hsub : 2 * m - m = m := by omega
        rw [hsub] at hs
        exact hs
      rw [hstar K hdegK, hω K hdegK]

/-- Standard binomial coefficient `binom n k`. -/
def binom : Nat → Nat → Nat
  | 0, 0 => 1
  | 0, _ + 1 => 0
  | _ + 1, 0 => 1
  | n + 1, k + 1 => binom n k + binom n (k + 1)

/-- Enumeration of all `2^n` masks on `Fin n`. -/
def allMasks : (n : Nat) → List (Mask n)
  | 0 => [emptyMask 0]
  | n + 1 => (allMasks n).map (consMask false) ++ (allMasks n).map (consMask true)

/-- Exact count of masks of degree `p` in `allMasks n` equals `binom n p`. -/
theorem countP_degMask_allMasks (n p : Nat) :
    (allMasks n).countP (fun I => degMask I == p) = binom n p := by
  induction n generalizing p with
  | zero =>
    cases p with
    | zero => rfl
    | succ p' => rfl
  | succ n ih =>
    simp only [allMasks, List.countP_append, List.countP_map]
    cases p with
    | zero =>
      have hf :
          List.countP ((fun I : Mask (n + 1) => degMask I == 0) ∘ consMask false) (allMasks n) =
          List.countP (fun I : Mask n => degMask I == 0) (allMasks n) := by
        congr 1
        funext I
        simp [Function.comp]
      have ht :
          List.countP ((fun I : Mask (n + 1) => degMask I == 0) ∘ consMask true) (allMasks n) = 0 := by
        rw [List.countP_eq_zero]
        intro I _
        simp [Function.comp]
      rw [hf, ht, Nat.add_zero, ih 0]
      cases n <;> rfl
    | succ p' =>
      have hf :
          List.countP ((fun I : Mask (n + 1) => degMask I == p' + 1) ∘ consMask false) (allMasks n) =
          List.countP (fun I : Mask n => degMask I == p' + 1) (allMasks n) := by
        congr 1
        funext I
        simp [Function.comp]
      have ht :
          List.countP ((fun I : Mask (n + 1) => degMask I == p' + 1) ∘ consMask true) (allMasks n) =
          List.countP (fun I : Mask n => degMask I == p') (allMasks n) := by
        congr 1
        funext I
        simp only [Function.comp, degMask_consMask, b2n_true]
        by_cases h : degMask I = p'
        · have h1 : (1 + degMask I == p' + 1) = true := by simp [beq_iff_eq]; omega
          have h2 : (degMask I == p') = true := by simp [beq_iff_eq, h]
          rw [h1, h2]
        · have h1 : (1 + degMask I == p' + 1) = false := by simp [beq_eq_false_iff_ne]; omega
          have h2 : (degMask I == p') = false := by simp [beq_eq_false_iff_ne, h]
          rw [h1, h2]
      rw [hf, ht, ih (p' + 1), ih p', binom]
      omega

theorem binom_zero_right (n : Nat) : binom n 0 = 1 := by
  cases n <;> rfl

theorem binom_eq_zero_of_lt (n k : Nat) (h : n < k) : binom n k = 0 := by
  induction n generalizing k with
  | zero =>
    cases k with
    | zero => omega
    | succ _ => rfl
  | succ m ih =>
    cases k with
    | zero => omega
    | succ k' =>
      rw [binom, ih k' (by omega), ih (k' + 1) (by omega)]

theorem binom_self (n : Nat) : binom n n = 1 := by
  induction n with
  | zero => rfl
  | succ m ih =>
    rw [binom, ih, binom_eq_zero_of_lt m (m + 1) (by omega)]

theorem binom_one (n : Nat) : binom n 1 = n := by
  induction n with
  | zero => rfl
  | succ m ih =>
    rw [binom, binom_zero_right, ih]
    omega

theorem binom_pred (n : Nat) : binom (n + 1) n = n + 1 := by
  induction n with
  | zero => rfl
  | succ m ih =>
    rw [binom, ih, binom_self]

theorem binom_pos (n k : Nat) (hk : k ≤ n) : 1 ≤ binom n k := by
  induction n generalizing k with
  | zero =>
    have hk0 : k = 0 := by omega
    subst hk0
    decide
  | succ n ih =>
    cases k with
    | zero => simp [binom]
    | succ k' =>
      rw [binom]
      have h := ih k' (by omega)
      omega

theorem binom_ge_n_of_between (n k : Nat) (hk1 : 1 ≤ k) (hkn : k < n) :
    n ≤ binom n k := by
  induction n generalizing k with
  | zero => omega
  | succ m ih =>
    cases k with
    | zero => omega
    | succ k' =>
      rw [binom]
      by_cases hk0 : k' = 0
      · subst hk0
        rw [binom_zero_right, binom_one]
        omega
      · by_cases htop : m = k' + 1
        · subst htop
          rw [binom_pred, binom_self]
          omega
        · have h1 : m ≤ binom m k' := ih k' (by omega) (by omega)
          have h2 : 1 ≤ binom m (k' + 1) := binom_pos m (k' + 1) (by omega)
          omega

/-- Algebraic rank (subspace codimension) of the self-duality condition `⋆ω = ω` inside `Λ^m(ℝ^{r,s})`:
    - `0` when `m = 0` and `s` even (`1` when `m = 0` and `s` odd),
    - `binom (2m - 1) m = (1/2) binom (2m) m` when `m ≥ 1` and `(m^2 + s) % 2 = 0` (`⋆^2 = +id`),
    - `binom (2m) m` when `m ≥ 1` and `(m^2 + s) % 2 = 1` (`⋆^2 = -id`, `Λ^m_+ = {0}`). -/
def selfDualSubspaceCodim (m s : Nat) : Nat :=
  if m = 0 then
    if s % 2 == 0 then 0 else 1
  else if (m * m + s) % 2 == 0 then
    binom (2 * m - 1) m
  else
    binom (2 * m) m

/--
  **Exact Characterization of Subspace Codimension One (`m ≥ 1`):**
  For positive middle degree `m ≥ 1`, the linear condition `⋆ω = ω` inside `Λ^m(ℝ^{r,s})`
  has subspace codimension `1` **if and only if `m = 1` AND `s` is odd** (e.g. `ℝ^{1,1}`).
-/
theorem selfDualSubspaceCodim_eq_one_iff {m : Nat} (hm : 1 ≤ m) (s : Nat) :
    selfDualSubspaceCodim m s = 1 ↔ (m = 1 ∧ s % 2 = 1) := by
  unfold selfDualSubspaceCodim
  have hm0 : m ≠ 0 := by omega
  simp only [hm0, ↓reduceIte]
  by_cases hm1 : m = 1
  · subst hm1
    have hs : s % 2 = 0 ∨ s % 2 = 1 := by omega
    rcases hs with hs0 | hs1
    · have hpar : (1 * 1 + s) % 2 = 1 := by omega
      have hbf : ((1 * 1 + s) % 2 == 0) = false := by simp [hpar]
      rw [hbf]
      have hb21 : binom 2 1 = 2 := rfl
      simp [hb21, hs0]
    · have hpar : (1 * 1 + s) % 2 = 0 := by omega
      have hbt : ((1 * 1 + s) % 2 == 0) = true := by simp [hpar]
      rw [hbt]
      have hb11 : binom 1 1 = 1 := rfl
      simp [hb11, hs1]
  · have hm2 : 2 ≤ m := by omega
    constructor
    · intro hcod
      by_cases hpar : ((m * m + s) % 2 == 0) = true
      · rw [if_pos hpar] at hcod
        have hge := binom_ge_n_of_between (2 * m - 1) m (by omega) (by omega)
        omega
      · rw [if_neg hpar] at hcod
        have hge := binom_ge_n_of_between (2 * m) m (by omega) (by omega)
        omega
    · rintro ⟨rfl, _⟩
      exact absurd rfl hm1

/--
  **Riemannian Subspace Codimension Obstruction:**
  In Riemannian signature (`s = 0`), for *every* `m : Nat` (`m = 0, 1, 2, ...`),
  the subspace codimension of `Λ^m_+(ℝ^{2m})` inside `Λ^m(ℝ^{2m})` is **never** `1`!
-/
theorem riemannian_selfDualSubspaceCodim_ne_one (m : Nat) :
    selfDualSubspaceCodim m 0 ≠ 1 := by
  cases m with
  | zero => decide
  | succ m' =>
    intro h1
    have hiff := (selfDualSubspaceCodim_eq_one_iff (by omega : 1 ≤ m' + 1) 0).mp h1
    omega

/-! ## 3. Explicit Positive Non-Vacuity Witnesses -/

private theorem one_smul_extForm {n : Nat} (α : ExtForm n) : (1 : Int) * α = α := by
  funext I
  simp

private theorem add_comm_extForm {n : Nat} (α β : ExtForm n) : α + β = β + α := by
  funext I
  simp only [addForm_apply]
  omega

/-- **Witness 1:** The Yang–Mills self-dual 2-form `e_0 ∧ e_1 + e_2 ∧ e_3` on Euclidean `ℝ^4` (`(4, 0)`). -/
def ymSelfDual2Form : ExtForm 4 :=
  wedge (covector ⟨0, by decide⟩) (covector ⟨1, by decide⟩) +
  wedge (covector ⟨2, by decide⟩) (covector ⟨3, by decide⟩)

theorem ymSelfDual2Form_eq_basis :
    ymSelfDual2Form =
      basisForm (orMask (singleMask (n := 4) ⟨0, by decide⟩) (singleMask ⟨1, by decide⟩)) +
      basisForm (orMask (singleMask (n := 4) ⟨2, by decide⟩) (singleMask ⟨3, by decide⟩)) := by
  unfold ymSelfDual2Form covector
  rw [wedge_basisForm, wedge_basisForm]
  have hd01 : disjointMask (singleMask (n := 4) ⟨0, by decide⟩) (singleMask ⟨1, by decide⟩) = true := by decide
  have hd23 : disjointMask (singleMask (n := 4) ⟨2, by decide⟩) (singleMask ⟨3, by decide⟩) = true := by decide
  have hs01 : signPow (invCount (singleMask (n := 4) ⟨0, by decide⟩) (singleMask ⟨1, by decide⟩)) = 1 := by decide
  have hs23 : signPow (invCount (singleMask (n := 4) ⟨2, by decide⟩) (singleMask ⟨3, by decide⟩)) = 1 := by decide
  rw [if_pos hd01, if_pos hd23, hs01, hs23, one_smul_extForm, one_smul_extForm]

theorem ymSelfDual2Form_homogeneous : IsHomogeneous 2 ymSelfDual2Form := by
  unfold ymSelfDual2Form
  exact ((isHomogeneous_covector _).wedge (isHomogeneous_covector _)).add
        ((isHomogeneous_covector _).wedge (isHomogeneous_covector _))

theorem ymSelfDual2Form_ne_zero : ymSelfDual2Form ≠ 0 := by
  intro h0
  rw [ymSelfDual2Form_eq_basis] at h0
  let I₀₁ := orMask (singleMask (n := 4) ⟨0, by decide⟩) (singleMask ⟨1, by decide⟩)
  have heval := congrFun h0 I₀₁
  exact absurd heval (by decide)

theorem ymSelfDual2Form_selfDual : IsSelfDual (riemSig 4) ymSelfDual2Form := by
  unfold IsSelfDual
  rw [ymSelfDual2Form_eq_basis, hodgeStar_add, hodgeStar_basisForm, hodgeStar_basisForm]
  let I₀₁ := orMask (singleMask (n := 4) ⟨0, by decide⟩) (singleMask ⟨1, by decide⟩)
  let I₂₃ := orMask (singleMask (n := 4) ⟨2, by decide⟩) (singleMask ⟨3, by decide⟩)
  have hc1 : compMask I₀₁ = I₂₃ := (maskEq_iff _ _).mp (by decide)
  have hc2 : compMask I₂₃ = I₀₁ := (maskEq_iff _ _).mp (by decide)
  have hs1 : etaSign (riemSig 4) I₀₁ * signPow (invCount I₀₁ (compMask I₀₁)) = 1 := by decide
  have hs2 : etaSign (riemSig 4) I₂₃ * signPow (invCount I₂₃ (compMask I₂₃)) = 1 := by decide
  change (etaSign (riemSig 4) I₀₁ * signPow (invCount I₀₁ (compMask I₀₁))) * basisForm (compMask I₀₁) +
         (etaSign (riemSig 4) I₂₃ * signPow (invCount I₂₃ (compMask I₂₃))) * basisForm (compMask I₂₃) =
         basisForm I₀₁ + basisForm I₂₃
  rw [hs1, hs2, hc1, hc2, one_smul_extForm, one_smul_extForm, add_comm_extForm]

/-- **Witness 2:** The lightcone self-dual 1-form `e_0 + e_1` on the Lorentzian plane `ℝ^{1,1}`. -/
def lor2SelfDual1Form : ExtForm 2 :=
  covector ⟨0, by decide⟩ + covector ⟨1, by decide⟩

theorem lor2SelfDual1Form_homogeneous : IsHomogeneous 1 lor2SelfDual1Form :=
  (isHomogeneous_covector _).add (isHomogeneous_covector _)

theorem lor2SelfDual1Form_ne_zero : lor2SelfDual1Form ≠ 0 := by
  intro h0
  have heval := congrFun h0 (singleMask (n := 2) ⟨0, by decide⟩)
  exact absurd heval (by decide)

theorem lor2SelfDual1Form_selfDual : IsSelfDual (sigOfRS 2 1) lor2SelfDual1Form := by
  unfold IsSelfDual lor2SelfDual1Form covector
  rw [hodgeStar_add, hodgeStar_basisForm, hodgeStar_basisForm]
  let I₀ := singleMask (n := 2) ⟨0, by decide⟩
  let I₁ := singleMask (n := 2) ⟨1, by decide⟩
  have hc0 : compMask I₀ = I₁ := (maskEq_iff _ _).mp (by decide)
  have hc1 : compMask I₁ = I₀ := (maskEq_iff _ _).mp (by decide)
  have hs0 : etaSign (sigOfRS 2 1) I₀ * signPow (invCount I₀ (compMask I₀)) = 1 := by decide
  have hs1 : etaSign (sigOfRS 2 1) I₁ * signPow (invCount I₁ (compMask I₁)) = 1 := by decide
  change (etaSign (sigOfRS 2 1) I₀ * signPow (invCount I₀ (compMask I₀))) * basisForm (compMask I₀) +
         (etaSign (sigOfRS 2 1) I₁ * signPow (invCount I₁ (compMask I₁))) * basisForm (compMask I₁) =
         basisForm I₀ + basisForm I₁
  rw [hs0, hs1, hc0, hc1, one_smul_extForm, one_smul_extForm, add_comm_extForm]

/-- **Witness 3:** A non-zero self-dual 3-form `e_0 ∧ e_1 ∧ e_2 + e_3 ∧ e_4 ∧ e_5` on Lorentzian `ℝ^{5,1}`
    at middle degree `3` (where codimension is `6 - 3 = 3 ≠ 1`). -/
def lor6SelfDual3Form : ExtForm 6 :=
  wedge (wedge (covector ⟨0, by decide⟩) (covector ⟨1, by decide⟩)) (covector ⟨2, by decide⟩) +
  wedge (wedge (covector ⟨3, by decide⟩) (covector ⟨4, by decide⟩)) (covector ⟨5, by decide⟩)

theorem lor6SelfDual3Form_eq_basis :
    lor6SelfDual3Form =
      basisForm (orMask (orMask (singleMask (n := 6) ⟨0, by decide⟩) (singleMask ⟨1, by decide⟩))
                        (singleMask ⟨2, by decide⟩)) +
      basisForm (orMask (orMask (singleMask (n := 6) ⟨3, by decide⟩) (singleMask ⟨4, by decide⟩))
                        (singleMask ⟨5, by decide⟩)) := by
  unfold lor6SelfDual3Form covector
  rw [wedge_basisForm (singleMask ⟨0, by decide⟩) (singleMask ⟨1, by decide⟩)]
  have hd01 : disjointMask (singleMask (n := 6) ⟨0, by decide⟩) (singleMask ⟨1, by decide⟩) = true := by decide
  have hs01 : signPow (invCount (singleMask (n := 6) ⟨0, by decide⟩) (singleMask ⟨1, by decide⟩)) = 1 := by decide
  rw [if_pos hd01, hs01, one_smul_extForm, wedge_basisForm]
  have hd012 : disjointMask (orMask (singleMask (n := 6) ⟨0, by decide⟩) (singleMask ⟨1, by decide⟩))
                            (singleMask ⟨2, by decide⟩) = true := by decide
  have hs012 : signPow (invCount (orMask (singleMask (n := 6) ⟨0, by decide⟩) (singleMask ⟨1, by decide⟩))
                                 (singleMask ⟨2, by decide⟩)) = 1 := by decide
  rw [if_pos hd012, hs012, one_smul_extForm]
  rw [wedge_basisForm (singleMask ⟨3, by decide⟩) (singleMask ⟨4, by decide⟩)]
  have hd34 : disjointMask (singleMask (n := 6) ⟨3, by decide⟩) (singleMask ⟨4, by decide⟩) = true := by decide
  have hs34 : signPow (invCount (singleMask (n := 6) ⟨3, by decide⟩) (singleMask ⟨4, by decide⟩)) = 1 := by decide
  rw [if_pos hd34, hs34, one_smul_extForm, wedge_basisForm]
  have hd345 : disjointMask (orMask (singleMask (n := 6) ⟨3, by decide⟩) (singleMask ⟨4, by decide⟩))
                            (singleMask ⟨5, by decide⟩) = true := by decide
  have hs345 : signPow (invCount (orMask (singleMask (n := 6) ⟨3, by decide⟩) (singleMask ⟨4, by decide⟩))
                                 (singleMask ⟨5, by decide⟩)) = 1 := by decide
  rw [if_pos hd345, hs345, one_smul_extForm]

theorem lor6SelfDual3Form_homogeneous : IsHomogeneous 3 lor6SelfDual3Form := by
  unfold lor6SelfDual3Form
  exact (((isHomogeneous_covector _).wedge (isHomogeneous_covector _)).wedge (isHomogeneous_covector _)).add
        (((isHomogeneous_covector _).wedge (isHomogeneous_covector _)).wedge (isHomogeneous_covector _))

theorem lor6SelfDual3Form_ne_zero : lor6SelfDual3Form ≠ 0 := by
  intro h0
  rw [lor6SelfDual3Form_eq_basis] at h0
  let I₀₁₂ := orMask (orMask (singleMask (n := 6) ⟨0, by decide⟩) (singleMask ⟨1, by decide⟩)) (singleMask ⟨2, by decide⟩)
  have heval := congrFun h0 I₀₁₂
  exact absurd heval (by decide)

theorem lor6SelfDual3Form_selfDual : IsSelfDual (sigOfRS 6 5) lor6SelfDual3Form := by
  unfold IsSelfDual
  rw [lor6SelfDual3Form_eq_basis, hodgeStar_add, hodgeStar_basisForm, hodgeStar_basisForm]
  let I₀₁₂ := orMask (orMask (singleMask (n := 6) ⟨0, by decide⟩) (singleMask ⟨1, by decide⟩)) (singleMask ⟨2, by decide⟩)
  let I₃₄₅ := orMask (orMask (singleMask (n := 6) ⟨3, by decide⟩) (singleMask ⟨4, by decide⟩)) (singleMask ⟨5, by decide⟩)
  have hc1 : compMask I₀₁₂ = I₃₄₅ := (maskEq_iff _ _).mp (by decide)
  have hc2 : compMask I₃₄₅ = I₀₁₂ := (maskEq_iff _ _).mp (by decide)
  have hs1 : etaSign (sigOfRS 6 5) I₀₁₂ * signPow (invCount I₀₁₂ (compMask I₀₁₂)) = 1 := by decide
  have hs2 : etaSign (sigOfRS 6 5) I₃₄₅ * signPow (invCount I₃₄₅ (compMask I₃₄₅)) = 1 := by decide
  change (etaSign (sigOfRS 6 5) I₀₁₂ * signPow (invCount I₀₁₂ (compMask I₀₁₂))) * basisForm (compMask I₀₁₂) +
         (etaSign (sigOfRS 6 5) I₃₄₅ * signPow (invCount I₃₄₅ (compMask I₃₄₅))) * basisForm (compMask I₃₄₅) =
         basisForm I₀₁₂ + basisForm I₃₄₅
  rw [hs1, hs2, hc1, hc2, one_smul_extForm, one_smul_extForm, add_comm_extForm]

/-! ## 4. Formal Refutations of Every False Clause & Complete Conjecture Disproofs -/

/--
  **Refutation 1A (Pseudo-Riemannian Signature Omission, `ℝ^{1,1}`, `p = 0`):**
  On `ℝ^{1,1}`, `⋆(⋆ 1) = -1`, refuting the signature-free formula `(-1)^{p(n-p)} 1 = +1`.
-/
theorem refute_sigFree_lor2_deg0 :
    hodgeStar (sigOfRS 2 1) (hodgeStar (sigOfRS 2 1) (unitForm 2)) ≠
      signPow (0 * (2 - 0)) * unitForm 2 := by
  intro h
  rw [hodgeStar_hodgeStar_sigOfRS (r := 1) (s := 1) rfl (isHomogeneous_unitForm 2)] at h
  have heval := congrFun h (emptyMask 2)
  simp only [smulForm_apply, unitForm, basisForm, ↓reduceIte] at heval
  exact absurd heval (by decide)

/--
  **Refutation 1B (4D Minkowski Spacetime `ℝ^{3,1}`, `p = 2`):**
  On 4D Minkowski spacetime `ℝ^{3,1}`, `⋆(⋆(e_0 ∧ e_1)) = -(e_0 ∧ e_1)`,
  refuting the signature-free formula `(-1)^{2(4-2)} (e_0 ∧ e_1) = +(e_0 ∧ e_1)`.
-/
theorem refute_sigFree_minkowski4_deg2 :
    let ω := wedge (covector (n := 4) ⟨0, by decide⟩) (covector (n := 4) ⟨1, by decide⟩)
    hodgeStar (sigOfRS 4 3) (hodgeStar (sigOfRS 4 3) ω) ≠ signPow (2 * (4 - 2)) * ω := by
  dsimp only
  intro h
  have hω_hom : IsHomogeneous 2 (wedge (covector (n := 4) ⟨0, by decide⟩) (covector ⟨1, by decide⟩)) :=
    (isHomogeneous_covector _).wedge (isHomogeneous_covector _)
  rw [hodgeStar_hodgeStar_sigOfRS (r := 3) (s := 1) rfl hω_hom] at h
  have hbasis :
      wedge (covector (n := 4) ⟨0, by decide⟩) (covector ⟨1, by decide⟩) =
        basisForm (orMask (singleMask (n := 4) ⟨0, by decide⟩) (singleMask ⟨1, by decide⟩)) := by
    unfold covector
    rw [wedge_basisForm]
    have hd : disjointMask (singleMask (n := 4) ⟨0, by decide⟩) (singleMask ⟨1, by decide⟩) = true := by decide
    have hs : signPow (invCount (singleMask (n := 4) ⟨0, by decide⟩) (singleMask ⟨1, by decide⟩)) = 1 := by decide
    rw [if_pos hd, hs, one_smul_extForm]
  rw [hbasis] at h
  let I₀₁ := orMask (singleMask (n := 4) ⟨0, by decide⟩) (singleMask ⟨1, by decide⟩)
  have heval := congrFun h I₀₁
  simp only [smulForm_apply, basisForm, ↓reduceIte] at heval
  exact absurd heval (by decide)

/--
  **Refutation 2 (Literal "Product of Codimensions" `(n - p)^2` in Riemannian Signature):**
  Even in positive-definite Euclidean `ℝ^3` (`s = 0`) on `0`-forms (`p = 0`),
  `⋆(⋆ 1) = +1`, whereas `(-1)^{(3 - 0)(3 - 0)} 1 = (-1)^9 1 = -1`.
-/
theorem refute_codimProduct_riem3_deg0 :
    hodgeStar (riemSig 3) (hodgeStar (riemSig 3) (unitForm 3)) ≠
      signPow ((3 - 0) * (3 - 0)) * unitForm 3 := by
  intro h
  rw [hodgeStar_hodgeStar_riemannian (isHomogeneous_unitForm 3)] at h
  have heval := congrFun h (emptyMask 3)
  simp only [smulForm_apply, unitForm, basisForm, ↓reduceIte] at heval
  exact absurd heval (by decide)

/--
  **Refutation 3A (Riemannian Middle Dimension at Codimension 1, `n = 2, p = 1`):**
  In the Euclidean plane `ℝ^2` (`n = 2`, middle degree `p = 1`, codimension `2 - 1 = 1`),
  `⋆(⋆ω) = -ω` and **no** non-zero self-dual 1-form exists (`⋆ω = ω ⟹ ω = 0`).
-/
theorem refute_riemannian_codim1_selfDual :
    ∀ ω : ExtForm 2, IsHomogeneous 1 ω → IsSelfDual (riemSig 2) ω → ω = 0 := by
  intro ω hω hsd
  exact no_nonzero_selfDual_of_odd (m := 1) (riemSig 2) rfl hω hsd

/--
  **Refutation 3B (Every Positive Riemannian Self-Dual Dimension Has Codimension `≥ 2 ≠ 1`):**
  Whenever `m ≥ 1` and Euclidean `ℝ^{2m}` admits a non-zero self-dual `m`-form,
  the form codimension `2m - m = m` satisfies `m ≥ 2` (hence `2m - m ≠ 1`) AND
  the subspace codimension `selfDualSubspaceCodim m 0` is also `≠ 1`.
-/
theorem riemannian_selfDual_codim_ne_one {m : Nat} (hm : 1 ≤ m)
    (hex : ∃ ω : ExtForm (2 * m), IsHomogeneous m ω ∧ ω ≠ 0 ∧ IsSelfDual (riemSig (2 * m)) ω) :
    2 * m - m ≠ 1 ∧ selfDualSubspaceCodim m 0 ≠ 1 := by
  have heven : m % 2 = 0 := (riemannian_selfDual_iff_even hm).mp hex
  exact ⟨by omega, riemannian_selfDualSubspaceCodim_ne_one m⟩

/--
  **Refutation 3C (Lorentzian Middle-Dimension Self-Duality Holds Beyond Codimension 1):**
  In Lorentzian signature (`s = 1`), middle-dimension self-duality is NOT restricted to
  codimension `1`: at `n = 6, m = 3` (`ℝ^{5,1}`), `lor6SelfDual3Form` is a non-zero self-dual
  `3`-form with form codimension `6 - 3 = 3 ≠ 1` and subspace codimension `10 ≠ 1`.
-/
theorem refute_lorentzian_exclusively_codim1 :
    (∃ ω : ExtForm 6, IsHomogeneous 3 ω ∧ ω ≠ 0 ∧ IsSelfDual (sigOfRS 6 5) ω) ∧
      (6 - 3 ≠ 1) ∧ (selfDualSubspaceCodim 3 1 ≠ 1) := by
  refine ⟨⟨lor6SelfDual3Form, lor6SelfDual3Form_homogeneous, lor6SelfDual3Form_ne_zero,
            lor6SelfDual3Form_selfDual⟩, by decide, by decide⟩

/-! ### Bundled Conjecture Statements and Formal Negations Under All Natural Readings -/

/-- **Reading I (Literal Riemannian Reading):**
    1. Exponent is the literal product of codimensions `(n - p) * (n - p)`; and
    2. Middle-dimension self-duality holds at codimension `1` (`n = 2, m = 1`). -/
def Conjecture7615_LiteralRiemannian : Prop :=
  (∀ (n p : Nat) (ω : ExtForm n),
    p ≤ n → IsHomogeneous p ω →
    hodgeStar (riemSig n) (hodgeStar (riemSig n) ω) = signPow ((n - p) * (n - p)) * ω) ∧
  (∃ ω : ExtForm 2, IsHomogeneous 1 ω ∧ ω ≠ 0 ∧ IsSelfDual (riemSig 2) ω)

theorem not_Conjecture7615_LiteralRiemannian : ¬ Conjecture7615_LiteralRiemannian := by
  rintro ⟨hlaw, _⟩
  exact refute_codimProduct_riem3_deg0 (hlaw 3 0 (unitForm 3) (by omega) (isHomogeneous_unitForm 3))

/-- **Reading II (Charitable Riemannian Reading — interpreting `p * (n - p)` as dual codimension product,
    and testing EITHER form codimension `n - m = 1` OR subspace codimension `selfDualSubspaceCodim m 0 = 1`):** -/
def Conjecture7615_CharitableRiemannian : Prop :=
  (∀ (n p : Nat) (ω : ExtForm n),
    p ≤ n → IsHomogeneous p ω →
    hodgeStar (riemSig n) (hodgeStar (riemSig n) ω) = signPow (p * (n - p)) * ω) ∧
  (∃ m : Nat, 1 ≤ m ∧
    (∃ ω : ExtForm (2 * m), IsHomogeneous m ω ∧ ω ≠ 0 ∧ IsSelfDual (riemSig (2 * m)) ω) ∧
    (2 * m - m = 1 ∨ selfDualSubspaceCodim m 0 = 1))

theorem not_Conjecture7615_CharitableRiemannian : ¬ Conjecture7615_CharitableRiemannian := by
  rintro ⟨_, ⟨m, hm, hex, hcod⟩⟩
  have hne := riemannian_selfDual_codim_ne_one hm hex
  rcases hcod with hc1 | hc2
  · exact hne.1 hc1
  · exact hne.2 hc2

/-- **Reading III (General Pseudo-Riemannian Reading — testing the signature-free exponent `p * (n - p)`
    on general signatures `(r, s)` alongside middle-dimension codimension-1 uniqueness):** -/
def Conjecture7615_PseudoRiemannian : Prop :=
  (∀ (n r s p : Nat) (ω : ExtForm n),
    r + s = n → p ≤ n → IsHomogeneous p ω →
    hodgeStar (sigOfRS n r) (hodgeStar (sigOfRS n r) ω) = signPow (p * (n - p)) * ω) ∧
  (∀ (m r s : Nat), 1 ≤ m → r + s = 2 * m →
    ((∃ ω : ExtForm (2 * m), IsHomogeneous m ω ∧ ω ≠ 0 ∧ IsSelfDual (sigOfRS (2 * m) r) ω) ↔
      2 * m - m = 1))

theorem not_Conjecture7615_PseudoRiemannian : ¬ Conjecture7615_PseudoRiemannian := by
  rintro ⟨hlaw, _⟩
  exact refute_sigFree_lor2_deg0
    (hlaw 2 1 1 0 (unitForm 2) rfl (by omega) (isHomogeneous_unitForm 2))

end HodgeDoubleStar
