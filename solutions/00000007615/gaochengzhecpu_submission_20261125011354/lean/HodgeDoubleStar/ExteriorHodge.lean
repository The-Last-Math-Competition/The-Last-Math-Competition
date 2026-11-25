/-
  HodgeDoubleStar/ExteriorHodge.lean
  First-principles construction of the exterior algebra Λ(ℝ^{r,s}), wedge product,
  pseudo-Riemannian Gram inner product, Hodge star duality characterization, and
  the exact double-star sign law theorem in core Lean 4.
-/
import HodgeDoubleStar.Basic

namespace HodgeDoubleStar

/-- Exterior form in `Λ(ℝ^n)` with integer coefficients, represented on the `2^n` basis bitmasks. -/
abbrev ExtForm (n : Nat) : Type := Mask n → Int

def zeroForm (n : Nat) : ExtForm n := fun _ => 0
def addForm {n : Nat} (α β : ExtForm n) : ExtForm n := fun I => α I + β I
def negForm {n : Nat} (α : ExtForm n) : ExtForm n := fun I => -(α I)
def subForm {n : Nat} (α β : ExtForm n) : ExtForm n := fun I => α I - β I
def smulForm {n : Nat} (c : Int) (α : ExtForm n) : ExtForm n := fun I => c * α I

instance {n : Nat} : Zero (ExtForm n) := ⟨zeroForm n⟩
instance {n : Nat} : Add (ExtForm n) := ⟨addForm⟩
instance {n : Nat} : Neg (ExtForm n) := ⟨negForm⟩
instance {n : Nat} : Sub (ExtForm n) := ⟨subForm⟩
instance {n : Nat} : HMul Int (ExtForm n) (ExtForm n) := ⟨smulForm⟩

@[simp] theorem zeroForm_apply {n : Nat} (I : Mask n) : (0 : ExtForm n) I = 0 := rfl
@[simp] theorem addForm_apply {n : Nat} (α β : ExtForm n) (I : Mask n) : (α + β) I = α I + β I := rfl
@[simp] theorem negForm_apply {n : Nat} (α : ExtForm n) (I : Mask n) : (-α) I = -(α I) := rfl
@[simp] theorem subForm_apply {n : Nat} (α β : ExtForm n) (I : Mask n) : (α - β) I = α I - β I := rfl
@[simp] theorem smulForm_apply {n : Nat} (c : Int) (α : ExtForm n) (I : Mask n) :
    (c * α) I = c * α I := rfl

/-- Standard basis blade `e_I = e_{i_1} ∧ ... ∧ e_{i_p}` associated to a subset `I : Mask n`. -/
def basisForm {n : Nat} (I : Mask n) : ExtForm n :=
  fun J => if J = I then 1 else 0

/-- Elementary 1-form `e_i ∈ Λ^1(ℝ^n)` for `i : Fin n`. -/
def singleMask {n : Nat} (i : Fin n) : Mask n :=
  fun j => decide (j.val = i.val)

def covector {n : Nat} (i : Fin n) : ExtForm n :=
  basisForm (singleMask i)

/-- Unit scalar 0-form `1 = e_∅ ∈ Λ^0(ℝ^n)`. -/
def unitForm (n : Nat) : ExtForm n :=
  basisForm (emptyMask n)

/-- Canonical orientation volume form `vol = e_0 ∧ e_1 ∧ ... ∧ e_{n-1} ∈ Λ^n(ℝ^n)`. -/
def volForm (n : Nat) : ExtForm n :=
  basisForm (fullMask n)

/-- Homogeneous `p`-form predicate (`ω ∈ Λ^p(ℝ^n)`). -/
def IsHomogeneous {n : Nat} (p : Nat) (ω : ExtForm n) : Prop :=
  ∀ I : Mask n, degMask I ≠ p → ω I = 0

/-- Typed submodule `Λ^p(ℝ^n)` of homogeneous `p`-forms. -/
abbrev LambdaP (n p : Nat) : Type := { ω : ExtForm n // IsHomogeneous p ω }

theorem isHomogeneous_zero (n p : Nat) : IsHomogeneous p (0 : ExtForm n) :=
  fun _ _ => rfl

theorem IsHomogeneous.add {n p : Nat} {α β : ExtForm n}
    (hα : IsHomogeneous p α) (hβ : IsHomogeneous p β) : IsHomogeneous p (α + β) := by
  intro I hI
  simp [hα I hI, hβ I hI]

theorem IsHomogeneous.neg {n p : Nat} {α : ExtForm n}
    (hα : IsHomogeneous p α) : IsHomogeneous p (-α) := by
  intro I hI
  simp [hα I hI]

theorem IsHomogeneous.sub {n p : Nat} {α β : ExtForm n}
    (hα : IsHomogeneous p α) (hβ : IsHomogeneous p β) : IsHomogeneous p (α - β) := by
  intro I hI
  simp [hα I hI, hβ I hI]

theorem IsHomogeneous.smul {n p : Nat} (c : Int) {α : ExtForm n}
    (hα : IsHomogeneous p α) : IsHomogeneous p (c * α) := by
  intro I hI
  simp [hα I hI]

theorem isHomogeneous_basisForm {n : Nat} (I : Mask n) :
    IsHomogeneous (degMask I) (basisForm I) := by
  intro J hJ
  simp only [basisForm]
  split
  · next hJI =>
    subst hJI
    exact absurd rfl hJ
  · rfl

theorem isHomogeneous_unitForm (n : Nat) : IsHomogeneous 0 (unitForm n) := by
  have h := isHomogeneous_basisForm (emptyMask n)
  simpa [unitForm] using h

theorem isHomogeneous_volForm (n : Nat) : IsHomogeneous n (volForm n) := by
  have h := isHomogeneous_basisForm (fullMask n)
  simpa [volForm] using h

theorem degMask_singleMask {n : Nat} (i : Fin n) : degMask (singleMask i) = 1 := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    refine Fin.cases ?_ ?_ i
    · have hhead : headMask (singleMask (0 : Fin (n + 1))) = true := rfl
      have htail : tailMask (singleMask (0 : Fin (n + 1))) = emptyMask n := by
        funext j
        simp [tailMask, singleMask, Fin.succ, emptyMask]
      rw [degMask, hhead, htail, b2n_true, degMask_empty]
    · intro j
      have hhead : headMask (singleMask j.succ) = false := by
        simp [headMask, singleMask, Fin.succ]
      have htail : tailMask (singleMask j.succ) = singleMask j := by
        funext k
        simp [tailMask, singleMask, Fin.succ]
      simp [degMask, hhead, htail, ih j]

theorem isHomogeneous_covector {n : Nat} (i : Fin n) : IsHomogeneous 1 (covector i) := by
  have h := isHomogeneous_basisForm (singleMask i)
  rw [degMask_singleMask] at h
  exact h

/-- Exact finite summation over all `2^n` masks `I : Mask n`. -/
def sumMasks : {n : Nat} → (Mask n → Int) → Int
  | 0, f => f (emptyMask 0)
  | _ + 1, f =>
      sumMasks (fun I => f (consMask false I)) + sumMasks (fun I => f (consMask true I))

@[simp] theorem sumMasks_zero (n : Nat) : sumMasks (fun _ : Mask n => (0 : Int)) = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [sumMasks, ih]

theorem sumMasks_congr {n : Nat} {f g : Mask n → Int} (h : ∀ I, f I = g I) :
    sumMasks f = sumMasks g := by
  congr 1
  funext I
  exact h I

theorem sumMasks_add {n : Nat} (f g : Mask n → Int) :
    sumMasks (fun I => f I + g I) = sumMasks f + sumMasks g := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [sumMasks, ih]
    omega

theorem sumMasks_mul_left {n : Nat} (c : Int) (f : Mask n → Int) :
    sumMasks (fun I => c * f I) = c * sumMasks f := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [sumMasks, ih, Int.mul_add]

theorem sumMasks_ite_eq {n : Nat} (I₀ : Mask n) (f : Mask n → Int) :
    sumMasks (fun I => if I = I₀ then f I else 0) = f I₀ := by
  induction n with
  | zero =>
    simp [sumMasks, mask_zero_eq (emptyMask 0) I₀]
  | succ n ih =>
    simp only [sumMasks]
    cases hh : headMask I₀
    · have hfalse : ∀ I : Mask n, (consMask false I = I₀) ↔ (I = tailMask I₀) := by
        intro I
        constructor
        · intro heq
          rw [← heq, tailMask_consMask]
        · intro heq
          rw [heq, ← hh, consMask_eta]
      have htrue : ∀ I : Mask n, consMask true I ≠ I₀ := by
        intro I heq
        have h0 := congrArg headMask heq
        simp [hh] at h0
      have hs1 :
          sumMasks (fun I => if consMask false I = I₀ then f (consMask false I) else 0) =
          sumMasks (fun I => if I = tailMask I₀ then f (consMask false I) else 0) := by
        apply sumMasks_congr
        intro I
        by_cases hI : I = tailMask I₀
        · have hc : consMask false I = I₀ := (hfalse I).mpr hI
          rw [if_pos hc, if_pos hI]
        · have hc : consMask false I ≠ I₀ := fun h => hI ((hfalse I).mp h)
          rw [if_neg hc, if_neg hI]
      have hs2 :
          sumMasks (fun I => if consMask true I = I₀ then f (consMask true I) else 0) = 0 := by
        rw [sumMasks_congr (g := fun _ => 0)]
        · exact sumMasks_zero n
        · intro I
          rw [if_neg (htrue I)]
      rw [hs1, hs2, Int.add_zero, ih (tailMask I₀) (fun I => f (consMask false I))]
      have heta : consMask false (tailMask I₀) = I₀ := by
        rw [← hh, consMask_eta]
      rw [heta]
    · have htrue : ∀ I : Mask n, (consMask true I = I₀) ↔ (I = tailMask I₀) := by
        intro I
        constructor
        · intro heq
          rw [← heq, tailMask_consMask]
        · intro heq
          rw [heq, ← hh, consMask_eta]
      have hfalse : ∀ I : Mask n, consMask false I ≠ I₀ := by
        intro I heq
        have h0 := congrArg headMask heq
        simp [hh] at h0
      have hs1 :
          sumMasks (fun I => if consMask false I = I₀ then f (consMask false I) else 0) = 0 := by
        rw [sumMasks_congr (g := fun _ => 0)]
        · exact sumMasks_zero n
        · intro I
          rw [if_neg (hfalse I)]
      have hs2 :
          sumMasks (fun I => if consMask true I = I₀ then f (consMask true I) else 0) =
          sumMasks (fun I => if I = tailMask I₀ then f (consMask true I) else 0) := by
        apply sumMasks_congr
        intro I
        by_cases hI : I = tailMask I₀
        · have hc : consMask true I = I₀ := (htrue I).mpr hI
          rw [if_pos hc, if_pos hI]
        · have hc : consMask true I ≠ I₀ := fun h => hI ((htrue I).mp h)
          rw [if_neg hc, if_neg hI]
      rw [hs1, hs2, Int.zero_add, ih (tailMask I₀) (fun I => f (consMask true I))]
      have heta : consMask true (tailMask I₀) = I₀ := by
        rw [← hh, consMask_eta]
      rw [heta]

/--
  Exterior **wedge product** `α ∧ β` on `ExtForm n`:
  `(e_I ∧ e_J) = (-1)^{inv(I, J)} e_{I ∪ J}` when `I ∩ J = ∅`, and `0` otherwise,
  extended bilinearly over all exterior forms.
-/
def wedge {n : Nat} (α β : ExtForm n) : ExtForm n :=
  fun K =>
    sumMasks (fun I =>
      sumMasks (fun J =>
        if (disjointMask I J == true) && (orMask I J = K) then
          α I * β J * signPow (invCount I J)
        else 0))

/-- Action of the wedge product on standard basis blades `e_I` and `e_J`. -/
theorem wedge_basisForm {n : Nat} (I₀ J₀ : Mask n) :
    wedge (basisForm I₀) (basisForm J₀) =
      if disjointMask I₀ J₀ = true then
        signPow (invCount I₀ J₀) * basisForm (orMask I₀ J₀)
      else 0 := by
  funext K
  unfold wedge
  have houter :
      sumMasks (fun I =>
        sumMasks (fun J =>
          if (disjointMask I J == true) && (orMask I J = K) then
            basisForm I₀ I * basisForm J₀ J * signPow (invCount I J)
          else 0)) =
      sumMasks (fun I =>
        if I = I₀ then
          sumMasks (fun J =>
            if (disjointMask I J == true) && (orMask I J = K) then
              basisForm J₀ J * signPow (invCount I J)
            else 0)
        else 0) := by
    apply sumMasks_congr
    intro I
    by_cases hI : I = I₀
    · subst hI
      simp only [↓reduceIte, basisForm, Int.one_mul]
    · simp only [hI, ↓reduceIte]
      rw [sumMasks_congr (g := fun _ => 0)]
      · exact sumMasks_zero n
      · intro J
        simp [basisForm, hI]
  rw [houter, sumMasks_ite_eq]
  have hinner :
      sumMasks (fun J =>
        if (disjointMask I₀ J == true) && (orMask I₀ J = K) then
          basisForm J₀ J * signPow (invCount I₀ J)
        else 0) =
      sumMasks (fun J =>
        if J = J₀ then
          if (disjointMask I₀ J == true) && (orMask I₀ J = K) then
            signPow (invCount I₀ J)
          else 0
        else 0) := by
    apply sumMasks_congr
    intro J
    by_cases hJ : J = J₀ <;> simp [basisForm, hJ]
  rw [hinner, sumMasks_ite_eq]
  by_cases hd : disjointMask I₀ J₀ = true
  · by_cases hor : orMask I₀ J₀ = K
    · subst hor
      simp [hd, basisForm]
    · have hne : K ≠ orMask I₀ J₀ := fun h => hor h.symm
      simp [hd, hor, hne, basisForm]
  · simp [hd]

/-- Nilpotency of 1-forms: `e_i ∧ e_i = 0`. -/
theorem covector_wedge_self {n : Nat} (i : Fin n) :
    wedge (covector i) (covector i) = 0 := by
  unfold covector
  rw [wedge_basisForm]
  have hnd : disjointMask (singleMask i) (singleMask i) ≠ true := by
    intro hd
    rw [disjointMask_iff] at hd
    have hi := hd i
    simp [singleMask] at hi
  simp [hnd]

/-- Anticommutativity of distinct elementary 1-forms: `e_i ∧ e_j = -(e_j ∧ e_i)` for `i ≠ j`. -/
theorem covector_wedge_anticomm {n : Nat} {i j : Fin n} (hij : i ≠ j) :
    wedge (covector i) (covector j) = -(wedge (covector j) (covector i)) := by
  unfold covector
  have hij_val : i.val ≠ j.val := fun h => hij (Fin.eq_of_val_eq h)
  have hd1 : disjointMask (singleMask i) (singleMask j) = true := by
    rw [disjointMask_iff]
    intro k
    by_cases hki : k.val = i.val
    · simp [singleMask, hki, hij_val]
    · simp [singleMask, hki]
  have hd2 : disjointMask (singleMask j) (singleMask i) = true := by
    rw [disjointMask_iff]
    intro k
    by_cases hkj : k.val = j.val
    · have hji_val : j.val ≠ i.val := fun h => hij_val h.symm
      simp [singleMask, hkj, hji_val]
    · simp [singleMask, hkj]
  have hor : orMask (singleMask i) (singleMask j) = orMask (singleMask j) (singleMask i) := by
    funext k
    simp [orMask, Bool.or_comm]
  have hinv := invCount_add_invCount_of_disjoint (singleMask i) (singleMask j) hd1
  rw [degMask_singleMask, degMask_singleMask] at hinv
  have hprod :
      signPow (invCount (singleMask i) (singleMask j)) *
        signPow (invCount (singleMask j) (singleMask i)) = -1 := by
    rw [← signPow_add, hinv]
    rfl
  rw [wedge_basisForm, wedge_basisForm, if_pos hd1, if_pos hd2, hor]
  funext K
  simp only [smulForm_apply, negForm_apply]
  have hs1 :
      signPow (invCount (singleMask i) (singleMask j)) = 1 ∨
      signPow (invCount (singleMask i) (singleMask j)) = -1 := by
    unfold signPow; split <;> simp
  have hs2 :
      signPow (invCount (singleMask j) (singleMask i)) = 1 ∨
      signPow (invCount (singleMask j) (singleMask i)) = -1 := by
    unfold signPow; split <;> simp
  rcases hs1 with h1 | h1 <;> rcases hs2 with h2 | h2 <;> rw [h1, h2] at hprod ⊢ <;> omega

/-- Grading of the wedge product: `α ∈ Λ^p, β ∈ Λ^q ⟹ α ∧ β ∈ Λ^{p + q}`. -/
theorem IsHomogeneous.wedge {n p q : Nat} {α β : ExtForm n}
    (hα : IsHomogeneous p α) (hβ : IsHomogeneous q β) :
    IsHomogeneous (p + q) (wedge α β) := by
  intro K hK
  unfold HodgeDoubleStar.wedge
  rw [sumMasks_congr (g := fun _ => 0)]
  · exact sumMasks_zero n
  · intro I
    rw [sumMasks_congr (g := fun _ => 0)]
    · exact sumMasks_zero n
    · intro J
      by_cases hcond : ((disjointMask I J == true) && (orMask I J = K)) = true
      · rw [if_pos hcond]
        simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hcond
        rcases hcond with ⟨hd, hor⟩
        have hdeg := degMask_or_of_disjoint I J hd
        rw [hor] at hdeg
        by_cases hIp : degMask I = p
        · have hJq : degMask J ≠ q := by omega
          simp [hβ J hJq]
        · simp [hα I hIp]
      · rw [if_neg hcond]

/-- Top-degree evaluation of `α ∧ γ` at `vol`: only complementary pairs `(I, I^c)` contribute. -/
theorem wedge_apply_fullMask {n : Nat} (α γ : ExtForm n) :
    (wedge α γ) (fullMask n) =
      sumMasks (fun I => α I * γ (compMask I) * signPow (invCount I (compMask I))) := by
  unfold wedge
  apply sumMasks_congr
  intro I
  have hinner :
      sumMasks (fun J =>
        if (disjointMask I J == true) && (orMask I J = fullMask n) then
          α I * γ J * signPow (invCount I J)
        else 0) =
      sumMasks (fun J =>
        if J = compMask I then
          α I * γ J * signPow (invCount I J)
        else 0) := by
    apply sumMasks_congr
    intro J
    by_cases hJ : J = compMask I
    · subst hJ
      have hc : ((disjointMask I (compMask I) == true) && (orMask I (compMask I) = fullMask n)) = true := by
        simp [disjointMask_comp_right, orMask_comp_right]
      rw [if_pos hc, if_pos rfl]
    · have hncond : ¬(disjointMask I J = true ∧ orMask I J = fullMask n) :=
        fun h => hJ ((disjoint_or_full_iff I J).mp h)
      have hc : ¬(((disjointMask I J == true) && (orMask I J = fullMask n)) = true) := by
        intro ht
        simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at ht
        exact hncond ht
      rw [if_neg hc, if_neg hJ]
  rw [hinner, sumMasks_ite_eq]

/--
  Pseudo-Riemannian Gram **inner product** `⟨α, β⟩` on `ExtForm n` induced by `eta : MetricSig n`:
  orthonormal on basis blades `e_I` with `⟨e_I, e_I⟩ = η_I ∈ {+1, -1}`.
-/
def inner {n : Nat} (eta : MetricSig n) (α β : ExtForm n) : Int :=
  sumMasks (fun I => etaSign eta I * α I * β I)

theorem inner_comm {n : Nat} (eta : MetricSig n) (α β : ExtForm n) :
    inner eta α β = inner eta β α := by
  unfold inner
  apply sumMasks_congr
  intro I
  ac_rfl

theorem inner_basisForm_left {n : Nat} (eta : MetricSig n) (I₀ : Mask n) (β : ExtForm n) :
    inner eta (basisForm I₀) β = etaSign eta I₀ * β I₀ := by
  unfold inner
  have h :
      sumMasks (fun I => etaSign eta I * basisForm I₀ I * β I) =
      sumMasks (fun I => if I = I₀ then etaSign eta I * β I else 0) := by
    apply sumMasks_congr
    intro I
    by_cases hI : I = I₀ <;> simp [basisForm, hI]
  rw [h, sumMasks_ite_eq]

theorem inner_basisForm {n : Nat} (eta : MetricSig n) (I J : Mask n) :
    inner eta (basisForm I) (basisForm J) = if I = J then etaSign eta I else 0 := by
  rw [inner_basisForm_left]
  by_cases h : J = I
  · subst h; simp [basisForm]
  · have hIJ : I ≠ J := fun heq => h heq.symm
    simp [basisForm, h, hIJ]

/--
  **The Hodge Star Operator** `⋆ : Λ^p(ℝ^{r,s}) → Λ^{n-p}(ℝ^{r,s})`:
  Defined on `ExtForm n` by mapping each basis blade `e_I` to `η_I * (-1)^{inv(I, I^c)} e_{I^c}`.
-/
def hodgeStar {n : Nat} (eta : MetricSig n) (ω : ExtForm n) : ExtForm n :=
  fun J => etaSign eta (compMask J) * signPow (invCount (compMask J) J) * ω (compMask J)

/-- Action of `hodgeStar` on a basis blade `e_I`. -/
theorem hodgeStar_basisForm {n : Nat} (eta : MetricSig n) (I : Mask n) :
    hodgeStar eta (basisForm I) =
      (etaSign eta I * signPow (invCount I (compMask I))) * basisForm (compMask I) := by
  funext J
  simp only [hodgeStar, basisForm, smulForm_apply]
  by_cases hJ : J = compMask I
  · subst hJ
    simp
  · have hcomp : compMask J ≠ I := by
      intro hc
      apply hJ
      rw [← hc, compMask_compMask]
    simp [hJ, hcomp]

theorem hodgeStar_zero {n : Nat} (eta : MetricSig n) :
    hodgeStar eta (0 : ExtForm n) = 0 := by
  funext J
  simp [hodgeStar]

theorem hodgeStar_add {n : Nat} (eta : MetricSig n) (α β : ExtForm n) :
    hodgeStar eta (α + β) = hodgeStar eta α + hodgeStar eta β := by
  funext J
  simp only [hodgeStar, addForm_apply]
  exact Int.mul_add _ _ _

theorem hodgeStar_smul {n : Nat} (eta : MetricSig n) (c : Int) (α : ExtForm n) :
    hodgeStar eta (c * α) = c * hodgeStar eta α := by
  funext J
  simp only [hodgeStar, smulForm_apply]
  ac_rfl

theorem hodgeStar_neg {n : Nat} (eta : MetricSig n) (α : ExtForm n) :
    hodgeStar eta (-α) = -(hodgeStar eta α) := by
  funext J
  simp only [hodgeStar, negForm_apply, Int.mul_neg]

/-- `hodgeStar` maps homogeneous `p`-forms (`p ≤ n`) to homogeneous `(n - p)`-forms. -/
theorem IsHomogeneous.hodgeStar {n p : Nat} (eta : MetricSig n) (hp : p ≤ n)
    {ω : ExtForm n} (hω : IsHomogeneous p ω) :
    IsHomogeneous (n - p) (HodgeDoubleStar.hodgeStar eta ω) := by
  intro J hJ
  simp only [HodgeDoubleStar.hodgeStar]
  have hdeg : degMask (compMask J) ≠ p := by
    have hsum := degMask_add_degMask_comp J
    omega
  rw [hω (compMask J) hdeg]
  simp

/-- Typed Hodge star operator `⋆ : Λ^p(ℝ^{r,s}) → Λ^{n-p}(ℝ^{r,s})`. -/
def hodgeStarP {n p : Nat} (eta : MetricSig n) (hp : p ≤ n) (ω : LambdaP n p) :
    LambdaP n (n - p) :=
  ⟨hodgeStar eta ω.val, ω.property.hodgeStar eta hp⟩

/--
  **Defining Duality-Map Identity of the Hodge Star:**
  For all `p ≤ n` and all homogeneous `p`-forms `α, β ∈ Λ^p(ℝ^{r,s})`,
  `α ∧ ⋆β = ⟨α, β⟩ vol`.
-/
theorem hodgeStar_wedge_duality {n p : Nat} (eta : MetricSig n) (hp : p ≤ n)
    {α β : ExtForm n} (hα : IsHomogeneous p α) (hβ : IsHomogeneous p β) :
    wedge α (hodgeStar eta β) = inner eta α β * volForm n := by
  have hstar : IsHomogeneous (n - p) (hodgeStar eta β) := hβ.hodgeStar eta hp
  have hwedge : IsHomogeneous n (wedge α (hodgeStar eta β)) := by
    have hw := hα.wedge hstar
    have hpn : p + (n - p) = n := by omega
    rw [hpn] at hw
    exact hw
  funext K
  by_cases hK : K = fullMask n
  · subst hK
    rw [wedge_apply_fullMask]
    simp only [smulForm_apply, volForm, basisForm, ↓reduceIte, Int.mul_one, inner]
    apply sumMasks_congr
    intro I
    simp only [hodgeStar, compMask_compMask]
    have hsq : signPow (invCount I (compMask I)) * signPow (invCount I (compMask I)) = 1 :=
      signPow_mul_self _
    calc
      α I * (etaSign eta I * signPow (invCount I (compMask I)) * β I) *
          signPow (invCount I (compMask I))
        = (etaSign eta I * α I * β I) *
            (signPow (invCount I (compMask I)) * signPow (invCount I (compMask I))) := by
              ac_rfl
      _ = etaSign eta I * α I * β I := by rw [hsq, Int.mul_one]
  · have hdegK : degMask K ≠ n := fun hd => hK ((degMask_eq_n_iff_full K).mp hd)
    rw [hwedge K hdegK]
    simp [volForm, basisForm, hK]

/--
  **Uniqueness of the Hodge Star Duality Map:**
  For `β ∈ Λ^p`, `⋆β` is the *unique* `(n - p)`-form `γ ∈ Λ^{n-p}` satisfying
  `α ∧ γ = ⟨α, β⟩ vol` for all `α ∈ Λ^p`.
-/
theorem hodgeStar_unique {n p : Nat} (eta : MetricSig n) (hp : p ≤ n)
    {β γ : ExtForm n} (hβ : IsHomogeneous p β) (hγ : IsHomogeneous (n - p) γ)
    (hdual : ∀ α : ExtForm n, IsHomogeneous p α → wedge α γ = inner eta α β * volForm n) :
    γ = hodgeStar eta β := by
  funext J
  by_cases hdegJ : degMask J = n - p
  · let I := compMask J
    have hdegI : degMask I = p := by
      have hsum := degMask_add_degMask_comp J
      dsimp [I]
      omega
    have hbasisI : IsHomogeneous p (basisForm I) := by
      rw [← hdegI]
      exact isHomogeneous_basisForm I
    have heval := congrFun (hdual (basisForm I) hbasisI) (fullMask n)
    rw [wedge_apply_fullMask, inner_basisForm_left] at heval
    simp only [smulForm_apply, volForm, basisForm, ↓reduceIte, Int.mul_one] at heval
    have hsum_collapse :
        sumMasks (fun K => (if K = I then 1 else 0) * γ (compMask K) * signPow (invCount K (compMask K))) =
        sumMasks (fun K => if K = I then γ (compMask K) * signPow (invCount K (compMask K)) else 0) := by
      apply sumMasks_congr
      intro K
      by_cases hKI : K = I <;> simp [hKI]
    rw [hsum_collapse, sumMasks_ite_eq] at heval
    have hcompI : compMask I = J := compMask_compMask J
    rw [hcompI] at heval
    have hmul := congrArg (fun x => signPow (invCount I J) * x) heval
    dsimp only at hmul
    have hlhs :
        signPow (invCount I J) * (γ J * signPow (invCount I J)) = γ J := by
      calc
        signPow (invCount I J) * (γ J * signPow (invCount I J))
          = (signPow (invCount I J) * signPow (invCount I J)) * γ J := by ac_rfl
        _ = 1 * γ J := by rw [signPow_mul_self]
        _ = γ J := Int.one_mul _
    rw [hlhs] at hmul
    simp only [hodgeStar]
    dsimp [I] at hmul
    calc
      γ J = signPow (invCount (compMask J) J) * (etaSign eta (compMask J) * β (compMask J)) := hmul
      _ = etaSign eta (compMask J) * signPow (invCount (compMask J) J) * β (compMask J) := by ac_rfl
  · rw [hγ J hdegJ]
    have hstar : IsHomogeneous (n - p) (hodgeStar eta β) := hβ.hodgeStar eta hp
    rw [hstar J hdegJ]

/-- Pointwise double-star formula on every basis coordinate `I : Mask n`. -/
theorem hodgeStar_hodgeStar_apply {n : Nat} (eta : MetricSig n) (ω : ExtForm n) (I : Mask n) :
    hodgeStar eta (hodgeStar eta ω) I =
      signPow (degMask I * degMask (compMask I) + negIndex eta) * ω I := by
  simp only [hodgeStar, compMask_compMask]
  have heta : etaSign eta I * etaSign eta (compMask I) = signPow (negIndex eta) :=
    etaSign_mul_etaSign_comp eta I
  have hinv :
      signPow (invCount I (compMask I)) * signPow (invCount (compMask I) I) =
        signPow (degMask I * degMask (compMask I)) := by
    rw [← signPow_add, invCount_add_invCount_comp]
  calc
    etaSign eta (compMask I) * signPow (invCount (compMask I) I) *
        (etaSign eta I * signPow (invCount I (compMask I)) * ω I)
      = (etaSign eta I * etaSign eta (compMask I)) *
          (signPow (invCount I (compMask I)) * signPow (invCount (compMask I) I)) * ω I := by
            ac_rfl
    _ = signPow (negIndex eta) * signPow (degMask I * degMask (compMask I)) * ω I := by
          rw [heta, hinv]
    _ = (signPow (degMask I * degMask (compMask I)) * signPow (negIndex eta)) * ω I := by
          ac_rfl
    _ = signPow (degMask I * degMask (compMask I) + negIndex eta) * ω I := by
          rw [← signPow_add]

/--
  **Master Exact Double-Star Sign Law Theorem:**
  On an `n`-dimensional oriented pseudo-Riemannian vector space with metric signature `eta`
  of negative index `s = negIndex eta`, for every homogeneous `p`-form `ω ∈ Λ^p`,
  `⋆(⋆ω) = (-1)^{p(n - p) + s} ω`.
-/
theorem hodgeStar_hodgeStar {n p : Nat} (eta : MetricSig n)
    {ω : ExtForm n} (hω : IsHomogeneous p ω) :
    hodgeStar eta (hodgeStar eta ω) = signPow (p * (n - p) + negIndex eta) * ω := by
  funext I
  rw [hodgeStar_hodgeStar_apply, smulForm_apply]
  by_cases hdeg : degMask I = p
  · have hcomp : degMask (compMask I) = n - p := by
      rw [degMask_comp, hdeg]
    rw [hdeg, hcomp]
  · rw [hω I hdeg]
    simp

/--
  **Canonical `(r, s)`-Signature Double-Star Theorem (`ℝ^{r,s}`, `r + s = n`):**
  For `n = r + s` and every `p`-form `ω ∈ Λ^p(ℝ^{r,s})`,
  `⋆(⋆ω) = (-1)^{p(n - p) + s} ω`.
-/
theorem hodgeStar_hodgeStar_sigOfRS {n r s p : Nat} (hn : r + s = n)
    {ω : ExtForm n} (hω : IsHomogeneous p ω) :
    hodgeStar (sigOfRS n r) (hodgeStar (sigOfRS n r) ω) = signPow (p * (n - p) + s) * ω := by
  rw [hodgeStar_hodgeStar (sigOfRS n r) hω, negIndex_sigOfRS n r s hn]

/--
  **Riemannian Double-Star Sign Corollary (`s = 0`):**
  In positive-definite signature `(n, 0)`, for every `p`-form `ω ∈ Λ^p(ℝ^n)`,
  `⋆(⋆ω) = (-1)^{p(n - p)} ω`.
-/
theorem hodgeStar_hodgeStar_riemannian {n p : Nat}
    {ω : ExtForm n} (hω : IsHomogeneous p ω) :
    hodgeStar (riemSig n) (hodgeStar (riemSig n) ω) = signPow (p * (n - p)) * ω := by
  rw [hodgeStar_hodgeStar (riemSig n) hω, negIndex_riemSig, Nat.add_zero]

/-- Typed double-star theorem on `LambdaP n p` (`p ≤ n`). -/
theorem hodgeStarP_hodgeStarP_val {n p : Nat} (eta : MetricSig n) (hp : p ≤ n)
    (ω : LambdaP n p) :
    (hodgeStarP eta (Nat.sub_le n p) (hodgeStarP eta hp ω)).val =
      signPow (p * (n - p) + negIndex eta) * ω.val :=
  hodgeStar_hodgeStar eta ω.property

/-!
  ### Extension to Arbitrary Characteristic-≠-2 Scalar Modules (including `ℝ` and `ℂ`)
  Because the Hodge star acts on the orthonormal basis `e_I` purely by `±1` signs,
  the double-star identity and the `⋆^2 = -id` self-duality obstruction hold over *any*
  additive group `K` without `2`-torsion (in particular `K = ℝ`, `ℚ`, or `ℂ`).
-/
section ArbitraryScalarField

/-- Action of `(-1)^k` on an arbitrary type `K` equipped with negation. -/
def signAct {K : Type} [Neg K] (k : Nat) (x : K) : K :=
  if k % 2 == 0 then x else -x

/-- Exterior forms with coefficients in an arbitrary scalar type `K` (e.g. `ℝ`). -/
abbrev ExtFormK (K : Type) (n : Nat) : Type := Mask n → K

def IsHomogeneousK {K : Type} [Zero K] {n : Nat} (p : Nat) (ω : ExtFormK K n) : Prop :=
  ∀ I : Mask n, degMask I ≠ p → ω I = 0

/-- Hodge star over an arbitrary scalar domain `K`. -/
def hodgeStarK {K : Type} [Neg K] {n : Nat} (eta : MetricSig n) (ω : ExtFormK K n) : ExtFormK K n :=
  fun J => signAct (degMask (andMask (compMask J) eta) + invCount (compMask J) J) (ω (compMask J))

theorem signAct_signAct {K : Type} [Neg K] (hneg_inv : ∀ x : K, -(-x) = x)
    (a b : Nat) (x : K) :
    signAct a (signAct b x) = signAct (a + b) x := by
  unfold signAct
  have ha : a % 2 = 0 ∨ a % 2 = 1 := by omega
  have hb : b % 2 = 0 ∨ b % 2 = 1 := by omega
  rcases ha with ha | ha <;> rcases hb with hb | hb
  · have hab : (a + b) % 2 = 0 := by omega
    simp [ha, hb, hab]
  · have hab : (a + b) % 2 = 1 := by omega
    simp [ha, hb, hab]
  · have hab : (a + b) % 2 = 1 := by omega
    simp [ha, hb, hab]
  · have hab : (a + b) % 2 = 0 := by omega
    simp [ha, hb, hab, hneg_inv]

/-- Exact double-star law over *any* involutive scalar type `K` (including `ℝ` and `ℂ`). -/
theorem hodgeStarK_hodgeStarK {K : Type} [Zero K] [Neg K]
    (hneg_zero : -(0 : K) = 0)
    (hneg_inv : ∀ x : K, -(-x) = x)
    {n p : Nat} (eta : MetricSig n) {ω : ExtFormK K n} (hω : IsHomogeneousK p ω) :
    hodgeStarK eta (hodgeStarK eta ω) = fun I => signAct (p * (n - p) + negIndex eta) (ω I) := by
  funext I
  simp only [hodgeStarK, compMask_compMask]
  rw [signAct_signAct hneg_inv]
  by_cases hdeg : degMask I = p
  · have hcomp : degMask (compMask I) = n - p := by rw [degMask_comp, hdeg]
    have hsum :
        (degMask (andMask (compMask I) eta) + invCount (compMask I) I +
          (degMask (andMask I eta) + invCount I (compMask I))) =
        p * (n - p) + negIndex eta := by
      have h1 := degMask_and_add_comp_and eta I
      have h2 := invCount_add_invCount_comp I
      rw [hdeg, hcomp] at h2
      omega
    rw [hsum]
  · rw [hω I hdeg]
    unfold signAct
    split <;> simp [hneg_zero]

/-- Over *any* scalar domain `K` with no `2`-torsion (`-x = x → x = 0`, such as `ℝ` or `ℂ`),
    if `(m * m + s) % 2 = 1`, no non-zero self-dual `m`-form `⋆ω = ω` exists in dimension `2m`. -/
theorem no_selfDualK_of_odd {K : Type} [Zero K] [Neg K]
    (hneg_zero : -(0 : K) = 0)
    (hneg_inv : ∀ x : K, -(-x) = x)
    (hno_torsion : ∀ x : K, -x = x → x = 0)
    {m : Nat} (eta : MetricSig (2 * m))
    (hodd : (m * m + negIndex eta) % 2 = 1)
    {ω : ExtFormK K (2 * m)} (hω : IsHomogeneousK m ω)
    (hsd : hodgeStarK eta ω = ω) :
    ω = fun _ => 0 := by
  have hdd := hodgeStarK_hodgeStarK hneg_zero hneg_inv eta hω
  rw [hsd, hsd] at hdd
  funext I
  have heval := congrFun hdd I
  have hsub : 2 * m - m = m := by omega
  rw [hsub] at heval
  unfold signAct at heval
  simp [hodd] at heval
  exact hno_torsion (ω I) heval.symm

end ArbitraryScalarField

end HodgeDoubleStar
