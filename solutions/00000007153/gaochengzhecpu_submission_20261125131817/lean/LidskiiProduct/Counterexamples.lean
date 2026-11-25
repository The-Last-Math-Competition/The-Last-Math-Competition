/-
  LidskiiProduct/Counterexamples.lean
  Formal statements and complete machine-checked disproofs of Conjecture 00000007153
  across all standard mathematical interpretations, together with positive non-vacuity
  witnesses and an all-dimensions (n ≥ 2) scaled-orthogonal SVD counterexample family.
-/
import LidskiiProduct.Matrix2

namespace LidskiiProduct

/-! ### 1. Positive Non-Vacuity Witnesses -/

def D1_pos : Mat2 := Mat2.diag 4 2
def D2_pos : Mat2 := Mat2.diag 5 1

/-- Positive non-vacuity witness: sorted non-negative diagonal matrices satisfy our
    definitions of `IsDiagonal`, `HasSingularValues`, `LogMajorizes2`, and `LogMajorizesEq2`. -/
theorem positive_witness_diagonal :
    Mat2.IsDiagonal D1_pos ∧
    Mat2.IsDiagonal D2_pos ∧
    Mat2.IsDiagonal (Mat2.mul D1_pos D2_pos) ∧
    HasSingularValues D1_pos 4 2 ∧
    HasSingularValues D2_pos 5 1 ∧
    HasSingularValues (Mat2.mul D1_pos D2_pos) 20 2 ∧
    LogMajorizesEq2 20 2 (4 * 5) (2 * 1) := by
  decide

/-! ### 2. Formal Statements of Conjecture 00000007153 Across Interpretations -/

/-- **Interpretation A1 (Canonical-basis diagonal factors)**:
    Product singular-value log-majorization holds AND equality holds iff `A` and `B`
    are diagonal operators. -/
def ConjectureInterpA_DiagFactors : Prop :=
  ∀ (A B : Mat2) (a1 a2 b1 b2 c1 c2 : Int),
    HasSingularValues A a1 a2 →
    HasSingularValues B b1 b2 →
    HasSingularValues (Mat2.mul A B) c1 c2 →
    (LogMajorizes2 c1 c2 (a1 * b1) (a2 * b2) ∧
      (LogMajorizesEq2 c1 c2 (a1 * b1) (a2 * b2) ↔
        (Mat2.IsDiagonal A ∧ Mat2.IsDiagonal B)))

/-- **Interpretation A2 (Canonical-basis diagonal product)**:
    Equality in product singular-value log-majorization forces at least one of
    `A`, `B`, or `AB` to be diagonal. -/
def ConjectureInterpA_AnyDiag : Prop :=
  ∀ (A B : Mat2) (a1 a2 b1 b2 c1 c2 : Int),
    HasSingularValues A a1 a2 →
    HasSingularValues B b1 b2 →
    HasSingularValues (Mat2.mul A B) c1 c2 →
    LogMajorizesEq2 c1 c2 (a1 * b1) (a2 * b2) →
    (Mat2.IsDiagonal A ∨ Mat2.IsDiagonal B ∨ Mat2.IsDiagonal (Mat2.mul A B))

/-- **Interpretation A3 (Unitarily diagonalizable / normal operators)**:
    Equality in product singular-value log-majorization forces at least one of
    `A`, `B`, or `AB` to be normal (`X^T X = X X^T`), or `A` and `B` to commute. -/
def ConjectureInterpA_NormalOrCommuting : Prop :=
  ∀ (A B : Mat2) (a1 a2 b1 b2 c1 c2 : Int),
    HasSingularValues A a1 a2 →
    HasSingularValues B b1 b2 →
    HasSingularValues (Mat2.mul A B) c1 c2 →
    LogMajorizesEq2 c1 c2 (a1 * b1) (a2 * b2) →
    (Mat2.IsNormal A ∨ Mat2.IsNormal B ∨ Mat2.IsNormal (Mat2.mul A B) ∨
      Mat2.mul A B = Mat2.mul B A)

/-- **Interpretation A4 (Similarity-diagonalizable operators)**:
    Equality in product singular-value log-majorization forces `A` or `AB` to be
    similar to a diagonal matrix. -/
def ConjectureInterpA_SimilarDiag : Prop :=
  ∀ (A B : Mat2) (a1 a2 b1 b2 c1 c2 : Int),
    HasSingularValues A a1 a2 →
    HasSingularValues B b1 b2 →
    HasSingularValues (Mat2.mul A B) c1 c2 →
    LogMajorizesEq2 c1 c2 (a1 * b1) (a2 * b2) →
    (Mat2.SimilarToDiagInt A ∨ Mat2.SimilarToDiagInt (Mat2.mul A B))

/-- **Interpretation B (Weyl eigenvalue-singular-value log-majorization)**:
    Equality in `|λ(M)| ≺_{log} σ(M)` holds iff `M` is diagonal. -/
def ConjectureInterpB_WeylDiag : Prop :=
  ∀ (M : Mat2) (l1 l2 s1 s2 : Int),
    HasRealEigenvalues M l1 l2 →
    HasSingularValues M s1 s2 →
    (LogMajorizesEq2 (absInt l1) (absInt l2) s1 s2 ↔ Mat2.IsDiagonal M)

/-- **Interpretation C (Diagonal-entry / pinching log-majorization)**:
    The sorted diagonal magnitudes `(|a11|, |a22|)↓` are weakly log-majorized by `σ(M)`. -/
def ConjectureInterpC_DiagWeakLogMaj : Prop :=
  ∀ (M : Mat2) (d1 d2 s1 s2 : Int),
    0 ≤ d2 → d2 ≤ d1 →
    ((d1 = absInt M.a11 ∧ d2 = absInt M.a22) ∨ (d1 = absInt M.a22 ∧ d2 = absInt M.a11)) →
    HasSingularValues M s1 s2 →
    WeakLogMajorizes2 d1 d2 s1 s2

/-! ### 3. Explicit 2x2 Counterexamples and Complete Disproofs -/

/-- Symmetric positive definite counterexample:
    `A_spd = [[3, 1], [1, 3]]` (`σ = (4, 2)`), `B_spd = [[3, 2], [2, 3]]` (`σ = (5, 1)`),
    `AB_spd = [[11, 9], [9, 11]]` (`σ = (20, 2)`). -/
def A_spd : Mat2 := ⟨3, 1, 1, 3⟩
def B_spd : Mat2 := ⟨3, 2, 2, 3⟩

theorem spd_counterexample_facts :
    HasSingularValues A_spd 4 2 ∧
    HasSingularValues B_spd 5 1 ∧
    HasSingularValues (Mat2.mul A_spd B_spd) 20 2 ∧
    LogMajorizesEq2 20 2 (4 * 5) (2 * 1) ∧
    ¬ Mat2.IsDiagonal A_spd ∧
    ¬ Mat2.IsDiagonal B_spd ∧
    ¬ Mat2.IsDiagonal (Mat2.mul A_spd B_spd) := by
  decide

theorem disproof_interpA_diagFactors : ¬ ConjectureInterpA_DiagFactors := by
  intro hconj
  rcases spd_counterexample_facts with ⟨hA, hB, hAB, heq, hnA, _, _⟩
  have hiff := (hconj A_spd B_spd 4 2 5 1 20 2 hA hB hAB).2
  exact hnA (hiff.mp heq).1

theorem disproof_interpA_anyDiag : ¬ ConjectureInterpA_AnyDiag := by
  intro hconj
  rcases spd_counterexample_facts with ⟨hA, hB, hAB, heq, hnA, hnB, hnAB⟩
  rcases hconj A_spd B_spd 4 2 5 1 20 2 hA hB hAB heq with h1 | h2 | h3
  · exact hnA h1
  · exact hnB h2
  · exact hnAB h3

/-- Defective, non-normal, non-commuting counterexample:
    `A_def = [[16, -12], [3, 4]]` (`σ = (20, 5)`, `χ_A(t) = (t - 10)^2`, Jordan block!),
    `B_def = [[173, -216], [-36, 212]]` (`σ = (340, 85)`),
    `AB_def = [[3200, -6000], [375, 200]]` (`σ = (6800, 425)`, `χ_{AB}(t) = (t - 1700)^2`, Jordan block!). -/
def A_def : Mat2 := ⟨16, -12, 3, 4⟩
def B_def : Mat2 := ⟨173, -216, -36, 212⟩

theorem defective_counterexample_facts :
    HasSingularValues A_def 20 5 ∧
    HasSingularValues B_def 340 85 ∧
    HasSingularValues (Mat2.mul A_def B_def) 6800 425 ∧
    LogMajorizesEq2 6800 425 (20 * 340) (5 * 85) ∧
    ¬ Mat2.IsDiagonal A_def ∧
    ¬ Mat2.IsDiagonal B_def ∧
    ¬ Mat2.IsDiagonal (Mat2.mul A_def B_def) ∧
    ¬ Mat2.IsNormal A_def ∧
    ¬ Mat2.IsNormal B_def ∧
    ¬ Mat2.IsNormal (Mat2.mul A_def B_def) ∧
    Mat2.mul A_def B_def ≠ Mat2.mul B_def A_def ∧
    Mat2.IsDefective A_def ∧
    Mat2.IsDefective (Mat2.mul A_def B_def) := by
  decide

theorem disproof_interpA_normalOrCommuting : ¬ ConjectureInterpA_NormalOrCommuting := by
  intro hconj
  rcases defective_counterexample_facts with
    ⟨hA, hB, hAB, heq, _, _, _, hnNormA, hnNormB, hnNormAB, hnComm, _, _⟩
  rcases hconj A_def B_def 20 5 340 85 6800 425 hA hB hAB heq with h1 | h2 | h3 | h4
  · exact hnNormA h1
  · exact hnNormB h2
  · exact hnNormAB h3
  · exact hnComm h4

theorem disproof_interpA_similarDiag : ¬ ConjectureInterpA_SimilarDiag := by
  intro hconj
  rcases defective_counterexample_facts with
    ⟨hA, hB, hAB, heq, _, _, _, _, _, _, _, hdefA, hdefAB⟩
  rcases hconj A_def B_def 20 5 340 85 6800 425 hA hB hAB heq with hsimA | hsimAB
  · exact Mat2.defective_not_similar_to_diag hdefA hsimA
  · exact Mat2.defective_not_similar_to_diag hdefAB hsimAB

/-- Symmetric counterexample for Interpretations B and C: `W_sym = [[2, 1], [1, 2]]`,
    with `λ(W_sym) = (3, 1)`, `σ(W_sym) = (3, 1)`, and `|diag(W_sym)| = (2, 2)`. -/
def W_sym : Mat2 := ⟨2, 1, 1, 2⟩

theorem disproof_interpB_weylDiag : ¬ ConjectureInterpB_WeylDiag := by
  intro hconj
  have heig : HasRealEigenvalues W_sym 3 1 := by decide
  have hsv : HasSingularValues W_sym 3 1 := by decide
  have heq : LogMajorizesEq2 (absInt 3) (absInt 1) 3 1 := by decide
  have hnotDiag : ¬ Mat2.IsDiagonal W_sym := by decide
  exact hnotDiag ((hconj W_sym 3 1 3 1 heig hsv).mp heq)

theorem disproof_interpC_diagWeakLogMaj :
    ¬ ConjectureInterpC_DiagWeakLogMaj ∧
    ¬ WeakLogMajorizes2 2 2 3 1 ∧
    ¬ WeakLogMajorizes2 3 1 2 2 := by
  refine ⟨?_, by decide, by decide⟩
  intro hconj
  have hsv : HasSingularValues W_sym 3 1 := by decide
  have hperm : (2 = absInt W_sym.a11 ∧ 2 = absInt W_sym.a22) ∨
      (2 = absInt W_sym.a22 ∧ 2 = absInt W_sym.a11) := by decide
  have hwlog := hconj W_sym 2 2 3 1 (by omega) (by omega) hperm hsv
  have hnot : ¬ WeakLogMajorizes2 2 2 3 1 := by decide
  exact hnot hwlog

/-! ### 4. All-Dimensions (`n = m + 2 ≥ 2`) Counterexample Family via Orthogonal SVD -/

abbrev MatN (n : Nat) := Fin n → Fin n → Int

def sumFin : (n : Nat) → (Fin n → Int) → Int
  | 0, _ => 0
  | n + 1, f => sumFin n (fun i => f ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩) + f ⟨n, Nat.lt_succ_self n⟩

def mulN {n : Nat} (A B : MatN n) : MatN n :=
  fun i j => sumFin n (fun k => A i k * B k j)

def transposeN {n : Nat} (A : MatN n) : MatN n :=
  fun i j => A j i

def diagVecN {n : Nat} (v : Fin n → Int) : MatN n :=
  fun i j => if i.val = j.val then v i else 0

def IsDiagonalN {n : Nat} (A : MatN n) : Prop :=
  ∀ i j : Fin n, i.val ≠ j.val → A i j = 0

/-- Partial product `∏_{j=0}^{k-1} v_j` of the first `k` entries of `v : Fin n → Int`. -/
def prodPrefix {n : Nat} (v : Fin n → Int) : (k : Nat) → k ≤ n → Int
  | 0, _ => 1
  | k + 1, hk => prodPrefix v k (Nat.le_of_succ_le hk) * v ⟨k, hk⟩

/-- Exact scaled-orthogonal SVD certificate on `n x n` matrices:
    `v` is non-negative and non-increasing (`v_0 ≥ v_1 ≥ ... ≥ v_{n-1} ≥ 0`),
    `U^T U = sU^2 I_n`, `V^T V = sV^2 I_n` (`sU, sV > 0`), and
    `(sU * sV) M = U diag(v) V^T`. -/
def HasScaledOrthogonalSVD {n : Nat} (M : MatN n) (v : Fin n → Int) : Prop :=
  (∀ i : Fin n, 0 ≤ v i) ∧
  (∀ i j : Fin n, i.val ≤ j.val → v j ≤ v i) ∧
  ∃ (U V : MatN n) (sU sV : Int),
    0 < sU ∧ 0 < sV ∧
    (∀ i j : Fin n, mulN (transposeN U) U i j = if i.val = j.val then sU ^ 2 else 0) ∧
    (∀ i j : Fin n, mulN (transposeN V) V i j = if i.val = j.val then sV ^ 2 else 0) ∧
    (∀ i j : Fin n, (sU * sV) * M i j = mulN (mulN U (diagVecN v)) (transposeN V) i j)

/-- Embed a `2 x 2` matrix `B2` into the top-left `{0, 1}` block of `MatN (m + 2)`
    and place `tailDiag` along the remaining diagonal entries `{2, ..., m + 1}`. -/
def blockExtend (B2 : Mat2) (tailDiag : Int) (m : Nat) : MatN (m + 2) :=
  fun i j =>
    if i.val = 0 ∧ j.val = 0 then B2.a11
    else if i.val = 0 ∧ j.val = 1 then B2.a12
    else if i.val = 1 ∧ j.val = 0 then B2.a21
    else if i.val = 1 ∧ j.val = 1 then B2.a22
    else if i.val = j.val then tailDiag
    else 0

def vecExtend (v0 v1 tailVal : Int) (m : Nat) : Fin (m + 2) → Int :=
  fun i =>
    if i.val = 0 then v0
    else if i.val = 1 then v1
    else tailVal

private theorem sumFin_zero : (n : Nat) → (f : Fin n → Int) → (∀ i : Fin n, f i = 0) →
    sumFin n f = 0
  | 0, _, _ => rfl
  | n + 1, f, hf => by
    dsimp [sumFin]
    rw [sumFin_zero n _ (fun i => hf ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩),
        hf ⟨n, Nat.lt_succ_self n⟩]
    omega

private theorem sumFin_congr : (n : Nat) → (f g : Fin n → Int) → (∀ i : Fin n, f i = g i) →
    sumFin n f = sumFin n g
  | 0, _, _, _ => rfl
  | n + 1, f, g, hfg => by
    dsimp [sumFin]
    rw [sumFin_congr n _ _ (fun i => hfg ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩),
        hfg ⟨n, Nat.lt_succ_self n⟩]

private theorem blockExtend_val_eq (B2 : Mat2) (d : Int) {m1 m2 : Nat}
    (i1 : Fin (m1 + 2)) (j1 : Fin (m1 + 2))
    (i2 : Fin (m2 + 2)) (j2 : Fin (m2 + 2))
    (hi : i1.val = i2.val) (hj : j1.val = j2.val) :
    blockExtend B2 d m1 i1 j1 = blockExtend B2 d m2 i2 j2 := by
  dsimp [blockExtend]
  rw [hi, hj]

private theorem blockExtend_off_last_left (B2 : Mat2) (d : Int) (m : Nat)
    (k : Fin (m + 3)) (hk : k.val < m + 2) :
    blockExtend B2 d (m + 1) ⟨m + 2, Nat.lt_succ_self (m + 2)⟩ k = 0 := by
  dsimp [blockExtend]
  have h5 : ¬ (m + 2 = k.val) := by omega
  rw [if_neg h5]

private theorem blockExtend_off_last_right (B2 : Mat2) (d : Int) (m : Nat)
    (i : Fin (m + 3)) (hi : i.val < m + 2) :
    blockExtend B2 d (m + 1) i ⟨m + 2, Nat.lt_succ_self (m + 2)⟩ = 0 := by
  dsimp [blockExtend]
  have h1 : ¬ (i.val = 0 ∧ m + 2 = 0) := by omega
  have h2 : ¬ (i.val = 0 ∧ m + 2 = 1) := by omega
  have h3 : ¬ (i.val = 1 ∧ m + 2 = 0) := by omega
  have h4 : ¬ (i.val = 1 ∧ m + 2 = 1) := by omega
  have h5 : ¬ (i.val = m + 2) := by omega
  rw [if_neg h1, if_neg h2, if_neg h3, if_neg h4, if_neg h5]

private theorem blockExtend_last_diag (B2 : Mat2) (d : Int) (m : Nat) :
    blockExtend B2 d (m + 1) ⟨m + 2, Nat.lt_succ_self (m + 2)⟩
      ⟨m + 2, Nat.lt_succ_self (m + 2)⟩ = d := by
  dsimp [blockExtend]
  simp

theorem mulN_blockExtend (X Y : Mat2) (dx dy : Int) :
    (m : Nat) → (i j : Fin (m + 2)) →
    mulN (blockExtend X dx m) (blockExtend Y dy m) i j =
      blockExtend (Mat2.mul X Y) (dx * dy) m i j
  | 0, i, j => by
    dsimp [mulN, sumFin, blockExtend, Mat2.mul]
    rcases i with ⟨iv, hi⟩
    rcases j with ⟨jv, hj⟩
    have hiv : iv = 0 ∨ iv = 1 := by omega
    have hjv : jv = 0 ∨ jv = 1 := by omega
    rcases hiv with rfl | rfl <;> rcases hjv with rfl | rfl <;> simp
  | m + 1, i, j => by
    have hstep : mulN (blockExtend X dx (m + 1)) (blockExtend Y dy (m + 1)) i j =
        sumFin (m + 2) (fun k =>
          blockExtend X dx (m + 1) i ⟨k.val, Nat.lt_succ_of_lt k.isLt⟩ *
            blockExtend Y dy (m + 1) ⟨k.val, Nat.lt_succ_of_lt k.isLt⟩ j) +
        blockExtend X dx (m + 1) i ⟨m + 2, Nat.lt_succ_self (m + 2)⟩ *
          blockExtend Y dy (m + 1) ⟨m + 2, Nat.lt_succ_self (m + 2)⟩ j := rfl
    rw [hstep]
    have hi_cases : i.val < m + 2 ∨ i = ⟨m + 2, Nat.lt_succ_self (m + 2)⟩ := by
      rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ i.isLt) with hlt | heq
      · exact Or.inl hlt
      · exact Or.inr (Fin.ext heq)
    have hj_cases : j.val < m + 2 ∨ j = ⟨m + 2, Nat.lt_succ_self (m + 2)⟩ := by
      rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ j.isLt) with hlt | heq
      · exact Or.inl hlt
      · exact Or.inr (Fin.ext heq)
    rcases hi_cases with hi_lt | rfl
    · rcases hj_cases with hj_lt | rfl
      · have hlast0 : blockExtend X dx (m + 1) i ⟨m + 2, Nat.lt_succ_self (m + 2)⟩ = 0 :=
          blockExtend_off_last_right X dx m i hi_lt
        rw [hlast0, Int.zero_mul, Int.add_zero]
        have hcongr := sumFin_congr (m + 2)
          (fun k =>
            blockExtend X dx (m + 1) i ⟨k.val, Nat.lt_succ_of_lt k.isLt⟩ *
              blockExtend Y dy (m + 1) ⟨k.val, Nat.lt_succ_of_lt k.isLt⟩ j)
          (fun k =>
            blockExtend X dx m ⟨i.val, hi_lt⟩ k *
              blockExtend Y dy m k ⟨j.val, hj_lt⟩)
          (fun k => by
            dsimp only
            rw [blockExtend_val_eq X dx i ⟨k.val, Nat.lt_succ_of_lt k.isLt⟩ ⟨i.val, hi_lt⟩ k rfl rfl,
                blockExtend_val_eq Y dy ⟨k.val, Nat.lt_succ_of_lt k.isLt⟩ j k ⟨j.val, hj_lt⟩ rfl rfl])
        rw [hcongr]
        have ih := mulN_blockExtend X Y dx dy m ⟨i.val, hi_lt⟩ ⟨j.val, hj_lt⟩
        dsimp [mulN] at ih
        rw [ih]
        exact blockExtend_val_eq (Mat2.mul X Y) (dx * dy) ⟨i.val, hi_lt⟩ ⟨j.val, hj_lt⟩ i j rfl rfl
      · have hzero_sum := sumFin_zero (m + 2)
          (fun k =>
            blockExtend X dx (m + 1) i ⟨k.val, Nat.lt_succ_of_lt k.isLt⟩ *
              blockExtend Y dy (m + 1) ⟨k.val, Nat.lt_succ_of_lt k.isLt⟩
                ⟨m + 2, Nat.lt_succ_self (m + 2)⟩)
          (fun k => by
            dsimp only
            rw [blockExtend_off_last_right Y dy m ⟨k.val, Nat.lt_succ_of_lt k.isLt⟩ k.isLt,
                Int.mul_zero])
        rw [hzero_sum, blockExtend_off_last_right X dx m i hi_lt, Int.zero_mul,
            blockExtend_off_last_right (Mat2.mul X Y) (dx * dy) m i hi_lt]
        omega
    · rcases hj_cases with hj_lt | rfl
      · have hzero_sum := sumFin_zero (m + 2)
          (fun k =>
            blockExtend X dx (m + 1) ⟨m + 2, Nat.lt_succ_self (m + 2)⟩
              ⟨k.val, Nat.lt_succ_of_lt k.isLt⟩ *
              blockExtend Y dy (m + 1) ⟨k.val, Nat.lt_succ_of_lt k.isLt⟩ j)
          (fun k => by
            dsimp only
            rw [blockExtend_off_last_left X dx m ⟨k.val, Nat.lt_succ_of_lt k.isLt⟩ k.isLt,
                Int.zero_mul])
        rw [hzero_sum, blockExtend_off_last_left Y dy m j hj_lt, Int.mul_zero,
            blockExtend_off_last_left (Mat2.mul X Y) (dx * dy) m j hj_lt]
        omega
      · have hzero_sum := sumFin_zero (m + 2)
          (fun k =>
            blockExtend X dx (m + 1) ⟨m + 2, Nat.lt_succ_self (m + 2)⟩
              ⟨k.val, Nat.lt_succ_of_lt k.isLt⟩ *
              blockExtend Y dy (m + 1) ⟨k.val, Nat.lt_succ_of_lt k.isLt⟩
                ⟨m + 2, Nat.lt_succ_self (m + 2)⟩)
          (fun k => by
            dsimp only
            rw [blockExtend_off_last_left X dx m ⟨k.val, Nat.lt_succ_of_lt k.isLt⟩ k.isLt,
                Int.zero_mul])
        rw [hzero_sum, Int.zero_add,
            blockExtend_last_diag X dx m,
            blockExtend_last_diag Y dy m,
            blockExtend_last_diag (Mat2.mul X Y) (dx * dy) m]

private theorem transposeN_blockExtend (B2 : Mat2) (d : Int) (m : Nat) (i j : Fin (m + 2)) :
    transposeN (blockExtend B2 d m) i j = blockExtend (Mat2.transpose B2) d m i j := by
  dsimp [transposeN, blockExtend, Mat2.transpose]
  have hi_cases : i.val = 0 ∨ i.val = 1 ∨ 2 ≤ i.val := by omega
  have hj_cases : j.val = 0 ∨ j.val = 1 ∨ 2 ≤ j.val := by omega
  rcases hi_cases with hi | hi | hi <;> rcases hj_cases with hj | hj | hj
  · rw [hi, hj]; rfl
  · rw [hi, hj]; rfl
  · have h1 : ¬ (j.val = 0 ∧ i.val = 0) := by omega
    have h2 : ¬ (j.val = 0 ∧ i.val = 1) := by omega
    have h3 : ¬ (j.val = 1 ∧ i.val = 0) := by omega
    have h4 : ¬ (j.val = 1 ∧ i.val = 1) := by omega
    have h5 : ¬ (j.val = i.val) := by omega
    have g1 : ¬ (i.val = 0 ∧ j.val = 0) := by omega
    have g2 : ¬ (i.val = 0 ∧ j.val = 1) := by omega
    have g3 : ¬ (i.val = 1 ∧ j.val = 0) := by omega
    have g4 : ¬ (i.val = 1 ∧ j.val = 1) := by omega
    have g5 : ¬ (i.val = j.val) := by omega
    rw [if_neg h1, if_neg h2, if_neg h3, if_neg h4, if_neg h5,
        if_neg g1, if_neg g2, if_neg g3, if_neg g4, if_neg g5]
  · rw [hi, hj]; rfl
  · rw [hi, hj]; rfl
  · have h1 : ¬ (j.val = 0 ∧ i.val = 0) := by omega
    have h2 : ¬ (j.val = 0 ∧ i.val = 1) := by omega
    have h3 : ¬ (j.val = 1 ∧ i.val = 0) := by omega
    have h4 : ¬ (j.val = 1 ∧ i.val = 1) := by omega
    have h5 : ¬ (j.val = i.val) := by omega
    have g1 : ¬ (i.val = 0 ∧ j.val = 0) := by omega
    have g2 : ¬ (i.val = 0 ∧ j.val = 1) := by omega
    have g3 : ¬ (i.val = 1 ∧ j.val = 0) := by omega
    have g4 : ¬ (i.val = 1 ∧ j.val = 1) := by omega
    have g5 : ¬ (i.val = j.val) := by omega
    rw [if_neg h1, if_neg h2, if_neg h3, if_neg h4, if_neg h5,
        if_neg g1, if_neg g2, if_neg g3, if_neg g4, if_neg g5]
  · have h1 : ¬ (j.val = 0 ∧ i.val = 0) := by omega
    have h2 : ¬ (j.val = 0 ∧ i.val = 1) := by omega
    have h3 : ¬ (j.val = 1 ∧ i.val = 0) := by omega
    have h4 : ¬ (j.val = 1 ∧ i.val = 1) := by omega
    have h5 : ¬ (j.val = i.val) := by omega
    have g1 : ¬ (i.val = 0 ∧ j.val = 0) := by omega
    have g2 : ¬ (i.val = 0 ∧ j.val = 1) := by omega
    have g3 : ¬ (i.val = 1 ∧ j.val = 0) := by omega
    have g4 : ¬ (i.val = 1 ∧ j.val = 1) := by omega
    have g5 : ¬ (i.val = j.val) := by omega
    rw [if_neg h1, if_neg h2, if_neg h3, if_neg h4, if_neg h5,
        if_neg g1, if_neg g2, if_neg g3, if_neg g4, if_neg g5]
  · have h1 : ¬ (j.val = 0 ∧ i.val = 0) := by omega
    have h2 : ¬ (j.val = 0 ∧ i.val = 1) := by omega
    have h3 : ¬ (j.val = 1 ∧ i.val = 0) := by omega
    have h4 : ¬ (j.val = 1 ∧ i.val = 1) := by omega
    have h5 : ¬ (j.val = i.val) := by omega
    have g1 : ¬ (i.val = 0 ∧ j.val = 0) := by omega
    have g2 : ¬ (i.val = 0 ∧ j.val = 1) := by omega
    have g3 : ¬ (i.val = 1 ∧ j.val = 0) := by omega
    have g4 : ¬ (i.val = 1 ∧ j.val = 1) := by omega
    have g5 : ¬ (i.val = j.val) := by omega
    rw [if_neg h1, if_neg h2, if_neg h3, if_neg h4, if_neg h5,
        if_neg g1, if_neg g2, if_neg g3, if_neg g4, if_neg g5]
  · have h1 : ¬ (j.val = 0 ∧ i.val = 0) := by omega
    have h2 : ¬ (j.val = 0 ∧ i.val = 1) := by omega
    have h3 : ¬ (j.val = 1 ∧ i.val = 0) := by omega
    have h4 : ¬ (j.val = 1 ∧ i.val = 1) := by omega
    have g1 : ¬ (i.val = 0 ∧ j.val = 0) := by omega
    have g2 : ¬ (i.val = 0 ∧ j.val = 1) := by omega
    have g3 : ¬ (i.val = 1 ∧ j.val = 0) := by omega
    have g4 : ¬ (i.val = 1 ∧ j.val = 1) := by omega
    rw [if_neg h1, if_neg h2, if_neg h3, if_neg h4,
        if_neg g1, if_neg g2, if_neg g3, if_neg g4]
    by_cases hij : i.val = j.val
    · have hji : j.val = i.val := hij.symm
      rw [if_pos hji, if_pos hij]
    · have hji : ¬ (j.val = i.val) := fun h => hij h.symm
      rw [if_neg hji, if_neg hij]

private theorem diagVecN_vecExtend (v0 v1 tailVal : Int) (m : Nat) (i j : Fin (m + 2)) :
    diagVecN (vecExtend v0 v1 tailVal m) i j = blockExtend (Mat2.diag v0 v1) tailVal m i j := by
  dsimp [diagVecN, vecExtend, blockExtend, Mat2.diag]
  have hi_cases : i.val = 0 ∨ i.val = 1 ∨ 2 ≤ i.val := by omega
  have hj_cases : j.val = 0 ∨ j.val = 1 ∨ 2 ≤ j.val := by omega
  rcases hi_cases with hi | hi | hi <;> rcases hj_cases with hj | hj | hj
  · rw [hi, hj]; rfl
  · rw [hi, hj]; rfl
  · have hne : ¬ (i.val = j.val) := by omega
    have g1 : ¬ (i.val = 0 ∧ j.val = 0) := by omega
    have g2 : ¬ (i.val = 0 ∧ j.val = 1) := by omega
    have g3 : ¬ (i.val = 1 ∧ j.val = 0) := by omega
    have g4 : ¬ (i.val = 1 ∧ j.val = 1) := by omega
    rw [if_neg hne, if_neg g1, if_neg g2, if_neg g3, if_neg g4, if_neg hne]
  · rw [hi, hj]; rfl
  · rw [hi, hj]; rfl
  · have hne : ¬ (i.val = j.val) := by omega
    have g1 : ¬ (i.val = 0 ∧ j.val = 0) := by omega
    have g2 : ¬ (i.val = 0 ∧ j.val = 1) := by omega
    have g3 : ¬ (i.val = 1 ∧ j.val = 0) := by omega
    have g4 : ¬ (i.val = 1 ∧ j.val = 1) := by omega
    rw [if_neg hne, if_neg g1, if_neg g2, if_neg g3, if_neg g4, if_neg hne]
  · have hne : ¬ (i.val = j.val) := by omega
    have g1 : ¬ (i.val = 0 ∧ j.val = 0) := by omega
    have g2 : ¬ (i.val = 0 ∧ j.val = 1) := by omega
    have g3 : ¬ (i.val = 1 ∧ j.val = 0) := by omega
    have g4 : ¬ (i.val = 1 ∧ j.val = 1) := by omega
    rw [if_neg hne, if_neg g1, if_neg g2, if_neg g3, if_neg g4, if_neg hne]
  · have hne : ¬ (i.val = j.val) := by omega
    have g1 : ¬ (i.val = 0 ∧ j.val = 0) := by omega
    have g2 : ¬ (i.val = 0 ∧ j.val = 1) := by omega
    have g3 : ¬ (i.val = 1 ∧ j.val = 0) := by omega
    have g4 : ¬ (i.val = 1 ∧ j.val = 1) := by omega
    rw [if_neg hne, if_neg g1, if_neg g2, if_neg g3, if_neg g4, if_neg hne]
  · have hi0 : ¬ (i.val = 0) := by omega
    have hi1 : ¬ (i.val = 1) := by omega
    have g1 : ¬ (i.val = 0 ∧ j.val = 0) := by omega
    have g2 : ¬ (i.val = 0 ∧ j.val = 1) := by omega
    have g3 : ¬ (i.val = 1 ∧ j.val = 0) := by omega
    have g4 : ¬ (i.val = 1 ∧ j.val = 1) := by omega
    rw [if_neg hi0, if_neg hi1, if_neg g1, if_neg g2, if_neg g3, if_neg g4]

private theorem prodPrefix_congr {n : Nat} (u w : Fin n → Int) (h : ∀ i : Fin n, u i = w i) :
    (k : Nat) → (hk : k ≤ n) → prodPrefix u k hk = prodPrefix w k hk
  | 0, _ => rfl
  | k + 1, hk => by
    dsimp [prodPrefix]
    rw [prodPrefix_congr u w h k (Nat.le_of_succ_le hk), h ⟨k, hk⟩]

def U2_rat : Mat2 := ⟨3, -4, 4, 3⟩
def A2_rat : Mat2 := ⟨34, 12, 12, 41⟩
def B2_rat : Mat2 := ⟨43, 24, 24, 57⟩

abbrev An_family (m : Nat) : MatN (m + 2) := blockExtend A2_rat 25 m
abbrev Bn_family (m : Nat) : MatN (m + 2) := blockExtend B2_rat 25 m
abbrev svAn (m : Nat) : Fin (m + 2) → Int := vecExtend 50 25 25 m
abbrev svBn (m : Nat) : Fin (m + 2) → Int := vecExtend 75 25 25 m
abbrev svABn (m : Nat) : Fin (m + 2) → Int := vecExtend 3750 625 625 m

private theorem mulN_ext_congr {n : Nat} {A1 A2 B1 B2 : MatN n}
    (hA : ∀ i j, A1 i j = A2 i j) (hB : ∀ i j, B1 i j = B2 i j) (i j : Fin n) :
    mulN A1 B1 i j = mulN A2 B2 i j := by
  dsimp [mulN]
  exact sumFin_congr n _ _ (fun k => by rw [hA i k, hB k j])

private theorem vecExtend_sorted {v0 v1 : Int} (hv1 : 0 ≤ v1) (hord : v1 ≤ v0) (m : Nat) :
    (∀ i : Fin (m + 2), 0 ≤ vecExtend v0 v1 v1 m i) ∧
    (∀ i j : Fin (m + 2), i.val ≤ j.val → vecExtend v0 v1 v1 m j ≤ vecExtend v0 v1 v1 m i) := by
  constructor
  · intro i
    dsimp [vecExtend]
    split
    · omega
    · split <;> omega
  · intro i j hij
    dsimp [vecExtend]
    by_cases hj0 : j.val = 0
    · have hi0 : i.val = 0 := by omega
      rw [if_pos hj0, if_pos hi0]
      omega
    · rw [if_neg hj0]
      have hlhs : (if j.val = 1 then v1 else v1) = v1 := by split <;> rfl
      rw [hlhs]
      split
      · exact hord
      · split <;> omega

/-- **All-Dimensions (`n = m + 2 ≥ 2`) Disproof Theorem**:
    For every dimension `n = m + 2 ≥ 2`, `An_family m` and `Bn_family m` admit exact
    scaled-orthogonal SVDs with strictly positive singular values `svAn m` and `svBn m`,
    their product `mulN (An_family m) (Bn_family m)` has singular values `svABn m`
    attaining exact partial-product equality for **every** `k ∈ {0, ..., m + 2}`,
    yet none of `An_family m`, `Bn_family m`, or `mulN (An_family m) (Bn_family m)` is diagonal. -/
theorem disproof_all_dimensions_ge_two (m : Nat) :
    HasScaledOrthogonalSVD (An_family m) (svAn m) ∧
    HasScaledOrthogonalSVD (Bn_family m) (svBn m) ∧
    HasScaledOrthogonalSVD (mulN (An_family m) (Bn_family m)) (svABn m) ∧
    (∀ (k : Nat) (hk : k ≤ m + 2),
      prodPrefix (svABn m) k hk =
        prodPrefix (fun i => svAn m i * svBn m i) k hk) ∧
    ¬ IsDiagonalN (An_family m) ∧
    ¬ IsDiagonalN (Bn_family m) ∧
    ¬ IsDiagonalN (mulN (An_family m) (Bn_family m)) := by
  have hU_orth : ∀ i j : Fin (m + 2),
      mulN (transposeN (blockExtend U2_rat 5 m)) (blockExtend U2_rat 5 m) i j =
        if i.val = j.val then (5 : Int) ^ 2 else 0 := by
    intro i j
    rw [mulN_ext_congr (transposeN_blockExtend U2_rat 5 m) (fun _ _ => rfl),
        mulN_blockExtend (Mat2.transpose U2_rat) U2_rat 5 5 m]
    have hU2 : Mat2.mul (Mat2.transpose U2_rat) U2_rat = Mat2.diag 25 25 := by decide
    rw [hU2, ← diagVecN_vecExtend 25 25 (5 * 5) m i j]
    dsimp [diagVecN]
    have hv : vecExtend 25 25 25 m i = 25 := by
      dsimp [vecExtend]
      split
      · rfl
      · split <;> rfl
    rw [hv]
  have hAn_svd : HasScaledOrthogonalSVD (An_family m) (svAn m) := by
    rcases vecExtend_sorted (by omega : (0 : Int) ≤ 25) (by omega : (25 : Int) ≤ 50) m with ⟨h0, hord⟩
    refine ⟨h0, hord, blockExtend U2_rat 5 m, blockExtend U2_rat 5 m, 5, 5,
      by omega, by omega, hU_orth, hU_orth, ?_⟩
    intro i j
    rw [mulN_ext_congr (mulN_ext_congr (fun _ _ => rfl) (diagVecN_vecExtend 50 25 25 m))
          (transposeN_blockExtend U2_rat 5 m),
        mulN_ext_congr (mulN_blockExtend U2_rat (Mat2.diag 50 25) 5 25 m) (fun _ _ => rfl),
        mulN_blockExtend (Mat2.mul U2_rat (Mat2.diag 50 25)) (Mat2.transpose U2_rat) (5 * 25) 5 m]
    have hA2 : Mat2.mul (Mat2.mul U2_rat (Mat2.diag 50 25)) (Mat2.transpose U2_rat) =
        Mat2.scale 25 A2_rat := by decide
    rw [hA2]
    dsimp [An_family, blockExtend, Mat2.scale]
    split
    · omega
    · split
      · omega
      · split
        · omega
        · split
          · omega
          · split <;> omega
  have hBn_svd : HasScaledOrthogonalSVD (Bn_family m) (svBn m) := by
    rcases vecExtend_sorted (by omega : (0 : Int) ≤ 25) (by omega : (25 : Int) ≤ 75) m with ⟨h0, hord⟩
    refine ⟨h0, hord, blockExtend U2_rat 5 m, blockExtend U2_rat 5 m, 5, 5,
      by omega, by omega, hU_orth, hU_orth, ?_⟩
    intro i j
    rw [mulN_ext_congr (mulN_ext_congr (fun _ _ => rfl) (diagVecN_vecExtend 75 25 25 m))
          (transposeN_blockExtend U2_rat 5 m),
        mulN_ext_congr (mulN_blockExtend U2_rat (Mat2.diag 75 25) 5 25 m) (fun _ _ => rfl),
        mulN_blockExtend (Mat2.mul U2_rat (Mat2.diag 75 25)) (Mat2.transpose U2_rat) (5 * 25) 5 m]
    have hB2 : Mat2.mul (Mat2.mul U2_rat (Mat2.diag 75 25)) (Mat2.transpose U2_rat) =
        Mat2.scale 25 B2_rat := by decide
    rw [hB2]
    dsimp [Bn_family, blockExtend, Mat2.scale]
    split
    · omega
    · split
      · omega
      · split
        · omega
        · split
          · omega
          · split <;> omega
  have hABn_svd : HasScaledOrthogonalSVD (mulN (An_family m) (Bn_family m)) (svABn m) := by
    rcases vecExtend_sorted (by omega : (0 : Int) ≤ 625) (by omega : (625 : Int) ≤ 3750) m with ⟨h0, hord⟩
    refine ⟨h0, hord, blockExtend U2_rat 5 m, blockExtend U2_rat 5 m, 5, 5,
      by omega, by omega, hU_orth, hU_orth, ?_⟩
    intro i j
    rw [mulN_blockExtend A2_rat B2_rat 25 25 m i j,
        mulN_ext_congr (mulN_ext_congr (fun _ _ => rfl) (diagVecN_vecExtend 3750 625 625 m))
          (transposeN_blockExtend U2_rat 5 m),
        mulN_ext_congr (mulN_blockExtend U2_rat (Mat2.diag 3750 625) 5 625 m) (fun _ _ => rfl),
        mulN_blockExtend (Mat2.mul U2_rat (Mat2.diag 3750 625)) (Mat2.transpose U2_rat) (5 * 625) 5 m]
    have hAB2 : Mat2.mul (Mat2.mul U2_rat (Mat2.diag 3750 625)) (Mat2.transpose U2_rat) =
        Mat2.scale 25 (Mat2.mul A2_rat B2_rat) := by decide
    rw [hAB2]
    dsimp [blockExtend, Mat2.scale]
    split
    · omega
    · split
      · omega
      · split
        · omega
        · split
          · omega
          · split <;> omega
  have hprod_eq : ∀ (k : Nat) (hk : k ≤ m + 2),
      prodPrefix (svABn m) k hk = prodPrefix (fun i => svAn m i * svBn m i) k hk := by
    intro k hk
    apply prodPrefix_congr
    intro i
    dsimp [svABn, svAn, svBn, vecExtend]
    split
    · omega
    · split <;> omega
  have hnotA : ¬ IsDiagonalN (An_family m) := by
    intro hd
    have h01 := hd ⟨0, by omega⟩ ⟨1, by omega⟩ (by dsimp; omega)
    dsimp [An_family, blockExtend, A2_rat] at h01
    omega
  have hnotB : ¬ IsDiagonalN (Bn_family m) := by
    intro hd
    have h01 := hd ⟨0, by omega⟩ ⟨1, by omega⟩ (by dsimp; omega)
    dsimp [Bn_family, blockExtend, B2_rat] at h01
    omega
  have hnotAB : ¬ IsDiagonalN (mulN (An_family m) (Bn_family m)) := by
    intro hd
    have h01 := hd ⟨0, by omega⟩ ⟨1, by omega⟩ (by dsimp; omega)
    rw [mulN_blockExtend A2_rat B2_rat 25 25 m ⟨0, by omega⟩ ⟨1, by omega⟩] at h01
    dsimp [blockExtend, Mat2.mul, A2_rat, B2_rat] at h01
    omega
  exact ⟨hAn_svd, hBn_svd, hABn_svd, hprod_eq, hnotA, hnotB, hnotAB⟩

end LidskiiProduct
