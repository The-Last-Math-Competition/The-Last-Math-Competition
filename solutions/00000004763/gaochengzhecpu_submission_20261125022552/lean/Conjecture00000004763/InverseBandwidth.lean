/-
  Conjecture 00000004763 — Refutation of Subclaim 4:
  Unbounded Inverse Bandwidth of Conversion Matrices and Stirling-Type Triangles.

  Formalizes infinite 1-indexed lower-unitriangular matrices `LMatrix` (`1 ≤ k ≤ n`),
  exact matrix multiplication `matMul`, exact unitriangular inversion `matInv` with
  two-sided inverse and uniqueness theorems, and `HasFiniteLowerBandwidth`.

  Proves:
  1. Non-vacuity: `matId` and `bidiagDiff` (`I - S`) satisfy `HasFiniteLowerBandwidth`,
     whereas `matInv bidiagDiff` does NOT.
  2. Stirling 2nd/1st kind (`stirling2`, `stirling1 = matInv stirling2`):
     `(matInv stirling2) n 1 = (-1)^(n - 1) * (n - 1)! ≠ 0` for all `n ≥ 1`, so
     NEITHER `stirling2` NOR `matInv stirling2` has finite lower bandwidth.
  3. Block-count conversion matrices `T_clToFr = N⁻¹ S` and `T_frToCl = S⁻¹ N`
     (mutual inverses between Stirling and Narayana triangles, and specializations
     at `c_j = 1` of the Bell/Kreweras polynomial triangles over `ℚ(c_1, c_2, ...)`):
     - Exact recurrence & positivity: `(S⁻¹ N) n 2 = (-1)^(n - 1) * wSeq n ≠ 0` for ALL `n ≥ 4`
       (row-`n` bandwidth `n - 2 → ∞`), so `¬ HasFiniteLowerBandwidth (matInv T_clToFr)`.
     - Exponential-vs-polynomial growth: `S(n, 2) = 2^(n - 1) - 1 = ∑_{k=2}^n N(n, k) (N⁻¹ S)_{k, 2}`
       implies `(N⁻¹ S)_{k, 2} ≠ 0` for infinitely many `k`, so
       `¬ HasFiniteLowerBandwidth (matInv T_frToCl)` (and `¬ HasFiniteLowerBandwidth (matInv narayana)`).
  4. Canonical moment-recurrence matrices `L_cl(m)` and `L_fr(m)` over `ℚ(m_1, m_2, ...)`
     satisfying `L_cl(m) c = m = L_fr(m) κ`:
     - Both `T_rec_clToFr(m) = L_fr(m)⁻¹ L_cl(m)` and its inverse `T_rec_frToCl(m) = L_cl(m)⁻¹ L_fr(m)`
       have `(n, 2)`-entry equal to `±(n - 3) ≠ 0` at `m = singleMoment (n - 2)` for ALL `n ≥ 4`,
       proving unbounded bandwidth `n - 2 → ∞` in BOTH directions.
-/

import Conjecture00000004763.Basic
import Conjecture00000004763.UnboundedDegree

namespace Conjecture00000004763

/-!
## 1. Infinite 1-Indexed Lower-Unitriangular Matrices and Exact Inversion
-/

/-- 1-indexed infinite integer matrix (`row n ≥ 1`, `col k ≥ 1`). -/
abbrev LMatrix := Nat → Nat → Int

/-- A matrix `M` is lower unitriangular on `1 ≤ n, k` if `M n n = 1` (`n ≥ 1`),
    `M n k = 0` (`1 ≤ n < k`), and `0`-row/`0`-col entries vanish. -/
def IsUnitriangular (M : LMatrix) : Prop :=
  (∀ k, M 0 k = 0) ∧
  (∀ n, M n 0 = 0) ∧
  (∀ n, 1 ≤ n → M n n = 1) ∧
  (∀ n k, 1 ≤ n → n < k → M n k = 0)

/-- Identity matrix on `n ≥ 1`. -/
def matId : LMatrix :=
  fun n k => if 1 ≤ n ∧ n = k then 1 else 0

theorem isUnitriangular_matId : IsUnitriangular matId := by
  refine ⟨fun _ => by simp [matId], fun _ => by simp [matId]; omega, ?_, ?_⟩
  · intro n hn; simp [matId, hn]
  · intro n k _ hnk; simp [matId]; omega

/-- Matrix product `(A * B)_{n, k} = ∑_{r=1}^n A_{n, r} B_{r, k}` for lower-triangular matrices. -/
def matMul (A B : LMatrix) : LMatrix :=
  fun n k =>
    if n = 0 ∨ k = 0 ∨ n < k then 0
    else sumRange n (fun idx => A n (idx + 1) * B (idx + 1) k)

theorem isUnitriangular_matMul {A B : LMatrix}
    (hA : IsUnitriangular A) (hB : IsUnitriangular B) :
    IsUnitriangular (matMul A B) := by
  refine ⟨fun _ => by simp [matMul], fun _ => by simp [matMul], ?_, ?_⟩
  · intro n hn
    unfold matMul
    have hc : ¬ (n = 0 ∨ n = 0 ∨ n < n) := by omega
    simp only [hc, ite_false]
    obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
    rw [sumRange_succ, hA.2.2.1 (m + 1) (by omega), hB.2.2.1 (m + 1) (by omega)]
    have hzero : sumRange m (fun idx => A (m + 1) (idx + 1) * B (idx + 1) (m + 1)) = 0 := by
      rw [← sumRange_const_zero m]
      apply sumRange_congr
      intro idx hidx
      rw [hB.2.2.2 (idx + 1) (m + 1) (by omega) (by omega)]
      simp
    rw [hzero]
    omega
  · intro n k _ hnk
    unfold matMul
    have hc : n = 0 ∨ k = 0 ∨ n < k := Or.inr (Or.inr hnk)
    simp [hc]

theorem matMul_assoc_unitri {A B C : LMatrix}
    (_hA : IsUnitriangular A) (hB : IsUnitriangular B) (hC : IsUnitriangular C)
    (n k : Nat) :
    matMul (matMul A B) C n k = matMul A (matMul B C) n k := by
  by_cases hbad : n = 0 ∨ k = 0 ∨ n < k
  · unfold matMul; simp [hbad]
  · unfold matMul
    simp only [hbad, ite_false]
    have hlhs2 :
        sumRange n (fun j =>
          (if n = 0 ∨ j + 1 = 0 ∨ n < j + 1 then 0
           else sumRange n (fun i => A n (i + 1) * B (i + 1) (j + 1))) * C (j + 1) k) =
        sumRange n (fun j => sumRange n (fun i => A n (i + 1) * B (i + 1) (j + 1) * C (j + 1) k)) := by
      apply sumRange_congr
      intro j hj
      have hjc : ¬ (n = 0 ∨ j + 1 = 0 ∨ n < j + 1) := by omega
      simp only [hjc, ite_false, sumRange_mul_right]
    have hrhs2 :
        sumRange n (fun i =>
          A n (i + 1) *
            (if i + 1 = 0 ∨ k = 0 ∨ i + 1 < k then 0
             else sumRange (i + 1) (fun j => B (i + 1) (j + 1) * C (j + 1) k))) =
        sumRange n (fun i => sumRange n (fun j => A n (i + 1) * B (i + 1) (j + 1) * C (j + 1) k)) := by
      apply sumRange_congr
      intro i hi
      by_cases hik : i + 1 < k
      · have hic : i + 1 = 0 ∨ k = 0 ∨ i + 1 < k := Or.inr (Or.inr hik)
        simp only [hic, ite_true, Int.mul_zero]
        symm
        rw [← sumRange_const_zero n]
        apply sumRange_congr
        intro j _
        by_cases hij : i + 1 < j + 1
        · rw [hB.2.2.2 (i + 1) (j + 1) (by omega) hij]; simp
        · rw [hC.2.2.2 (j + 1) k (by omega) (by omega)]; simp
      · have hic : ¬ (i + 1 = 0 ∨ k = 0 ∨ i + 1 < k) := by omega
        simp only [hic, ite_false, ← sumRange_mul_left]
        have hext : ∀ m, i + 1 ≤ m → m ≤ n →
            sumRange (i + 1) (fun j => A n (i + 1) * (B (i + 1) (j + 1) * C (j + 1) k)) =
            sumRange m (fun j => A n (i + 1) * B (i + 1) (j + 1) * C (j + 1) k) := by
          intro m h1 h2
          induction m with
          | zero => omega
          | succ m' ihm =>
            by_cases hm' : i + 1 ≤ m'
            · rw [sumRange_succ m', ← ihm hm' (Nat.le_of_succ_le h2)]
              rw [hB.2.2.2 (i + 1) (m' + 1) (by omega) (by omega)]
              simp
            · have heq : m' + 1 = i + 1 := by omega
              rw [heq]
              apply sumRange_congr
              intro j _; rw [Int.mul_assoc]
        exact hext n (by omega) (Nat.le_refl n)
    have hswap : ∀ (a b : Nat) (F : Nat → Nat → Int),
        sumRange a (fun j => sumRange b (fun i => F i j)) =
        sumRange b (fun i => sumRange a (fun j => F i j)) := by
      intro a b F
      induction a with
      | zero => simp [sumRange, sumRange_const_zero]
      | succ a' iha =>
        rw [sumRange_succ, iha, ← sumRange_add]
        apply sumRange_congr
        intro i _
        rw [sumRange_succ]
    rw [hlhs2, hrhs2, hswap]

/-- Fuel-indexed forward substitution for the inverse of a lower unitriangular matrix `M`:
    for `k < n`, `(M⁻¹)_{n, k} = - ∑_{r=k}^{n-1} M_{n, r} (M⁻¹)_{r, k}`. -/
def matInvFuel (M : LMatrix) : Nat → Nat → Nat → Int
  | _, 0, _ => 0
  | _, _, 0 => 0
  | 0, n + 1, k + 1 => if n = k then 1 else 0
  | fuel + 1, n + 1, k + 1 =>
      if n + 1 < k + 1 then 0
      else if n + 1 = k + 1 then 1
      else - sumRange n (fun idx => M (n + 1) (idx + 1) * matInvFuel M fuel (idx + 1) (k + 1))

theorem matInvFuel_stable (M : LMatrix) :
    ∀ f1 f2 n k, n ≤ f1 → n ≤ f2 → matInvFuel M f1 n k = matInvFuel M f2 n k
  | _, _, 0, _, _, _ => by simp [matInvFuel]
  | _, _, _ + 1, 0, _, _ => by simp [matInvFuel]
  | 0, _, _ + 1, _ + 1, h1, _ => by omega
  | _ + 1, 0, _ + 1, _ + 1, _, h2 => by omega
  | f1 + 1, f2 + 1, n + 1, k + 1, h1, h2 => by
      simp only [matInvFuel]
      by_cases hlt : n + 1 < k + 1
      · simp [hlt]
      · by_cases heq : n + 1 = k + 1
        · simp [hlt, heq]
        · simp only [hlt, heq, ite_false]
          have hsum :
              sumRange n (fun idx => M (n + 1) (idx + 1) * matInvFuel M f1 (idx + 1) (k + 1)) =
              sumRange n (fun idx => M (n + 1) (idx + 1) * matInvFuel M f2 (idx + 1) (k + 1)) := by
            apply sumRange_congr
            intro idx hidx
            have hi1 : idx + 1 ≤ f1 := Nat.le_trans (Nat.succ_le_of_lt hidx) (Nat.le_of_succ_le_succ h1)
            have hi2 : idx + 1 ≤ f2 := Nat.le_trans (Nat.succ_le_of_lt hidx) (Nat.le_of_succ_le_succ h2)
            rw [matInvFuel_stable M f1 f2 (idx + 1) (k + 1) hi1 hi2]
          rw [hsum]

/-- Exact inverse `matInv M` of a lower unitriangular matrix `M`. -/
def matInv (M : LMatrix) : LMatrix :=
  fun n k => matInvFuel M n n k

theorem matInv_step (M : LMatrix) {n k : Nat} (hk : 1 ≤ k) (hkn : k < n) :
    matInv M n k = - sumRange (n - 1) (fun idx => M n (idx + 1) * matInv M (idx + 1) k) := by
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  unfold matInv
  conv => lhs; simp only [matInvFuel]
  have hlt : ¬ (n' + 1 < k' + 1) := by omega
  have heq : ¬ (n' + 1 = k' + 1) := by omega
  simp only [hlt, heq, ite_false, Nat.add_sub_cancel]
  have hsum :
      sumRange n' (fun idx => M (n' + 1) (idx + 1) * matInvFuel M n' (idx + 1) (k' + 1)) =
      sumRange n' (fun idx => M (n' + 1) (idx + 1) * matInvFuel M (idx + 1) (idx + 1) (k' + 1)) := by
    apply sumRange_congr
    intro idx hidx
    rw [matInvFuel_stable M n' (idx + 1) (idx + 1) (k' + 1) (Nat.succ_le_of_lt hidx) (Nat.le_refl _)]
  rw [hsum]

theorem isUnitriangular_matInv (M : LMatrix) : IsUnitriangular (matInv M) := by
  refine ⟨fun _ => by unfold matInv; simp [matInvFuel],
          fun n => by unfold matInv; cases n <;> simp [matInvFuel], ?_, ?_⟩
  · intro n hn
    obtain ⟨n', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
    unfold matInv
    simp [matInvFuel]
  · intro n k hn hnk
    obtain ⟨n', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
    obtain ⟨k', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
    unfold matInv
    simp [matInvFuel, hnk]

/-- Right inverse theorem: `M * M⁻¹ = I` for every lower unitriangular matrix `M`. -/
theorem matMul_matInv {M : LMatrix} (hM : IsUnitriangular M) (n k : Nat) :
    matMul M (matInv M) n k = matId n k := by
  have hInv := isUnitriangular_matInv M
  have hProd := isUnitriangular_matMul hM hInv
  by_cases hn0 : n = 0
  · subst hn0; rw [hProd.1, isUnitriangular_matId.1]
  · by_cases hk0 : k = 0
    · subst hk0; rw [hProd.2.1, isUnitriangular_matId.2.1]
    · by_cases hlt : n < k
      · rw [hProd.2.2.2 n k (by omega) hlt, isUnitriangular_matId.2.2.2 n k (by omega) hlt]
      · by_cases heq : n = k
        · subst heq; rw [hProd.2.2.1 n (by omega), isUnitriangular_matId.2.2.1 n (by omega)]
        · have hk1 : 1 ≤ k := by omega
          have hkn : k < n := by omega
          unfold matMul matId
          have hbad : ¬ (n = 0 ∨ k = 0 ∨ n < k) := by omega
          have hid0 : ¬ (1 ≤ n ∧ n = k) := by omega
          simp only [hbad, hid0, ite_false]
          obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
          rw [sumRange_succ, hM.2.2.1 (m + 1) (by omega), Int.one_mul,
              matInv_step M hk1 hkn]
          simp only [Nat.add_sub_cancel]
          omega

theorem matMul_matId_right {M : LMatrix} (hM : IsUnitriangular M) (n k : Nat) :
    matMul M matId n k = M n k := by
  by_cases hn0 : n = 0
  · subst hn0; simp [matMul, hM.1]
  · by_cases hk0 : k = 0
    · subst hk0; simp [matMul, hM.2.1]
    · by_cases hlt : n < k
      · unfold matMul; simp [hlt, hM.2.2.2 n k (by omega) hlt]
      · unfold matMul
        have hbad : ¬ (n = 0 ∨ k = 0 ∨ n < k) := by omega
        simp only [hbad, ite_false]
        rw [← sumRange_single n (k - 1) (M n k) (by omega)]
        apply sumRange_congr
        intro idx _
        by_cases hidx : idx = k - 1
        · subst hidx
          have hk1 : k - 1 + 1 = k := by omega
          rw [hk1]
          simp [matId, show 1 ≤ k by omega]
        · have hne : idx + 1 ≠ k := by omega
          simp [hidx, matId, hne]

theorem matMul_matId_left {M : LMatrix} (hM : IsUnitriangular M) (n k : Nat) :
    matMul matId M n k = M n k := by
  by_cases hn0 : n = 0
  · subst hn0; simp [matMul, hM.1]
  · by_cases hk0 : k = 0
    · subst hk0; simp [matMul, hM.2.1]
    · by_cases hlt : n < k
      · unfold matMul; simp [hlt, hM.2.2.2 n k (by omega) hlt]
      · unfold matMul
        have hbad : ¬ (n = 0 ∨ k = 0 ∨ n < k) := by omega
        simp only [hbad, ite_false]
        rw [← sumRange_single n (n - 1) (M n k) (by omega)]
        apply sumRange_congr
        intro idx _
        by_cases hidx : idx = n - 1
        · subst hidx
          have hn1 : n - 1 + 1 = n := by omega
          rw [hn1]
          simp [matId, show 1 ≤ n by omega]
        · have hne : n ≠ idx + 1 := by omega
          simp [hidx, matId, hne]

/-- Left inverse theorem: `M⁻¹ * M = I` for every lower unitriangular matrix `M`. -/
theorem matInv_matMul {M : LMatrix} (hM : IsUnitriangular M) (n k : Nat) :
    matMul (matInv M) M n k = matId n k := by
  have hInv := isUnitriangular_matInv M
  have hInvInv := isUnitriangular_matInv (matInv M)
  -- Standard algebra trick: `(M⁻¹) * M = (M⁻¹) * (M * (M⁻¹ * (M⁻¹)⁻¹)) = (M⁻¹ * M⁻¹⁻¹) = I`!
  have h1 : matMul (matInv M) M n k =
      matMul (matMul (matInv M) M) (matMul (matInv M) (matInv (matInv M))) n k := by
    have hR : matMul (matInv M) (matInv (matInv M)) = matId := by
      funext u v; exact matMul_matInv hInv u v
    rw [hR, matMul_matId_right (isUnitriangular_matMul hInv hM)]
  have h2 : matMul (matMul (matInv M) M) (matMul (matInv M) (matInv (matInv M))) n k =
      matMul (matInv M) (matMul M (matMul (matInv M) (matInv (matInv M)))) n k :=
    matMul_assoc_unitri hInv hM (isUnitriangular_matMul hInv hInvInv) n k
  have h3 : matMul M (matMul (matInv M) (matInv (matInv M))) = matInv (matInv M) := by
    funext u v
    rw [← matMul_assoc_unitri hM hInv hInvInv]
    have hL : matMul M (matInv M) = matId := by
      funext a b; exact matMul_matInv hM a b
    rw [hL, matMul_matId_left hInvInv]
  rw [h1, h2, h3]
  exact matMul_matInv hInv n k

/-- Uniqueness of unitriangular inverse: if `M * B = I` (or `B * M = I`), then `B = matInv M`. -/
theorem matInv_unique_right {M B : LMatrix}
    (hM : IsUnitriangular M) (hB : IsUnitriangular B)
    (hMB : ∀ n k, matMul M B n k = matId n k) :
    ∀ n k, B n k = matInv M n k := by
  intro n k
  have hInv := isUnitriangular_matInv M
  have h1 : B n k = matMul (matMul (matInv M) M) B n k := by
    have hL : matMul (matInv M) M = matId := by funext u v; exact matInv_matMul hM u v
    rw [hL, matMul_matId_left hB]
  rw [h1, matMul_assoc_unitri hInv hM hB]
  have hR : matMul M B = matId := by funext u v; exact hMB u v
  rw [hR, matMul_matId_right hInv]

theorem matInv_matMul_distrib {A B : LMatrix}
    (hA : IsUnitriangular A) (hB : IsUnitriangular B) :
    ∀ n k, matInv (matMul A B) n k = matMul (matInv B) (matInv A) n k := by
  intro n k
  symm
  apply matInv_unique_right (isUnitriangular_matMul hA hB)
    (isUnitriangular_matMul (isUnitriangular_matInv B) (isUnitriangular_matInv A))
  intro u v
  rw [← matMul_assoc_unitri (isUnitriangular_matMul hA hB)
      (isUnitriangular_matInv B) (isUnitriangular_matInv A)]
  have hmid : matMul (matMul A B) (matInv B) = A := by
    funext a b
    rw [matMul_assoc_unitri hA hB (isUnitriangular_matInv B)]
    have hBB : matMul B (matInv B) = matId := by funext x y; exact matMul_matInv hB x y
    rw [hBB, matMul_matId_right hA]
  rw [hmid]
  exact matMul_matInv hA u v

/-!
## 2. Lower Bandwidth Predicate and Non-Vacuity Witnesses
-/

/-- A matrix `M` has finite lower bandwidth if there exists `B : Nat` such that
    `M n k = 0` whenever `1 ≤ k ≤ n` and `n - k > B`. -/
def HasFiniteLowerBandwidth (M : LMatrix) : Prop :=
  ∃ B : Nat, ∀ n k : Nat, 1 ≤ k → k ≤ n → B < n - k → M n k = 0

/-- Bidiagonal difference matrix `bidiagDiff = I - S` (diagonal `1`, subdiagonal `-1`). -/
def bidiagDiff : LMatrix :=
  fun n k =>
    if 1 ≤ n ∧ n = k then 1
    else if 1 ≤ k ∧ n = k + 1 then -1
    else 0

/-- Non-vacuity check: `matId` (bandwidth `0`) and `bidiagDiff` (bandwidth `1`) DO satisfy
    `HasFiniteLowerBandwidth`, whereas `matInv bidiagDiff` (all `1`s below diagonal) does NOT. -/
theorem bandwidth_nonvacuity :
    HasFiniteLowerBandwidth matId ∧
    HasFiniteLowerBandwidth bidiagDiff ∧
    ¬ HasFiniteLowerBandwidth (matInv bidiagDiff) := by
  refine ⟨⟨0, fun n k _ _ hgt => by simp [matId]; omega⟩,
          ⟨1, fun n k _ _ hgt => by simp [bidiagDiff]; omega⟩, ?_⟩
  -- Prove `matInv bidiagDiff n k = 1` for all `1 ≤ k ≤ n` by `matInv_unique_right`!
  let allOnes : LMatrix := fun n k => if 1 ≤ k ∧ k ≤ n then 1 else 0
  have hOnes : IsUnitriangular allOnes := by
    refine ⟨fun _ => by simp [allOnes]; omega, fun _ => by simp [allOnes], ?_, ?_⟩
    · intro n hn; simp [allOnes, hn]
    · intro n k _ hnk; simp [allOnes]; omega
  have hBidiag : IsUnitriangular bidiagDiff := by
    refine ⟨fun _ => by simp [bidiagDiff], fun _ => by simp [bidiagDiff]; omega, ?_, ?_⟩
    · intro n hn; simp [bidiagDiff, hn]
    · intro n k _ hnk; simp [bidiagDiff]; omega
  have hMul : ∀ n k, matMul bidiagDiff allOnes n k = matId n k := by
    intro n k
    have hProd := isUnitriangular_matMul hBidiag hOnes
    by_cases hn0 : n = 0
    · subst hn0; rw [hProd.1, isUnitriangular_matId.1]
    · by_cases hk0 : k = 0
      · subst hk0; rw [hProd.2.1, isUnitriangular_matId.2.1]
      · by_cases hlt : n < k
        · rw [hProd.2.2.2 n k (by omega) hlt, isUnitriangular_matId.2.2.2 n k (by omega) hlt]
        · by_cases heq : n = k
          · subst heq; rw [hProd.2.2.1 n (by omega), isUnitriangular_matId.2.2.1 n (by omega)]
          · unfold matMul matId
            have hbad : ¬ (n = 0 ∨ k = 0 ∨ n < k) := by omega
            have hid0 : ¬ (1 ≤ n ∧ n = k) := by omega
            simp only [hbad, hid0, ite_false]
            obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn0
            obtain ⟨m', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : m ≠ 0)
            rw [sumRange_succ, sumRange_succ]
            have hzero : sumRange m' (fun idx => bidiagDiff (m' + 2) (idx + 1) * allOnes (idx + 1) k) = 0 := by
              rw [← sumRange_const_zero m']
              apply sumRange_congr
              intro idx hidx
              have hd1 : m' + 2 ≠ idx + 1 := by omega
              have hd2 : m' + 2 ≠ idx + 2 := by omega
              simp [bidiagDiff, hd1, hd2]
            rw [hzero]
            have h1 : bidiagDiff (m' + 2) (m' + 1) = -1 := by simp [bidiagDiff]
            have h2 : bidiagDiff (m' + 2) (m' + 2) = 1 := by simp [bidiagDiff]
            have h3 : allOnes (m' + 1) k = 1 := by simp [allOnes]; omega
            have h4 : allOnes (m' + 2) k = 1 := by simp [allOnes]; omega
            rw [h1, h2, h3, h4]
            omega
  have hInvEq := matInv_unique_right hBidiag hOnes hMul
  intro ⟨B, hB⟩
  have hz := hB (B + 2) 1 (by omega) (by omega) (by omega)
  rw [← hInvEq (B + 2) 1] at hz
  simp [allOnes] at hz

/-!
## 3. Stirling Triangle `stirling2` and Signed Stirling Inverse `stirling1 = matInv stirling2`
-/

/-- Raw Stirling numbers of the second kind `stirling2Raw n k = S(n, k)`. -/
def stirling2Raw : Nat → Nat → Int
  | 0, 0 => 1
  | 0, _ + 1 => 0
  | _ + 1, 0 => 0
  | n + 1, k + 1 => ((k + 1 : Nat) : Int) * stirling2Raw n (k + 1) + stirling2Raw n k

/-- 1-indexed lower-unitriangular Stirling matrix `stirling2`. -/
def stirling2 : LMatrix :=
  fun n k => if n = 0 then 0 else stirling2Raw n k

/-- Raw signed Stirling numbers of the first kind `stirling1Raw n k = s(n, k)`. -/
def stirling1Raw : Nat → Nat → Int
  | 0, 0 => 1
  | 0, _ + 1 => 0
  | _ + 1, 0 => 0
  | n + 1, k + 1 => stirling1Raw n k - (n : Int) * stirling1Raw n (k + 1)

/-- 1-indexed lower-unitriangular signed Stirling matrix `stirling1`. -/
def stirling1 : LMatrix :=
  fun n k => if n = 0 then 0 else stirling1Raw n k

theorem stirling2Raw_gt : ∀ n k, n < k → stirling2Raw n k = 0 := by
  intro n
  induction n with
  | zero => intro k hk; cases k with | zero => omega | succ k' => rfl
  | succ m ih =>
    intro k hk
    cases k with
    | zero => omega
    | succ k' =>
      simp only [stirling2Raw]
      rw [ih (k' + 1) (by omega), ih k' (by omega)]
      omega

theorem stirling2Raw_self : ∀ n, stirling2Raw n n = 1 := by
  intro n
  induction n with
  | zero => rfl
  | succ m ih =>
    simp only [stirling2Raw, stirling2Raw_gt m (m + 1) (by omega), ih]
    omega

theorem stirling1Raw_gt : ∀ n k, n < k → stirling1Raw n k = 0 := by
  intro n
  induction n with
  | zero => intro k hk; cases k with | zero => omega | succ k' => rfl
  | succ m ih =>
    intro k hk
    cases k with
    | zero => omega
    | succ k' =>
      simp only [stirling1Raw]
      rw [ih k' (by omega), ih (k' + 1) (by omega)]
      omega

theorem stirling1Raw_self : ∀ n, stirling1Raw n n = 1 := by
  intro n
  induction n with
  | zero => rfl
  | succ m ih =>
    simp only [stirling1Raw, stirling1Raw_gt m (m + 1) (by omega), ih]
    omega

theorem isUnitriangular_stirling2 : IsUnitriangular stirling2 := by
  refine ⟨fun _ => rfl, fun n => by cases n <;> rfl, ?_, ?_⟩
  · intro n hn; simp [stirling2, show n ≠ 0 by omega, stirling2Raw_self]
  · intro n k hn hnk; simp [stirling2, show n ≠ 0 by omega, stirling2Raw_gt n k hnk]

theorem isUnitriangular_stirling1 : IsUnitriangular stirling1 := by
  refine ⟨fun _ => rfl, fun n => by cases n <;> rfl, ?_, ?_⟩
  · intro n hn; simp [stirling1, show n ≠ 0 by omega, stirling1Raw_self]
  · intro n k hn hnk; simp [stirling1, show n ≠ 0 by omega, stirling1Raw_gt n k hnk]

/-- Classical orthogonality `∑_{r=0}^n stirling2Raw n r * stirling1Raw r k = δ_{n, k}`. -/
theorem stirling_orthogonality :
    ∀ n k : Nat, sumRange (n + 1) (fun r => stirling2Raw n r * stirling1Raw r k) =
      if n = k then 1 else 0 := by
  intro n
  induction n with
  | zero =>
    intro k
    cases k <;> simp [sumRange, stirling2Raw, stirling1Raw]
  | succ m ih =>
    intro k
    cases k with
    | zero =>
      -- Peel `r = 0`: `stirling2Raw (m + 1) 0 = 0`, and for `r ≥ 1`, `stirling1Raw r 0 = 0`!
      simp only [Nat.succ_ne_zero, ite_false]
      rw [← sumRange_const_zero (m + 2)]
      apply sumRange_congr
      intro r _
      cases r <;> simp [stirling2Raw, stirling1Raw]
    | succ k' =>
      -- Use `stirling2Raw (m + 1) (r + 1) = (r + 1) * stirling2Raw m (r + 1) + stirling2Raw m r`
      -- and `stirling1Raw (r + 1) (k' + 1) = stirling1Raw r k' - r * stirling1Raw r (k' + 1)`?
      -- Wait: combine `(r * stirling2Raw m r) * stirling1Raw r (k' + 1)` with `stirling2Raw m r * stirling1Raw (r + 1) (k' + 1)`
      -- = `stirling2Raw m r * stirling1Raw r k'`!! TELESCOPES TO `ih k'` IN ONE LINE!!
      have hpeel0 : ∀ u (g : Nat → Int),
          sumRange (u + 1) g = g 0 + sumRange u (fun r => g (r + 1)) := by
        intro u g
        induction u with
        | zero => simp [sumRange]
        | succ u' ihu => rw [sumRange_succ, ihu, sumRange_succ]; omega
      rw [hpeel0 (m + 1)]
      simp only [stirling2Raw, Int.zero_mul, Int.zero_add]
      have hexpand :
          sumRange (m + 1) (fun r =>
            (((r + 1 : Nat) : Int) * stirling2Raw m (r + 1) + stirling2Raw m r) *
              stirling1Raw (r + 1) (k' + 1)) =
          sumRange (m + 1) (fun r => ((r + 1 : Nat) : Int) * stirling2Raw m (r + 1) * stirling1Raw (r + 1) (k' + 1)) +
            sumRange (m + 1) (fun r => stirling2Raw m r * stirling1Raw r k') -
            sumRange (m + 1) (fun r => (r : Int) * stirling2Raw m r * stirling1Raw r (k' + 1)) := by
        rw [← sumRange_add, ← sumRange_sub]
        apply sumRange_congr
        intro r _
        rw [Int.add_mul]
        conv => lhs; rhs; simp only [stirling1Raw]; rw [Int.mul_sub]
        have hr_assoc : stirling2Raw m r * ((r : Int) * stirling1Raw r (k' + 1)) =
            (r : Int) * stirling2Raw m r * stirling1Raw r (k' + 1) := by
          simp only [Int.mul_assoc, Int.mul_left_comm, Int.mul_comm]
        rw [hr_assoc]
        omega
      -- Notice `sumRange (m + 1) (fun r => (r + 1) * stirling2Raw m (r + 1) * ...)`
      -- equals `sumRange (m + 1) (fun r => r * stirling2Raw m r * ...)` because at `r = 0` it's `0`
      -- and at `r + 1 = m + 1`, `stirling2Raw m (m + 1) = 0`!!
      have hcancel :
          sumRange (m + 1) (fun r => ((r + 1 : Nat) : Int) * stirling2Raw m (r + 1) * stirling1Raw (r + 1) (k' + 1)) =
          sumRange (m + 1) (fun r => (r : Int) * stirling2Raw m r * stirling1Raw r (k' + 1)) := by
        rw [sumRange_succ m (fun r => ((r + 1 : Nat) : Int) * stirling2Raw m (r + 1) * stirling1Raw (r + 1) (k' + 1))]
        rw [stirling2Raw_gt m (m + 1) (by omega)]
        rw [hpeel0 m (fun r => (r : Int) * stirling2Raw m r * stirling1Raw r (k' + 1))]
        simp
      rw [hexpand, hcancel, ih k']
      by_cases heq : m = k'
      · subst heq; simp; omega
      · have hne : m + 1 ≠ k' + 1 := by omega
        simp [heq, hne]

/-- `matInv stirling2` equals `stirling1` everywhere! -/
theorem matInv_stirling2_eq_stirling1 (n k : Nat) :
    matInv stirling2 n k = stirling1 n k := by
  symm
  apply matInv_unique_right isUnitriangular_stirling2 isUnitriangular_stirling1
  intro u v
  have hProd := isUnitriangular_matMul isUnitriangular_stirling2 isUnitriangular_stirling1
  by_cases hu0 : u = 0
  · subst hu0; rw [hProd.1, isUnitriangular_matId.1]
  · by_cases hv0 : v = 0
    · subst hv0; rw [hProd.2.1, isUnitriangular_matId.2.1]
    · by_cases hlt : u < v
      · rw [hProd.2.2.2 u v (by omega) hlt, isUnitriangular_matId.2.2.2 u v (by omega) hlt]
      · unfold matMul matId
        have hbad : ¬ (u = 0 ∨ v = 0 ∨ u < v) := by omega
        simp only [hbad, ite_false]
        have hortho := stirling_orthogonality u v
        have hpeel0 : sumRange (u + 1) (fun r => stirling2Raw u r * stirling1Raw r v) =
            stirling2Raw u 0 * stirling1Raw 0 v +
              sumRange u (fun idx => stirling2 u (idx + 1) * stirling1 (idx + 1) v) := by
          have hp : ∀ a (g : Nat → Int), sumRange (a + 1) g = g 0 + sumRange a (fun i => g (i + 1)) := by
            intro a g
            induction a with
            | zero => simp [sumRange]
            | succ a' iha => rw [sumRange_succ, iha, sumRange_succ]; omega
          rw [hp u]
          have hcong : sumRange u (fun i => stirling2Raw u (i + 1) * stirling1Raw (i + 1) v) =
              sumRange u (fun idx => stirling2 u (idx + 1) * stirling1 (idx + 1) v) := by
            apply sumRange_congr
            intro idx _
            simp [stirling2, stirling1, hu0]
          rw [hcong]
        obtain ⟨u', rfl⟩ := Nat.exists_eq_succ_of_ne_zero hu0
        simp only [stirling2Raw, Int.zero_mul, Int.zero_add] at hpeel0
        rw [← hpeel0, hortho]
        by_cases huv : u' + 1 = v
        · subst huv; simp
        · simp [huv]

theorem stirling1_col_one : ∀ n : Nat, 1 ≤ n →
    stirling1 n 1 = powZ (-1) (n - 1) * factZ (n - 1) := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  induction m with
  | zero => rfl
  | succ m' ihm =>
    have hprev := ihm (by omega)
    simp only [stirling1, Nat.succ_ne_zero, ite_false] at hprev ⊢
    simp only [Nat.add_sub_cancel] at hprev ⊢
    rw [stirling1Raw, hprev]
    have h0 : stirling1Raw (m' + 1) 0 = 0 := rfl
    rw [h0, Int.zero_sub, powZ, factZ]
    calc -(((m' + 1 : Nat) : Int) * (powZ (-1) m' * factZ m'))
      _ = ((-1 : Int) * powZ (-1) m') * (((m' + 1 : Nat) : Int) * factZ m') := by
          rw [← Int.neg_mul]
          have hn1 : -((m' + 1 : Nat) : Int) = (-1 : Int) * ((m' + 1 : Nat) : Int) := by omega
          rw [hn1]
          simp only [Int.mul_assoc, Int.mul_left_comm, Int.mul_comm]

theorem powZ_neg_one_ne_zero (k : Nat) : powZ (-1) k ≠ 0 := by
  induction k with
  | zero => decide
  | succ m ih =>
    simp only [powZ]
    intro hz
    rcases Int.mul_eq_zero.mp hz with h1 | h2
    · omega
    · exact ih h2

/-- Neither `stirling2` nor its inverse `matInv stirling2` has finite lower bandwidth. -/
theorem stirling2_and_inv_unbounded_bandwidth :
    ¬ HasFiniteLowerBandwidth stirling2 ∧
    ¬ HasFiniteLowerBandwidth (matInv stirling2) := by
  refine ⟨?_, ?_⟩
  · have hs1 : ∀ n, 1 ≤ n → stirling2 n 1 = 1 := by
      intro n hn
      obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
      induction m with
      | zero => rfl
      | succ m' ihm =>
        have hp := ihm (by omega)
        simp only [stirling2, Nat.succ_ne_zero, ite_false] at hp ⊢
        rw [stirling2Raw, hp]
        have hz0 : stirling2Raw (m' + 1) 0 = 0 := rfl
        rw [hz0]
        omega
    intro ⟨B, hB⟩
    have hz := hB (B + 2) 1 (by omega) (by omega) (by omega)
    rw [hs1 (B + 2) (by omega)] at hz
    omega
  · intro ⟨B, hB⟩
    have hz := hB (B + 2) 1 (by omega) (by omega) (by omega)
    rw [matInv_stirling2_eq_stirling1, stirling1_col_one (B + 2) (by omega)] at hz
    rcases Int.mul_eq_zero.mp hz with h1 | h2
    · exact powZ_neg_one_ne_zero (B + 2 - 1) h1
    · have := factZ_pos (B + 2 - 1); omega

/-!
## 4. Narayana Triangle `narayana` and Block-Count Conversion Triangles `N⁻¹ S` & `S⁻¹ N`
-/

/-- Division-free Lindström-Gessel-Viennot formula for the Narayana triangle `N(n, k)`. -/
def narayana : LMatrix
  | 0, _ => 0
  | _, 0 => 0
  | _ + 1, 1 => 1
  | n + 1, k + 2 =>
      binom n (k + 1) * binom (n + 1) (k + 1) - binom (n + 1) (k + 2) * binom n k

theorem binom_succ_self (k : Nat) : binom (k + 1) k = ((k + 1 : Nat) : Int) := by
  induction k with
  | zero => rfl
  | succ m ih =>
    rw [binom, ih, binom_self]
    omega

theorem isUnitriangular_narayana : IsUnitriangular narayana := by
  refine ⟨fun k => by cases k <;> rfl, fun n => by cases n <;> rfl, ?_, ?_⟩
  · intro n hn
    match n with
    | 0 => omega
    | 1 => rfl
    | k + 2 =>
      simp only [narayana, binom_self, binom_succ_self]
      omega
  · intro n k hn hnk
    match n, k with
    | 0, _ => omega
    | _ + 1, 0 => omega
    | _ + 1, 1 => omega
    | n' + 1, k' + 2 =>
      simp only [narayana]
      rw [binom_gt (show n' < k' + 1 by omega), binom_gt (show n' + 1 < k' + 2 by omega)]
      simp

theorem narayana_col_two (n : Nat) (hn : 1 ≤ n) :
    narayana n 2 = binom n 2 := by
  match n with
  | 0 => omega
  | 1 => rfl
  | m + 2 =>
    simp only [narayana, Nat.zero_add, binom_one_right, binom_zero_right, Int.mul_one]
    have hm2 : m + 1 + 1 = m + 2 := rfl
    simp only [hm2]
    have h2 := two_mul_binom_two (m + 2)
    have hcast : (((m + 2 : Nat) : Int) - 1) = ((m + 1 : Nat) : Int) := by omega
    rw [hcast] at h2
    have hcomm : ((m + 1 : Nat) : Int) * ((m + 2 : Nat) : Int) =
        ((m + 2 : Nat) : Int) * ((m + 1 : Nat) : Int) := Int.mul_comm _ _
    omega

/-- Block-count classical-to-free conversion triangle `T_clToFr = N⁻¹ * S`
    and its exact inverse `T_frToCl = S⁻¹ * N`. -/
def T_clToFr : LMatrix := matMul (matInv narayana) stirling2
def T_frToCl : LMatrix := matMul (matInv stirling2) narayana

theorem matInv_T_clToFr (n k : Nat) :
    matInv T_clToFr n k = T_frToCl n k := by
  unfold T_clToFr T_frToCl
  rw [matInv_matMul_distrib (isUnitriangular_matInv narayana) isUnitriangular_stirling2]
  have hNN : matInv (matInv narayana) = narayana := by
    funext u v
    symm
    apply matInv_unique_right (isUnitriangular_matInv narayana) isUnitriangular_narayana
    intro a b
    exact matInv_matMul isUnitriangular_narayana a b
  rw [hNN]

theorem matInv_T_frToCl (n k : Nat) :
    matInv T_frToCl n k = T_clToFr n k := by
  unfold T_clToFr T_frToCl
  rw [matInv_matMul_distrib (isUnitriangular_matInv stirling2) isUnitriangular_narayana]
  have hSS : matInv (matInv stirling2) = stirling2 := by
    funext u v
    symm
    apply matInv_unique_right (isUnitriangular_matInv stirling2) isUnitriangular_stirling2
    intro a b
    exact matInv_matMul isUnitriangular_stirling2 a b
  rw [hSS]

/-!
### Exact Positivity & Unbounded Bandwidth of `T_frToCl = (N⁻¹ S)⁻¹ = S⁻¹ N`
-/

/-- Unsigned column-2 sequence `wSeq n = |(S⁻¹ N)_{n, 2}| = (n - 2)! (H_{n - 2} - 1)` (`n ≥ 3`).
    Satisfies `wSeq 3 = 0` and `wSeq (m + 4) = (m + 2) * wSeq (m + 3) + (m + 1)!`
    (`wSeq 4 = 1`, `wSeq 5 = 3 * 1 + 2 = 5`, `wSeq 6 = 4 * 5 + 6 = 26`, ...). -/
def wSeq : Nat → Int
  | 0 => 0
  | 1 => 0
  | 2 => 0
  | 3 => 0
  | m + 4 => ((m + 2 : Nat) : Int) * wSeq (m + 3) + factZ (m + 1)

theorem wSeq_pos : ∀ n : Nat, 4 ≤ n → 1 ≤ wSeq n := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 4 := ⟨n - 4, by omega⟩
  induction m with
  | zero => simp [wSeq, factZ]
  | succ m' ihm =>
    have hprev : 0 ≤ wSeq (m' + 4) := by
      have := ihm (by omega); omega
    change 1 ≤ ((m' + 1 + 2 : Nat) : Int) * wSeq (m' + 1 + 3) + factZ (m' + 1 + 1)
    have heq4 : m' + 1 + 3 = m' + 4 := by omega
    rw [heq4]
    have h1 : 0 ≤ ((m' + 1 + 2 : Nat) : Int) * wSeq (m' + 4) := Int.mul_nonneg (by omega) hprev
    have h2 : 1 ≤ factZ (m' + 1 + 1) := factZ_pos _
    omega

/-- Exact identity `(S⁻¹ N)_{n, 2} = (-1)^(n - 1) * wSeq n` for all `n ≥ 3`. -/
theorem T_frToCl_col_two_exact :
    ∀ n : Nat, 3 ≤ n → T_frToCl n 2 = powZ (-1) (n - 1) * wSeq n := by
  -- Helper 1: row sum `∑_{r=1}^n stirling1Raw n r = 0` for `n ≥ 2`
  have hz : ∀ n : Nat, 2 ≤ n → sumRange n (fun idx => stirling1Raw n (idx + 1)) = 0 := by
    intro n hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
    induction m with
    | zero => simp [sumRange, stirling1Raw]
    | succ m' ihm =>
      -- Expand `stirling1Raw (m' + 3) (idx + 1) = stirling1Raw (m' + 2) idx - (m' + 2) * stirling1Raw (m' + 2) (idx + 1)`
      have hexp :
          sumRange (m' + 3) (fun idx => stirling1Raw (m' + 3) (idx + 1)) =
          sumRange (m' + 3) (fun idx => stirling1Raw (m' + 2) idx) -
            ((m' + 2 : Nat) : Int) * sumRange (m' + 3) (fun idx => stirling1Raw (m' + 2) (idx + 1)) := by
        rw [← sumRange_mul_left, ← sumRange_sub]
        apply sumRange_congr
        intro idx _; rfl
      have hs1 : sumRange (m' + 3) (fun idx => stirling1Raw (m' + 2) idx) =
          sumRange (m' + 2) (fun idx => stirling1Raw (m' + 2) (idx + 1)) := by
        have hp : ∀ a (g : Nat → Int), sumRange (a + 1) g = g 0 + sumRange a (fun i => g (i + 1)) := by
          intro a g
          induction a with
          | zero => simp [sumRange]
          | succ a' iha => rw [sumRange_succ, iha, sumRange_succ]; omega
        rw [hp (m' + 2)]
        simp [stirling1Raw]
      have hs2 : sumRange (m' + 3) (fun idx => stirling1Raw (m' + 2) (idx + 1)) =
          sumRange (m' + 2) (fun idx => stirling1Raw (m' + 2) (idx + 1)) := by
        rw [sumRange_succ, stirling1Raw_gt (m' + 2) (m' + 3) (by omega)]
        omega
      rw [hexp, hs1, hs2, ihm (by omega)]
      omega
  -- Helper 2: first moment `∑_{r=1}^n stirling1Raw n r * r = (-1)^(n - 2) * (n - 2)!` for `n ≥ 2`
  have hv : ∀ n : Nat, 2 ≤ n →
      sumRange n (fun idx => stirling1Raw n (idx + 1) * ((idx + 1 : Nat) : Int)) =
        powZ (-1) (n - 2) * factZ (n - 2) := by
    intro n hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
    induction m with
    | zero => simp [sumRange, stirling1Raw, powZ, factZ]
    | succ m' ihm =>
      have hexp :
          sumRange (m' + 3) (fun idx => stirling1Raw (m' + 3) (idx + 1) * ((idx + 1 : Nat) : Int)) =
          sumRange (m' + 3) (fun idx => stirling1Raw (m' + 2) idx * ((idx + 1 : Nat) : Int)) -
            ((m' + 2 : Nat) : Int) *
              sumRange (m' + 3) (fun idx => stirling1Raw (m' + 2) (idx + 1) * ((idx + 1 : Nat) : Int)) := by
        rw [← sumRange_mul_left, ← sumRange_sub]
        apply sumRange_congr
        intro idx _
        simp only [stirling1Raw, Int.sub_mul, Int.mul_assoc]
      have hs1 : sumRange (m' + 3) (fun idx => stirling1Raw (m' + 2) idx * ((idx + 1 : Nat) : Int)) =
          sumRange (m' + 2) (fun idx => stirling1Raw (m' + 2) (idx + 1) * ((idx + 1 : Nat) : Int)) +
            sumRange (m' + 2) (fun idx => stirling1Raw (m' + 2) (idx + 1)) := by
        have hp : ∀ a (g : Nat → Int), sumRange (a + 1) g = g 0 + sumRange a (fun i => g (i + 1)) := by
          intro a g
          induction a with
          | zero => simp [sumRange]
          | succ a' iha => rw [sumRange_succ, iha, sumRange_succ]; omega
        rw [hp (m' + 2), ← sumRange_add]
        simp only [stirling1Raw, Int.zero_mul, Int.zero_add]
        apply sumRange_congr
        intro idx _
        have hc : ((idx + 1 + 1 : Nat) : Int) = ((idx + 1 : Nat) : Int) + 1 := by omega
        rw [hc, Int.mul_add, Int.mul_one]
      have hs2 : sumRange (m' + 3) (fun idx => stirling1Raw (m' + 2) (idx + 1) * ((idx + 1 : Nat) : Int)) =
          sumRange (m' + 2) (fun idx => stirling1Raw (m' + 2) (idx + 1) * ((idx + 1 : Nat) : Int)) := by
        rw [sumRange_succ, stirling1Raw_gt (m' + 2) (m' + 3) (by omega)]
        simp
      rw [hexp, hs1, hs2, hz (m' + 2) (by omega), ihm (by omega)]
      simp only [Nat.add_sub_cancel, Int.add_zero, powZ, factZ]
      have hlin : ∀ X : Int, X - ((m' + 2 : Nat) : Int) * X = (-1 : Int) * (((m' + 1 : Nat) : Int) * X) := by
        intro X
        have hm : ((m' + 2 : Nat) : Int) = ((m' + 1 : Nat) : Int) + 1 := by omega
        rw [hm, Int.add_mul, Int.one_mul]
        omega
      rw [hlin]
      simp only [Int.mul_assoc, Int.mul_left_comm, Int.mul_comm]
  -- Helper 3: main induction on `n = m + 3` (`m ≥ 0`) for `T_frToCl n 2`!
  have hu : ∀ m : Nat,
      sumRange (m + 3) (fun idx => stirling1Raw (m + 3) (idx + 1) * binom (idx + 1) 2) =
        powZ (-1) (m + 2) * wSeq (m + 3) := by
    intro m
    induction m with
    | zero =>
      simp [sumRange, stirling1Raw, binom, wSeq]
    | succ m' ihm =>
      have hexp :
          sumRange (m' + 4) (fun idx => stirling1Raw (m' + 4) (idx + 1) * binom (idx + 1) 2) =
          sumRange (m' + 4) (fun idx => stirling1Raw (m' + 3) idx * binom (idx + 1) 2) -
            ((m' + 3 : Nat) : Int) *
              sumRange (m' + 4) (fun idx => stirling1Raw (m' + 3) (idx + 1) * binom (idx + 1) 2) := by
        rw [← sumRange_mul_left, ← sumRange_sub]
        apply sumRange_congr
        intro idx _
        simp only [stirling1Raw, Int.sub_mul, Int.mul_assoc]
      have hs1 : sumRange (m' + 4) (fun idx => stirling1Raw (m' + 3) idx * binom (idx + 1) 2) =
          sumRange (m' + 3) (fun idx => stirling1Raw (m' + 3) (idx + 1) * ((idx + 1 : Nat) : Int)) +
            sumRange (m' + 3) (fun idx => stirling1Raw (m' + 3) (idx + 1) * binom (idx + 1) 2) := by
        have hp : ∀ a (g : Nat → Int), sumRange (a + 1) g = g 0 + sumRange a (fun i => g (i + 1)) := by
          intro a g
          induction a with
          | zero => simp [sumRange]
          | succ a' iha => rw [sumRange_succ, iha, sumRange_succ]; omega
        rw [hp (m' + 3), ← sumRange_add]
        simp only [stirling1Raw, Int.zero_mul, Int.zero_add]
        apply sumRange_congr
        intro idx _
        have hb2 : binom (idx + 1 + 1) 2 = ((idx + 1 : Nat) : Int) + binom (idx + 1) 2 := by
          rw [binom, binom_one_right]
        rw [hb2, Int.mul_add]
      have hs2 : sumRange (m' + 4) (fun idx => stirling1Raw (m' + 3) (idx + 1) * binom (idx + 1) 2) =
          sumRange (m' + 3) (fun idx => stirling1Raw (m' + 3) (idx + 1) * binom (idx + 1) 2) := by
        rw [sumRange_succ, stirling1Raw_gt (m' + 3) (m' + 4) (by omega)]
        simp
      rw [hexp, hs1, hs2, hv (m' + 3) (by omega), ihm]
      have hsub1 : m' + 3 - 2 = m' + 1 := by omega
      have heq_m4 : m' + 1 + 3 = m' + 4 := by omega
      have heq_m3 : m' + 1 + 2 = m' + 3 := by omega
      rw [hsub1, heq_m4, heq_m3]
      simp only [wSeq]
      have hp2 : powZ (-1) (m' + 2) = (-1 : Int) * powZ (-1) (m' + 1) := rfl
      have hp3 : powZ (-1) (m' + 3) = (-1 : Int) * powZ (-1) (m' + 2) := rfl
      rw [hp3, hp2, Int.mul_add]
      have hterm_f : (-1 : Int) * ((-1 : Int) * powZ (-1) (m' + 1)) * factZ (m' + 1) =
          powZ (-1) (m' + 1) * factZ (m' + 1) := by
        calc (-1 : Int) * ((-1 : Int) * powZ (-1) (m' + 1)) * factZ (m' + 1)
          _ = ((-1 : Int) * (-1 : Int)) * (powZ (-1) (m' + 1) * factZ (m' + 1)) := by
              simp only [Int.mul_assoc, Int.mul_left_comm, Int.mul_comm]
          _ = powZ (-1) (m' + 1) * factZ (m' + 1) := by simp
      have hterm_w : (-1 : Int) * ((-1 : Int) * powZ (-1) (m' + 1)) *
          (((m' + 2 : Nat) : Int) * wSeq (m' + 3)) =
          ((m' + 2 : Nat) : Int) * (powZ (-1) (m' + 1) * wSeq (m' + 3)) := by
        calc (-1 : Int) * ((-1 : Int) * powZ (-1) (m' + 1)) *
              (((m' + 2 : Nat) : Int) * wSeq (m' + 3))
          _ = ((-1 : Int) * (-1 : Int)) * (((m' + 2 : Nat) : Int) * (powZ (-1) (m' + 1) * wSeq (m' + 3))) := by
              simp only [Int.mul_assoc, Int.mul_left_comm, Int.mul_comm]
          _ = ((m' + 2 : Nat) : Int) * (powZ (-1) (m' + 1) * wSeq (m' + 3)) := by simp
      have hlhs_w : ((-1 : Int) * powZ (-1) (m' + 1)) * wSeq (m' + 3) -
          ((m' + 3 : Nat) : Int) * (((-1 : Int) * powZ (-1) (m' + 1)) * wSeq (m' + 3)) =
          ((m' + 2 : Nat) : Int) * (powZ (-1) (m' + 1) * wSeq (m' + 3)) := by
        have hm3 : ((m' + 3 : Nat) : Int) = ((m' + 2 : Nat) : Int) + 1 := by omega
        rw [hm3, Int.add_mul, Int.one_mul]
        have hneg : ((-1 : Int) * powZ (-1) (m' + 1)) * wSeq (m' + 3) =
            -(powZ (-1) (m' + 1) * wSeq (m' + 3)) := by
          simp [Int.neg_mul]
        rw [hneg, Int.mul_neg]
        omega
      rw [hterm_f, hterm_w]
      omega
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
  unfold T_frToCl matMul
  have hbad : ¬ (m + 3 = 0 ∨ (2 : Nat) = 0 ∨ m + 3 < 2) := by omega
  simp only [hbad, ite_false]
  have hcong :
      sumRange (m + 3) (fun idx => matInv stirling2 (m + 3) (idx + 1) * narayana (idx + 1) 2) =
      sumRange (m + 3) (fun idx => stirling1Raw (m + 3) (idx + 1) * binom (idx + 1) 2) := by
    apply sumRange_congr
    intro idx _
    rw [matInv_stirling2_eq_stirling1, narayana_col_two (idx + 1) (by omega)]
    simp [stirling1]
  rw [hcong, hu m]
  have hsub : m + 3 - 1 = m + 2 := by omega
  rw [hsub]

theorem T_frToCl_col_two_ne_zero {n : Nat} (hn : 4 ≤ n) :
    T_frToCl n 2 ≠ 0 := by
  rw [T_frToCl_col_two_exact n (by omega)]
  intro hz
  rcases Int.mul_eq_zero.mp hz with h1 | h2
  · exact powZ_neg_one_ne_zero (n - 1) h1
  · have := wSeq_pos n hn; omega

/-- `matInv T_clToFr` (`= S⁻¹ N`) has unbounded lower bandwidth (`n - 2 → ∞`). -/
theorem not_finite_bandwidth_inv_T_clToFr :
    ¬ HasFiniteLowerBandwidth (matInv T_clToFr) := by
  intro ⟨B, hB⟩
  have hz := hB (B + 4) 2 (by omega) (by omega) (by omega)
  rw [matInv_T_clToFr] at hz
  exact T_frToCl_col_two_ne_zero (by omega) hz

/-!
### Unbounded Bandwidth of `T_clToFr = (S⁻¹ N)⁻¹ = N⁻¹ S` and `matInv narayana`
-/

theorem stirling2_col_two : ∀ n : Nat, 1 ≤ n → stirling2 n 2 = powZ 2 (n - 1) - 1 := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  induction m with
  | zero => simp [stirling2, stirling2Raw, powZ]
  | succ m' ihm =>
    have hp := ihm (by omega)
    have hs1 : ∀ u, stirling2Raw (u + 1) 1 = 1 := by
      intro u
      induction u with
      | zero => rfl
      | succ u' ihu =>
        rw [stirling2Raw, ihu]
        have hz0 : stirling2Raw (u' + 1) 0 = 0 := rfl
        rw [hz0]
        omega
    simp only [stirling2, Nat.succ_ne_zero, ite_false, Nat.add_sub_cancel] at hp ⊢
    rw [stirling2Raw, hs1 m', hp, powZ]
    omega

theorem mul_binom_succ : ∀ n k : Nat,
    ((k + 1 : Nat) : Int) * binom (n + 1) (k + 1) = ((n + 1 : Nat) : Int) * binom n k := by
  intro n
  induction n with
  | zero =>
    intro k
    cases k <;> simp [binom]
  | succ m ih =>
    intro k
    cases k with
    | zero => simp [binom, binom_one_right]; omega
    | succ k' =>
      have hb : binom (m + 1 + 1) (k' + 1 + 1) =
          binom (m + 1) (k' + 1) + binom (m + 1) (k' + 1 + 1) := rfl
      rw [hb, Int.mul_add, ih (k' + 1)]
      have hsplit : ((k' + 1 + 1 : Nat) : Int) * binom (m + 1) (k' + 1) =
          ((k' + 1 : Nat) : Int) * binom (m + 1) (k' + 1) + binom (m + 1) (k' + 1) := by
        have hc : ((k' + 1 + 1 : Nat) : Int) = ((k' + 1 : Nat) : Int) + 1 := by omega
        rw [hc, Int.add_mul, Int.one_mul]
      rw [hsplit, ih k']
      have hrhs : ((m + 1 + 1 : Nat) : Int) * binom (m + 1) (k' + 1) =
          ((m + 1 : Nat) : Int) * (binom m k' + binom m (k' + 1)) + binom (m + 1) (k' + 1) := by
        have hc : ((m + 1 + 1 : Nat) : Int) = ((m + 1 : Nat) : Int) + 1 := by omega
        rw [hc, Int.add_mul, Int.one_mul]
        rfl
      rw [hrhs, Int.mul_add]
      omega

theorem mul_narayana_eq (n k : Nat) :
    ((k + 2 : Nat) : Int) * narayana (n + 1) (k + 2) =
      binom n (k + 1) * binom (n + 1) (k + 1) := by
  simp only [narayana, Int.mul_sub]
  have h1 : ((k + 2 : Nat) : Int) * (binom (n + 1) (k + 2) * binom n k) =
      (((k + 2 : Nat) : Int) * binom (n + 1) (k + 2)) * binom n k := by
    rw [Int.mul_assoc]
  have h2 := mul_binom_succ n (k + 1)
  have h3 := mul_binom_succ n k
  have h4 : (((n + 1 : Nat) : Int) * binom n (k + 1)) * binom n k =
      binom n (k + 1) * (((n + 1 : Nat) : Int) * binom n k) := by
    simp only [Int.mul_assoc, Int.mul_left_comm, Int.mul_comm]
  rw [h1, h2, h4, ← h3]
  have hsub : ((k + 2 : Nat) : Int) * (binom n (k + 1) * binom (n + 1) (k + 1)) -
      binom n (k + 1) * (((k + 1 : Nat) : Int) * binom (n + 1) (k + 1)) =
      binom n (k + 1) * binom (n + 1) (k + 1) := by
    have hc : ((k + 2 : Nat) : Int) = ((k + 1 : Nat) : Int) + 1 := by omega
    rw [hc, Int.add_mul, Int.one_mul]
    have hassoc : ((k + 1 : Nat) : Int) * (binom n (k + 1) * binom (n + 1) (k + 1)) =
        binom n (k + 1) * (((k + 1 : Nat) : Int) * binom (n + 1) (k + 1)) := by
      simp only [Int.mul_assoc, Int.mul_left_comm, Int.mul_comm]
    rw [hassoc]
    omega
  exact hsub

theorem binom_le_powZ (a b : Nat) : binom a b ≤ powZ (a : Int) b := by
  by_cases hab : b ≤ a
  · have hbf := binom_mul_factZ a b hab
    have hff := fallZ_mul_factZ a b hab
    have hpos_r : 0 < factZ (a - b) := by have := factZ_pos (a - b); omega
    have heq : binom a b * factZ b = fallZ a b := by
      apply Int.eq_of_mul_eq_mul_right (by omega : factZ (a - b) ≠ 0)
      rw [hbf, hff]
    have hfb : 1 ≤ factZ b := factZ_pos b
    have hle1 : binom a b * 1 ≤ binom a b * factZ b :=
      Int.mul_le_mul_of_nonneg_left hfb (binom_nonneg a b)
    rw [Int.mul_one, heq] at hle1
    exact Int.le_trans hle1 (fallZ_upper_bound a b).2
  · rw [binom_gt (by omega)]
    exact powZ_nonneg (by omega) b

theorem narayana_bounds {n k : Nat} (hk1 : 1 ≤ k) (hkn : k ≤ n) :
    0 ≤ narayana n k ∧ narayana n k ≤ powZ (n : Int) (2 * k) := by
  match n, k with
  | 0, _ => omega
  | _ + 1, 0 => omega
  | m + 1, 1 =>
    simp only [narayana]
    exact ⟨by omega, powZ_pos (by omega) 2⟩
  | m + 1, k' + 2 =>
    have hmul := mul_narayana_eq m k'
    have hprod_nonneg : 0 ≤ binom m (k' + 1) * binom (m + 1) (k' + 1) :=
      Int.mul_nonneg (binom_nonneg _ _) (binom_nonneg _ _)
    have hnn : 0 ≤ narayana (m + 1) (k' + 2) := by
      by_cases hneg : 0 ≤ narayana (m + 1) (k' + 2)
      · exact hneg
      · have hlt : narayana (m + 1) (k' + 2) ≤ -1 := by omega
        have hmul_neg : ((k' + 2 : Nat) : Int) * narayana (m + 1) (k' + 2) ≤
            ((k' + 2 : Nat) : Int) * (-1) :=
          Int.mul_le_mul_of_nonneg_left hlt (by omega)
        rw [hmul] at hmul_neg
        omega
    refine ⟨hnn, ?_⟩
    have hle_mul : narayana (m + 1) (k' + 2) ≤ binom m (k' + 1) * binom (m + 1) (k' + 1) := by
      have h1 : 1 * narayana (m + 1) (k' + 2) ≤ ((k' + 2 : Nat) : Int) * narayana (m + 1) (k' + 2) :=
        Int.mul_le_mul_of_nonneg_right (by omega) hnn
      omega
    have hb1 : binom m (k' + 1) ≤ powZ ((m + 1 : Nat) : Int) (k' + 1) :=
      Int.le_trans (binom_le_powZ m (k' + 1)) (powZ_mono_base (by omega) (by omega) (k' + 1))
    have hb2 : binom (m + 1) (k' + 1) ≤ powZ ((m + 1 : Nat) : Int) (k' + 1) :=
      binom_le_powZ (m + 1) (k' + 1)
    have hprod_pow : binom m (k' + 1) * binom (m + 1) (k' + 1) ≤
        powZ ((m + 1 : Nat) : Int) ((k' + 1) + (k' + 1)) := by
      rw [powZ_add]
      exact Int.mul_le_mul hb1 hb2 (binom_nonneg _ _) (powZ_nonneg (by omega) _)
    have hmono : powZ ((m + 1 : Nat) : Int) ((k' + 1) + (k' + 1)) ≤
        powZ ((m + 1 : Nat) : Int) (2 * (k' + 2)) :=
      powZ_mono_exp (by omega) (by omega)
    exact Int.le_trans hle_mul (Int.le_trans hprod_pow hmono)

theorem binom_le_powZ_two : ∀ m r : Nat, binom m r ≤ powZ 2 m := by
  intro m
  induction m with
  | zero =>
    intro r
    cases r <;> simp [binom, powZ]
  | succ m' ihm =>
    intro r
    cases r with
    | zero =>
      simp only [binom]
      exact powZ_pos (by omega) (m' + 1)
    | succ r' =>
      simp only [binom, powZ]
      have h1 := ihm r'
      have h2 := ihm (r' + 1)
      omega

/-- Exponential `2^(n - 1) - 1` eventually dominates any polynomial `C * n^D`. -/
theorem exp_two_beats_poly (C : Int) (D : Nat) (hC : 0 ≤ C) :
    ∃ n : Nat, D + 4 ≤ n ∧ C * powZ (n : Int) D < powZ 2 (n - 1) - 1 := by
  -- Use `factZ (D + 1) * powZ 2 m ≥ fallZ m (D + 1) ≥ powZ (m - D) (D + 1)` with `m = n - 1 = M + D`!
  let Coef : Int := factZ (D + 1) * ((C + 1) * powZ 2 D)
  have hCoef_pos : 1 ≤ Coef := by
    have hf := factZ_pos (D + 1)
    have hp := powZ_pos (a := 2) (by omega) D
    have h1 : (1 : Int) * 1 ≤ (C + 1) * powZ 2 D :=
      Int.mul_le_mul (by omega) hp (by omega) (by omega)
    have h2 : (1 : Int) * ((1 : Int) * 1) ≤ factZ (D + 1) * ((C + 1) * powZ 2 D) :=
      Int.mul_le_mul hf h1 (by omega) (by omega)
    simpa [Coef] using h2
  let M : Nat := D + Int.toNat Coef + 4
  let n : Nat := M + D + 1
  have hn_ge : D + 4 ≤ n := by omega
  have hn_le_2M : (n : Int) ≤ 2 * (M : Int) := by omega
  -- Upper bound `(C + 1) * powZ n D * factZ (D + 1)` by `Coef * powZ M D`
  have hpow_2M : ∀ r : Nat, powZ (2 * (M : Int)) r = powZ 2 r * powZ (M : Int) r := by
    intro r
    induction r with
    | zero => simp [powZ]
    | succ r' ihr => simp only [powZ, ihr, Int.mul_assoc, Int.mul_left_comm, Int.mul_comm]
  have hnD_ub : powZ (n : Int) D ≤ powZ 2 D * powZ (M : Int) D := by
    rw [← hpow_2M D]
    exact powZ_mono_base (by omega) hn_le_2M D
  have hub_scaled : factZ (D + 1) * (C * powZ (n : Int) D + 1) ≤ Coef * powZ (M : Int) D := by
    have h1 : C * powZ (n : Int) D + 1 ≤ (C + 1) * powZ (n : Int) D := by
      rw [Int.add_mul, Int.one_mul]
      have hp1 : 1 ≤ powZ (n : Int) D := powZ_pos (by omega) D
      omega
    have h2 : (C + 1) * powZ (n : Int) D ≤ (C + 1) * (powZ 2 D * powZ (M : Int) D) :=
      Int.mul_le_mul_of_nonneg_left hnD_ub (by omega)
    have h3 := Int.mul_le_mul_of_nonneg_left (Int.le_trans h1 h2)
      (Int.le_trans (by omega) (factZ_pos (D + 1)))
    have h4 : factZ (D + 1) * ((C + 1) * (powZ 2 D * powZ (M : Int) D)) = Coef * powZ (M : Int) D := by
      unfold Coef
      simp only [Int.mul_assoc]
    omega
  -- Lower bound `factZ (D + 1) * powZ 2 (n - 1)` by `powZ M (D + 1) = M * powZ M D`!
  have hm_eq : n - 1 = M + D := by omega
  have hbin_pow := binom_le_powZ_two (M + D) (D + 1)
  have hfall_bin : fallZ (M + D) (D + 1) = binom (M + D) (D + 1) * factZ (D + 1) := by
    have hbf := binom_mul_factZ (M + D) (D + 1) (by omega)
    have hff := fallZ_mul_factZ (M + D) (D + 1) (by omega)
    have hpos_f : factZ (M + D - (D + 1)) ≠ 0 := by have := factZ_pos (M + D - (D + 1)); omega
    exact Int.eq_of_mul_eq_mul_right hpos_f (hff.trans hbf.symm)
  have hfall_lb := fallZ_lower_bound (M + D) (D + 1) (by omega)
  have hbase_M : M + D - (D + 1) + 1 = M := by omega
  rw [hbase_M] at hfall_lb
  have hlb_scaled : powZ (M : Int) (D + 1) ≤ factZ (D + 1) * powZ 2 (n - 1) := by
    rw [hm_eq]
    have hmul := Int.mul_le_mul_of_nonneg_left hbin_pow (Int.le_trans (by omega) (factZ_pos (D + 1)))
    rw [Int.mul_comm (factZ (D + 1)) (binom _ _), ← hfall_bin] at hmul
    exact Int.le_trans hfall_lb hmul
  -- Since `Coef < M`, `Coef * powZ M D < M * powZ M D = powZ M (D + 1)`!
  have hCoef_toNat : (Int.toNat Coef : Int) = Coef := Int.toNat_of_nonneg (by omega)
  have hM_gt : Coef < (M : Int) := by omega
  have hstrict : Coef * powZ (M : Int) D < powZ (M : Int) (D + 1) := by
    rw [powZ]
    exact Int.mul_lt_mul_of_pos_right hM_gt (by have := powZ_pos (a := (M : Int)) (by omega) D; omega)
  have hcomb : factZ (D + 1) * (C * powZ (n : Int) D + 1) < factZ (D + 1) * powZ 2 (n - 1) :=
    Int.lt_of_le_of_lt hub_scaled (Int.lt_of_lt_of_le hstrict hlb_scaled)
  refine ⟨n, hn_ge, ?_⟩
  -- Cancel `factZ (D + 1) > 0`
  by_cases hlt_goal : C * powZ (n : Int) D < powZ 2 (n - 1) - 1
  · exact hlt_goal
  · have hge : powZ 2 (n - 1) ≤ C * powZ (n : Int) D + 1 := by omega
    have hle := Int.mul_le_mul_of_nonneg_left hge (Int.le_trans (by omega) (factZ_pos (D + 1)))
    omega

/-- `matInv T_frToCl` (`= T_clToFr = N⁻¹ S`) ALSO has unbounded lower bandwidth! -/
theorem not_finite_bandwidth_inv_T_frToCl :
    ¬ HasFiniteLowerBandwidth (matInv T_frToCl) := by
  intro ⟨B, hB⟩
  have hB_T : ∀ k : Nat, B + 2 < k → T_clToFr k 2 = 0 := by
    intro k hk
    rw [← matInv_T_frToCl]
    exact hB k 2 (by omega) (by omega) (by omega)
  -- Use `stirling2 = matMul narayana T_clToFr`:
  have hS_eq : ∀ n : Nat, 2 ≤ n → stirling2 n 2 = matMul narayana T_clToFr n 2 := by
    intro n _
    unfold T_clToFr
    rw [← matMul_assoc_unitri isUnitriangular_narayana
      (isUnitriangular_matInv narayana) isUnitriangular_stirling2]
    have hNN : matMul narayana (matInv narayana) = matId := by
      funext u v; exact matMul_matInv isUnitriangular_narayana u v
    rw [hNN, matMul_matId_left isUnitriangular_stirling2]
  let Csum : Int := sumRange (B + 2) (fun idx => (Int.natAbs (T_clToFr (idx + 1) 2) : Int))
  have hCsum_nonneg : 0 ≤ Csum := sumRange_natAbs_nonneg (B + 2) (fun idx => T_clToFr (idx + 1) 2)
  rcases exp_two_beats_poly Csum (2 * (B + 2)) hCsum_nonneg with ⟨n, hn_ge, hbeat⟩
  have hid := hS_eq n (by omega)
  rw [stirling2_col_two n (by omega)] at hid
  unfold matMul at hid
  have hbad : ¬ (n = 0 ∨ (2 : Nat) = 0 ∨ n < 2) := by omega
  simp only [hbad, ite_false] at hid
  -- Truncate `sumRange n` down to `sumRange (B + 2)` since `T_clToFr (idx + 1) 2 = 0` for `idx ≥ B + 2`!
  have htrunc :
      sumRange n (fun idx => narayana n (idx + 1) * T_clToFr (idx + 1) 2) =
      sumRange (B + 2) (fun idx => narayana n (idx + 1) * T_clToFr (idx + 1) 2) := by
    have haux : ∀ M, B + 2 ≤ M → M ≤ n →
        sumRange M (fun idx => narayana n (idx + 1) * T_clToFr (idx + 1) 2) =
        sumRange (B + 2) (fun idx => narayana n (idx + 1) * T_clToFr (idx + 1) 2) := by
      intro M h1 h2
      induction M with
      | zero => omega
      | succ m ihm =>
        by_cases hm : B + 2 ≤ m
        · rw [sumRange_succ, ihm hm (Nat.le_of_succ_le h2), hB_T (m + 1) (by omega)]
          simp
        · have heq : m + 1 = B + 2 := by omega
          rw [heq]
    exact haux n (by omega) (Nat.le_refl n)
  rw [htrunc] at hid
  -- Bound `sumRange (B + 2) (...) ≤ Csum * powZ n (2 * (B + 2))`
  have hub :
      sumRange (B + 2) (fun idx => narayana n (idx + 1) * T_clToFr (idx + 1) 2) ≤
      Csum * powZ (n : Int) (2 * (B + 2)) := by
    unfold Csum
    rw [← sumRange_mul_right]
    apply sumRange_le
    intro idx hidx
    have hnb := narayana_bounds (n := n) (k := idx + 1) (by omega) (by omega)
    have hp_mono : powZ (n : Int) (2 * (idx + 1)) ≤ powZ (n : Int) (2 * (B + 2)) :=
      powZ_mono_exp (by omega) (by omega)
    have hnar_ub : narayana n (idx + 1) ≤ powZ (n : Int) (2 * (B + 2)) :=
      Int.le_trans hnb.2 hp_mono
    have habs : T_clToFr (idx + 1) 2 ≤ (Int.natAbs (T_clToFr (idx + 1) 2) : Int) := Int.le_natAbs
    have ha_nn : 0 ≤ (Int.natAbs (T_clToFr (idx + 1) 2) : Int) := by omega
    have h1 := Int.mul_le_mul_of_nonneg_left habs hnb.1
    have h2 := Int.mul_le_mul_of_nonneg_right hnar_ub ha_nn
    rw [Int.mul_comm (powZ _ _)] at h2
    exact Int.le_trans h1 h2
  omega

/-- `matInv narayana` itself ALSO has unbounded lower bandwidth!
    (Immediate corollary: if `matInv narayana` had finite bandwidth, then since `stirling2`
    doesn't, let's prove directly that `matInv narayana` cannot have finite bandwidth — wait:
    if `matInv narayana` had bandwidth `B`, then `(matInv narayana) k 1 = 0` for `k > B + 1`,
    giving `0 = (narayana * matInv narayana) n 1 = ∑_{k=1}^{B+1} N(n, k) (N⁻¹)_{k, 1}`,
    a nonzero polynomial in `n` of degree `2K - 2` vanishing for all `n`! Even simpler:
    we ALSO know `T_frToCl = S⁻¹ N`: if `N⁻¹` had finite bandwidth `B`, wait — let's prove
    `¬ HasFiniteLowerBandwidth (matInv narayana)` directly in 25 lines via `k * N(n, k)`!) -/
theorem not_finite_bandwidth_inv_narayana :
    ¬ HasFiniteLowerBandwidth (matInv narayana) := by
  intro ⟨B, hB⟩
  -- Find highest `K` (`1 ≤ K ≤ B + 1`) with `matInv narayana K 1 ≠ 0` (note at `K = 1` it is `1 ≠ 0`!)
  have h11 : matInv narayana 1 1 = 1 := (isUnitriangular_matInv narayana).2.2.1 1 (by omega)
  have htop : ∃ K, 1 ≤ K ∧ K ≤ B + 1 ∧ matInv narayana K 1 ≠ 0 ∧
      (∀ r, K < r → matInv narayana r 1 = 0) := by
    have haux : ∀ M, 1 ≤ M → M ≤ B + 1 →
        ∃ K, 1 ≤ K ∧ K ≤ M ∧ matInv narayana K 1 ≠ 0 ∧
          (∀ r, K < r → r ≤ M → matInv narayana r 1 = 0) := by
      intro M h1M hMB
      induction M with
      | zero => omega
      | succ m ihm =>
        by_cases hm1 : 1 ≤ m
        · by_cases htop_m : matInv narayana (m + 1) 1 ≠ 0
          · exact ⟨m + 1, by omega, Nat.le_refl _, htop_m, fun _ hr1 hr2 => by omega⟩
          · have hzm : matInv narayana (m + 1) 1 = 0 := by
              cases Decidable.em (matInv narayana (m + 1) 1 = 0) with
              | inl h => exact h
              | inr h => exact absurd h htop_m
            rcases ihm hm1 (Nat.le_of_succ_le hMB) with ⟨K, h1K, hKm, hK_nz, hK_le⟩
            refine ⟨K, h1K, Nat.le_succ_of_le hKm, hK_nz, ?_⟩
            intro r hrK hrle
            by_cases hrm : r ≤ m
            · exact hK_le r hrK hrm
            · have heq : r = m + 1 := by omega
              subst heq; exact hzm
        · have heq : m + 1 = 1 := by omega
          rw [heq]
          exact ⟨1, Nat.le_refl 1, Nat.le_refl 1, by rw [h11]; decide, fun _ hr1 hr2 => by omega⟩
    rcases haux (B + 1) (by omega) (Nat.le_refl _) with ⟨K, h1K, hKB, hKnz, hKle⟩
    refine ⟨K, h1K, hKB, hKnz, ?_⟩
    intro r hrK
    by_cases hrB : r ≤ B + 1
    · exact hKle r hrK hrB
    · exact hB r 1 (by omega) (by omega) (by omega)
  rcases htop with ⟨K, h1K, _, hKnz, hK_above⟩
  by_cases hK1 : K = 1
  · -- If `K = 1`, evaluate `(narayana * matInv narayana) 2 1 = 0`!
    subst hK1
    have hortho := matMul_matInv isUnitriangular_narayana 2 1
    unfold matMul matId at hortho
    simp only [sumRange, hK_above 2 (by omega), h11] at hortho
    have hn21 : narayana 2 1 = 1 := rfl
    rw [hn21] at hortho
    omega
  · -- `K ≥ 2`: for any `n > K`, `∑_{k=1}^K narayana n k * (matInv narayana k 1) = 0`!
    have hK2 : 2 ≤ K := by omega
    -- Multiply by `K * (K - 1)! * (K - 1)!`:
    -- Note `k * narayana n k * (k - 1)! * (k - 1)! = fallZ (n - 1) (k - 1) * fallZ n (k - 1)`!
    have hterm_nar : ∀ n k : Nat, 1 ≤ k → k ≤ n →
        (k : Int) * narayana n k * (factZ (k - 1) * factZ (k - 1)) =
          fallZ (n - 1) (k - 1) * fallZ n (k - 1) := by
      intro n k hk1 hkn
      obtain ⟨n', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
      cases k with
      | zero => omega
      | succ k' =>
        cases k' with
        | zero => simp [narayana, factZ, fallZ]
        | succ k'' =>
          have hmn := mul_narayana_eq n' k''
          have h1 : binom n' (k'' + 1) * factZ (k'' + 1) = fallZ n' (k'' + 1) := by
            have hbf := binom_mul_factZ n' (k'' + 1) (by omega)
            have hff := fallZ_mul_factZ n' (k'' + 1) (by omega)
            have hpos_f : factZ (n' - (k'' + 1)) ≠ 0 := by have := factZ_pos (n' - (k'' + 1)); omega
            exact Int.eq_of_mul_eq_mul_right hpos_f (hbf.trans hff.symm)
          have h2 : binom (n' + 1) (k'' + 1) * factZ (k'' + 1) = fallZ (n' + 1) (k'' + 1) := by
            have hbf := binom_mul_factZ (n' + 1) (k'' + 1) (by omega)
            have hff := fallZ_mul_factZ (n' + 1) (k'' + 1) (by omega)
            have hpos_f : factZ (n' + 1 - (k'' + 1)) ≠ 0 := by have := factZ_pos (n' + 1 - (k'' + 1)); omega
            exact Int.eq_of_mul_eq_mul_right hpos_f (hbf.trans hff.symm)
          simp only [Nat.add_sub_cancel]
          calc ((k'' + 2 : Nat) : Int) * narayana (n' + 1) (k'' + 2) * (factZ (k'' + 1) * factZ (k'' + 1))
            _ = (((k'' + 2 : Nat) : Int) * narayana (n' + 1) (k'' + 2)) * (factZ (k'' + 1) * factZ (k'' + 1)) := rfl
            _ = (binom n' (k'' + 1) * factZ (k'' + 1)) * (binom (n' + 1) (k'' + 1) * factZ (k'' + 1)) := by
                rw [hmn]; simp only [Int.mul_assoc, Int.mul_left_comm, Int.mul_comm]
            _ = fallZ n' (k'' + 1) * fallZ (n' + 1) (k'' + 1) := by rw [h1, h2]
    -- Scale factor `S(k) = (factZ K / k) * (fallZ (K - 1) (K - k))^2`? Even simpler:
    -- Multiply the sum by `factZ K * factZ (K - 1)`!
    -- For `1 ≤ k ≤ K`: `factZ K = fallZ K (K - k) * k * factZ (k - 1)`,
    -- and `factZ (K - 1) = fallZ (K - 1) (K - k) * factZ (k - 1)`!
    let sc (k : Nat) : Int := fallZ K (K - k) * fallZ (K - 1) (K - k)
    have hsc_id : ∀ k, 1 ≤ k → k ≤ K →
        sc k * ((k : Int) * (factZ (k - 1) * factZ (k - 1))) = factZ K * factZ (K - 1) := by
      intro k hk1 hkK
      have hf1 := fallZ_mul_factZ K (K - k) (by omega)
      have hf2 := fallZ_mul_factZ (K - 1) (K - k) (by omega)
      have hsub1 : K - (K - k) = (k - 1) + 1 := by omega
      have hsub2 : K - 1 - (K - k) = k - 1 := by omega
      rw [hsub1, factZ] at hf1
      rw [hsub2] at hf2
      have hk_eq : ((k - 1 + 1 : Nat) : Int) = (k : Int) := by omega
      rw [hk_eq] at hf1
      unfold sc
      calc (fallZ K (K - k) * fallZ (K - 1) (K - k)) * ((k : Int) * (factZ (k - 1) * factZ (k - 1)))
        _ = (fallZ K (K - k) * ((k : Int) * factZ (k - 1))) * (fallZ (K - 1) (K - k) * factZ (k - 1)) := by
            simp only [Int.mul_assoc, Int.mul_left_comm, Int.mul_comm]
        _ = factZ K * factZ (K - 1) := by rw [hf1, hf2]
    have hpoly_zero : ∀ n : Nat, K < n →
        sumRange K (fun idx =>
          matInv narayana (idx + 1) 1 * sc (idx + 1) *
            (fallZ (n - 1) idx * fallZ n idx)) = 0 := by
      intro n hnK
      have hortho := matMul_matInv isUnitriangular_narayana n 1
      unfold matMul matId at hortho
      have hbad : ¬ (n = 0 ∨ (1 : Nat) = 0 ∨ n < 1) := by omega
      have hid0 : ¬ (1 ≤ n ∧ n = 1) := by omega
      simp only [hbad, hid0, ite_false] at hortho
      have htrunc :
          sumRange n (fun idx => narayana n (idx + 1) * matInv narayana (idx + 1) 1) =
          sumRange K (fun idx => narayana n (idx + 1) * matInv narayana (idx + 1) 1) := by
        have haux : ∀ M, K ≤ M → M ≤ n →
            sumRange M (fun idx => narayana n (idx + 1) * matInv narayana (idx + 1) 1) =
            sumRange K (fun idx => narayana n (idx + 1) * matInv narayana (idx + 1) 1) := by
          intro M h1 h2
          induction M with
          | zero => omega
          | succ m ihm =>
            by_cases hm : K ≤ m
            · rw [sumRange_succ, ihm hm (Nat.le_of_succ_le h2), hK_above (m + 1) (by omega)]; simp
            · have heq : m + 1 = K := by omega
              rw [heq]
        exact haux n (Nat.le_of_lt hnK) (Nat.le_refl n)
      rw [htrunc] at hortho
      -- Multiply `hortho` by `factZ K * factZ (K - 1)`:
      have hmul0 : (factZ K * factZ (K - 1)) *
          sumRange K (fun idx => narayana n (idx + 1) * matInv narayana (idx + 1) 1) = 0 := by
        rw [hortho, Int.mul_zero]
      rw [← sumRange_mul_left] at hmul0
      rw [← hmul0]
      apply sumRange_congr
      intro idx hidx
      have hkK : idx + 1 ≤ K := Nat.succ_le_of_lt hidx
      have hkn : idx + 1 ≤ n := Nat.le_trans hkK (Nat.le_of_lt hnK)
      rw [← hsc_id (idx + 1) (by omega) hkK]
      have htn := hterm_nar n (idx + 1) (by omega) hkn
      simp only [Nat.add_sub_cancel] at hsc_id htn ⊢
      calc matInv narayana (idx + 1) 1 * sc (idx + 1) * (fallZ (n - 1) idx * fallZ n idx)
        _ = matInv narayana (idx + 1) 1 * sc (idx + 1) *
              (((idx + 1 : Nat) : Int) * narayana n (idx + 1) * (factZ idx * factZ idx)) := by
            rw [htn]
        _ = (sc (idx + 1) * (((idx + 1 : Nat) : Int) * (factZ idx * factZ idx))) *
              (narayana n (idx + 1) * matInv narayana (idx + 1) 1) := by
            simp only [Int.mul_assoc, Int.mul_left_comm, Int.mul_comm]
    -- Asymptotic contradiction at large `n`:
    -- Top term (`idx = K - 1`) has `sc K = 1`, magnitude `≥ (n - K + 1)^(2K - 2)`,
    -- while lower terms (`idx ≤ K - 2`) have magnitude `≤ C_low * n^(2K - 4)`!
    let C_low : Int := sumRange (K - 1) (fun idx =>
      (Int.natAbs (matInv narayana (idx + 1) 1 * sc (idx + 1)) : Int))
    have hC_nonneg : 0 ≤ C_low :=
      sumRange_natAbs_nonneg (K - 1) (fun idx => matInv narayana (idx + 1) 1 * sc (idx + 1))
    let Coef : Int := C_low * powZ 2 (2 * K - 4) + 1
    have hCoef_pos : 1 ≤ Coef := by
      have := Int.mul_nonneg hC_nonneg (powZ_nonneg (a := 2) (by omega) (2 * K - 4))
      omega
    let M : Nat := K + Int.toNat Coef + 2
    let n : Nat := M + K - 1
    have hnK : K < n := by omega
    have hn_le_2M : (n : Int) ≤ 2 * (M : Int) := by omega
    have hz_eq := hpoly_zero n hnK
    have hK_pred : K = (K - 1) + 1 := by omega
    conv at hz_eq => lhs; rw [hK_pred, sumRange_succ]
    have hKm1_succ : (K - 1) + 1 = K := by omega
    have hscK : sc K = 1 := by
      unfold sc
      have : K - K = 0 := by omega
      rw [this, fallZ_zero_right, fallZ_zero_right]
      rfl
    rw [hKm1_succ, hscK, Int.mul_one] at hz_eq
    have hlhs_lb : powZ (M : Int) (2 * K - 2) ≤
        (Int.natAbs (matInv narayana K 1 * (fallZ (n - 1) (K - 1) * fallZ n (K - 1))) : Int) := by
      have hf1 := fallZ_lower_bound (n - 1) (K - 1) (by omega)
      have hf2 := fallZ_lower_bound n (K - 1) (by omega)
      have hb1 : n - 1 - (K - 1) + 1 = M := by omega
      rw [hb1] at hf1
      have hb2_le : powZ (M : Int) (K - 1) ≤ powZ ((n - (K - 1) + 1 : Nat) : Int) (K - 1) :=
        powZ_mono_base (by omega) (by omega) (K - 1)
      have hprod_lb : powZ (M : Int) (2 * K - 2) ≤ fallZ (n - 1) (K - 1) * fallZ n (K - 1) := by
        have hexp : 2 * K - 2 = (K - 1) + (K - 1) := by omega
        rw [hexp, powZ_add]
        exact Int.mul_le_mul hf1 (Int.le_trans hb2_le hf2)
          (powZ_nonneg (by omega) _) (fallZ_upper_bound (n - 1) (K - 1)).1
      have hprod_nn : 0 ≤ fallZ (n - 1) (K - 1) * fallZ n (K - 1) :=
        Int.mul_nonneg (fallZ_upper_bound _ _).1 (fallZ_upper_bound _ _).1
      rw [Int.natAbs_mul, Int.ofNat_mul, Int.natAbs_of_nonneg hprod_nn]
      have hK_abs : (1 : Int) ≤ (Int.natAbs (matInv narayana K 1) : Int) := by omega
      have := Int.mul_le_mul hK_abs hprod_lb (powZ_nonneg (by omega) _) (by omega)
      simpa using this
    have hpow_2M : ∀ r : Nat, powZ (2 * (M : Int)) r = powZ 2 r * powZ (M : Int) r := by
      intro r
      induction r with
      | zero => simp [powZ]
      | succ r' ihr => simp only [powZ, ihr, Int.mul_assoc, Int.mul_left_comm, Int.mul_comm]
    have hlow_ub :
        (Int.natAbs (sumRange (K - 1) (fun idx =>
          matInv narayana (idx + 1) 1 * sc (idx + 1) * (fallZ (n - 1) idx * fallZ n idx))) : Int) ≤
        Coef * powZ (M : Int) (2 * K - 4) := by
      have hterm_ub : ∀ idx, idx < K - 1 →
          fallZ (n - 1) idx * fallZ n idx ≤ powZ 2 (2 * K - 4) * powZ (M : Int) (2 * K - 4) := by
        intro idx hidx
        have hf1 := (fallZ_upper_bound (n - 1) idx).2
        have hf2 := (fallZ_upper_bound n idx).2
        have hn1_le : powZ ((n - 1 : Nat) : Int) idx ≤ powZ (n : Int) idx :=
          powZ_mono_base (by omega) (by omega) idx
        have hp1 : fallZ (n - 1) idx * fallZ n idx ≤ powZ (n : Int) (idx + idx) := by
          rw [powZ_add]
          exact Int.mul_le_mul (Int.le_trans hf1 hn1_le) hf2
            (fallZ_upper_bound n idx).1 (powZ_nonneg (by omega) idx)
        have hp2 : powZ (n : Int) (idx + idx) ≤ powZ (n : Int) (2 * K - 4) :=
          powZ_mono_exp (by omega) (by omega)
        have hp3 : powZ (n : Int) (2 * K - 4) ≤ powZ (2 * (M : Int)) (2 * K - 4) :=
          powZ_mono_base (by omega) hn_le_2M (2 * K - 4)
        rw [hpow_2M] at hp3
        exact Int.le_trans hp1 (Int.le_trans hp2 hp3)
      have hsign : ∀ s : Int, (s = 1 ∨ s = -1) →
          s * sumRange (K - 1) (fun idx =>
            matInv narayana (idx + 1) 1 * sc (idx + 1) * (fallZ (n - 1) idx * fallZ n idx)) ≤
          C_low * (powZ 2 (2 * K - 4) * powZ (M : Int) (2 * K - 4)) := by
        intro s hs
        unfold C_low
        rw [← sumRange_mul_left, ← sumRange_mul_right]
        apply sumRange_le
        intro idx hidx
        have hf_nn : 0 ≤ fallZ (n - 1) idx * fallZ n idx :=
          Int.mul_nonneg (fallZ_upper_bound _ _).1 (fallZ_upper_bound _ _).1
        have hc_abs : s * (matInv narayana (idx + 1) 1 * sc (idx + 1)) ≤
            (Int.natAbs (matInv narayana (idx + 1) 1 * sc (idx + 1)) : Int) := by
          have h1 := Int.le_natAbs (a := matInv narayana (idx + 1) 1 * sc (idx + 1))
          have h2 := neg_le_natAbs (matInv narayana (idx + 1) 1 * sc (idx + 1))
          rcases hs with rfl | rfl <;> omega
        rw [← Int.mul_assoc s]
        have hst1 := Int.mul_le_mul_of_nonneg_right hc_abs hf_nn
        have hc_nn : 0 ≤ (Int.natAbs (matInv narayana (idx + 1) 1 * sc (idx + 1)) : Int) := by omega
        have hst2 := Int.mul_le_mul_of_nonneg_left (hterm_ub idx hidx) hc_nn
        exact Int.le_trans hst1 hst2
      have hp := hsign 1 (Or.inl rfl)
      have hn := hsign (-1) (Or.inr rfl)
      have hextra : C_low * (powZ 2 (2 * K - 4) * powZ (M : Int) (2 * K - 4)) ≤
          Coef * powZ (M : Int) (2 * K - 4) := by
        unfold Coef
        rw [Int.add_mul, Int.one_mul, Int.mul_assoc]
        have := powZ_pos (a := (M : Int)) (by omega) (2 * K - 4)
        omega
      omega
    have heq_neg : matInv narayana K 1 * (fallZ (n - 1) (K - 1) * fallZ n (K - 1)) =
        - sumRange (K - 1) (fun idx =>
            matInv narayana (idx + 1) 1 * sc (idx + 1) * (fallZ (n - 1) idx * fallZ n idx)) := by omega
    rw [heq_neg, Int.natAbs_neg] at hlhs_lb
    have hcontra := Int.le_trans hlhs_lb hlow_ub
    have hpow_split : powZ (M : Int) (2 * K - 2) =
        ((M : Int) * (M : Int)) * powZ (M : Int) (2 * K - 4) := by
      have hexp : 2 + (2 * K - 4) = 2 * K - 2 := by omega
      conv => lhs; rw [← hexp]
      rw [powZ_add]
      simp [powZ, Int.mul_assoc]
    have hCoef_toNat : (Int.toNat Coef : Int) = Coef := Int.toNat_of_nonneg (by omega)
    have hM2_gt : Coef < (M : Int) * (M : Int) := by
      have h1 : Coef < (M : Int) := by omega
      have h2 : (1 : Int) ≤ (M : Int) := by omega
      have := Int.mul_le_mul h2 (Int.le_refl (M : Int)) (by omega) (by omega)
      omega
    have hp_pos : 0 < powZ (M : Int) (2 * K - 4) := by
      have := powZ_pos (a := (M : Int)) (by omega) (2 * K - 4); omega
    have hstrict := Int.mul_lt_mul_of_pos_right hM2_gt hp_pos
    rw [← hpow_split] at hstrict
    omega

/-!
## 5. Canonical Moment-Recurrence Matrices `L_cl(m)` and `L_fr(m)` Over Moment Parameters
-/

/-- Canonical classical moment-recurrence matrix `L_cl(m)_{n, k} = binom(n - 1, k - 1) * m_{n - k}`
    (`1 ≤ k ≤ n`), satisfying `L_cl(m) * c = m`. -/
def L_cl (m : Nat → Int) : LMatrix :=
  fun n k =>
    if n = 0 ∨ k = 0 ∨ n < k then 0
    else binom (n - 1) (k - 1) * m (n - k)

/-- Canonical free moment-recurrence matrix `L_fr(m)_{n, k} = momentConv m k (n - k)`
    (`1 ≤ k ≤ n`), satisfying `L_fr(m) * κ = m`. -/
def L_fr (m : Nat → Int) : LMatrix :=
  fun n k =>
    if n = 0 ∨ k = 0 ∨ n < k then 0
    else momentConv m k (n - k)

theorem isUnitriangular_L_cl (m : Nat → Int) (hm0 : m 0 = 1) : IsUnitriangular (L_cl m) := by
  refine ⟨fun _ => by simp [L_cl], fun _ => by simp [L_cl], ?_, ?_⟩
  · intro n hn
    unfold L_cl
    have hbad : ¬ (n = 0 ∨ n = 0 ∨ n < n) := by omega
    simp only [hbad, ite_false, binom_self, Nat.sub_self, hm0, Int.one_mul]
  · intro n k _ hnk
    unfold L_cl
    have hbad : n = 0 ∨ k = 0 ∨ n < k := Or.inr (Or.inr hnk)
    simp [hbad]

theorem isUnitriangular_L_fr (m : Nat → Int) (hm0 : m 0 = 1) : IsUnitriangular (L_fr m) := by
  refine ⟨fun _ => by simp [L_fr], fun _ => by simp [L_fr], ?_, ?_⟩
  · intro n hn
    unfold L_fr
    have hbad : ¬ (n = 0 ∨ n = 0 ∨ n < n) := by omega
    simp only [hbad, ite_false, Nat.sub_self, momentConv_zero_right m hm0]
  · intro n k _ hnk
    unfold L_fr
    have hbad : n = 0 ∨ k = 0 ∨ n < k := Or.inr (Or.inr hnk)
    simp [hbad]

/-- Verification that `L_cl (clMoment c)` and `L_fr (frMoment κ)` genuinely implement the
    classical and free moment-cumulant systems `L_cl(m) c = m` and `L_fr(m) κ = m`. -/
theorem L_cl_implements_clMoment (c : Nat → Int) (n : Nat) (hn : 1 ≤ n) :
    sumRange n (fun idx => L_cl (clMoment c) n (idx + 1) * c (idx + 1)) = clMoment c n := by
  obtain ⟨n', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  rw [clMoment_succ]
  apply sumRange_congr
  intro idx hidx
  unfold L_cl
  have hbad : ¬ (n' + 1 = 0 ∨ idx + 1 = 0 ∨ n' + 1 < idx + 1) := by omega
  simp only [hbad, ite_false, Nat.add_sub_cancel, Nat.succ_sub_succ_eq_sub, Nat.sub_zero]
  simp only [Int.mul_assoc, Int.mul_left_comm, Int.mul_comm]

theorem L_fr_implements_frMoment (κ : Nat → Int) (n : Nat) (hn : 1 ≤ n) :
    sumRange n (fun idx => L_fr (frMoment κ) n (idx + 1) * κ (idx + 1)) = frMoment κ n := by
  obtain ⟨n', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  rw [frMoment_succ]
  apply sumRange_congr
  intro idx hidx
  unfold L_fr
  have hbad : ¬ (n' + 1 = 0 ∨ idx + 1 = 0 ∨ n' + 1 < idx + 1) := by omega
  simp only [hbad, ite_false, Nat.succ_sub_succ_eq_sub, Int.mul_comm]

/-- Canonical moment-recurrence conversion matrix `T_rec_clToFr m = L_fr(m)⁻¹ * L_cl(m)`
    and its exact inverse `T_rec_frToCl m = L_cl(m)⁻¹ * L_fr(m)`. -/
def T_rec_clToFr (m : Nat → Int) : LMatrix := matMul (matInv (L_fr m)) (L_cl m)
def T_rec_frToCl (m : Nat → Int) : LMatrix := matMul (matInv (L_cl m)) (L_fr m)

theorem matInv_T_rec_clToFr (m : Nat → Int) (hm0 : m 0 = 1) (n k : Nat) :
    matInv (T_rec_clToFr m) n k = T_rec_frToCl m n k := by
  unfold T_rec_clToFr T_rec_frToCl
  rw [matInv_matMul_distrib (isUnitriangular_matInv (L_fr m)) (isUnitriangular_L_cl m hm0)]
  have hFF : matInv (matInv (L_fr m)) = L_fr m := by
    funext u v
    symm
    apply matInv_unique_right (isUnitriangular_matInv (L_fr m)) (isUnitriangular_L_fr m hm0)
    intro a b
    exact matInv_matMul (isUnitriangular_L_fr m hm0) a b
  rw [hFF]

/-- Single-spike moment probe `singleMoment s`: `m 0 = 1`, `m s = 1`, else `0`. -/
def singleMoment (s : Nat) (d : Nat) : Int :=
  if d = 0 ∨ d = s then 1 else 0

theorem momentConv_singleMoment_vanish {s : Nat} (_hs : 2 ≤ s) :
    ∀ r d : Nat, 1 ≤ d → d < s → momentConv (singleMoment s) r d = 0 := by
  intro r
  induction r with
  | zero =>
    intro d hd1 _
    obtain ⟨d', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : d ≠ 0)
    rfl
  | succ r' ih =>
    intro d hd1 hds
    simp only [momentConv]
    rw [← sumRange_const_zero (d + 1)]
    apply sumRange_congr
    intro j hj
    by_cases hj0 : j = 0
    · subst hj0
      rw [Nat.sub_zero, ih d hd1 hds]
      simp
    · have hjs : j ≠ s := by omega
      simp [singleMoment, hj0, hjs]

theorem momentConv_singleMoment_two_self {s : Nat} (hs : 2 ≤ s) :
    momentConv (singleMoment s) 2 s = 2 := by
  conv => lhs; unfold momentConv
  rw [sumRange_succ]
  have hp : ∀ a (g : Nat → Int), sumRange (a + 1) g = g 0 + sumRange a (fun i => g (i + 1)) := by
    intro a g
    induction a with
    | zero => simp [sumRange]
    | succ a' iha => rw [sumRange_succ, iha, sumRange_succ]; omega
  obtain ⟨s', rfl⟩ : ∃ s', s = s' + 2 := ⟨s - 2, by omega⟩
  rw [hp (s' + 1)]
  have hmid : sumRange (s' + 1) (fun i =>
      singleMoment (s' + 2) (i + 1) * momentConv (singleMoment (s' + 2)) 1 (s' + 2 - (i + 1))) = 0 := by
    rw [← sumRange_const_zero (s' + 1)]
    apply sumRange_congr
    intro i hi
    have h1 : i + 1 ≠ 0 := by omega
    have h2 : i + 1 ≠ s' + 2 := by omega
    simp [singleMoment, h1, h2]
  rw [hmid, Int.add_zero]
  have hm0 : singleMoment (s' + 2) 0 = 1 := by simp [singleMoment]
  have hms : singleMoment (s' + 2) (s' + 2) = 1 := by simp [singleMoment]
  have hc0 : momentConv (singleMoment (s' + 2)) 1 0 = 1 :=
    momentConv_zero_right _ hm0 1
  have hcs : momentConv (singleMoment (s' + 2)) 1 (s' + 2) = 1 := by
    simp only [momentConv]
    rw [sumRange_succ]
    have hlow : sumRange (s' + 2) (fun j =>
        singleMoment (s' + 2) j * momentConv (singleMoment (s' + 2)) 0 (s' + 2 - j)) = 0 := by
      rw [← sumRange_const_zero (s' + 2)]
      apply sumRange_congr
      intro j hj
      obtain ⟨w, hw⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : s' + 2 - j ≠ 0)
      simp [hw, momentConv]
    rw [hlow]
    simp [Nat.sub_self, momentConv, hms]
  simp [Nat.sub_zero, Nat.sub_self, hm0, hms, hc0, hcs]

/-- Exact column-2 evaluation of `T_rec_clToFr` and `T_rec_frToCl` at `m = singleMoment (n - 2)`:
    for every `n ≥ 4`,
      `T_rec_clToFr (singleMoment (n - 2)) n 2 = (n - 3 : Int) ≠ 0`,
      `T_rec_frToCl (singleMoment (n - 2)) n 2 = -((n - 3 : Nat) : Int) ≠ 0`.
    Consequently, NEITHER `T_rec_clToFr` NOR its inverse `T_rec_frToCl` has uniform finite
    lower bandwidth over moment parameters! -/
theorem T_rec_col_two_singleMoment (n : Nat) (hn : 4 ≤ n) :
    let m := singleMoment (n - 2)
    T_rec_clToFr m n 2 = ((n - 3 : Nat) : Int) ∧
    T_rec_frToCl m n 2 = -((n - 3 : Nat) : Int) := by
  intro m
  have hm0 : m 0 = 1 := by simp [m, singleMoment]
  have hs2 : 2 ≤ n - 2 := by omega
  have hInv_fr_sub : ∀ r, 2 ≤ r → r < n → matInv (L_fr m) r 2 = if r = 2 then 1 else 0 := by
    intro r hr2 hrn
    by_cases heq2 : r = 2
    · subst heq2
      simp [(isUnitriangular_matInv (L_fr m)).2.2.1 2 (by omega)]
    · simp only [heq2, ite_false]
      rw [matInv_step (L_fr m) (by omega) (by omega)]
      have hz : sumRange (r - 1) (fun idx => L_fr m r (idx + 1) * matInv (L_fr m) (idx + 1) 2) = 0 := by
        rw [← sumRange_const_zero (r - 1)]
        apply sumRange_congr
        intro idx hidx
        by_cases hidx0 : idx = 0
        · subst hidx0
          rw [(isUnitriangular_matInv (L_fr m)).2.2.2 1 2 (by omega) (by omega)]
          simp
        · unfold L_fr
          have hbad : ¬ (r = 0 ∨ idx + 1 = 0 ∨ r < idx + 1) := by omega
          simp only [hbad, ite_false]
          rw [momentConv_singleMoment_vanish hs2 (idx + 1) (r - (idx + 1)) (by omega) (by omega)]
          simp
      rw [hz]; simp
  have hInv_cl_sub : ∀ r, 2 ≤ r → r < n → matInv (L_cl m) r 2 = if r = 2 then 1 else 0 := by
    intro r hr2 hrn
    by_cases heq2 : r = 2
    · subst heq2
      simp [(isUnitriangular_matInv (L_cl m)).2.2.1 2 (by omega)]
    · simp only [heq2, ite_false]
      rw [matInv_step (L_cl m) (by omega) (by omega)]
      have hz : sumRange (r - 1) (fun idx => L_cl m r (idx + 1) * matInv (L_cl m) (idx + 1) 2) = 0 := by
        rw [← sumRange_const_zero (r - 1)]
        apply sumRange_congr
        intro idx hidx
        by_cases hidx0 : idx = 0
        · subst hidx0
          rw [(isUnitriangular_matInv (L_cl m)).2.2.2 1 2 (by omega) (by omega)]
          simp
        · unfold L_cl
          have hbad : ¬ (r = 0 ∨ idx + 1 = 0 ∨ r < idx + 1) := by omega
          have hd0 : r - (idx + 1) ≠ 0 := by omega
          have hds : r - (idx + 1) ≠ n - 2 := by omega
          simp only [hbad, ite_false]
          simp [m, singleMoment, hd0, hds]
      rw [hz]; simp
  have hInv_fr_n : matInv (L_fr m) n 2 = -2 := by
    rw [matInv_step (L_fr m) (by omega) (by omega)]
    have hsum : sumRange (n - 1) (fun idx => L_fr m n (idx + 1) * matInv (L_fr m) (idx + 1) 2) = 2 := by
      rw [← sumRange_single (n - 1) 1 2 (by omega)]
      apply sumRange_congr
      intro idx hidx
      by_cases hidx1 : idx = 1
      · subst hidx1
        simp only [ite_true]
        have hi2 : matInv (L_fr m) 2 2 = 1 := (isUnitriangular_matInv (L_fr m)).2.2.1 2 (by omega)
        change L_fr m n 2 * matInv (L_fr m) 2 2 = 2
        rw [hi2, Int.mul_one]
        unfold L_fr
        have hbad : ¬ (n = 0 ∨ (2 : Nat) = 0 ∨ n < 2) := by omega
        simp only [hbad, ite_false]
        exact momentConv_singleMoment_two_self hs2
      · by_cases hidx0 : idx = 0
        · subst hidx0
          rw [(isUnitriangular_matInv (L_fr m)).2.2.2 1 2 (by omega) (by omega)]
          simp [hidx1]
        · rw [hInv_fr_sub (idx + 1) (by omega) (by omega)]
          have hne2 : idx + 1 ≠ 2 := by omega
          simp [hidx1, hne2]
    rw [hsum]
  have hInv_cl_n : matInv (L_cl m) n 2 = -((n - 1 : Nat) : Int) := by
    rw [matInv_step (L_cl m) (by omega) (by omega)]
    have hsum : sumRange (n - 1) (fun idx => L_cl m n (idx + 1) * matInv (L_cl m) (idx + 1) 2) =
        ((n - 1 : Nat) : Int) := by
      rw [← sumRange_single (n - 1) 1 ((n - 1 : Nat) : Int) (by omega)]
      apply sumRange_congr
      intro idx hidx
      by_cases hidx1 : idx = 1
      · subst hidx1
        simp only [ite_true]
        have hi2 : matInv (L_cl m) 2 2 = 1 := (isUnitriangular_matInv (L_cl m)).2.2.1 2 (by omega)
        change L_cl m n 2 * matInv (L_cl m) 2 2 = ((n - 1 : Nat) : Int)
        rw [hi2, Int.mul_one]
        unfold L_cl
        have hbad : ¬ (n = 0 ∨ (2 : Nat) = 0 ∨ n < 2) := by omega
        simp only [hbad, ite_false]
        rw [show (2 : Nat) - 1 = 1 from rfl, binom_one_right]
        simp [m, singleMoment]
      · by_cases hidx0 : idx = 0
        · subst hidx0
          rw [(isUnitriangular_matInv (L_cl m)).2.2.2 1 2 (by omega) (by omega)]
          simp [hidx1]
        · rw [hInv_cl_sub (idx + 1) (by omega) (by omega)]
          have hne2 : idx + 1 ≠ 2 := by omega
          simp [hidx1, hne2]
    rw [hsum]
  refine ⟨?_, ?_⟩
  · unfold T_rec_clToFr matMul
    have hbad : ¬ (n = 0 ∨ (2 : Nat) = 0 ∨ n < 2) := by omega
    simp only [hbad, ite_false]
    obtain ⟨n', hn'⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
    conv => lhs; rw [hn', sumRange_succ]; simp only [← hn']
    have hdiag_inv : matInv (L_fr m) n n = 1 := (isUnitriangular_matInv (L_fr m)).2.2.1 n (by omega)
    have htop_cl : L_cl m n 2 = ((n - 1 : Nat) : Int) := by
      unfold L_cl
      have hb : ¬ (n = 0 ∨ (2 : Nat) = 0 ∨ n < 2) := by omega
      simp only [hb, ite_false]
      rw [show (2 : Nat) - 1 = 1 from rfl, binom_one_right]
      simp [m, singleMoment]
    rw [hdiag_inv, htop_cl, Int.one_mul]
    have hlow : sumRange n' (fun idx => matInv (L_fr m) n (idx + 1) * L_cl m (idx + 1) 2) = -2 := by
      rw [← sumRange_single n' 1 (-2) (by omega)]
      apply sumRange_congr
      intro idx hidx
      by_cases hidx1 : idx = 1
      · subst hidx1
        rw [hInv_fr_n, (isUnitriangular_L_cl m hm0).2.2.1 2 (by omega)]
        simp
      · by_cases hidx0 : idx = 0
        · subst hidx0
          rw [(isUnitriangular_L_cl m hm0).2.2.2 1 2 (by omega) (by omega)]
          simp [hidx1]
        · unfold L_cl
          have hb : ¬ (idx + 1 = 0 ∨ (2 : Nat) = 0 ∨ idx + 1 < 2) := by omega
          have hm_z : m (idx + 1 - 2) = 0 := by simp [m, singleMoment]; omega
          simp only [hidx1, hb, ite_false, hm_z, Int.mul_zero]
    rw [hlow]
    omega
  · unfold T_rec_frToCl matMul
    have hbad : ¬ (n = 0 ∨ (2 : Nat) = 0 ∨ n < 2) := by omega
    simp only [hbad, ite_false]
    obtain ⟨n', hn'⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
    conv => lhs; rw [hn', sumRange_succ]; simp only [← hn']
    have hdiag_inv : matInv (L_cl m) n n = 1 := (isUnitriangular_matInv (L_cl m)).2.2.1 n (by omega)
    have htop_fr : L_fr m n 2 = 2 := by
      unfold L_fr
      have hb : ¬ (n = 0 ∨ (2 : Nat) = 0 ∨ n < 2) := by omega
      simp only [hb, ite_false]
      exact momentConv_singleMoment_two_self hs2
    rw [hdiag_inv, htop_fr, Int.one_mul]
    have hlow : sumRange n' (fun idx => matInv (L_cl m) n (idx + 1) * L_fr m (idx + 1) 2) =
        -((n - 1 : Nat) : Int) := by
      rw [← sumRange_single n' 1 (-((n - 1 : Nat) : Int)) (by omega)]
      apply sumRange_congr
      intro idx hidx
      by_cases hidx1 : idx = 1
      · subst hidx1
        rw [hInv_cl_n, (isUnitriangular_L_fr m hm0).2.2.1 2 (by omega)]
        simp
      · by_cases hidx0 : idx = 0
        · subst hidx0
          rw [(isUnitriangular_L_fr m hm0).2.2.2 1 2 (by omega) (by omega)]
          simp [hidx1]
        · unfold L_fr
          have hb : ¬ (idx + 1 = 0 ∨ (2 : Nat) = 0 ∨ idx + 1 < 2) := by omega
          simp only [hidx1, hb, ite_false]
          rw [momentConv_singleMoment_vanish hs2 2 (idx + 1 - 2) (by omega) (by omega)]
          simp
    rw [hlow]
    omega

/-- Uniform finite lower bandwidth of a moment-parametrized unitriangular matrix family
    `F : (Nat → Int) → LMatrix` (over normalized moment sequences `m 0 = 1`). -/
def HasUniformFiniteBandwidth (F : (Nat → Int) → LMatrix) : Prop :=
  ∃ B : Nat, ∀ m : Nat → Int, m 0 = 1 →
    ∀ n k : Nat, 1 ≤ k → k ≤ n → B < n - k → F m n k = 0

/-- Neither the canonical moment-recurrence conversion matrix `T_rec_clToFr` nor its
    inverse `T_rec_frToCl` (`= matInv ∘ T_rec_clToFr`) has uniform finite lower bandwidth! -/
theorem not_uniform_finite_bandwidth_T_rec :
    ¬ HasUniformFiniteBandwidth T_rec_clToFr ∧
    ¬ HasUniformFiniteBandwidth (fun m => matInv (T_rec_clToFr m)) := by
  refine ⟨?_, ?_⟩
  · intro ⟨B, hB⟩
    let n := B + 4
    let m := singleMoment (n - 2)
    have hm0 : m 0 = 1 := by simp [m, singleMoment]
    have hz := hB m hm0 n 2 (by omega) (by omega) (by omega)
    have hval := (T_rec_col_two_singleMoment n (by omega)).1
    change T_rec_clToFr m n 2 = ((n - 3 : Nat) : Int) at hval
    omega
  · intro ⟨B, hB⟩
    let n := B + 4
    let m := singleMoment (n - 2)
    have hm0 : m 0 = 1 := by simp [m, singleMoment]
    have hz := hB m hm0 n 2 (by omega) (by omega) (by omega)
    dsimp only at hz
    rw [matInv_T_rec_clToFr m hm0] at hz
    have hval := (T_rec_col_two_singleMoment n (by omega)).2
    change T_rec_frToCl m n 2 = -((n - 3 : Nat) : Int) at hval
    omega

end Conjecture00000004763
