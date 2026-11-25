/-
  LinearAlgebra.lean
  Core Lean 4.19.0 formalization of integer matrices, textbook Laplace determinant,
  elementary row operations (Hermite row reduction), triangular matrix determinants,
  permutation-triangularity obstructions, and power-of-two divisibility obstructions.
-/

namespace Conjecture00000000441

abbrev Mat (n : Nat) := Fin n → Fin n → Int

def signPow (k : Nat) : Int :=
  if k % 2 == 0 then 1 else -1

theorem signPow_zero : signPow 0 = 1 := rfl

theorem signPow_succ (k : Nat) : signPow (k + 1) = -signPow k := by
  unfold signPow
  by_cases hk : k % 2 = 0
  · have hk1 : (k + 1) % 2 ≠ 0 := by omega
    simp [hk, hk1]
  · have hk1 : (k + 1) % 2 = 0 := by omega
    simp [hk, hk1]

theorem signPow_add (a b : Nat) : signPow (a + b) = signPow a * signPow b := by
  induction b with
  | zero =>
    rw [Nat.add_zero, signPow_zero, Int.mul_one]
  | succ b ih =>
    rw [Nat.add_succ, signPow_succ, signPow_succ, ih, Int.mul_neg]

def finSum : (n : Nat) → (Fin n → Int) → Int
  | 0, _ => 0
  | n + 1, f =>
      f ⟨0, Nat.zero_lt_succ n⟩ + finSum n (fun i => f ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩)

theorem finSum_zero_len (f : Fin 0 → Int) : finSum 0 f = 0 := rfl

theorem finSum_succ (n : Nat) (f : Fin (n + 1) → Int) :
    finSum (n + 1) f =
      f ⟨0, Nat.zero_lt_succ n⟩ + finSum n (fun i => f ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩) :=
  rfl

theorem finSum_congr {n : Nat} {f g : Fin n → Int} (h : ∀ i, f i = g i) :
    finSum n f = finSum n g := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [finSum_succ, finSum_succ, h ⟨0, Nat.zero_lt_succ n⟩,
      ih (fun i => h ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩)]

theorem finSum_zero (n : Nat) : finSum n (fun _ => 0) = 0 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [finSum_succ, ih, Int.add_zero]

theorem finSum_add {n : Nat} (f g : Fin n → Int) :
    finSum n (fun i => f i + g i) = finSum n f + finSum n g := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [finSum_succ, finSum_succ, finSum_succ, ih]
    omega

theorem finSum_mul_left {n : Nat} (c : Int) (f : Fin n → Int) :
    finSum n (fun i => c * f i) = c * finSum n f := by
  induction n with
  | zero => simp [finSum_zero_len]
  | succ n ih =>
    rw [finSum_succ, finSum_succ, ih, Int.mul_add]

theorem finSum_comm {m n : Nat} (G : Fin m → Fin n → Int) :
    finSum m (fun i => finSum n (fun j => G i j)) =
      finSum n (fun j => finSum m (fun i => G i j)) := by
  induction m with
  | zero =>
    rw [finSum_zero_len]
    exact (finSum_zero n).symm
  | succ m ih =>
    rw [finSum_succ, ih, ← finSum_add]
    apply finSum_congr
    intro j
    rw [finSum_succ]

theorem finSum_skew {m : Nat} (G : Fin m → Fin m → Int)
    (hskew : ∀ i j, G i j + G j i = 0) :
    finSum m (fun i => finSum m (fun j => G i j)) = 0 := by
  have hcomm := finSum_comm G
  have hsum :
      finSum m (fun i => finSum m (fun j => G i j)) +
        finSum m (fun j => finSum m (fun i => G i j)) = 0 := by
    rw [← finSum_add]
    have hinner : ∀ i, finSum m (fun j => G i j) + finSum m (fun j => G j i) = 0 := by
      intro i
      rw [← finSum_add, finSum_congr (fun j => hskew i j)]
      exact finSum_zero m
    rw [finSum_congr hinner]
    exact finSum_zero m
  omega

def skipFin {n : Nat} (j : Fin (n + 1)) (k : Fin n) : Fin (n + 1) :=
  if k.val < j.val then ⟨k.val, Nat.lt_trans k.isLt (Nat.lt_succ_self n)⟩
  else ⟨k.val + 1, Nat.succ_lt_succ k.isLt⟩

theorem finSum_insertZero :
    ∀ {n : Nat} (j : Fin (n + 1)) (g : Fin (n + 1) → Int),
      g j = 0 → finSum n (fun k => g (skipFin j k)) = finSum (n + 1) g
  | 0, ⟨0, _⟩, g, hj => by
    rw [finSum_zero_len, finSum_succ, finSum_zero_len, hj, Int.add_zero]
  | n + 1, ⟨0, _⟩, g, hj => by
    rw [finSum_succ (n + 1), hj, Int.zero_add]
    apply finSum_congr
    intro k
    simp [skipFin]
  | n + 1, ⟨j + 1, hjlt⟩, g, hj => by
    rw [finSum_succ n, finSum_succ (n + 1)]
    have h0 : skipFin ⟨j + 1, hjlt⟩ ⟨0, Nat.zero_lt_succ n⟩ = ⟨0, Nat.zero_lt_succ (n + 1)⟩ := by
      simp [skipFin]
    rw [h0]
    have htail : ∀ k : Fin n,
        g (skipFin ⟨j + 1, hjlt⟩ ⟨k.val + 1, Nat.succ_lt_succ k.isLt⟩) =
          (fun i : Fin (n + 1) => g ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩)
            (skipFin ⟨j, Nat.lt_of_succ_lt_succ hjlt⟩ k) := by
      intro k
      simp only [skipFin]
      by_cases hkj : k.val < j
      · have hkj1 : k.val + 1 < j + 1 := Nat.succ_lt_succ hkj
        simp [hkj, hkj1]
      · have hkj1 : ¬(k.val + 1 < j + 1) := by omega
        simp [hkj, hkj1]
    rw [finSum_congr htail]
    rw [finSum_insertZero ⟨j, Nat.lt_of_succ_lt_succ hjlt⟩
      (fun i : Fin (n + 1) => g ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩) hj]

def subMat {n : Nat} (A : Mat (n + 1)) (r c : Fin (n + 1)) : Mat n :=
  fun i j => A (skipFin r i) (skipFin c j)

/-- Textbook recursive Laplace expansion along row 0. -/
def det : {n : Nat} → Mat n → Int
  | 0, _ => 1
  | n + 1, A =>
      finSum (n + 1) (fun j =>
        signPow j.val * A ⟨0, Nat.zero_lt_succ n⟩ j *
          det (subMat A ⟨0, Nat.zero_lt_succ n⟩ j))

theorem det_zero (A : Mat 0) : det A = 1 := rfl

theorem det_succ (n : Nat) (A : Mat (n + 1)) :
    det A =
      finSum (n + 1) (fun j =>
        signPow j.val * A ⟨0, Nat.zero_lt_succ n⟩ j *
          det (subMat A ⟨0, Nat.zero_lt_succ n⟩ j)) :=
  rfl

/-- Replace row `r` of `A` by vector `v`. -/
def setRow {n : Nat} (A : Mat n) (r : Fin n) (v : Fin n → Int) : Mat n :=
  fun i j => if i = r then v j else A i j

theorem det_setRow_linear :
    ∀ {n : Nat} (A : Mat n) (r : Fin n) (u v : Fin n → Int) (c : Int),
      det (setRow A r (fun j => u j + c * v j)) =
        det (setRow A r u) + c * det (setRow A r v)
  | 0, _, r, _, _, _ => Fin.elim0 r
  | n + 1, A, ⟨0, h0lt⟩, u, v, c => by
    have hz_eq : (⟨0, h0lt⟩ : Fin (n + 1)) = ⟨0, Nat.zero_lt_succ n⟩ := rfl
    rw [hz_eq]
    rw [det_succ, det_succ, det_succ]
    have hsub : ∀ (w : Fin (n + 1) → Int) (j : Fin (n + 1)),
        subMat (setRow A ⟨0, Nat.zero_lt_succ n⟩ w) ⟨0, Nat.zero_lt_succ n⟩ j =
          subMat A ⟨0, Nat.zero_lt_succ n⟩ j := by
      intro w j
      funext a b
      simp only [subMat, setRow, skipFin]
      have hlt : ¬(a.val < 0) := by omega
      have hne : (⟨a.val + 1, Nat.succ_lt_succ a.isLt⟩ : Fin (n + 1)) ≠
          ⟨0, Nat.zero_lt_succ n⟩ := by
        intro heq
        have : a.val + 1 = 0 := congrArg Fin.val heq
        omega
      simp [hlt, hne]
    have hterm : ∀ j : Fin (n + 1),
        signPow j.val *
            setRow A ⟨0, Nat.zero_lt_succ n⟩ (fun k => u k + c * v k) ⟨0, Nat.zero_lt_succ n⟩ j *
            det (subMat (setRow A ⟨0, Nat.zero_lt_succ n⟩ (fun k => u k + c * v k))
              ⟨0, Nat.zero_lt_succ n⟩ j) =
          signPow j.val * setRow A ⟨0, Nat.zero_lt_succ n⟩ u ⟨0, Nat.zero_lt_succ n⟩ j *
              det (subMat (setRow A ⟨0, Nat.zero_lt_succ n⟩ u) ⟨0, Nat.zero_lt_succ n⟩ j) +
            c * (signPow j.val * setRow A ⟨0, Nat.zero_lt_succ n⟩ v ⟨0, Nat.zero_lt_succ n⟩ j *
              det (subMat (setRow A ⟨0, Nat.zero_lt_succ n⟩ v) ⟨0, Nat.zero_lt_succ n⟩ j)) := by
      intro j
      rw [hsub, hsub, hsub]
      simp only [setRow, ↓reduceIte]
      have hring : ∀ (s u0 v0 c0 m : Int),
          s * (u0 + c0 * v0) * m = s * u0 * m + c0 * (s * v0 * m) := by
        intro s u0 v0 c0 m
        rw [Int.mul_add s u0 (c0 * v0), Int.add_mul]
        have h2 : s * (c0 * v0) * m = c0 * (s * v0 * m) := by
          rw [← Int.mul_assoc s c0 v0, Int.mul_comm s c0, Int.mul_assoc c0 s v0,
            Int.mul_assoc c0 (s * v0) m]
        rw [h2]
      exact hring (signPow j.val) (u j) (v j) c (det (subMat A ⟨0, Nat.zero_lt_succ n⟩ j))
    rw [finSum_congr hterm, finSum_add, finSum_mul_left]
  | n + 1, A, ⟨r + 1, hr⟩, u, v, c => by
    rw [det_succ, det_succ, det_succ]
    have h0 : ∀ (w : Fin (n + 1) → Int) (j : Fin (n + 1)),
        setRow A ⟨r + 1, hr⟩ w ⟨0, Nat.zero_lt_succ n⟩ j = A ⟨0, Nat.zero_lt_succ n⟩ j := by
      intro w j
      simp only [setRow]
      have hne : (⟨0, Nat.zero_lt_succ n⟩ : Fin (n + 1)) ≠ ⟨r + 1, hr⟩ := by
        intro heq
        have : 0 = r + 1 := congrArg Fin.val heq
        omega
      simp [hne]
    have hsub : ∀ (w : Fin (n + 1) → Int) (j : Fin (n + 1)),
        subMat (setRow A ⟨r + 1, hr⟩ w) ⟨0, Nat.zero_lt_succ n⟩ j =
          setRow (subMat A ⟨0, Nat.zero_lt_succ n⟩ j) ⟨r, Nat.lt_of_succ_lt_succ hr⟩
            (fun k => w (skipFin j k)) := by
      intro w j
      funext a b
      simp only [subMat, setRow, skipFin]
      have hlt0 : ¬(a.val < 0) := by omega
      simp only [hlt0, ↓reduceIte]
      by_cases har : a.val = r
      · have h1 : (⟨a.val + 1, Nat.succ_lt_succ a.isLt⟩ : Fin (n + 1)) = ⟨r + 1, hr⟩ := by
          apply Fin.ext; exact congrArg (· + 1) har
        have h2 : a = ⟨r, Nat.lt_of_succ_lt_succ hr⟩ := by
          apply Fin.ext; exact har
        simp [h1, h2]
      · have h1 : (⟨a.val + 1, Nat.succ_lt_succ a.isLt⟩ : Fin (n + 1)) ≠ ⟨r + 1, hr⟩ := by
          intro heq
          have hv : a.val + 1 = r + 1 := congrArg Fin.val heq
          omega
        have h2 : a ≠ ⟨r, Nat.lt_of_succ_lt_succ hr⟩ := by
          intro heq
          exact har (congrArg Fin.val heq)
        simp [h1, h2]
    have hterm : ∀ j : Fin (n + 1),
        signPow j.val * setRow A ⟨r + 1, hr⟩ (fun k => u k + c * v k) ⟨0, Nat.zero_lt_succ n⟩ j *
            det (subMat (setRow A ⟨r + 1, hr⟩ (fun k => u k + c * v k))
              ⟨0, Nat.zero_lt_succ n⟩ j) =
          signPow j.val * setRow A ⟨r + 1, hr⟩ u ⟨0, Nat.zero_lt_succ n⟩ j *
              det (subMat (setRow A ⟨r + 1, hr⟩ u) ⟨0, Nat.zero_lt_succ n⟩ j) +
            c * (signPow j.val * setRow A ⟨r + 1, hr⟩ v ⟨0, Nat.zero_lt_succ n⟩ j *
              det (subMat (setRow A ⟨r + 1, hr⟩ v) ⟨0, Nat.zero_lt_succ n⟩ j)) := by
      intro j
      rw [h0, h0, h0, hsub, hsub, hsub]
      rw [det_setRow_linear (subMat A ⟨0, Nat.zero_lt_succ n⟩ j)
        ⟨r, Nat.lt_of_succ_lt_succ hr⟩
        (fun k => u (skipFin j k)) (fun k => v (skipFin j k)) c]
      have hring : ∀ (a m1 c0 m2 : Int), a * (m1 + c0 * m2) = a * m1 + c0 * (a * m2) := by
        intro a m1 c0 m2
        rw [Int.mul_add, ← Int.mul_assoc a c0 m2, Int.mul_comm a c0, Int.mul_assoc c0 a m2]
      exact hring (signPow j.val * A ⟨0, Nat.zero_lt_succ n⟩ j) _ c _
    rw [finSum_congr hterm, finSum_add, finSum_mul_left]

/-- Double column deletion for `b < a`. -/
def del2Mat {n : Nat} (A : Mat (n + 2)) (a b : Fin (n + 2)) (hba : b.val < a.val) : Mat n :=
  subMat (subMat A ⟨0, Nat.zero_lt_succ (n + 1)⟩ a) ⟨0, Nat.zero_lt_succ n⟩
    ⟨b.val, Nat.lt_of_lt_of_le hba (Nat.le_of_lt_succ a.isLt)⟩

theorem subMat_subMat_swap {n : Nat} (A : Mat (n + 2)) (a b : Fin (n + 2))
    (hba : b.val < a.val) (ha1 : a.val - 1 < n + 1) :
    subMat (subMat A ⟨0, Nat.zero_lt_succ (n + 1)⟩ b) ⟨0, Nat.zero_lt_succ n⟩ ⟨a.val - 1, ha1⟩ =
      del2Mat A a b hba := by
  funext i m
  simp only [del2Mat, subMat, skipFin]
  have hi0 : ¬(i.val < 0) := by omega
  have hi1 : ¬(i.val + 1 < 0) := by omega
  simp only [hi0, hi1, ↓reduceIte]
  apply congrArg (A ⟨i.val + 1 + 1, Nat.succ_lt_succ (Nat.succ_lt_succ i.isLt)⟩)
  apply Fin.ext
  by_cases hmb : m.val < b.val
  · have hma : m.val < a.val - 1 := by omega
    have hma2 : m.val < a.val := by omega
    simp [hmb, hma, hma2]
  · by_cases hma : m.val < a.val - 1
    · have hm1a : m.val + 1 < a.val := by omega
      have hm1b : ¬(m.val + 1 < b.val) := by omega
      simp [hmb, hma, hm1a, hm1b]
    · have hm1a : ¬(m.val + 1 < a.val) := by omega
      have hm1b : ¬(m.val + 1 < b.val) := by omega
      simp [hmb, hma, hm1a, hm1b]

theorem det_row0_eq_row1 {n : Nat} (A : Mat (n + 2))
    (heq : ∀ j : Fin (n + 2),
      A ⟨0, Nat.zero_lt_succ (n + 1)⟩ j = A ⟨1, Nat.succ_lt_succ (Nat.zero_lt_succ n)⟩ j) :
    det A = 0 := by
  let z1 : Fin (n + 2) := ⟨0, Nat.zero_lt_succ (n + 1)⟩
  let r1 : Fin (n + 2) := ⟨1, Nat.succ_lt_succ (Nat.zero_lt_succ n)⟩
  let z0 : Fin (n + 1) := ⟨0, Nat.zero_lt_succ n⟩
  let G : Fin (n + 2) → Fin (n + 2) → Int := fun j c =>
    if hcj : c.val < j.val then
      signPow (j.val + c.val) * A z1 j * A r1 c * det (del2Mat A j c hcj)
    else if hjc : j.val < c.val then
      -(signPow (j.val + c.val) * A z1 j * A r1 c * det (del2Mat A c j hjc))
    else 0
  have hrow : ∀ j : Fin (n + 2),
      signPow j.val * A z1 j * det (subMat A z1 j) = finSum (n + 2) (G j) := by
    intro j
    rw [det_succ]
    rw [← finSum_mul_left]
    have hgj : G j j = 0 := by simp [G]
    rw [← finSum_insertZero j (G j) hgj]
    apply finSum_congr
    intro k
    have hsub0 : subMat A z1 j z0 k = A r1 (skipFin j k) := by
      simp [subMat, skipFin, z1, z0, r1]
    change signPow j.val * A z1 j *
        (signPow k.val * subMat A z1 j z0 k * det (subMat (subMat A z1 j) z0 k)) =
      G j (skipFin j k)
    rw [hsub0]
    by_cases hkj : k.val < j.val
    · have hsk : skipFin j k = ⟨k.val, Nat.lt_trans k.isLt (Nat.lt_succ_self (n + 1))⟩ := by
        simp [skipFin, hkj]
      rw [hsk]
      simp only [G, hkj, ↓reduceDIte, del2Mat]
      rw [signPow_add j.val k.val]
      have hring : ∀ (sj aj sk ak m : Int), sj * aj * (sk * ak * m) = sj * sk * aj * ak * m := by
        intro sj aj sk ak m
        have h1 : sj * aj * (sk * ak * m) = sj * (aj * (sk * (ak * m))) := by
          simp [Int.mul_assoc]
        have h2 : aj * (sk * (ak * m)) = sk * (aj * (ak * m)) := by
          rw [← Int.mul_assoc aj sk, Int.mul_comm aj sk, Int.mul_assoc]
        rw [h1, h2]
        simp [Int.mul_assoc]
      exact hring (signPow j.val) (A z1 j) (signPow k.val) _ _
    · have hsk : skipFin j k = ⟨k.val + 1, Nat.succ_lt_succ k.isLt⟩ := by
        simp [skipFin, hkj]
      rw [hsk]
      have hlt1 : ¬(k.val + 1 < j.val) := by omega
      have hlt2 : j.val < k.val + 1 := by omega
      simp only [G, hlt1, hlt2, ↓reduceDIte]
      have hswap := subMat_subMat_swap A ⟨k.val + 1, Nat.succ_lt_succ k.isLt⟩ j hlt2 k.isLt
      change signPow j.val * A z1 j *
          (signPow k.val * A r1 ⟨k.val + 1, Nat.succ_lt_succ k.isLt⟩ *
            det (subMat (subMat A z1 j) z0 k)) = _
      have hk_eq : (⟨(⟨k.val + 1, Nat.succ_lt_succ k.isLt⟩ : Fin (n + 2)).val - 1,
          k.isLt⟩ : Fin (n + 1)) = k := by
        apply Fin.ext; simp
      rw [hk_eq] at hswap
      rw [hswap]
      have hsp : signPow (j.val + (k.val + 1)) = -(signPow j.val * signPow k.val) := by
        rw [← Nat.add_assoc, signPow_succ, signPow_add]
      rw [hsp]
      have hring : ∀ (sj aj sk ak m : Int),
          sj * aj * (sk * ak * m) = -(-(sj * sk) * aj * ak * m) := by
        intro sj aj sk ak m
        have h1 : -(-(sj * sk) * aj * ak * m) = sj * sk * aj * ak * m := by
          simp [Int.neg_mul, Int.neg_neg]
        rw [h1]
        have h2 : sj * aj * (sk * ak * m) = sj * (aj * (sk * (ak * m))) := by
          simp [Int.mul_assoc]
        have h3 : aj * (sk * (ak * m)) = sk * (aj * (ak * m)) := by
          rw [← Int.mul_assoc aj sk, Int.mul_comm aj sk, Int.mul_assoc]
        rw [h2, h3]
        simp [Int.mul_assoc]
      exact hring (signPow j.val) (A z1 j) (signPow k.val) _ _
  have hskew : ∀ j c : Fin (n + 2), G j c + G c j = 0 := by
    intro j c
    by_cases hcj : c.val < j.val
    · have hjc : ¬(j.val < c.val) := by omega
      simp only [G, hcj, hjc, ↓reduceDIte]
      have hcomm_add : j.val + c.val = c.val + j.val := Nat.add_comm j.val c.val
      rw [hcomm_add]
      have hprod : signPow (c.val + j.val) * A z1 j * A r1 c =
          signPow (c.val + j.val) * A z1 c * A r1 j := by
        rw [← heq j, ← heq c, Int.mul_assoc, Int.mul_comm (A z1 j) (A z1 c), ← Int.mul_assoc]
      rw [hprod]
      omega
    · by_cases hjc : j.val < c.val
      · simp only [G, hcj, hjc, ↓reduceDIte]
        have hcomm_add : j.val + c.val = c.val + j.val := Nat.add_comm j.val c.val
        rw [hcomm_add]
        have hprod : signPow (c.val + j.val) * A z1 j * A r1 c =
            signPow (c.val + j.val) * A z1 c * A r1 j := by
          rw [← heq j, ← heq c, Int.mul_assoc, Int.mul_comm (A z1 j) (A z1 c), ← Int.mul_assoc]
        rw [hprod]
        omega
      · simp [G, hcj, hjc]
  rw [det_succ, finSum_congr hrow]
  exact finSum_skew G hskew

theorem det_adjEq :
    ∀ {n : Nat} (A : Mat n) (r : Nat) (hr : r + 1 < n),
      (∀ j : Fin n, A ⟨r, Nat.lt_of_succ_lt hr⟩ j = A ⟨r + 1, hr⟩ j) → det A = 0
  | 0, _, _, hr, _ => by omega
  | 1, _, _, hr, _ => by omega
  | n + 2, A, 0, _, heq => det_row0_eq_row1 A heq
  | n + 2, A, r + 1, hr, heq => by
    rw [det_succ]
    have hminor : ∀ j : Fin (n + 2),
        det (subMat A ⟨0, Nat.zero_lt_succ (n + 1)⟩ j) = 0 := by
      intro j
      apply det_adjEq (subMat A ⟨0, Nat.zero_lt_succ (n + 1)⟩ j) r (by omega)
      intro k
      simp only [subMat, skipFin]
      have h1 : ¬(r < 0) := by omega
      have h2 : ¬(r + 1 < 0) := by omega
      simp only [h1, h2, ↓reduceIte]
      exact heq (skipFin j k)
    have hterm : ∀ j : Fin (n + 2),
        signPow j.val * A ⟨0, Nat.zero_lt_succ (n + 1)⟩ j *
          det (subMat A ⟨0, Nat.zero_lt_succ (n + 1)⟩ j) = 0 := by
      intro j
      rw [hminor j, Int.mul_zero]
    rw [finSum_congr hterm, finSum_zero]

def swapRows {n : Nat} (A : Mat n) (r1 r2 : Fin n) : Mat n :=
  fun i j => if i = r1 then A r2 j else if i = r2 then A r1 j else A i j

theorem det_adjSwap {n : Nat} (A : Mat n) (r : Nat) (hr : r + 1 < n) :
    det (swapRows A ⟨r, Nat.lt_of_succ_lt hr⟩ ⟨r + 1, hr⟩) = -det A := by
  let r1 : Fin n := ⟨r, Nat.lt_of_succ_lt hr⟩
  let r2 : Fin n := ⟨r + 1, hr⟩
  have hne : r1 ≠ r2 := by
    intro heq; have : r = r + 1 := congrArg Fin.val heq; omega
  let u := fun j => A r1 j
  let v := fun j => A r2 j
  let B := setRow (setRow A r1 (fun j => u j + 1 * v j)) r2 (fun j => u j + 1 * v j)
  have hB0 : det B = 0 := by
    apply det_adjEq B r hr
    intro j
    simp [B, setRow, r1, r2, hne]
  have hexp1 : det B =
      det (setRow (setRow A r1 (fun j => u j + 1 * v j)) r2 u) +
        1 * det (setRow (setRow A r1 (fun j => u j + 1 * v j)) r2 v) :=
    det_setRow_linear _ r2 u v 1
  have hcomm_set : ∀ (w1 w2 : Fin n → Int),
      setRow (setRow A r1 w1) r2 w2 = setRow (setRow A r2 w2) r1 w1 := by
    intro w1 w2
    funext i j
    simp only [setRow]
    by_cases hi1 : i = r1
    · subst hi1; simp [hne]
    · by_cases hi2 : i = r2
      · subst hi2; simp [hi1]
      · simp [hi1, hi2]
  rw [hcomm_set _ u, hcomm_set _ v] at hexp1
  rw [det_setRow_linear _ r1 u v 1, det_setRow_linear _ r1 u v 1] at hexp1
  have huu : det (setRow (setRow A r2 u) r1 u) = 0 := by
    apply det_adjEq _ r hr
    intro j; simp [setRow, r1, r2, hne]
  have hvv : det (setRow (setRow A r2 v) r1 v) = 0 := by
    apply det_adjEq _ r hr
    intro j; simp [setRow, r1, r2, hne]
  have huv : setRow (setRow A r2 v) r1 u = A := by
    funext i j; simp only [setRow, u, v]
    by_cases hi1 : i = r1
    · subst hi1; simp
    · by_cases hi2 : i = r2
      · subst hi2; simp [hi1]
      · simp [hi1, hi2]
  have hvu : setRow (setRow A r2 u) r1 v = swapRows A r1 r2 := rfl
  rw [hB0, huu, hvv, huv, hvu] at hexp1
  dsimp only [r1, r2] at hexp1
  omega

theorem det_eqRows_lt :
    ∀ (d : Nat) {n : Nat} (A : Mat n) (r1 r2 : Fin n),
      r1.val < r2.val → r2.val - r1.val = d →
      (∀ j : Fin n, A r1 j = A r2 j) → det A = 0
  | 0, _, _, r1, r2, hlt, hd, _ => by omega
  | 1, n, A, r1, r2, hlt, hd, heq => by
    have hr2lt : r2.val < n := r2.isLt
    have hr1_succ : r1.val + 1 < n := by omega
    apply det_adjEq A r1.val hr1_succ
    intro j
    have hr1_eq : (⟨r1.val, Nat.lt_of_succ_lt hr1_succ⟩ : Fin n) = r1 := Fin.ext rfl
    have hr2_eq : (⟨r1.val + 1, hr1_succ⟩ : Fin n) = r2 := by
      apply Fin.ext; dsimp; omega
    rw [hr1_eq, hr2_eq]
    exact heq j
  | d + 2, n, A, r1, r2, hlt, hd, heq => by
    have hr2lt : r2.val < n := r2.isLt
    have hr_prev_lt : r2.val - 1 + 1 < n := by omega
    let rp : Fin n := ⟨r2.val - 1, by omega⟩
    have hrp_val : rp.val = r2.val - 1 := rfl
    have hrp1 : (⟨r2.val - 1 + 1, hr_prev_lt⟩ : Fin n) = r2 := by
      apply Fin.ext; dsimp; omega
    let A' := swapRows A rp r2
    have hswap : det A' = -det A := by
      have h := det_adjSwap A (r2.val - 1) hr_prev_lt
      have hrp_eq : (⟨r2.val - 1, Nat.lt_of_succ_lt hr_prev_lt⟩ : Fin n) = rp := rfl
      rw [hrp_eq, hrp1] at h
      exact h
    have hA'0 : det A' = 0 := by
      apply det_eqRows_lt (d + 1) A' r1 rp (by omega) (by omega)
      intro j
      have hne1 : r1 ≠ rp := by
        intro h; have hv := congrArg Fin.val h; omega
      have hne2 : r1 ≠ r2 := by
        intro h; have hv := congrArg Fin.val h; omega
      simp [A', swapRows, hne1, hne2, heq j]
    omega

theorem det_eqRows {n : Nat} (A : Mat n) (r1 r2 : Fin n) (hne : r1 ≠ r2)
    (heq : ∀ j : Fin n, A r1 j = A r2 j) : det A = 0 := by
  have hval : r1.val ≠ r2.val := fun h => hne (Fin.ext h)
  by_cases hlt : r1.val < r2.val
  · exact det_eqRows_lt (r2.val - r1.val) A r1 r2 hlt rfl heq
  · have hgt : r2.val < r1.val := by omega
    exact det_eqRows_lt (r1.val - r2.val) A r2 r1 hgt rfl (fun j => (heq j).symm)

def addRowMul {n : Nat} (A : Mat n) (dst src : Fin n) (c : Int) : Mat n :=
  setRow A dst (fun j => A dst j + c * A src j)

theorem det_addRowMul {n : Nat} (A : Mat n) (dst src : Fin n) (hne : dst ≠ src) (c : Int) :
    det (addRowMul A dst src c) = det A := by
  unfold addRowMul
  rw [det_setRow_linear A dst (fun j => A dst j) (fun j => A src j) c]
  have hself : setRow A dst (fun j => A dst j) = A := by
    funext i j; simp only [setRow]
    by_cases h : i = dst
    · subst h; simp
    · simp [h]
  have hzero : det (setRow A dst (fun j => A src j)) = 0 := by
    apply det_eqRows _ dst src hne
    intro j
    simp [setRow, hne.symm]
  rw [hself, hzero]
  omega

theorem det_swapRows {n : Nat} (A : Mat n) (r1 r2 : Fin n) (hne : r1 ≠ r2) :
    det (swapRows A r1 r2) = -det A := by
  let u := fun j => A r1 j
  let v := fun j => A r2 j
  let B := setRow (setRow A r1 (fun j => u j + 1 * v j)) r2 (fun j => u j + 1 * v j)
  have hB0 : det B = 0 := by
    apply det_eqRows B r1 r2 hne
    intro j; simp [B, setRow, hne]
  have hexp1 : det B =
      det (setRow (setRow A r1 (fun j => u j + 1 * v j)) r2 u) +
        1 * det (setRow (setRow A r1 (fun j => u j + 1 * v j)) r2 v) :=
    det_setRow_linear _ r2 u v 1
  have hcomm_set : ∀ (w1 w2 : Fin n → Int),
      setRow (setRow A r1 w1) r2 w2 = setRow (setRow A r2 w2) r1 w1 := by
    intro w1 w2
    funext i j; simp only [setRow]
    by_cases hi1 : i = r1
    · subst hi1; simp [hne]
    · by_cases hi2 : i = r2
      · subst hi2; simp [hi1]
      · simp [hi1, hi2]
  rw [hcomm_set _ u, hcomm_set _ v] at hexp1
  rw [det_setRow_linear _ r1 u v 1, det_setRow_linear _ r1 u v 1] at hexp1
  have huu : det (setRow (setRow A r2 u) r1 u) = 0 := by
    apply det_eqRows _ r1 r2 hne; intro j; simp [setRow, hne]
  have hvv : det (setRow (setRow A r2 v) r1 v) = 0 := by
    apply det_eqRows _ r1 r2 hne; intro j; simp [setRow, hne]
  have huv : setRow (setRow A r2 v) r1 u = A := by
    funext i j; simp only [setRow, u, v]
    by_cases hi1 : i = r1
    · subst hi1; simp
    · by_cases hi2 : i = r2
      · subst hi2; simp [hi1]
      · simp [hi1, hi2]
  have hvu : setRow (setRow A r2 u) r1 v = swapRows A r1 r2 := rfl
  rw [hB0, huu, hvv, huv, hvu] at hexp1
  omega

/-- Diagonal product of an `n × n` matrix. -/
def diagProd : {n : Nat} → Mat n → Int
  | 0, _ => 1
  | n + 1, A =>
      A ⟨0, Nat.zero_lt_succ n⟩ ⟨0, Nat.zero_lt_succ n⟩ *
        diagProd (subMat A ⟨0, Nat.zero_lt_succ n⟩ ⟨0, Nat.zero_lt_succ n⟩)

theorem diagProd_succ (n : Nat) (A : Mat (n + 1)) :
    diagProd A =
      A ⟨0, Nat.zero_lt_succ n⟩ ⟨0, Nat.zero_lt_succ n⟩ *
        diagProd (subMat A ⟨0, Nat.zero_lt_succ n⟩ ⟨0, Nat.zero_lt_succ n⟩) :=
  rfl

theorem diag_dvd_diagProd :
    ∀ {n : Nat} (A : Mat n) (k : Fin n), A k k ∣ diagProd A
  | 0, _, k => Fin.elim0 k
  | n + 1, A, ⟨0, _⟩ => by
    rw [diagProd_succ]
    exact ⟨diagProd (subMat A ⟨0, Nat.zero_lt_succ n⟩ ⟨0, Nat.zero_lt_succ n⟩), rfl⟩
  | n + 1, A, ⟨k + 1, hk⟩ => by
    rw [diagProd_succ]
    have ih := diag_dvd_diagProd (subMat A ⟨0, Nat.zero_lt_succ n⟩ ⟨0, Nat.zero_lt_succ n⟩)
      ⟨k, Nat.lt_of_succ_lt_succ hk⟩
    have hentry : subMat A ⟨0, Nat.zero_lt_succ n⟩ ⟨0, Nat.zero_lt_succ n⟩
        ⟨k, Nat.lt_of_succ_lt_succ hk⟩ ⟨k, Nat.lt_of_succ_lt_succ hk⟩ = A ⟨k + 1, hk⟩ ⟨k + 1, hk⟩ := by
      simp only [subMat, skipFin]
      have hlt : ¬(k < 0) := by omega
      simp [hlt]
    rw [hentry] at ih
    obtain ⟨q, hq⟩ := ih
    refine ⟨A ⟨0, Nat.zero_lt_succ n⟩ ⟨0, Nat.zero_lt_succ n⟩ * q, ?_⟩
    rw [hq, ← Int.mul_assoc, Int.mul_comm (A ⟨0, Nat.zero_lt_succ n⟩ ⟨0, Nat.zero_lt_succ n⟩),
      Int.mul_assoc]

def IsUpperTri {n : Nat} (A : Mat n) : Prop :=
  ∀ i j : Fin n, j.val < i.val → A i j = 0

def IsLowerTri {n : Nat} (A : Mat n) : Prop :=
  ∀ i j : Fin n, i.val < j.val → A i j = 0

theorem det_col0_zero :
    ∀ {n : Nat} (A : Mat (n + 1)),
      (∀ i : Fin (n + 1), A i ⟨0, Nat.zero_lt_succ n⟩ = 0) → det A = 0
  | 0, A, hcol => by
    rw [det_succ, finSum_succ, finSum_zero_len, det_zero, hcol ⟨0, Nat.zero_lt_succ 0⟩]
    decide
  | n + 1, A, hcol => by
    let z : Fin (n + 2) := ⟨0, Nat.zero_lt_succ (n + 1)⟩
    rw [det_succ, finSum_succ]
    change signPow 0 * A z z * det (subMat A z z) +
      finSum (n + 1) (fun k =>
        signPow (k.val + 1) * A z ⟨k.val + 1, Nat.succ_lt_succ k.isLt⟩ *
          det (subMat A z ⟨k.val + 1, Nat.succ_lt_succ k.isLt⟩)) = 0
    rw [hcol z, Int.mul_zero, Int.zero_mul, Int.zero_add]
    have htail : ∀ k : Fin (n + 1),
        signPow (k.val + 1) * A z ⟨k.val + 1, Nat.succ_lt_succ k.isLt⟩ *
          det (subMat A z ⟨k.val + 1, Nat.succ_lt_succ k.isLt⟩) = 0 := by
      intro k
      have hm0 : det (subMat A z ⟨k.val + 1, Nat.succ_lt_succ k.isLt⟩) = 0 := by
        apply det_col0_zero
        intro i
        simp only [subMat, skipFin]
        have hlt : (0 : Nat) < k.val + 1 := Nat.zero_lt_succ k.val
        have hi0 : ¬(i.val < 0) := by omega
        simp only [hlt, hi0, ↓reduceIte]
        exact hcol ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩
      rw [hm0, Int.mul_zero]
    rw [finSum_congr htail, finSum_zero]

theorem det_upperTri : ∀ {n : Nat} (A : Mat n), IsUpperTri A → det A = diagProd A
  | 0, _, _ => rfl
  | n + 1, A, hup => by
    let z : Fin (n + 1) := ⟨0, Nat.zero_lt_succ n⟩
    rw [det_succ, finSum_succ, diagProd_succ]
    change signPow 0 * A z z * det (subMat A z z) +
      finSum n (fun k =>
        signPow (k.val + 1) * A z ⟨k.val + 1, Nat.succ_lt_succ k.isLt⟩ *
          det (subMat A z ⟨k.val + 1, Nat.succ_lt_succ k.isLt⟩)) =
      A z z * diagProd (subMat A z z)
    rw [signPow_zero, Int.one_mul]
    have hsub_up : IsUpperTri (subMat A z z) := by
      intro i j hij
      simp only [subMat, skipFin, z]
      have hi0 : ¬(i.val < 0) := by omega
      have hj0 : ¬(j.val < 0) := by omega
      simp only [hi0, hj0, ↓reduceIte]
      exact hup ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩ ⟨j.val + 1, Nat.succ_lt_succ j.isLt⟩
        (Nat.succ_lt_succ hij)
    rw [det_upperTri (subMat A z z) hsub_up]
    have htail : ∀ k : Fin n,
        signPow (k.val + 1) * A z ⟨k.val + 1, Nat.succ_lt_succ k.isLt⟩ *
          det (subMat A z ⟨k.val + 1, Nat.succ_lt_succ k.isLt⟩) = 0 := by
      intro k
      cases n with
      | zero => exact Fin.elim0 k
      | succ m =>
        have hm0 : det (subMat A z ⟨k.val + 1, Nat.succ_lt_succ k.isLt⟩) = 0 := by
          apply det_col0_zero
          intro i
          simp only [subMat, skipFin, z]
          have hlt : (0 : Nat) < k.val + 1 := Nat.zero_lt_succ k.val
          have hi0 : ¬(i.val < 0) := by omega
          simp only [hlt, hi0, ↓reduceIte]
          exact hup ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩ z (Nat.zero_lt_succ i.val)
        rw [hm0, Int.mul_zero]
    rw [finSum_congr htail, finSum_zero, Int.add_zero]

theorem det_lowerTri : ∀ {n : Nat} (A : Mat n), IsLowerTri A → det A = diagProd A
  | 0, _, _ => rfl
  | n + 1, A, hlo => by
    let z : Fin (n + 1) := ⟨0, Nat.zero_lt_succ n⟩
    rw [det_succ, finSum_succ, diagProd_succ]
    change signPow 0 * A z z * det (subMat A z z) +
      finSum n (fun k =>
        signPow (k.val + 1) * A z ⟨k.val + 1, Nat.succ_lt_succ k.isLt⟩ *
          det (subMat A z ⟨k.val + 1, Nat.succ_lt_succ k.isLt⟩)) =
      A z z * diagProd (subMat A z z)
    rw [signPow_zero, Int.one_mul]
    have hsub_lo : IsLowerTri (subMat A z z) := by
      intro i j hij
      simp only [subMat, skipFin, z]
      have hi0 : ¬(i.val < 0) := by omega
      have hj0 : ¬(j.val < 0) := by omega
      simp only [hi0, hj0, ↓reduceIte]
      exact hlo ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩ ⟨j.val + 1, Nat.succ_lt_succ j.isLt⟩
        (Nat.succ_lt_succ hij)
    rw [det_lowerTri (subMat A z z) hsub_lo]
    have htail : ∀ k : Fin n,
        signPow (k.val + 1) * A z ⟨k.val + 1, Nat.succ_lt_succ k.isLt⟩ *
          det (subMat A z ⟨k.val + 1, Nat.succ_lt_succ k.isLt⟩) = 0 := by
      intro k
      have hz0 : A z ⟨k.val + 1, Nat.succ_lt_succ k.isLt⟩ = 0 :=
        hlo z ⟨k.val + 1, Nat.succ_lt_succ k.isLt⟩ (Nat.zero_lt_succ k.val)
      rw [hz0, Int.mul_zero, Int.zero_mul]
    rw [finSum_congr htail, finSum_zero, Int.add_zero]

/-- Eager list-based matrix representation for fast kernel Hermite reduction. -/
def matOfRows (n : Nat) (rows : List (List Int)) : Mat n :=
  fun i j => (rows.getD i.val []).getD j.val 0

def toRows {n : Nat} (A : Mat n) : List (List Int) :=
  (List.range n).map (fun i =>
    if hi : i < n then
      (List.range n).map (fun j => if hj : j < n then A ⟨i, hi⟩ ⟨j, hj⟩ else 0)
    else [])

theorem getD_map_range :
    ∀ (m : Nat) (f : Nat → α) (d : α) (k : Nat),
      k < m → ((List.range m).map f).getD k d = f k := by
  intro m
  induction m with
  | zero => intro _ _ _ hk; omega
  | succ m ih =>
    intro f d k hk
    rw [List.range_succ, List.map_append, List.map_singleton]
    by_cases hkm : k < m
    · have hlen : ((List.range m).map f).length = m := by simp
      rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by omega)]
      rw [← List.getD_eq_getElem?_getD]
      exact ih f d k hkm
    · have hkeq : k = m := by omega
      subst hkeq
      have hlen : ((List.range k).map f).length = k := by simp
      rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega)]
      simp [hlen]

theorem matOfRows_toRows {n : Nat} (A : Mat n) : matOfRows n (toRows A) = A := by
  funext i j
  simp only [matOfRows, toRows]
  rw [getD_map_range n _ [] i.val i.isLt]
  simp only [i.isLt, ↓reduceDIte]
  rw [getD_map_range n _ 0 j.val j.isLt]
  simp [j.isLt]

inductive RowOp (n : Nat) where
  | swap (r1 r2 : Fin n)
  | addMul (dst src : Fin n) (c : Int)

def swapRowsList (n : Nat) (rows : List (List Int)) (r1 r2 : Fin n) : List (List Int) :=
  let row1 := rows.getD r1.val []
  let row2 := rows.getD r2.val []
  (List.range n).map (fun i =>
    if i == r1.val then row2
    else if i == r2.val then row1
    else rows.getD i [])

def addRowMulList (n : Nat) (rows : List (List Int)) (dst src : Fin n) (c : Int) :
    List (List Int) :=
  let rDst := rows.getD dst.val []
  let rSrc := rows.getD src.val []
  let newRow := (List.range n).map (fun j => rDst.getD j 0 + c * rSrc.getD j 0)
  (List.range n).map (fun i =>
    if i == dst.val then newRow else rows.getD i [])

theorem matOfRows_swapRowsList {n : Nat} (rows : List (List Int)) (r1 r2 : Fin n) :
    matOfRows n (swapRowsList n rows r1 r2) = swapRows (matOfRows n rows) r1 r2 := by
  funext i j
  simp only [matOfRows, swapRowsList, swapRows]
  rw [getD_map_range n _ [] i.val i.isLt]
  by_cases h1 : i = r1
  · subst h1; simp
  · have h1v : (i.val == r1.val) = false := by
      cases h : i.val == r1.val with
      | false => rfl
      | true => exfalso; apply h1; apply Fin.ext; exact beq_iff_eq.mp h
    by_cases h2 : i = r2
    · subst h2; simp [h1, h1v]
    · have h2v : (i.val == r2.val) = false := by
        cases h : i.val == r2.val with
        | false => rfl
        | true => exfalso; apply h2; apply Fin.ext; exact beq_iff_eq.mp h
      simp [h1, h2, h1v, h2v]

theorem matOfRows_addRowMulList {n : Nat} (rows : List (List Int)) (dst src : Fin n) (c : Int) :
    matOfRows n (addRowMulList n rows dst src c) = addRowMul (matOfRows n rows) dst src c := by
  funext i j
  simp only [matOfRows, addRowMulList, addRowMul, setRow]
  rw [getD_map_range n _ [] i.val i.isLt]
  by_cases h : i = dst
  · subst h
    simp only [beq_self_eq_true, ↓reduceIte]
    rw [getD_map_range n _ 0 j.val j.isLt]
  · have hv : (i.val == dst.val) = false := by
      cases hb : i.val == dst.val with
      | false => rfl
      | true => exfalso; apply h; apply Fin.ext; exact beq_iff_eq.mp hb
    simp [h, hv]

def applyRowOps (n : Nat) : List (List Int) → List (RowOp n) → (List (List Int) × Int)
  | rows, [] => (rows, 1)
  | rows, RowOp.swap r1 r2 :: rest =>
      if r1 == r2 then applyRowOps n rows rest
      else
        let res := applyRowOps n (swapRowsList n rows r1 r2) rest
        (res.1, -res.2)
  | rows, RowOp.addMul dst src c :: rest =>
      if dst == src then applyRowOps n rows rest
      else applyRowOps n (addRowMulList n rows dst src c) rest

theorem det_applyRowOps (n : Nat) :
    ∀ (rows : List (List Int)) (ops : List (RowOp n)),
      det (matOfRows n rows) =
        (applyRowOps n rows ops).2 * det (matOfRows n (applyRowOps n rows ops).1)
  | rows, [] => by simp [applyRowOps]
  | rows, RowOp.swap r1 r2 :: rest => by
    cases h : r1 == r2 with
    | true =>
      simp only [applyRowOps, h, ↓reduceIte]
      exact det_applyRowOps n rows rest
    | false =>
      simp only [applyRowOps, h]
      have hite : (false = true) ↔ False := by decide
      simp only [hite, ↓reduceIte]
      have hne : r1 ≠ r2 := by
        intro heq
        have ht : (r1 == r2) = true := beq_iff_eq.mpr heq
        rw [h] at ht
        contradiction
      have ih := det_applyRowOps n (swapRowsList n rows r1 r2) rest
      rw [matOfRows_swapRowsList, det_swapRows _ r1 r2 hne] at ih
      rw [Int.neg_mul]
      omega
  | rows, RowOp.addMul dst src c :: rest => by
    cases h : dst == src with
    | true =>
      simp only [applyRowOps, h, ↓reduceIte]
      exact det_applyRowOps n rows rest
    | false =>
      simp only [applyRowOps, h]
      have hite : (false = true) ↔ False := by decide
      simp only [hite, ↓reduceIte]
      have hne : dst ≠ src := by
        intro heq
        have ht : (dst == src) = true := beq_iff_eq.mpr heq
        rw [h] at ht
        contradiction
      have ih := det_applyRowOps n (addRowMulList n rows dst src c) rest
      rw [matOfRows_addRowMulList, det_addRowMul _ dst src hne c] at ih
      exact ih

theorem det_via_rowOps {n : Nat} (A : Mat n) (ops : List (RowOp n)) (d : Int)
    (hup : IsUpperTri (matOfRows n (applyRowOps n (toRows A) ops).1))
    (hval : (applyRowOps n (toRows A) ops).2 *
      diagProd (matOfRows n (applyRowOps n (toRows A) ops).1) = d) :
    det A = d := by
  rw [← matOfRows_toRows A, det_applyRowOps n (toRows A) ops, det_upperTri _ hup, hval]

def checkUpperTriBool (n : Nat) (rows : List (List Int)) : Bool :=
  (List.range n).all (fun i =>
    (List.range i).all (fun j => (rows.getD i []).getD j 0 == 0))

theorem list_all_range_iff (m : Nat) (p : Nat → Bool) :
    (List.range m).all p = true ↔ ∀ k, k < m → p k = true := by
  rw [List.all_eq_true]
  constructor
  · intro h k hk
    exact h k (List.mem_range.mpr hk)
  · intro h k hk
    exact h k (List.mem_range.mp hk)

theorem checkUpperTriBool_sound (n : Nat) (rows : List (List Int))
    (h : checkUpperTriBool n rows = true) :
    IsUpperTri (matOfRows n rows) := by
  unfold checkUpperTriBool at h
  rw [list_all_range_iff] at h
  intro i j hij
  have hi := h i.val i.isLt
  rw [list_all_range_iff] at hi
  exact beq_iff_eq.mp (hi j.val hij)

def checkLowerTriBool (n : Nat) (rows : List (List Int)) : Bool :=
  (List.range n).all (fun j =>
    (List.range j).all (fun i => (rows.getD i []).getD j 0 == 0))

theorem checkLowerTriBool_sound (n : Nat) (rows : List (List Int))
    (h : checkLowerTriBool n rows = true) :
    IsLowerTri (matOfRows n rows) := by
  unfold checkLowerTriBool at h
  rw [list_all_range_iff] at h
  intro i j hij
  have hj := h j.val j.isLt
  rw [list_all_range_iff] at hj
  exact beq_iff_eq.mp (hj i.val hij)

theorem det_matOfRows_via_ops (n : Nat) (rows : List (List Int)) (ops : List (RowOp n)) (d : Int)
    (hcheck :
      let res := applyRowOps n rows ops
      checkUpperTriBool n res.1 && (res.2 * diagProd (matOfRows n res.1) == d)) :
    det (matOfRows n rows) = d := by
  dsimp only at hcheck
  cases h1 : checkUpperTriBool n (applyRowOps n rows ops).1 with
  | false => rw [h1] at hcheck; contradiction
  | true =>
    rw [h1, Bool.true_and] at hcheck
    have hval := beq_iff_eq.mp hcheck
    rw [det_applyRowOps n rows ops, det_upperTri _ (checkUpperTriBool_sound n _ h1), hval]

theorem det_matOfRows_lowerTri (n : Nat) (rows : List (List Int)) (d : Int)
    (hcheck : checkLowerTriBool n rows && (diagProd (matOfRows n rows) == d)) :
    det (matOfRows n rows) = d := by
  cases h1 : checkLowerTriBool n rows with
  | false => rw [h1] at hcheck; contradiction
  | true =>
    rw [h1, Bool.true_and] at hcheck
    rw [det_lowerTri _ (checkLowerTriBool_sound n rows h1), beq_iff_eq.mp hcheck]

/-! ### Permutation-Triangularity and Obstruction Theorems -/

structure Perm (n : Nat) where
  toFun : Fin n → Fin n
  invFun : Fin n → Fin n
  left_inv : ∀ i, invFun (toFun i) = i
  right_inv : ∀ i, toFun (invFun i) = i

def revPerm (n : Nat) : Perm n where
  toFun := fun i => ⟨n - 1 - i.val, by omega⟩
  invFun := fun i => ⟨n - 1 - i.val, by omega⟩
  left_inv := fun i => by apply Fin.ext; dsimp; have := i.isLt; omega
  right_inv := fun i => by apply Fin.ext; dsimp; have := i.isLt; omega

def compPerm {n : Nat} (σ τ : Perm n) : Perm n where
  toFun := fun i => σ.toFun (τ.toFun i)
  invFun := fun i => τ.invFun (σ.invFun i)
  left_inv := fun i => by rw [σ.left_inv, τ.left_inv]
  right_inv := fun i => by rw [τ.right_inv, σ.right_inv]

def IsPermUpperTri {n : Nat} (A : Mat n) : Prop :=
  ∃ σ τ : Perm n, IsUpperTri (fun i j => A (σ.toFun i) (τ.toFun j))

def IsPermLowerTri {n : Nat} (A : Mat n) : Prop :=
  ∃ σ τ : Perm n, IsLowerTri (fun i j => A (σ.toFun i) (τ.toFun j))

def IsPermTriangular {n : Nat} (A : Mat n) : Prop :=
  IsPermUpperTri A ∨ IsPermLowerTri A

theorem isPermLowerTri_iff_upper {n : Nat} (A : Mat n) :
    IsPermLowerTri A ↔ IsPermUpperTri A := by
  constructor
  · rintro ⟨σ, τ, hlo⟩
    refine ⟨compPerm σ (revPerm n), compPerm τ (revPerm n), ?_⟩
    intro i j hij
    have hi := i.isLt
    have hj := j.isLt
    exact hlo ⟨n - 1 - i.val, by omega⟩ ⟨n - 1 - j.val, by omega⟩ (by dsimp; omega)
  · rintro ⟨σ, τ, hup⟩
    refine ⟨compPerm σ (revPerm n), compPerm τ (revPerm n), ?_⟩
    intro i j hij
    have hi := i.isLt
    have hj := j.isLt
    exact hup ⟨n - 1 - i.val, by omega⟩ ⟨n - 1 - j.val, by omega⟩ (by dsimp; omega)

/-- Obstruction 1: If `n ≥ 2` and every row of `A` has at least two nonzero entries,
    then `A` cannot be triangular under any row and column permutations. -/
theorem not_permTriangular_of_two_nonzeros_each_row {n : Nat} (hn : 2 ≤ n) (A : Mat n)
    (h2 : ∀ r : Fin n, ∃ c1 c2 : Fin n, c1 ≠ c2 ∧ A r c1 ≠ 0 ∧ A r c2 ≠ 0) :
    ¬IsPermTriangular A := by
  have hno_up : ¬IsPermUpperTri A := by
    rintro ⟨σ, τ, hup⟩
    let ilast : Fin n := ⟨n - 1, by omega⟩
    obtain ⟨c1, c2, hne, hc1, hc2⟩ := h2 (σ.toFun ilast)
    have hzero_off : ∀ c : Fin n, c ≠ τ.toFun ilast → A (σ.toFun ilast) c = 0 := by
      intro c hc
      let j := τ.invFun c
      have hj_ne : j ≠ ilast := by
        intro heq
        apply hc
        rw [← heq, τ.right_inv]
      have hj_lt : j.val < ilast.val := by
        have hlt := j.isLt
        have hval : j.val ≠ n - 1 := fun hv => hj_ne (Fin.ext hv)
        change j.val < n - 1
        omega
      have h : A (σ.toFun ilast) (τ.toFun j) = 0 := hup ilast j hj_lt
      rw [τ.right_inv] at h
      exact h
    by_cases h1 : c1 = τ.toFun ilast
    · have h2ne : c2 ≠ τ.toFun ilast := by rw [← h1]; exact hne.symm
      exact hc2 (hzero_off c2 h2ne)
    · exact hc1 (hzero_off c1 h1)
  rintro (hup | hlo)
  · exact hno_up hup
  · exact hno_up ((isPermLowerTri_iff_upper A).mp hlo)

/-- Obstruction 2: If `n ≥ 3`, `A r0 c0 ≠ 0`, and every row `r ≠ r0` has at least two
    distinct nonzero entries outside column `c0`, then `A` cannot be triangular under
    any row and column permutations. -/
theorem not_permTriangular_of_unique_singleton_row {n : Nat} (hn : 3 ≤ n) (A : Mat n)
    (r0 c0 : Fin n) (h00 : A r0 c0 ≠ 0)
    (hother : ∀ r : Fin n, r ≠ r0 →
      ∃ c1 c2 : Fin n, c1 ≠ c2 ∧ c1 ≠ c0 ∧ c2 ≠ c0 ∧ A r c1 ≠ 0 ∧ A r c2 ≠ 0) :
    ¬IsPermTriangular A := by
  have hno_up : ¬IsPermUpperTri A := by
    rintro ⟨σ, τ, hup⟩
    let ilast : Fin n := ⟨n - 1, by omega⟩
    have hzero_last : ∀ c : Fin n, c ≠ τ.toFun ilast → A (σ.toFun ilast) c = 0 := by
      intro c hc
      let j := τ.invFun c
      have hj_ne : j ≠ ilast := by
        intro heq; apply hc; rw [← heq, τ.right_inv]
      have hj_lt : j.val < ilast.val := by
        have hlt := j.isLt
        have hval : j.val ≠ n - 1 := fun hv => hj_ne (Fin.ext hv)
        change j.val < n - 1
        omega
      have h : A (σ.toFun ilast) (τ.toFun j) = 0 := hup ilast j hj_lt
      rw [τ.right_inv] at h
      exact h
    have hr_last : σ.toFun ilast = r0 := by
      by_cases hne : σ.toFun ilast = r0
      · exact hne
      · exfalso
        obtain ⟨c1, c2, hc12, _, _, hn1, hn2⟩ := hother (σ.toFun ilast) hne
        by_cases h1 : c1 = τ.toFun ilast
        · exact hn2 (hzero_last c2 (by rw [← h1]; exact hc12.symm))
        · exact hn1 (hzero_last c1 h1)
    have hc_last : τ.toFun ilast = c0 := by
      by_cases hne : τ.toFun ilast = c0
      · exact hne
      · exfalso
        have hz := hzero_last c0 (Ne.symm hne)
        rw [hr_last] at hz
        exact h00 hz
    let iprev : Fin n := ⟨n - 2, by omega⟩
    have hiprev_ne : iprev ≠ ilast := by
      intro heq; have : n - 2 = n - 1 := congrArg Fin.val heq; omega
    have hr_prev_ne : σ.toFun iprev ≠ r0 := by
      intro heq
      apply hiprev_ne
      have : σ.invFun (σ.toFun iprev) = σ.invFun (σ.toFun ilast) := by
        rw [heq, hr_last]
      rw [σ.left_inv, σ.left_inv] at this
      exact this
    have hzero_prev : ∀ c : Fin n, c ≠ c0 → c ≠ τ.toFun iprev → A (σ.toFun iprev) c = 0 := by
      intro c hcc0 hcp
      let j := τ.invFun c
      have hj_ne_last : j ≠ ilast := by
        intro heq; apply hcc0; rw [← hc_last, ← heq, τ.right_inv]
      have hj_ne_prev : j ≠ iprev := by
        intro heq; apply hcp; rw [← heq, τ.right_inv]
      have hj_lt : j.val < iprev.val := by
        have hlt := j.isLt
        have h1 : j.val ≠ n - 1 := fun hv => hj_ne_last (Fin.ext hv)
        have h2 : j.val ≠ n - 2 := fun hv => hj_ne_prev (Fin.ext hv)
        change j.val < n - 2
        omega
      have h : A (σ.toFun iprev) (τ.toFun j) = 0 := hup iprev j hj_lt
      rw [τ.right_inv] at h
      exact h
    obtain ⟨c1, c2, hc12, hc10, hc20, hn1, hn2⟩ := hother (σ.toFun iprev) hr_prev_ne
    by_cases h1 : c1 = τ.toFun iprev
    · exact hn2 (hzero_prev c2 hc20 (by rw [← h1]; exact hc12.symm))
    · exact hn1 (hzero_prev c1 hc10 h1)
  rintro (hup | hlo)
  · exact hno_up hup
  · exact hno_up ((isPermLowerTri_iff_upper A).mp hlo)

def hasTwoTrueBool (n : Nat) (p : Nat → Bool) : Bool :=
  (List.range n).any (fun c1 =>
    (List.range c1).any (fun c2 => p c1 && p c2))

theorem hasTwoTrueBool_sound {n : Nat} {p : Nat → Bool}
    (h : hasTwoTrueBool n p = true) :
    ∃ c1 c2 : Fin n, c1 ≠ c2 ∧ p c1.val = true ∧ p c2.val = true := by
  unfold hasTwoTrueBool at h
  obtain ⟨c1, hc1_mem, hc1_any⟩ := List.any_eq_true.mp h
  obtain ⟨c2, hc2_mem, hboth⟩ := List.any_eq_true.mp hc1_any
  have hc1_lt : c1 < n := List.mem_range.mp hc1_mem
  have hc2_lt_c1 : c2 < c1 := List.mem_range.mp hc2_mem
  have hc2_lt : c2 < n := Nat.lt_trans hc2_lt_c1 hc1_lt
  cases hp1 : p c1 with
  | false => rw [hp1] at hboth; contradiction
  | true =>
    rw [hp1, Bool.true_and] at hboth
    refine ⟨⟨c1, hc1_lt⟩, ⟨c2, hc2_lt⟩, ?_, hp1, hboth⟩
    intro heq
    have hv := congrArg Fin.val heq
    dsimp at hv
    omega

def checkTwoNonzerosEachRowBool (n : Nat) (rows : List (List Int)) : Bool :=
  (List.range n).all (fun r =>
    hasTwoTrueBool n (fun c => (rows.getD r []).getD c 0 != 0))

theorem not_permTriangular_via_two_nonzeros (n : Nat) (hn : 2 ≤ n) (rows : List (List Int))
    (hcheck : checkTwoNonzerosEachRowBool n rows = true) :
    ¬IsPermTriangular (matOfRows n rows) := by
  apply not_permTriangular_of_two_nonzeros_each_row hn
  intro r
  unfold checkTwoNonzerosEachRowBool at hcheck
  rw [list_all_range_iff] at hcheck
  obtain ⟨c1, c2, hne, hc1, hc2⟩ := hasTwoTrueBool_sound (hcheck r.val r.isLt)
  refine ⟨c1, c2, hne, ?_, ?_⟩
  · intro hz
    change (rows.getD r.val []).getD c1.val 0 = 0 at hz
    rw [hz] at hc1; contradiction
  · intro hz
    change (rows.getD r.val []).getD c2.val 0 = 0 at hz
    rw [hz] at hc2; contradiction

def checkUniqueSingletonRowBool (n : Nat) (rows : List (List Int)) (r0 c0 : Fin n) : Bool :=
  ((rows.getD r0.val []).getD c0.val 0 != 0) &&
  (List.range n).all (fun r =>
    (r == r0.val) ||
    hasTwoTrueBool n (fun c => (c != c0.val) && ((rows.getD r []).getD c 0 != 0)))

theorem not_permTriangular_via_singleton_row (n : Nat) (hn : 3 ≤ n) (rows : List (List Int))
    (r0 c0 : Fin n) (hcheck : checkUniqueSingletonRowBool n rows r0 c0 = true) :
    ¬IsPermTriangular (matOfRows n rows) := by
  unfold checkUniqueSingletonRowBool at hcheck
  cases h00b : ((rows.getD r0.val []).getD c0.val 0 != 0) with
  | false => rw [h00b] at hcheck; contradiction
  | true =>
    rw [h00b, Bool.true_and, list_all_range_iff] at hcheck
    have h00 : matOfRows n rows r0 c0 ≠ 0 := by
      intro hz
      change (rows.getD r0.val []).getD c0.val 0 = 0 at hz
      rw [hz] at h00b; contradiction
    apply not_permTriangular_of_unique_singleton_row hn (matOfRows n rows) r0 c0 h00
    intro r hrne
    have hr := hcheck r.val r.isLt
    have hrb : (r.val == r0.val) = false := by
      cases hb : r.val == r0.val with
      | false => rfl
      | true => exfalso; exact hrne (Fin.ext (beq_iff_eq.mp hb))
    rw [hrb, Bool.false_or] at hr
    obtain ⟨c1, c2, hne, hc1, hc2⟩ := hasTwoTrueBool_sound hr
    cases h1a : (c1.val != c0.val) with
    | false => rw [h1a] at hc1; contradiction
    | true =>
      rw [h1a, Bool.true_and] at hc1
      cases h2a : (c2.val != c0.val) with
      | false => rw [h2a] at hc2; contradiction
      | true =>
        rw [h2a, Bool.true_and] at hc2
        refine ⟨c1, c2, hne, ?_, ?_, ?_, ?_⟩
        · intro heq; rw [heq] at h1a; exact absurd rfl (bne_iff_ne.mp h1a)
        · intro heq; rw [heq] at h2a; exact absurd rfl (bne_iff_ne.mp h2a)
        · intro hz; change (rows.getD r.val []).getD c1.val 0 = 0 at hz; rw [hz] at hc1; contradiction
        · intro hz; change (rows.getD r.val []).getD c2.val 0 = 0 at hz; rw [hz] at hc2; contradiction

/-! ### Power-of-Two Determinant Predicates and Odd-Divisor Obstruction -/

/-- `d` is `± 2^k` for some natural exponent `k` (covers both literal `2^k` and signed `± 2^k`,
    as well as inverse transition matrices over `ℚ` having determinant `± 2^(-k)`). -/
def IsPowerOfTwoUpToSign (d : Int) : Prop :=
  ∃ k : Nat, d = (2 : Int) ^ k ∨ d = -((2 : Int) ^ k)

def IsExactPowerOfTwo (d : Int) : Prop :=
  ∃ k : Nat, d = (2 : Int) ^ k

theorem isExact_imp_upToSign {d : Int} (h : IsExactPowerOfTwo d) : IsPowerOfTwoUpToSign d := by
  obtain ⟨k, hk⟩ := h
  exact ⟨k, Or.inl hk⟩

theorem two_pow_mod_three_ne_zero : ∀ k : Nat, ((2 : Int) ^ k) % 3 ≠ 0
  | 0 => by decide
  | k + 1 => by
    have ih := two_pow_mod_three_ne_zero k
    have hpow : (2 : Int) ^ (k + 1) = (2 : Int) ^ k * 2 := Int.pow_succ 2 k
    rw [hpow]
    omega

theorem not_isPowerOfTwoUpToSign_of_dvd_three {d : Int} (h3 : (3 : Int) ∣ d) :
    ¬IsPowerOfTwoUpToSign d := by
  rintro ⟨k, hk | hk⟩
  · obtain ⟨q, hq⟩ := h3
    have hmod := two_pow_mod_three_ne_zero k
    omega
  · obtain ⟨q, hq⟩ := h3
    have hmod := two_pow_mod_three_ne_zero k
    omega

theorem two_pow_pos : ∀ k : Nat, (0 : Int) < (2 : Int) ^ k
  | 0 => by decide
  | k + 1 => by
    have ih := two_pow_pos k
    have hpow : (2 : Int) ^ (k + 1) = (2 : Int) ^ k * 2 := Int.pow_succ 2 k
    rw [hpow]
    omega

theorem not_isExactPowerOfTwo_of_neg {d : Int} (hneg : d < 0) : ¬IsExactPowerOfTwo d := by
  rintro ⟨k, hk⟩
  have hpos := two_pow_pos k
  rw [hk] at hneg
  omega

end Conjecture00000000441
