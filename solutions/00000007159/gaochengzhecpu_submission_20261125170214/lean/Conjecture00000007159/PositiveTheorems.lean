/-
  Conjecture 00000007159 — General Arbitrary-Dimension Positive Theorems
  Proves that in the commuting regime (all `m, k, n`) and the noncommuting two-matrix
  regime (`m = 2`, low degrees and log-convexity for all `k, n`), the simplex-lattice
  trace-product inequalities genuinely hold.
  Core Lean 4.19.0 (zero external dependencies)
-/
import Conjecture00000007159.SimplexSystems

namespace Conjecture00000007159

open Mat

/-! ### 1. Degree-4 Lieb-Thirring & Degree-5 Word-Grouping Commutator Identities -/

/-- For all `n × n` symmetric matrices `A, B`,
    `‖[A, B]‖_F^2 = 2 tr(A^2 B^2) - 2 tr((A B)^2)`. -/
theorem tr_sq_commutator_identity {n : Nat} (A B : Mat n)
    (hA : IsSymm A) (hB : IsSymm B) :
    frobNormSq (commutator A B) =
      2 * tr (mul (pow A 2) (pow B 2)) - 2 * tr (pow (mul A B) 2) := by
  dsimp [frobNormSq, frobInner, commutator]
  rw [transpose_sub, transpose_mul, transpose_mul, hA, hB]
  rw [sub_mul, mul_sub, mul_sub, tr_sub, tr_sub, tr_sub]
  have t1 : tr (mul (mul B A) (mul A B)) = tr (mul (pow A 2) (pow B 2)) := by
    rw [pow_two, pow_two, tr_mul_comm (mul B A) (mul A B)]
    rw [mul_assoc, ← mul_assoc B B A, ← mul_assoc A (mul B B) A]
    rw [tr_mul_comm (mul A (mul B B)) A, ← mul_assoc]
  have t2 : tr (mul (mul B A) (mul B A)) = tr (pow (mul A B) 2) := by
    rw [pow_two, mul_assoc B A (mul B A), tr_mul_comm B (mul A (mul B A))]
    simp [mul_assoc]
  have t3 : tr (mul (mul A B) (mul A B)) = tr (pow (mul A B) 2) := by
    rw [pow_two]
  have t4 : tr (mul (mul A B) (mul B A)) = tr (mul (pow A 2) (pow B 2)) := by
    rw [tr_mul_comm (mul A B) (mul B A)]
    exact t1
  rw [t1, t2, t3, t4]
  omega

/-- Universal degree-4 Lieb-Thirring inequality for all symmetric `n × n` matrices:
    `tr((A B)^2) ≤ tr(A^2 B^2)`. -/
theorem lieb_thirring_deg4_symm {n : Nat} (A B : Mat n)
    (hA : IsSymm A) (hB : IsSymm B) :
    tr (pow (mul A B) 2) ≤ tr (mul (pow A 2) (pow B 2)) := by
  have hnn : 0 ≤ frobNormSq (commutator A B) := frobNormSq_nonneg _
  have hid := tr_sq_commutator_identity A B hA hB
  omega

/-- Universal degree-5 word-grouping identity for Gram PSD `A = X^T X` and symmetric `B`:
    `‖X [A, B]‖_F^2 = tr(A^3 B^2) - tr(A^2 B A B)`, hence `tr(A^2 B A B) ≤ tr(A^3 B^2)`. -/
theorem word_grouping_deg5_gram {n : Nat} (A B : Mat n)
    (hA : IsGramPSD A) (hB : IsSymm B) :
    tr (mul (mul (pow A 2) B) (mul A B)) ≤ tr (mul (pow A 3) (pow B 2)) := by
  have hAsymm : IsSymm A := isGramPSD_isSymm hA
  rcases hA with ⟨X, hX⟩
  let C := commutator A B
  have hnn : 0 ≤ frobNormSq (mul X C) := frobNormSq_nonneg _
  have hexp : frobNormSq (mul X C) =
      tr (mul (pow A 3) (pow B 2)) - tr (mul (mul (pow A 2) B) (mul A B)) := by
    dsimp [frobNormSq, frobInner]
    rw [transpose_mul, mul_assoc (transpose C) (transpose X) (mul X C)]
    rw [← mul_assoc (transpose X) X C, ← hX]
    dsimp [C, commutator]
    rw [transpose_sub, transpose_mul, transpose_mul, hAsymm, hB]
    rw [mul_sub A (mul A B) (mul B A)]
    rw [sub_mul, mul_sub, mul_sub, tr_sub, tr_sub, tr_sub]
    have p3 : pow A 3 = mul (mul A A) A := by simp [pow, one_mul]
    have s1 : tr (mul (mul B A) (mul A (mul A B))) = tr (mul (pow A 3) (pow B 2)) := by
      rw [p3, pow_two, tr_mul_comm (mul B A) (mul A (mul A B))]
      rw [← mul_assoc (mul A (mul A B)) B A]
      rw [mul_assoc A (mul A B) B, mul_assoc A B B]
      rw [← mul_assoc A A (mul B B)]
      rw [tr_mul_comm (mul (mul A A) (mul B B)) A]
      rw [← mul_assoc A (mul A A) (mul B B)]
      have ha3 : mul A (mul A A) = mul (mul A A) A := (mul_assoc A A A).symm
      rw [ha3]
    have s2 : tr (mul (mul B A) (mul A (mul B A))) = tr (mul (mul (pow A 2) B) (mul A B)) := by
      rw [pow_two, mul_assoc B A (mul A (mul B A)), tr_mul_comm B (mul A (mul A (mul B A)))]
      simp [mul_assoc]
    have s3 : tr (mul (mul A B) (mul A (mul A B))) = tr (mul (mul (pow A 2) B) (mul A B)) := by
      rw [pow_two, tr_mul_comm (mul A B) (mul A (mul A B))]
      simp [mul_assoc]
    have s4 : tr (mul (mul A B) (mul A (mul B A))) = tr (mul (mul (pow A 2) B) (mul A B)) := by
      rw [pow_two, ← mul_assoc (mul A B) A (mul B A), ← mul_assoc (mul (mul A B) A) B A]
      rw [tr_mul_comm (mul (mul (mul A B) A) B) A]
      simp [mul_assoc]
    rw [s1, s2, s3, s4]
    omega
  omega

/-! ### 2. Universal Two-Matrix Positivity, Submultiplicativity at `k = 2`, and Cauchy-Schwarz -/

/-- For all Gram PSD `A, B`, `0 ≤ tr(A B) ≤ tr(A) tr(B)`. -/
theorem two_matrix_submult_deg2 {n : Nat} (A B : Mat n)
    (hA : IsGramPSD A) (hB : IsGramPSD B) :
    0 ≤ tr (mul A B) ∧ tr (mul A B) ≤ tr A * tr B := by
  rcases hA with ⟨X, rfl⟩
  rcases hB with ⟨Y, rfl⟩
  have htr : tr (mul (mul (transpose X) X) (mul (transpose Y) Y)) =
      frobNormSq (mul X (transpose Y)) := by
    dsimp [frobNormSq, frobInner]
    rw [transpose_mul, transpose_transpose]
    rw [mul_assoc Y (transpose X) (mul X (transpose Y))]
    rw [tr_mul_comm Y (mul (transpose X) (mul X (transpose Y)))]
    simp [mul_assoc]
  have htrX : tr (mul (transpose X) X) = frobNormSq X := rfl
  have htrY : tr (mul (transpose Y) Y) = frobNormSq (transpose Y) := by
    dsimp [frobNormSq, frobInner]
    rw [transpose_transpose, tr_mul_comm]
  rw [htr, htrX, htrY]
  exact ⟨frobNormSq_nonneg _, frobNormSq_mul_le X (transpose Y)⟩

/-- Hilbert-Schmidt Cauchy-Schwarz for symmetric matrices: `tr(A B)^2 ≤ tr(A^2) tr(B^2)`. -/
theorem two_matrix_cauchy_schwarz {n : Nat} (A B : Mat n)
    (hA : IsSymm A) (hB : IsSymm B) :
    tr (mul A B) * tr (mul A B) ≤ tr (pow A 2) * tr (pow B 2) := by
  have hcs := frob_cauchy_schwarz A B
  dsimp [frobInner, frobNormSq] at hcs
  rw [hA, hB, ← pow_two A, ← pow_two B] at hcs
  exact hcs

/-! ### 3. Universal Two-Matrix Simplex-Lattice Log-Convexity (`m = 2`, All `n, p, q`) -/

theorem nat_even_or_odd (m : Nat) : (∃ r, m = 2 * r) ∨ (∃ r, m = 2 * r + 1) := by
  induction m with
  | zero => exact Or.inl ⟨0, rfl⟩
  | succ k ih =>
    rcases ih with ⟨r, hr⟩ | ⟨r, hr⟩
    · exact Or.inr ⟨r, by omega⟩
    · exact Or.inl ⟨r + 1, by omega⟩

theorem mul_self_pow {n : Nat} (M : Mat n) (k : Nat) : mul M (pow M k) = pow M (1 + k) := by
  have h := (pow_add M 1 k).symm
  rw [pow_one] at h
  exact h

/-- On the two-matrix simplex lattice `Δ_k^(2)` (`m = 2`), log-convexity
    `tr(A^{p+1} B^{q+1})^2 ≤ tr(A^{p+2} B^q) tr(A^p B^{q+2})`
    holds universally for ALL dimensions `n`, ALL `p, q : Nat`, and ALL Gram PSD `A, B`. -/
theorem two_matrix_simplex_log_convex {n : Nat} (A B : Mat n)
    (hA : IsGramPSD A) (hB : IsGramPSD B) (p q : Nat) :
    tr (mul (pow A (p + 1)) (pow B (q + 1))) * tr (mul (pow A (p + 1)) (pow B (q + 1))) ≤
      tr (mul (pow A (p + 2)) (pow B q)) * tr (mul (pow A p) (pow B (q + 2))) := by
  have hAs : IsSymm A := isGramPSD_isSymm hA
  have hBs : IsSymm B := isGramPSD_isSymm hB
  rcases hA with ⟨X, hX⟩
  rcases hB with ⟨Y, hY⟩
  rcases nat_even_or_odd p with ⟨r, hp⟩ | ⟨r, hp⟩ <;>
    rcases nat_even_or_odd q with ⟨s, hq⟩ | ⟨s, hq⟩
  · -- Case 1: `p = 2r`, `q = 2s`
    subst hp; subst hq
    let U := mul (pow A (r + 1)) (pow B s)
    let V := mul (pow A r) (pow B (s + 1))
    have hcs := frob_cauchy_schwarz U V
    have hIP : frobInner U V = tr (mul (pow A (2 * r + 1)) (pow B (2 * s + 1))) := by
      dsimp [frobInner, U, V]
      rw [transpose_mul, symm_pow hAs, symm_pow hBs]
      rw [mul_assoc (pow B s) (pow A (r + 1)) (mul (pow A r) (pow B (s + 1)))]
      rw [← mul_assoc (pow A (r + 1)) (pow A r) (pow B (s + 1)), ← pow_add A (r + 1) r]
      rw [tr_mul_comm (pow B s) _, mul_assoc, ← pow_add B (s + 1) s]
      have er : r + 1 + r = 2 * r + 1 := by omega
      have es : s + 1 + s = 2 * s + 1 := by omega
      rw [er, es]
    have hNU : frobNormSq U = tr (mul (pow A (2 * r + 2)) (pow B (2 * s))) := by
      dsimp [frobNormSq, frobInner, U]
      rw [transpose_mul, symm_pow hAs, symm_pow hBs]
      rw [mul_assoc (pow B s) (pow A (r + 1)) (mul (pow A (r + 1)) (pow B s))]
      rw [← mul_assoc (pow A (r + 1)) (pow A (r + 1)) (pow B s), ← pow_add A (r + 1) (r + 1)]
      rw [tr_mul_comm (pow B s) _, mul_assoc, ← pow_add B s s]
      have er : r + 1 + (r + 1) = 2 * r + 2 := by omega
      have es : s + s = 2 * s := by omega
      rw [er, es]
    have hNV : frobNormSq V = tr (mul (pow A (2 * r)) (pow B (2 * s + 2))) := by
      dsimp [frobNormSq, frobInner, V]
      rw [transpose_mul, symm_pow hAs, symm_pow hBs]
      rw [mul_assoc (pow B (s + 1)) (pow A r) (mul (pow A r) (pow B (s + 1)))]
      rw [← mul_assoc (pow A r) (pow A r) (pow B (s + 1)), ← pow_add A r r]
      rw [tr_mul_comm (pow B (s + 1)) _, mul_assoc, ← pow_add B (s + 1) (s + 1)]
      have er : r + r = 2 * r := by omega
      have es : s + 1 + (s + 1) = 2 * s + 2 := by omega
      rw [er, es]
    rw [hIP, hNU, hNV] at hcs
    exact hcs
  · -- Case 2: `p = 2r`, `q = 2s + 1`
    subst hp; subst hq
    let U := mul Y (mul (pow B s) (pow A (r + 1)))
    let V := mul Y (mul (pow B (s + 1)) (pow A r))
    have hcs := frob_cauchy_schwarz U V
    have hHelperB : ∀ (a₁ a₂ b₁ b₂ : Nat),
        frobInner (mul Y (mul (pow B b₁) (pow A a₁))) (mul Y (mul (pow B b₂) (pow A a₂))) =
          tr (mul (pow A (a₂ + a₁)) (pow B (b₁ + (1 + b₂)))) := by
      intro a₁ a₂ b₁ b₂
      dsimp [frobInner]
      rw [transpose_mul, transpose_mul, symm_pow hAs, symm_pow hBs]
      rw [mul_assoc (mul (pow A a₁) (pow B b₁)) (transpose Y) (mul Y (mul (pow B b₂) (pow A a₂)))]
      rw [← mul_assoc (transpose Y) Y _, ← hY]
      rw [← mul_assoc B (pow B b₂) (pow A a₂), mul_self_pow B b₂]
      rw [mul_assoc (pow A a₁) (pow B b₁) _, ← mul_assoc (pow B b₁), ← pow_add B b₁ (1 + b₂)]
      rw [tr_mul_comm (pow A a₁) _, mul_assoc, tr_mul_comm (pow B _) _, ← pow_add A a₂ a₁]
    have hIP : frobInner U V = tr (mul (pow A (2 * r + 1)) (pow B (2 * s + 1 + 1))) := by
      dsimp [U, V]; rw [hHelperB (r + 1) r s (s + 1)]
      have er : r + (r + 1) = 2 * r + 1 := by omega
      have es : s + (1 + (s + 1)) = 2 * s + 1 + 1 := by omega
      rw [er, es]
    have hNU : frobNormSq U = tr (mul (pow A (2 * r + 2)) (pow B (2 * s + 1))) := by
      dsimp [frobNormSq, U]; rw [hHelperB (r + 1) (r + 1) s s]
      have er : r + 1 + (r + 1) = 2 * r + 2 := by omega
      have es : s + (1 + s) = 2 * s + 1 := by omega
      rw [er, es]
    have hNV : frobNormSq V = tr (mul (pow A (2 * r)) (pow B (2 * s + 1 + 2))) := by
      dsimp [frobNormSq, V]; rw [hHelperB r r (s + 1) (s + 1)]
      have er : r + r = 2 * r := by omega
      have es : s + 1 + (1 + (s + 1)) = 2 * s + 1 + 2 := by omega
      rw [er, es]
    rw [hIP, hNU, hNV] at hcs
    exact hcs
  · -- Case 3: `p = 2r + 1`, `q = 2s`
    subst hp; subst hq
    let U := mul X (mul (pow A (r + 1)) (pow B s))
    let V := mul X (mul (pow A r) (pow B (s + 1)))
    have hcs := frob_cauchy_schwarz U V
    have hHelperA : ∀ (a₁ a₂ b₁ b₂ : Nat),
        frobInner (mul X (mul (pow A a₁) (pow B b₁))) (mul X (mul (pow A a₂) (pow B b₂))) =
          tr (mul (pow A (a₁ + (1 + a₂))) (pow B (b₂ + b₁))) := by
      intro a₁ a₂ b₁ b₂
      dsimp [frobInner]
      rw [transpose_mul, transpose_mul, symm_pow hAs, symm_pow hBs]
      rw [mul_assoc (mul (pow B b₁) (pow A a₁)) (transpose X) (mul X (mul (pow A a₂) (pow B b₂)))]
      rw [← mul_assoc (transpose X) X _, ← hX]
      rw [← mul_assoc A (pow A a₂) (pow B b₂), mul_self_pow A a₂]
      rw [mul_assoc (pow B b₁) (pow A a₁) _, ← mul_assoc (pow A a₁), ← pow_add A a₁ (1 + a₂)]
      rw [tr_mul_comm (pow B b₁) _, mul_assoc, ← pow_add B b₂ b₁]
    have hIP : frobInner U V = tr (mul (pow A (2 * r + 1 + 1)) (pow B (2 * s + 1))) := by
      dsimp [U, V]; rw [hHelperA (r + 1) r s (s + 1)]
      have er : r + 1 + (1 + r) = 2 * r + 1 + 1 := by omega
      have es : s + 1 + s = 2 * s + 1 := by omega
      rw [er, es]
    have hNU : frobNormSq U = tr (mul (pow A (2 * r + 1 + 2)) (pow B (2 * s))) := by
      dsimp [frobNormSq, U]; rw [hHelperA (r + 1) (r + 1) s s]
      have er : r + 1 + (1 + (r + 1)) = 2 * r + 1 + 2 := by omega
      have es : s + s = 2 * s := by omega
      rw [er, es]
    have hNV : frobNormSq V = tr (mul (pow A (2 * r + 1)) (pow B (2 * s + 2))) := by
      dsimp [frobNormSq, V]; rw [hHelperA r r (s + 1) (s + 1)]
      have er : r + (1 + r) = 2 * r + 1 := by omega
      have es : s + 1 + (s + 1) = 2 * s + 2 := by omega
      rw [er, es]
    rw [hIP, hNU, hNV] at hcs
    exact hcs
  · -- Case 4: `p = 2r + 1`, `q = 2s + 1`
    subst hp; subst hq
    let U := mul X (mul (pow A (r + 1)) (mul (pow B s) (transpose Y)))
    let V := mul X (mul (pow A r) (mul (pow B (s + 1)) (transpose Y)))
    have hcs := frob_cauchy_schwarz U V
    have hHelperAB : ∀ (a₁ a₂ b₁ b₂ : Nat),
        frobInner (mul X (mul (pow A a₁) (mul (pow B b₁) (transpose Y))))
                  (mul X (mul (pow A a₂) (mul (pow B b₂) (transpose Y)))) =
          tr (mul (pow A (a₁ + (1 + a₂))) (pow B (b₂ + (1 + b₁)))) := by
      intro a₁ a₂ b₁ b₂
      dsimp [frobInner]
      rw [transpose_mul, transpose_mul, transpose_mul, transpose_transpose, symm_pow hAs, symm_pow hBs]
      rw [mul_assoc (mul (mul Y (pow B b₁)) (pow A a₁)) (transpose X) _]
      rw [← mul_assoc (transpose X) X _, ← hX]
      rw [← mul_assoc A (pow A a₂) _, mul_self_pow A a₂]
      rw [mul_assoc (mul Y (pow B b₁)) (pow A a₁) _]
      rw [← mul_assoc (pow A a₁) (pow A (1 + a₂)) _, ← pow_add A a₁ (1 + a₂)]
      rw [mul_assoc Y (pow B b₁) _, tr_mul_comm Y _]
      rw [mul_assoc (pow B b₁) _ Y, tr_mul_comm (pow B b₁) _]
      simp only [mul_assoc]
      rw [← mul_assoc (transpose Y) Y (pow B b₁), ← hY, mul_self_pow B b₁, ← pow_add B b₂ (1 + b₁)]
    have hIP : frobInner U V = tr (mul (pow A (2 * r + 1 + 1)) (pow B (2 * s + 1 + 1))) := by
      dsimp [U, V]; rw [hHelperAB (r + 1) r s (s + 1)]
      have er : r + 1 + (1 + r) = 2 * r + 1 + 1 := by omega
      have es : s + 1 + (1 + s) = 2 * s + 1 + 1 := by omega
      rw [er, es]
    have hNU : frobNormSq U = tr (mul (pow A (2 * r + 1 + 2)) (pow B (2 * s + 1))) := by
      dsimp [frobNormSq, U]; rw [hHelperAB (r + 1) (r + 1) s s]
      have er : r + 1 + (1 + (r + 1)) = 2 * r + 1 + 2 := by omega
      have es : s + (1 + s) = 2 * s + 1 := by omega
      rw [er, es]
    have hNV : frobNormSq V = tr (mul (pow A (2 * r + 1)) (pow B (2 * s + 1 + 2))) := by
      dsimp [frobNormSq, V]; rw [hHelperAB r r (s + 1) (s + 1)]
      have er : r + (1 + r) = 2 * r + 1 := by omega
      have es : s + 1 + (1 + (s + 1)) = 2 * s + 1 + 2 := by omega
      rw [er, es]
    rw [hIP, hNU, hNV] at hcs
    exact hcs

/-! ### 4. Commuting Diagonal PSD Regime (`m ≥ 1` Arbitrary, All `n, k`) -/

def natPowInt (x : Int) : Nat → Int
  | 0 => 1
  | k + 1 => natPowInt x k * x

theorem natPowInt_nonneg {x : Int} (hx : 0 ≤ x) (k : Nat) : 0 ≤ natPowInt x k := by
  induction k with
  | zero => simp [natPowInt]
  | succ m ih => exact Int.mul_nonneg ih hx

theorem natPowInt_add (x : Int) (p q : Nat) :
    natPowInt x (p + q) = natPowInt x p * natPowInt x q := by
  induction q with
  | zero => simp [natPowInt]
  | succ m ih =>
    rw [Nat.add_succ, natPowInt, natPowInt, ih, Int.mul_assoc]

theorem diag_mul {n : Nat} (d₁ d₂ : Fin n → Int) :
    mul (diag d₁) (diag d₂) = diag (fun i => d₁ i * d₂ i) := by
  ext i j
  dsimp [mul, diag]
  by_cases hij : i = j
  · subst hij
    have hcong : finSum (fun k => (if i = k then d₁ i else 0) * (if k = i then d₂ k else 0)) =
        finSum (fun k => if k = i then d₁ i * d₂ k else 0) := by
      apply finSum_congr
      intro k
      by_cases hki : k = i
      · subst hki; simp
      · have hik : i ≠ k := fun e => hki e.symm
        simp [hki, hik]
    rw [hcong, finSum_ite_eq]
    simp
  · have hpt : ∀ k : Fin n,
        (if i = k then d₁ i else 0) * (if k = j then d₂ k else 0) = 0 := by
      intro k
      by_cases hik : i = k
      · subst hik; simp [hij]
      · simp [hik]
    rw [finSum_congr hpt, finSum_zero]
    simp [hij]

theorem diag_pow {n : Nat} (d : Fin n → Int) (p : Nat) :
    pow (diag d) p = diag (fun i => natPowInt (d i) p) := by
  induction p with
  | zero =>
    ext i j
    simp [pow, one, diag, natPowInt]
  | succ m ih =>
    rw [pow, ih, diag_mul]
    rfl

def diagProdEntry {n : Nat} : {m : Nat} → (Fin m → Fin n → Int) → ExpVec m → Fin n → Int
  | 0, _, _, _ => 1
  | m + 1, ds, α, j =>
    diagProdEntry (fun i : Fin m => ds ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩)
                  (fun i : Fin m => α ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩) j *
      natPowInt (ds ⟨m, Nat.lt_succ_self m⟩ j) (α ⟨m, Nat.lt_succ_self m⟩)

theorem orderedProd_diag {n : Nat} :
    ∀ {m : Nat} (ds : Fin m → Fin n → Int) (α : ExpVec m),
      orderedProd (fun i => diag (ds i)) α = diag (diagProdEntry ds α)
  | 0, _, _ => by
    ext i j
    simp [orderedProd, one, diag, diagProdEntry]
  | m + 1, ds, α => by
    simp only [orderedProd]
    rw [orderedProd_diag, diag_pow, diag_mul]
    rfl

theorem diagProdEntry_nonneg {n : Nat} :
    ∀ {m : Nat} (ds : Fin m → Fin n → Int),
      (∀ i j, 0 ≤ ds i j) → ∀ (α : ExpVec m) (j : Fin n), 0 ≤ diagProdEntry ds α j
  | 0, _, _, _, _ => by simp [diagProdEntry]
  | m + 1, ds, hds, α, j => by
    simp only [diagProdEntry]
    exact Int.mul_nonneg
      (diagProdEntry_nonneg
        (fun i : Fin m => ds ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩)
        (fun i l => hds _ l)
        (fun i : Fin m => α ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩) j)
      (natPowInt_nonneg (hds _ j) _)

theorem diagProdEntry_add {n : Nat} :
    ∀ {m : Nat} (ds : Fin m → Fin n → Int) (α β : ExpVec m) (j : Fin n),
      diagProdEntry ds (expAdd α β) j = diagProdEntry ds α j * diagProdEntry ds β j
  | 0, _, _, _, _ => by simp [diagProdEntry]
  | m + 1, ds, α, β, j => by
    simp only [diagProdEntry]
    have hrec := diagProdEntry_add
      (fun i : Fin m => ds ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩)
      (fun i : Fin m => α ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩)
      (fun i : Fin m => β ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩) j
    have heq_add : (fun i : Fin m => (expAdd α β) ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩) =
        expAdd (fun i : Fin m => α ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩)
               (fun i : Fin m => β ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩) := rfl
    rw [heq_add, hrec, show expAdd α β ⟨m, Nat.lt_succ_self m⟩ =
        α ⟨m, Nat.lt_succ_self m⟩ + β ⟨m, Nat.lt_succ_self m⟩ from rfl, natPowInt_add]
    simp [Int.mul_assoc, Int.mul_left_comm, Int.mul_comm]

theorem diagProdEntry_midpoint {n : Nat} :
    ∀ {m : Nat} (ds : Fin m → Fin n → Int) {α β γ : ExpVec m},
      IsLatticeMidpoint α β γ → ∀ (j : Fin n),
        diagProdEntry ds β j * diagProdEntry ds β j =
          diagProdEntry ds α j * diagProdEntry ds γ j
  | 0, _, _, _, _, _, _ => by simp [diagProdEntry]
  | m + 1, ds, α, β, γ, hmid, j => by
    simp only [diagProdEntry]
    have hrec := diagProdEntry_midpoint
      (fun i : Fin m => ds ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩)
      (α := fun i : Fin m => α ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩)
      (β := fun i : Fin m => β ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩)
      (γ := fun i : Fin m => γ ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩)
      (fun i => hmid _) j
    let x := ds ⟨m, Nat.lt_succ_self m⟩ j
    have hlast := hmid ⟨m, Nat.lt_succ_self m⟩
    have hpow : natPowInt x (β ⟨m, Nat.lt_succ_self m⟩) * natPowInt x (β ⟨m, Nat.lt_succ_self m⟩) =
        natPowInt x (α ⟨m, Nat.lt_succ_self m⟩) * natPowInt x (γ ⟨m, Nat.lt_succ_self m⟩) := by
      rw [← natPowInt_add, ← natPowInt_add]
      congr 1
      omega
    let b0 := diagProdEntry (fun i : Fin m => ds ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩)
                (fun i : Fin m => β ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩) j
    let a0 := diagProdEntry (fun i : Fin m => ds ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩)
                (fun i : Fin m => α ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩) j
    let c0 := diagProdEntry (fun i : Fin m => ds ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩)
                (fun i : Fin m => γ ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩) j
    let pb := natPowInt x (β ⟨m, Nat.lt_succ_self m⟩)
    let pa := natPowInt x (α ⟨m, Nat.lt_succ_self m⟩)
    let pc := natPowInt x (γ ⟨m, Nat.lt_succ_self m⟩)
    change (b0 * pb) * (b0 * pb) = (a0 * pa) * (c0 * pc)
    have rearr1 : (b0 * pb) * (b0 * pb) = (b0 * b0) * (pb * pb) := by
      simp [Int.mul_assoc, Int.mul_left_comm, Int.mul_comm]
    have rearr2 : (a0 * pa) * (c0 * pc) = (a0 * c0) * (pa * pc) := by
      simp [Int.mul_assoc, Int.mul_left_comm, Int.mul_comm]
    rw [rearr1, rearr2, hrec, hpow]

theorem diff_of_squares_int (a b : Int) : (a - b) * (a + b) = a * a - b * b := by
  rw [Int.sub_mul, Int.mul_add, Int.mul_add, Int.mul_comm b a]
  omega

/-- In the commuting non-negative diagonal regime (`m ≥ 1` arbitrary), EVERY simplex-lattice
    midpoint inequality `F(β)^2 ≤ F(α) F(γ)` holds across all dimensions `n` and degrees `k`. -/
theorem commuting_diag_simplex_log_convex {n m : Nat}
    (ds : Fin m → Fin n → Int) (hds : ∀ i j, 0 ≤ ds i j)
    {α β γ : ExpVec m} (hmid : IsLatticeMidpoint α β γ) :
    orderedProdTrace (fun i => diag (ds i)) β * orderedProdTrace (fun i => diag (ds i)) β ≤
      orderedProdTrace (fun i => diag (ds i)) α * orderedProdTrace (fun i => diag (ds i)) γ := by
  dsimp [orderedProdTrace]
  rw [orderedProd_diag, orderedProd_diag, orderedProd_diag]
  dsimp [tr, diag]
  simp only [↓reduceIte]
  let u := fun j => diagProdEntry ds α j
  let v := fun j => diagProdEntry ds γ j
  let w := fun j => diagProdEntry ds β j
  have h_amgm : ∀ i j : Fin n, 2 * (w i * w j) ≤ u i * v j + u j * v i := by
    intro i j
    have hu_i : 0 ≤ u i := diagProdEntry_nonneg ds hds α i
    have hv_j : 0 ≤ v j := diagProdEntry_nonneg ds hds γ j
    have hu_j : 0 ≤ u j := diagProdEntry_nonneg ds hds α j
    have hv_i : 0 ≤ v i := diagProdEntry_nonneg ds hds γ i
    have hw_i : 0 ≤ w i := diagProdEntry_nonneg ds hds β i
    have hw_j : 0 ≤ w j := diagProdEntry_nonneg ds hds β j
    have hwi2 : w i * w i = u i * v i := diagProdEntry_midpoint ds hmid i
    have hwj2 : w j * w j = u j * v j := diagProdEntry_midpoint ds hmid j
    let L := 2 * (w i * w j)
    let R := u i * v j + u j * v i
    have hL_nn : 0 ≤ L := by
      dsimp [L]
      have hwij : 0 ≤ w i * w j := Int.mul_nonneg hw_i hw_j
      omega
    have hR_nn : 0 ≤ R := by
      dsimp [R]
      have p1 : 0 ≤ u i * v j := Int.mul_nonneg hu_i hv_j
      have p2 : 0 ≤ u j * v i := Int.mul_nonneg hu_j hv_i
      omega
    have hsq_diff : R * R - L * L = (u i * v j - u j * v i) * (u i * v j - u j * v i) := by
      dsimp [R, L]
      have e1 : (u i * v j + u j * v i) * (u i * v j + u j * v i) =
          (u i * v j) * (u i * v j) + 2 * ((u i * v j) * (u j * v i)) + (u j * v i) * (u j * v i) := by
        rw [Int.add_mul, Int.mul_add, Int.mul_add]
        have m0 : (u j * v i) * (u i * v j) = (u i * v j) * (u j * v i) := Int.mul_comm _ _
        rw [m0]
        omega
      have e2 : (u i * v j - u j * v i) * (u i * v j - u j * v i) =
          (u i * v j) * (u i * v j) - 2 * ((u i * v j) * (u j * v i)) + (u j * v i) * (u j * v i) := by
        rw [Int.sub_mul, Int.mul_sub, Int.mul_sub]
        have m0 : (u j * v i) * (u i * v j) = (u i * v j) * (u j * v i) := Int.mul_comm _ _
        rw [m0]
        omega
      have e3 : (2 * (w i * w j)) * (2 * (w i * w j)) = 4 * ((u i * v j) * (u j * v i)) := by
        have p : (2 * (w i * w j)) * (2 * (w i * w j)) = 4 * ((w i * w i) * (w j * w j)) := by
          simp [Int.mul_assoc, Int.mul_left_comm, Int.mul_comm]
        have q : (u i * v i) * (u j * v j) = (u i * v j) * (u j * v i) := by
          simp [Int.mul_assoc, Int.mul_left_comm, Int.mul_comm]
        rw [p, hwi2, hwj2, q]
      rw [e1, e2, e3]
      omega
    have hdiff_nn : 0 ≤ R * R - L * L := by
      rw [hsq_diff]
      exact sq_nonneg_int _
    by_cases hle : L ≤ R
    · exact hle
    · exfalso
      have hgt : 0 < L - R := by omega
      have hsum_pos : 0 < L + R := by omega
      have hprod_pos : 0 < (L - R) * (L + R) := Int.mul_pos hgt hsum_pos
      have hexp2 : (L - R) * (L + R) = L * L - R * R := diff_of_squares_int L R
      omega
  have hsum_j : ∀ i : Fin n,
      2 * (w i * finSum w) ≤ u i * finSum v + finSum u * v i := by
    intro i
    have hl : finSum (fun j => 2 * (w i * w j)) = 2 * (w i * finSum w) := by
      rw [finSum_mul_left, finSum_mul_left]
    have hr : finSum (fun j => u i * v j + u j * v i) = u i * finSum v + finSum u * v i := by
      rw [finSum_add, finSum_mul_left, finSum_mul_right]
    rw [← hl, ← hr]
    exact finSum_le (fun j => h_amgm i j)
  have hsum_i :
      2 * (finSum w * finSum w) ≤ 2 * (finSum u * finSum v) := by
    have hl : finSum (fun i => 2 * (w i * finSum w)) = 2 * (finSum w * finSum w) := by
      rw [finSum_mul_left, finSum_mul_right]
    have hr : finSum (fun i => u i * finSum v + finSum u * v i) = 2 * (finSum u * finSum v) := by
      rw [finSum_add, finSum_mul_right, finSum_mul_left]
      omega
    rw [← hl, ← hr]
    exact finSum_le hsum_j
  dsimp [u, v, w] at hsum_i
  omega

/-- In the commuting non-negative diagonal regime (`m ≥ 1` arbitrary), lattice-semigroup
    submultiplicativity `F(α + β) ≤ F(α) F(β)` holds universally across all `n, m`. -/
theorem commuting_diag_submult {n m : Nat}
    (ds : Fin m → Fin n → Int) (hds : ∀ i j, 0 ≤ ds i j) (α β : ExpVec m) :
    orderedProdTrace (fun i => diag (ds i)) (expAdd α β) ≤
      orderedProdTrace (fun i => diag (ds i)) α * orderedProdTrace (fun i => diag (ds i)) β := by
  dsimp [orderedProdTrace]
  rw [orderedProd_diag, orderedProd_diag, orderedProd_diag]
  dsimp [tr, diag]
  simp only [↓reduceIte]
  let u := fun j => diagProdEntry ds α j
  let v := fun j => diagProdEntry ds β j
  have hrewrite : finSum (fun j => diagProdEntry ds (expAdd α β) j) =
      finSum (fun j => u j * v j) :=
    finSum_congr (fun j => diagProdEntry_add ds α β j)
  rw [hrewrite]
  have hsub : ∀ {r : Nat} (f g : Fin r → Int),
      (∀ i, 0 ≤ f i) → (∀ i, 0 ≤ g i) →
      finSum (fun i => f i * g i) ≤ finSum f * finSum g := by
    intro r
    induction r with
    | zero => intros; simp [finSum]
    | succ r' ih =>
      intro f g hf hg
      simp only [finSum]
      let f' : Fin r' → Int := fun i => f ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩
      let g' : Fin r' → Int := fun i => g ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩
      let a := f ⟨r', Nat.lt_succ_self r'⟩
      let b := g ⟨r', Nat.lt_succ_self r'⟩
      have hih : finSum (fun i => f' i * g' i) ≤ finSum f' * finSum g' :=
        ih f' g' (fun i => hf _) (fun i => hg _)
      have hsf : 0 ≤ finSum f' := finSum_nonneg (fun i => hf _)
      have hsg : 0 ≤ finSum g' := finSum_nonneg (fun i => hg _)
      have ha : 0 ≤ a := hf _
      have hb : 0 ≤ b := hg _
      have cross1 : 0 ≤ finSum f' * b := Int.mul_nonneg hsf hb
      have cross2 : 0 ≤ a * finSum g' := Int.mul_nonneg ha hsg
      have hexp : (finSum f' + a) * (finSum g' + b) =
          finSum f' * finSum g' + finSum f' * b + a * finSum g' + a * b := by
        rw [Int.add_mul, Int.mul_add, Int.mul_add]
        omega
      change finSum (fun i => f' i * g' i) + a * b ≤ (finSum f' + a) * (finSum g' + b)
      omega
  exact hsub u v (fun j => diagProdEntry_nonneg ds hds α j) (fun j => diagProdEntry_nonneg ds hds β j)

end Conjecture00000007159
