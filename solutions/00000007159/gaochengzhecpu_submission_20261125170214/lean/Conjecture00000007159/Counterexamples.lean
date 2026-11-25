/-
  Conjecture 00000007159 — Exact Kernel-Verified Counterexamples in `M_2(ℤ)`
  Refutes every candidate simplex-lattice multiplicative trace-product system
  using strictly positive definite `2 × 2` integer Gram matrices `A = L^T L` (`det L ≠ 0`).
  Core Lean 4.19.0 (zero external dependencies, zero `native_decide`)
-/
import Conjecture00000007159.SimplexSystems

namespace Conjecture00000007159

open Mat

/-! ### Constructive Gram Factors `L ∈ M_2(ℤ)` with `det L ≠ 0` -/

def L_1_m1_0_1 : Mat 2 := mat2 1 (-1) 0 1
def L_1_1_0_1  : Mat 2 := mat2 1 1 0 1
def L_m1_m1_1_0 : Mat 2 := mat2 (-1) (-1) 1 0
def L_m2_m1_1_0 : Mat 2 := mat2 (-2) (-1) 1 0
def L_m1_1_1_m2 : Mat 2 := mat2 (-1) 1 1 (-2)
def L_2_1_1_1   : Mat 2 := mat2 2 1 1 1
def L_1_0_0_2   : Mat 2 := mat2 1 0 0 2
def L_1_2_0_1   : Mat 2 := mat2 1 2 0 1
def L_m1_0_1_m1 : Mat 2 := mat2 (-1) 0 1 (-1)
def L_m2_0_1_m2 : Mat 2 := mat2 (-2) 0 1 (-2)
def L_m3_1_m1_0 : Mat 2 := mat2 (-3) 1 (-1) 0
def L_1_0_3_1   : Mat 2 := mat2 1 0 3 1
def L_1_m3_0_1  : Mat 2 := mat2 1 (-3) 0 1
def L_1_0_m2_1  : Mat 2 := mat2 1 0 (-2) 1

def gramOf (L : Mat 2) : Mat 2 := mul (transpose L) L

theorem gramOf_isStrictGramSPD2 (L : Mat 2) (hdet : det2 L ≠ 0) :
    IsStrictGramSPD2 (gramOf L) :=
  ⟨L, hdet, rfl⟩

theorem gramOf_isGramPSD (L : Mat 2) : IsGramPSD (gramOf L) :=
  ⟨L, rfl⟩

/-! ### 1. Disproof of Two-Matrix Lattice Submultiplicativity (`m = 2, k = 4`) -/

/-- Explicit unimodular SPD witness `A = [[1,-1],[-1,2]], B = [[1,1],[1,2]]`:
    `tr(A^2 B^2) = 11 > 9 = 3^2 = tr(A B)^2`. -/
theorem witness_submult_m2 :
    let A := gramOf L_1_m1_0_1
    let B := gramOf L_1_1_0_1
    IsStrictGramSPD2 A ∧ IsStrictGramSPD2 B ∧
      orderedProdTrace (vec2 A B) (vec2 1 1) = 3 ∧
      orderedProdTrace (vec2 A B) (vec2 2 2) = 11 ∧
      orderedProdTrace (vec2 A B) (vec2 1 1) * orderedProdTrace (vec2 A B) (vec2 1 1) <
        orderedProdTrace (vec2 A B) (vec2 2 2) := by
  refine ⟨gramOf_isStrictGramSPD2 _ (by decide), gramOf_isStrictGramSPD2 _ (by decide), rfl, rfl, ?_⟩
  decide

theorem disproof_submultiplicative_m2 : ¬ SimplexSubmultiplicativeSystem 2 2 := by
  intro hsys
  let A := gramOf L_1_m1_0_1
  let B := gramOf L_1_1_0_1
  have hgram : ∀ i : Fin 2, IsGramPSD (vec2 A B i) := by
    intro i
    by_cases hi : i.val = 0
    · simp [vec2, hi]; exact gramOf_isGramPSD _
    · simp [vec2, hi]; exact gramOf_isGramPSD _
  have hineq := hsys (vec2 A B) hgram 2 2 (vec2 1 1) (vec2 1 1)
    (by decide) (by decide) rfl rfl
  have hbad : ¬ (orderedProdTrace (vec2 A B) (expAdd (vec2 1 1) (vec2 1 1)) ≤
      orderedProdTrace (vec2 A B) (vec2 1 1) * orderedProdTrace (vec2 A B) (vec2 1 1)) := by
    decide
  exact hbad hineq

/-! ### 2. Disproof of Simplex-Lattice Interior Positivity (`m = 3, k = 3`) -/

/-- Explicit unimodular SPD witness `A = [[1,1],[1,2]], B = [[5,2],[2,1]], C = [[2,-3],[-3,5]]`:
    at the interior point `(1, 1, 1) ∈ Δ_3^(3)`, `tr(A B C) = -2 < 0`. -/
theorem witness_interior_negativity_m3 :
    let A := gramOf L_1_1_0_1
    let B := gramOf L_m2_m1_1_0
    let C := gramOf L_m1_1_1_m2
    IsStrictGramSPD2 A ∧ IsStrictGramSPD2 B ∧ IsStrictGramSPD2 C ∧
      orderedProdTrace (vec3 A B C) (vec3 1 1 1) = -2 := by
  refine ⟨gramOf_isStrictGramSPD2 _ (by decide),
          gramOf_isStrictGramSPD2 _ (by decide),
          gramOf_isStrictGramSPD2 _ (by decide), rfl⟩

theorem gram_vec3 {A B C : Mat 2} (hA : IsGramPSD A) (hB : IsGramPSD B) (hC : IsGramPSD C) :
    ∀ i : Fin 3, IsGramPSD (vec3 A B C i) := by
  intro i
  match i with
  | ⟨0, _⟩ => exact hA
  | ⟨1, _⟩ => exact hB
  | ⟨2, _⟩ => exact hC

theorem disproof_interior_positivity_m3 : ¬ SimplexPositivitySystem 2 3 3 := by
  intro hsys
  let A := gramOf L_1_1_0_1
  let B := gramOf L_m2_m1_1_0
  let C := gramOf L_m1_1_1_m2
  have hineq := hsys (vec3 A B C)
    (gram_vec3 (gramOf_isGramPSD _) (gramOf_isGramPSD _) (gramOf_isGramPSD _))
    (vec3 1 1 1) rfl
  have hbad : ¬ (0 ≤ orderedProdTrace (vec3 A B C) (vec3 1 1 1)) := by decide
  exact hbad hineq

/-! ### 3. Disproof of Cycle-Partition Trace-Product Dominance (`tr(ABC) ≤ tr(AB) tr(C)`) -/

/-- Explicit unimodular SPD witness `A = [[1,1],[1,2]], B = [[5,2],[2,1]], C = [[5,3],[3,2]]`:
    `tr(A B C) = 79 > 77 = 11 * 7 = tr(A B) tr(C)`. -/
theorem witness_cycle_trace_product_m3 :
    let A := gramOf L_1_1_0_1
    let B := gramOf L_m2_m1_1_0
    let C := gramOf L_2_1_1_1
    IsStrictGramSPD2 A ∧ IsStrictGramSPD2 B ∧ IsStrictGramSPD2 C ∧
      orderedProdTrace (vec3 A B C) (vec3 1 1 1) = 79 ∧
      orderedProdTrace (vec3 A B C) (vec3 1 1 0) * orderedProdTrace (vec3 A B C) (vec3 0 0 1) = 77 := by
  refine ⟨gramOf_isStrictGramSPD2 _ (by decide),
          gramOf_isStrictGramSPD2 _ (by decide),
          gramOf_isStrictGramSPD2 _ (by decide), rfl, rfl⟩

theorem disproof_submultiplicative_m3 : ¬ SimplexSubmultiplicativeSystem 2 3 := by
  intro hsys
  let A := gramOf L_1_1_0_1
  let B := gramOf L_m2_m1_1_0
  let C := gramOf L_2_1_1_1
  have hineq := hsys (vec3 A B C)
    (gram_vec3 (gramOf_isGramPSD _) (gramOf_isGramPSD _) (gramOf_isGramPSD _))
    2 1 (vec3 1 1 0) (vec3 0 0 1) (by decide) (by decide) rfl rfl
  have hbad : ¬ (orderedProdTrace (vec3 A B C) (expAdd (vec3 1 1 0) (vec3 0 0 1)) ≤
      orderedProdTrace (vec3 A B C) (vec3 1 1 0) * orderedProdTrace (vec3 A B C) (vec3 0 0 1)) := by
    decide
  exact hbad hineq

/-! ### 4. Disproof of Simplex-Lattice Log-Convexity on `Δ_4^(3)` and Interior `Δ_5^(3)` -/

/-- Degree-4 SPD witness on `Δ_4^(3)` with strictly positive traces:
    `(1, 2, 1) = ((2, 1, 1) + (0, 3, 1)) / 2`, yet `F(1,2,1)^2 = 36^2 = 1296 > 1287 = 39 * 33`. -/
theorem witness_log_convex_deg4_m3 :
    let A := gramOf L_1_1_0_1
    let B := gramOf L_m1_m1_1_0
    let C := gramOf L_1_0_0_2
    IsStrictGramSPD2 A ∧ IsStrictGramSPD2 B ∧ IsStrictGramSPD2 C ∧
      orderedProdTrace (vec3 A B C) (vec3 1 2 1) = 36 ∧
      orderedProdTrace (vec3 A B C) (vec3 2 1 1) = 39 ∧
      orderedProdTrace (vec3 A B C) (vec3 0 3 1) = 33 := by
  refine ⟨gramOf_isStrictGramSPD2 _ (by decide),
          gramOf_isStrictGramSPD2 _ (by decide),
          gramOf_isStrictGramSPD2 _ (by decide), rfl, rfl, rfl⟩

/-- Pure interior degree-5 unimodular SPD witness on `Δ_5^(3)` with strictly positive traces:
    `(2, 1, 2) = ((3, 1, 1) + (1, 1, 3)) / 2`, yet `F(2,1,2)^2 = 459^2 = 210681 > 209898 = 207 * 1014`. -/
theorem witness_log_convex_interior_deg5_m3 :
    let A := gramOf L_1_1_0_1
    let B := gramOf L_m1_m1_1_0
    let C := gramOf L_1_2_0_1
    IsStrictGramSPD2 A ∧ IsStrictGramSPD2 B ∧ IsStrictGramSPD2 C ∧
      orderedProdTrace (vec3 A B C) (vec3 2 1 2) = 459 ∧
      orderedProdTrace (vec3 A B C) (vec3 3 1 1) = 207 ∧
      orderedProdTrace (vec3 A B C) (vec3 1 1 3) = 1014 := by
  refine ⟨gramOf_isStrictGramSPD2 _ (by decide),
          gramOf_isStrictGramSPD2 _ (by decide),
          gramOf_isStrictGramSPD2 _ (by decide), rfl, rfl, rfl⟩

theorem midpoint_helper {a₁ b₁ c₁ a₂ b₂ c₂ a₃ b₃ c₃ : Nat}
    (h0 : 2 * a₂ = a₁ + a₃) (h1 : 2 * b₂ = b₁ + b₃) (h2 : 2 * c₂ = c₁ + c₃) :
    IsLatticeMidpoint (vec3 a₁ b₁ c₁) (vec3 a₂ b₂ c₂) (vec3 a₃ b₃ c₃) := by
  intro i
  match i with
  | ⟨0, _⟩ => exact h0
  | ⟨1, _⟩ => exact h1
  | ⟨2, _⟩ => exact h2

theorem disproof_simplex_log_convex_m3_deg4 : ¬ SimplexLogConvexSystem 2 3 4 := by
  intro hsys
  let A := gramOf L_1_1_0_1
  let B := gramOf L_m1_m1_1_0
  let C := gramOf L_1_0_0_2
  have hineq := hsys (vec3 A B C)
    (gram_vec3 (gramOf_isGramPSD _) (gramOf_isGramPSD _) (gramOf_isGramPSD _))
    (vec3 2 1 1) (vec3 1 2 1) (vec3 0 3 1)
    rfl rfl (midpoint_helper rfl rfl rfl)
  have hbad : ¬ (orderedProdTrace (vec3 A B C) (vec3 1 2 1) * orderedProdTrace (vec3 A B C) (vec3 1 2 1) ≤
      orderedProdTrace (vec3 A B C) (vec3 2 1 1) * orderedProdTrace (vec3 A B C) (vec3 0 3 1)) := by
    decide
  exact hbad hineq

theorem disproof_simplex_log_convex_m3_deg5 : ¬ SimplexLogConvexSystem 2 3 5 := by
  intro hsys
  let A := gramOf L_1_1_0_1
  let B := gramOf L_m1_m1_1_0
  let C := gramOf L_1_2_0_1
  have hineq := hsys (vec3 A B C)
    (gram_vec3 (gramOf_isGramPSD _) (gramOf_isGramPSD _) (gramOf_isGramPSD _))
    (vec3 3 1 1) (vec3 2 1 2) (vec3 1 1 3)
    rfl rfl (midpoint_helper rfl rfl rfl)
  have hbad : ¬ (orderedProdTrace (vec3 A B C) (vec3 2 1 2) * orderedProdTrace (vec3 A B C) (vec3 2 1 2) ≤
      orderedProdTrace (vec3 A B C) (vec3 3 1 1) * orderedProdTrace (vec3 A B C) (vec3 1 1 3)) := by
    decide
  exact hbad hineq

/-! ### 5. Disproof of Frobenius-Norm / Sandwich Log-Convexity (`m = 3, k = 3`) -/

/-- Even for the manifestly positive definite functional `G(α) = ‖A^{α_1} B^{α_2} C^{α_3}‖_F^2`,
    at `(1, 1, 1) = ((2, 0, 1) + (0, 2, 1)) / 2 ∈ Δ_3^(3)`,
    `G(1, 1, 1)^2 = 43^2 = 1849 > 490 = 7 * 70 = G(2, 0, 1) G(0, 2, 1)`. -/
theorem witness_frobenius_log_convex_m3 :
    let A := gramOf L_1_1_0_1
    let B := gramOf L_m1_m1_1_0
    let C := gramOf L_m1_0_1_m1
    IsStrictGramSPD2 A ∧ IsStrictGramSPD2 B ∧ IsStrictGramSPD2 C ∧
      orderedProdFrobSq (vec3 A B C) (vec3 1 1 1) = 43 ∧
      orderedProdFrobSq (vec3 A B C) (vec3 2 0 1) = 7 ∧
      orderedProdFrobSq (vec3 A B C) (vec3 0 2 1) = 70 := by
  refine ⟨gramOf_isStrictGramSPD2 _ (by decide),
          gramOf_isStrictGramSPD2 _ (by decide),
          gramOf_isStrictGramSPD2 _ (by decide), rfl, rfl, rfl⟩

theorem disproof_frobenius_log_convex_m3 : ¬ SimplexFrobeniusLogConvexSystem 2 3 3 := by
  intro hsys
  let A := gramOf L_1_1_0_1
  let B := gramOf L_m1_m1_1_0
  let C := gramOf L_m1_0_1_m1
  have hineq := hsys (vec3 A B C)
    (gram_vec3 (gramOf_isGramPSD _) (gramOf_isGramPSD _) (gramOf_isGramPSD _))
    (vec3 2 0 1) (vec3 1 1 1) (vec3 0 2 1)
    rfl rfl (midpoint_helper rfl rfl rfl)
  have hbad : ¬ (orderedProdFrobSq (vec3 A B C) (vec3 1 1 1) * orderedProdFrobSq (vec3 A B C) (vec3 1 1 1) ≤
      orderedProdFrobSq (vec3 A B C) (vec3 2 0 1) * orderedProdFrobSq (vec3 A B C) (vec3 0 2 1)) := by
    decide
  exact hbad hineq

/-! ### 6. Disproof of Three-Matrix Lieb-Thirring / Word-Grouping Extrema (`m = 3, k = 6`) -/

/-- At `(2, 2, 2) ∈ Δ_6^(3)`, `tr((A B C)^2) = 193 > 175 = tr(A^2 B^2 C^2) > 0`
    and `‖A B C‖_F^2 = tr((A B C)^T (A B C)) = 337 > 175`. -/
theorem witness_word_extrema_m3 :
    let A := gramOf L_1_1_0_1
    let B := gramOf L_m1_m1_1_0
    let C := gramOf L_m2_0_1_m2
    let w : List (Fin 3) := [0, 1, 2, 0, 1, 2]
    IsStrictGramSPD2 A ∧ IsStrictGramSPD2 B ∧ IsStrictGramSPD2 C ∧
      wordTrace (vec3 A B C) w = 193 ∧
      frobNormSq (orderedProd (vec3 A B C) (vec3 1 1 1)) = 337 ∧
      orderedProdTrace (vec3 A B C) (vec3 2 2 2) = 175 := by
  refine ⟨gramOf_isStrictGramSPD2 _ (by decide),
          gramOf_isStrictGramSPD2 _ (by decide),
          gramOf_isStrictGramSPD2 _ (by decide), rfl, rfl, rfl⟩

theorem disproof_word_extrema_m3 : ¬ SimplexWordExtremaSystem 2 3 6 := by
  intro hsys
  let A := gramOf L_1_1_0_1
  let B := gramOf L_m1_m1_1_0
  let C := gramOf L_m2_0_1_m2
  let w : List (Fin 3) := [0, 1, 2, 0, 1, 2]
  have hineq := hsys (vec3 A B C)
    (gram_vec3 (gramOf_isGramPSD _) (gramOf_isGramPSD _) (gramOf_isGramPSD _))
    w rfl
  have hbad : ¬ (wordTrace (vec3 A B C) w ≤ orderedProdTrace (vec3 A B C) (wordWeight w)) := by
    decide
  exact hbad hineq

/-! ### 7. Disproof of Both Symmetrized Matrix Muirhead Systems on `Δ_k^(3)` -/

theorem transfer_321_222 :
    IsElementaryTransfer (vec3 3 2 1) (vec3 2 2 2) (0 : Fin 3) (2 : Fin 3) := by
  refine ⟨by decide, by decide, rfl, rfl, ?_⟩
  intro i h0 h2
  match i with
  | ⟨0, _⟩ => exact absurd rfl h0
  | ⟨1, _⟩ => rfl
  | ⟨2, _⟩ => exact absurd rfl h2

theorem transfer_311_221 :
    IsElementaryTransfer (vec3 3 1 1) (vec3 2 2 1) (0 : Fin 3) (1 : Fin 3) := by
  refine ⟨by decide, by decide, rfl, rfl, ?_⟩
  intro i h0 h1
  match i with
  | ⟨0, _⟩ => exact absurd rfl h0
  | ⟨1, _⟩ => exact absurd rfl h1
  | ⟨2, _⟩ => rfl

/-- Ordered Matrix Muirhead failure on `Δ_6^(3)` (`(3, 2, 1) ≻ (2, 2, 2)`):
    `M^ord_{(3,2,1)}(A, B, C) = -8606 < -6900 = M^ord_{(2,2,2)}(A, B, C) < 0`. -/
theorem witness_ordered_muirhead_m3 :
    let A := gramOf L_1_m1_0_1
    let B := gramOf L_1_2_0_1
    let C := gramOf L_m3_1_m1_0
    IsStrictGramSPD2 A ∧ IsStrictGramSPD2 B ∧ IsStrictGramSPD2 C ∧
      orderedMuirhead3 A B C 3 2 1 = -8606 ∧
      orderedMuirhead3 A B C 2 2 2 = -6900 := by
  refine ⟨gramOf_isStrictGramSPD2 _ (by decide),
          gramOf_isStrictGramSPD2 _ (by decide),
          gramOf_isStrictGramSPD2 _ (by decide), rfl, rfl⟩

theorem disproof_ordered_muirhead_m3 : ¬ SimplexOrderedMuirhead3System 2 6 := by
  intro hsys
  let A := gramOf L_1_m1_0_1
  let B := gramOf L_1_2_0_1
  let C := gramOf L_m3_1_m1_0
  have hineq := hsys A B C (gramOf_isGramPSD _) (gramOf_isGramPSD _) (gramOf_isGramPSD _)
    3 2 1 2 2 2 0 2 rfl transfer_321_222
  have hbad : ¬ (orderedMuirhead3 A B C 2 2 2 ≤ orderedMuirhead3 A B C 3 2 1) := by decide
  exact hbad hineq

/-- Hurwitz / BMV Word-Averaged Muirhead failure on `Δ_5^(3)` (`(3, 1, 1) ≻ (2, 2, 1)`):
    with unimodular SPD matrices, the average word trace at `(3,1,1)` is `7224` (`144480 / 20`)
    which is strictly less than the average word trace `7360` (`220800 / 30`) at `(2,2,1)`. -/
theorem witness_hurwitz_muirhead_m3 :
    let A := gramOf L_1_0_3_1
    let B := gramOf L_1_m3_0_1
    let C := gramOf L_1_0_m2_1
    IsStrictGramSPD2 A ∧ IsStrictGramSPD2 B ∧ IsStrictGramSPD2 C ∧
      multinom3 3 1 1 = 20 ∧
      multinom3 2 2 1 = 30 ∧
      hurwitzSymWordSum3 A B C 3 1 1 = 144480 ∧
      hurwitzSymWordSum3 A B C 2 2 1 = 220800 := by
  refine ⟨gramOf_isStrictGramSPD2 _ (by decide),
          gramOf_isStrictGramSPD2 _ (by decide),
          gramOf_isStrictGramSPD2 _ (by decide), rfl, rfl, rfl, rfl⟩

theorem disproof_hurwitz_muirhead_m3 : ¬ SimplexHurwitzMuirhead3System 2 5 := by
  intro hsys
  let A := gramOf L_1_0_3_1
  let B := gramOf L_1_m3_0_1
  let C := gramOf L_1_0_m2_1
  have hineq := hsys A B C (gramOf_isGramPSD _) (gramOf_isGramPSD _) (gramOf_isGramPSD _)
    3 1 1 2 2 1 0 1 rfl transfer_311_221
  have hbad : ¬ ((multinom3 3 1 1 : Int) * hurwitzSymWordSum3 A B C 2 2 1 ≤
      (multinom3 2 2 1 : Int) * hurwitzSymWordSum3 A B C 3 1 1) := by decide
  exact hbad hineq

end Conjecture00000007159
