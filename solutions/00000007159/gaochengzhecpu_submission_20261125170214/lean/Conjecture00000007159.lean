/-
  Conjecture 00000007159 — Master Resolution Module
  "Definition: MMT extrema with the multiplicative inequalities of matrices.
   Conjecture: The complete system of trace product inequalities holds, and the
   generation of the system is the simplex lattice. (simplex-lattice MMT trace-product system)"

  Verdict: FALSE (Disproved across all canonical interpretations, already on `2 × 2`
  strictly positive definite integer Gram matrices `M_2(ℤ)`).
-/
import Conjecture00000007159.MatrixTrace
import Conjecture00000007159.SimplexSystems
import Conjecture00000007159.PositiveTheorems
import Conjecture00000007159.Counterexamples

namespace Conjecture00000007159

/-- Non-vacuity & positive regime theorem:
    1. In the commuting PSD regime (`m ≥ 1` arbitrary, all dimensions `n` and degrees `k`),
       both simplex-lattice midpoint log-convexity and lattice-semigroup trace-product
       submultiplicativity hold universally.
    2. In the noncommuting two-matrix PSD regime (`m = 2`, all dimensions `n`),
       degree-2 submultiplicativity `0 ≤ tr(A B) ≤ tr(A) tr(B)`, degree-4 Lieb-Thirring
       `tr((A B)^2) ≤ tr(A^2 B^2)`, degree-5 word grouping `tr(A^2 B A B) ≤ tr(A^3 B^2)`,
       and simplex-lattice log-convexity `tr(A^{p+1} B^{q+1})^2 ≤ tr(A^{p+2} B^q) tr(A^p B^{q+2})`
       all hold universally. -/
theorem positive_simplex_regimes :
    (∀ {n m : Nat} (ds : Fin m → Fin n → Int), (∀ i j, 0 ≤ ds i j) →
      ∀ {α β γ : ExpVec m}, IsLatticeMidpoint α β γ →
        orderedProdTrace (fun i => Mat.diag (ds i)) β *
          orderedProdTrace (fun i => Mat.diag (ds i)) β ≤
        orderedProdTrace (fun i => Mat.diag (ds i)) α *
          orderedProdTrace (fun i => Mat.diag (ds i)) γ) ∧
    (∀ {n m : Nat} (ds : Fin m → Fin n → Int), (∀ i j, 0 ≤ ds i j) →
      ∀ (α β : ExpVec m),
        orderedProdTrace (fun i => Mat.diag (ds i)) (expAdd α β) ≤
        orderedProdTrace (fun i => Mat.diag (ds i)) α *
          orderedProdTrace (fun i => Mat.diag (ds i)) β) ∧
    (∀ {n : Nat} (A B : Mat n), Mat.IsGramPSD A → Mat.IsGramPSD B →
      0 ≤ Mat.tr (Mat.mul A B) ∧ Mat.tr (Mat.mul A B) ≤ Mat.tr A * Mat.tr B) ∧
    (∀ {n : Nat} (A B : Mat n), Mat.IsSymm A → Mat.IsSymm B →
      Mat.tr (Mat.pow (Mat.mul A B) 2) ≤ Mat.tr (Mat.mul (Mat.pow A 2) (Mat.pow B 2))) ∧
    (∀ {n : Nat} (A B : Mat n), Mat.IsGramPSD A → Mat.IsSymm B →
      Mat.tr (Mat.mul (Mat.mul (Mat.pow A 2) B) (Mat.mul A B)) ≤
        Mat.tr (Mat.mul (Mat.pow A 3) (Mat.pow B 2))) ∧
    (∀ {n : Nat} (A B : Mat n), Mat.IsGramPSD A → Mat.IsGramPSD B → ∀ p q : Nat,
      Mat.tr (Mat.mul (Mat.pow A (p + 1)) (Mat.pow B (q + 1))) *
        Mat.tr (Mat.mul (Mat.pow A (p + 1)) (Mat.pow B (q + 1))) ≤
      Mat.tr (Mat.mul (Mat.pow A (p + 2)) (Mat.pow B q)) *
        Mat.tr (Mat.mul (Mat.pow A p) (Mat.pow B (q + 2)))) :=
  ⟨fun ds hds _ _ _ hmid => commuting_diag_simplex_log_convex ds hds hmid,
   fun ds hds α β => commuting_diag_submult ds hds α β,
   fun A B hA hB => two_matrix_submult_deg2 A B hA hB,
   fun A B hA hB => lieb_thirring_deg4_symm A B hA hB,
   fun A B hA hB => word_grouping_deg5_gram A B hA hB,
   fun A B hA hB p q => two_matrix_simplex_log_convex A B hA hB p q⟩

/-- Master disproof of Conjecture 00000007159:
    Already for `2 × 2` strictly positive definite integer Gram matrices (`n = 2`),
    every candidate formulation of a complete simplex-lattice multiplicative
    trace-product system fails:
    1. Two-matrix lattice-semigroup submultiplicativity fails (`tr(A^2 B^2) > tr(AB)^2`);
    2. Three-matrix lattice submultiplicativity / cycle-trace dominance fails (`tr(ABC) > tr(AB) tr(C)`);
    3. Simplex-lattice ordered-product positivity fails at `(1, 1, 1) ∈ Δ_3^(3)` (`tr(ABC) < 0`);
    4. Simplex-lattice midpoint log-convexity fails on `Δ_4^(3)` and in the strict interior of `Δ_5^(3)`
       even when all involved traces are strictly positive;
    5. Frobenius-norm / Hermitian-sandwich log-convexity fails on `Δ_3^(3)`;
    6. Three-matrix Lieb-Thirring / word-grouping extrema fail at `(2, 2, 2) ∈ Δ_6^(3)`;
    7. Both `S_3`-symmetrized Ordered Matrix Muirhead (`Δ_6^(3)`) and Word-Averaged Hurwitz/BMV
       Matrix Muirhead (`Δ_5^(3)`) majorization systems fail along elementary lattice transfers. -/
theorem conjecture_00000007159_disproved :
    ¬ SimplexSubmultiplicativeSystem 2 2 ∧
    ¬ SimplexSubmultiplicativeSystem 2 3 ∧
    ¬ SimplexPositivitySystem 2 3 3 ∧
    ¬ SimplexLogConvexSystem 2 3 4 ∧
    ¬ SimplexLogConvexSystem 2 3 5 ∧
    ¬ SimplexFrobeniusLogConvexSystem 2 3 3 ∧
    ¬ SimplexWordExtremaSystem 2 3 6 ∧
    ¬ SimplexOrderedMuirhead3System 2 6 ∧
    ¬ SimplexHurwitzMuirhead3System 2 5 :=
  ⟨disproof_submultiplicative_m2,
   disproof_submultiplicative_m3,
   disproof_interior_positivity_m3,
   disproof_simplex_log_convex_m3_deg4,
   disproof_simplex_log_convex_m3_deg5,
   disproof_frobenius_log_convex_m3,
   disproof_word_extrema_m3,
   disproof_ordered_muirhead_m3,
   disproof_hurwitz_muirhead_m3⟩

end Conjecture00000007159
