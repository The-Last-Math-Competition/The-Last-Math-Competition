/-
  LidskiiProduct.lean
  Top-level entry point for Conjecture 00000007153 ("Diagonal-equality Lidskii product majorization").
-/
import LidskiiProduct.Algebra
import LidskiiProduct.Matrix2
import LidskiiProduct.Counterexamples

namespace LidskiiProduct

/-- Master summary theorem combining the complete multi-interpretation
    refutation of Conjecture 00000007153:
    1. Refutation of Interpretation A under canonical-basis diagonality (`disproof_interpA_diagFactors`,
       `disproof_interpA_anyDiag`), normality/commutativity (`disproof_interpA_normalOrCommuting`),
       and similarity to diagonal matrices (`disproof_interpA_similarDiag`);
    2. Refutation of Interpretation B (Weyl eigenvalue-singular-value log-majorization equality)
       (`disproof_interpB_weylDiag`);
    3. Refutation of Interpretation C (diagonal-entry weak log-majorization)
       (`disproof_interpC_diagWeakLogMaj`). -/
theorem conjecture_00000007153_disproved :
    ¬ ConjectureInterpA_DiagFactors ∧
    ¬ ConjectureInterpA_AnyDiag ∧
    ¬ ConjectureInterpA_NormalOrCommuting ∧
    ¬ ConjectureInterpA_SimilarDiag ∧
    ¬ ConjectureInterpB_WeylDiag ∧
    ¬ ConjectureInterpC_DiagWeakLogMaj :=
  ⟨disproof_interpA_diagFactors,
   disproof_interpA_anyDiag,
   disproof_interpA_normalOrCommuting,
   disproof_interpA_similarDiag,
   disproof_interpB_weylDiag,
   disproof_interpC_diagWeakLogMaj.1⟩

end LidskiiProduct

-- Axiom audit of all principal theorems:
#print axioms LidskiiProduct.hasSingularValues_unique
#print axioms LidskiiProduct.logMajorizes2_implies_weakMajorizes2
#print axioms LidskiiProduct.lidskii_product_log_majorization
#print axioms LidskiiProduct.lidskii_product_eq_iff_gram_aligned
#print axioms LidskiiProduct.weyl_log_majorization
#print axioms LidskiiProduct.diag_abs_eq_sv_implies_diagonal
#print axioms LidskiiProduct.Mat2.defective_not_similar_to_diag
#print axioms LidskiiProduct.positive_witness_diagonal
#print axioms LidskiiProduct.disproof_interpA_diagFactors
#print axioms LidskiiProduct.disproof_interpA_anyDiag
#print axioms LidskiiProduct.disproof_interpA_normalOrCommuting
#print axioms LidskiiProduct.disproof_interpA_similarDiag
#print axioms LidskiiProduct.disproof_interpB_weylDiag
#print axioms LidskiiProduct.disproof_interpC_diagWeakLogMaj
#print axioms LidskiiProduct.disproof_all_dimensions_ge_two
#print axioms LidskiiProduct.conjecture_00000007153_disproved
