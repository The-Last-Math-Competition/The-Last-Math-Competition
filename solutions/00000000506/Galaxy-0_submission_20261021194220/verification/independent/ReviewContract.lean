import Main

namespace Independent506Review
open TLMC506

example (p : Poly) : ∃ l : Raw.Poly, ofRaw l = p := ofRaw_surjective p
example (p q : Poly) : mul p q = mul q p := mul_comm p q
example (p q r : Poly) : mul (mul p q) r = mul p (mul q r) := mul_assoc p q r
example (p : Poly) : mul X p = xMul p := X_mul p
example (p : Poly) : mul Y p = yMul p := Y_mul p
example : IsTwoMonomialGeneratedIdeal InIdeal := witness_is_monomial_ideal
example (v : FreeTwo) : IsSyzygy v ↔ ∃ h : Poly, v = koszul h := kernel_exact v
example (v : FreeTwo) (hv : IsSyzygy v) :
    ∃ h : Poly, v = koszul h ∧ ∀ h', v = koszul h' → h' = h :=
  kernel_free_rank_one v hv
example (v : FreeTwo) : InMaximalTimesSyzygy v ↔ IdealSyzygyProduct v :=
  maximal_times_syzygy_is_ideal_product v
example (p : Poly) : InMaximalTimesIdeal p ↔ IdealProduct p :=
  maximal_times_ideal_is_product p
example (q : SyzygyQuotient) : residueClass (quotientResidue q) = q :=
  residueClass_quotientResidue q
example (q : SyzygyQuotient) :
    ∃ c : Bool, quotientScale c quotientGenerator = q ∧
      ∀ c', quotientScale c' quotientGenerator = q → c' = c := quotient_basis q
example : quotientGenerator ≠ quotientZero := quotient_generator_nonzero
example (d : Int) : FirstBettiSupportZ d ↔ d = 2 := first_betti_supportZ_iff d
example (d : Int) : QuotientFirstBettiSupportZ d ↔ d = 1 :=
  quotient_first_betti_supportZ_iff d
example (isOpen : (Int → Prop) → Prop) (h : isOpen (fun _ => True)) :
    IsTwoMonomialGeneratedIdeal InIdeal ∧ VerifiedMinimalResolution ∧
      (∀ d, FirstBettiSupportZ d ↔ d = 2) ∧
      ¬ NoIsolatedPoints isOpen FirstBettiSupportZ := conjecture506_counterexample isOpen h
example (adjacent : Int → Int → Prop) (h : ∀ n, ¬ adjacent n n) :
    FirstBettiSupportZ 2 ∧ ¬ ∃ j, FirstBettiSupportZ j ∧ adjacent 2 j :=
  first_betti_supportZ_graph_isolated adjacent h

end Independent506Review

#print TLMC506.IsIdeal
#print TLMC506.IsMonomial
#print TLMC506.IsTwoMonomialGeneratedIdeal
#print TLMC506.IsSyzygy
#print TLMC506.PresentationHomogeneousZ
#print TLMC506.FirstBettiSupportZ
#print TLMC506.InMaximalTimesSyzygy
#print TLMC506.IdealSyzygyProduct
#print TLMC506.SyzygyResidueEq
#print TLMC506.VerifiedMinimalResolution
#print TLMC506.IsolatedInSubset
#print TLMC506.NoIsolatedPoints
#print axioms TLMC506.conjecture506_counterexample
