import PolynomialRingExtras
import MinimalPresentation
import SyzygyQuotient
import PolynomialGrading

namespace TLMC506

/-- An ideal is given by its ordinary closure properties in the verified ring. -/
def IsIdeal (I : Poly → Prop) : Prop :=
  I zero ∧ (∀ p q, I p → I q → I (add p q)) ∧
    (∀ p q, I q → I (mul p q))

theorem witness_is_ideal : IsIdeal InIdeal :=
  ⟨zero_in_ideal, fun _ _ hp hq => add_in_ideal hp hq,
    fun p _ hq => mul_in_ideal p hq⟩

def IsMonomial (p : Poly) : Prop :=
  ∃ a b : Nat, ∀ i j, p.coeff i j = decide (i = a ∧ j = b)

theorem X_is_monomial : IsMonomial X := by
  refine ⟨1, 0, ?_⟩
  intro i j
  cases i <;> simp [X]

theorem Y_is_monomial : IsMonomial Y := by
  refine ⟨0, 1, ?_⟩
  intro i j
  cases j <;> simp [Y]

def IsTwoMonomialGeneratedIdeal (I : Poly → Prop) : Prop :=
  IsIdeal I ∧ ∃ g h : Poly, IsMonomial g ∧ IsMonomial h ∧
    ∀ p, I p ↔ ∃ a b : Poly, p = add (mul g a) (mul h b)

theorem witness_is_monomial_ideal : IsTwoMonomialGeneratedIdeal InIdeal := by
  refine ⟨witness_is_ideal, X, Y, X_is_monomial, Y_is_monomial, ?_⟩
  intro p
  simp only [X_mul, Y_mul]
  rfl

/-- Actual ideal product mI: finite sums of arbitrary products p*q with p∈m,q∈I.
In this example I=m, so both factors satisfy InIdeal. -/
inductive IdealProduct : Poly → Prop
  | zero : IdealProduct zero
  | single (p q : Poly) : InIdeal p → InIdeal q → IdealProduct (mul p q)
  | add {p q : Poly} : IdealProduct p → IdealProduct q → IdealProduct (add p q)

theorem maximal_times_ideal_add {p q : Poly}
    (hp : InMaximalTimesIdeal p) (hq : InMaximalTimesIdeal q) :
    InMaximalTimesIdeal (add p q) := by
  rw [maximal_times_ideal_iff] at hp hq ⊢
  simp [hp.1, hp.2.1, hp.2.2, hq.1, hq.2.1, hq.2.2]

theorem maximal_times_ideal_is_product (p : Poly) :
    InMaximalTimesIdeal p ↔ IdealProduct p := by
  constructor
  · rintro ⟨a, b, ha, hb, rfl⟩
    rw [← X_mul, ← Y_mul]
    exact IdealProduct.add (IdealProduct.single X a X_in_ideal ha)
      (IdealProduct.single Y b Y_in_ideal hb)
  · intro hp
    induction hp with
    | zero => exact (maximal_times_ideal_iff _).mpr ⟨rfl,rfl,rfl⟩
    | single p q hp hq =>
      obtain ⟨a,b,rfl⟩ := hp
      refine ⟨mul a q, mul b q, mul_in_ideal a hq, mul_in_ideal b hq, ?_⟩
      rw [add_mul, xMul_mul, yMul_mul]
    | add hp hq ihp ihq => exact maximal_times_ideal_add ihp ihq

/-- The first differential really is multiplication by the relation (Y,X). -/
theorem koszul_basis_action (p : Poly) : koszul p = pairMul p (koszul one) := by
  simpa only [mul_one] using koszul_mul p one

/-- A concrete exact minimal graded free resolution, with all structural
conditions proved: R(-2) → R(-1)^2 → I. The left map is injective, so the
resolution stops there. Minimality of the original presentation is established
by the separate I/mI basis theorem rather than assumed. -/
def VerifiedMinimalResolution : Prop :=
  (∀ p, InIdeal p → ∃ v, augmentation v = p) ∧
  (∀ v, IsSyzygy v ↔ ∃ h, v = koszul h) ∧
  (∀ p q, koszul p = koszul q → p = q) ∧
  (∀ p q, koszul (add p q) = pairAdd (koszul p) (koszul q)) ∧
  (∀ p q, koszul (mul p q) = pairMul p (koszul q)) ∧
  (∀ v w, augmentation (pairAdd v w) = add (augmentation v) (augmentation w)) ∧
  (∀ p v, augmentation (pairMul p v) = mul p (augmentation v)) ∧
  (∀ h d, PresentationHomogeneous (koszul h) d ↔ ShiftHomogeneous h 2 d) ∧
  (∀ v d, PresentationHomogeneous v d → Homogeneous (augmentation v) d) ∧
  (∀ h, InIdeal (koszul h).1 ∧ InIdeal (koszul h).2) ∧
  (∀ p, InIdeal p → ∃ a b : Bool,
    InMaximalTimesIdeal (add p (generatorCombination a b)) ∧
    ∀ a' b', InMaximalTimesIdeal (add p (generatorCombination a' b')) →
      a' = a ∧ b' = b)

theorem verified_minimal_resolution : VerifiedMinimalResolution :=
  ⟨augmentation_surjective, kernel_exact, fun _ _ h => koszul_injective h,
    koszul_add, koszul_mul, augmentation_add, augmentation_mul, koszul_homogeneous_iff,
    fun _ _ h => augmentation_homogeneous h, differential_minimal,
    presentation_minimal_basis⟩

/-- A packaged counterexample to the explicit no-isolated-points clause in
conjecture 506. Its support is obtained from the genuine minimal-generator
quotient of the syzygy module of the verified monomial ideal. -/
theorem conjecture506_counterexample
    (isOpen : (Int → Prop) → Prop) (open_univ : isOpen (fun _ => True)) :
    IsTwoMonomialGeneratedIdeal InIdeal ∧
    VerifiedMinimalResolution ∧
    (∀ d, FirstBettiSupportZ d ↔ d = 2) ∧
    ¬ NoIsolatedPoints isOpen FirstBettiSupportZ :=
  ⟨witness_is_monomial_ideal, verified_minimal_resolution,
    first_betti_supportZ_iff, first_betti_no_isolatedZ_clause_false isOpen open_univ⟩

end TLMC506
