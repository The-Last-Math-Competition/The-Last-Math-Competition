import BettiSupport

namespace TLMC506

/-- mI = XI+YI. The ring/module bridge later proves this agrees with the
product by the entire ideal m=(X,Y), not just a selected relation family. -/
def InMaximalTimesIdeal (p : Poly) : Prop :=
  ∃ a b : Poly, InIdeal a ∧ InIdeal b ∧ p = add (xMul a) (yMul b)

theorem maximal_times_ideal_iff (p : Poly) :
    InMaximalTimesIdeal p ↔
      p.coeff 0 0 = false ∧ p.coeff 1 0 = false ∧ p.coeff 0 1 = false := by
  constructor
  · rintro ⟨a, b, ha, hb, rfl⟩
    have ha0 := (ideal_iff_constant_zero a).mp ha
    have hb0 := (ideal_iff_constant_zero b).mp hb
    simp [ha0, hb0]
  · rintro ⟨h0, hx, hy⟩
    refine ⟨dropX p, axisY p, ?_, ?_, ?_⟩
    · exact (ideal_iff_constant_zero _).mpr hx
    · apply (ideal_iff_constant_zero _).mpr
      simpa [axisY] using hy
    · simpa only [h0, constant_false, zero_add] using constant_split p

def generatorCombination (a b : Bool) : Poly := add (scale a X) (scale b Y)

@[simp] theorem generatorCombination_constant (a b : Bool) :
    (generatorCombination a b).coeff 0 0 = false := by
  simp [generatorCombination, X, Y]
@[simp] theorem generatorCombination_x (a b : Bool) :
    (generatorCombination a b).coeff 1 0 = a := by
  simp [generatorCombination, X, Y]
@[simp] theorem generatorCombination_y (a b : Bool) :
    (generatorCombination a b).coeff 0 1 = b := by
  simp [generatorCombination, X, Y]

theorem generatorCombination_in_ideal (a b : Bool) :
    InIdeal (generatorCombination a b) :=
  (ideal_iff_constant_zero _).mpr (generatorCombination_constant a b)

theorem generator_independence (a b : Bool) :
    InMaximalTimesIdeal (generatorCombination a b) ↔ a = false ∧ b = false := by
  simp only [maximal_times_ideal_iff, generatorCombination_constant,
    generatorCombination_x, generatorCombination_y, true_and]

theorem generator_spanning {p : Poly} (hp : InIdeal p) :
    InMaximalTimesIdeal
      (add p (generatorCombination (p.coeff 1 0) (p.coeff 0 1))) := by
  rw [maximal_times_ideal_iff]
  have hp0 := (ideal_iff_constant_zero p).mp hp
  simp [hp0]

theorem generator_coefficients_unique (p : Poly) (a b : Bool)
    (h : InMaximalTimesIdeal (add p (generatorCombination a b))) :
    a = p.coeff 1 0 ∧ b = p.coeff 0 1 := by
  have hh := (maximal_times_ideal_iff _).mp h
  constructor
  · apply Eq.symm
    apply (xor_eq_false_iff _ _).mp
    simpa only [add_coeff, generatorCombination_x] using hh.2.1
  · apply Eq.symm
    apply (xor_eq_false_iff _ _).mp
    simpa only [add_coeff, generatorCombination_y] using hh.2.2

/-- Every residue in I/mI has a UNIQUE expansion a[X]+b[Y] over F₂.
This proves that X,Y form a minimal generating set, not merely a generating set. -/
theorem presentation_minimal_basis (p : Poly) (hp : InIdeal p) :
    ∃ a b : Bool,
      InMaximalTimesIdeal (add p (generatorCombination a b)) ∧
      ∀ a' b', InMaximalTimesIdeal (add p (generatorCombination a' b')) →
        a' = a ∧ b' = b := by
  refine ⟨p.coeff 1 0, p.coeff 0 1, generator_spanning hp, ?_⟩
  intro a' b' h
  exact generator_coefficients_unique p a' b' h

theorem X_homogeneous_one : Homogeneous X 1 := by
  intro i j hij
  cases i with
  | zero => cases hij
  | succ i =>
    have h : i = 0 ∧ j = 0 := by simpa [X] using hij
    omega

theorem Y_homogeneous_one : Homogeneous Y 1 := by
  intro i j hij
  cases j with
  | zero => cases hij
  | succ j =>
    have h : i = 0 ∧ j = 0 := by simpa [Y] using hij
    omega

/-- Both entries of the syzygy differential are in the homogeneous maximal
ideal. This is the standard minimal-complex condition for the resolution. -/
theorem differential_minimal (h : Poly) :
    InIdeal (koszul h).1 ∧ InIdeal (koszul h).2 :=
  ⟨yMul_in_ideal h, xMul_in_ideal h⟩

theorem augmentation_surjective (p : Poly) (hp : InIdeal p) :
    ∃ v : FreeTwo, augmentation v = p := by
  obtain ⟨a, b, hab⟩ := hp
  exact ⟨(a,b), hab.symm⟩

/-- Under the alternative quotient-ring convention, the first relation module
of R/I is I itself, and its minimal-generator quotient is I/mI. -/
def QuotientFirstBettiSupportZ (d : Int) : Prop :=
  ∃ p : Poly, InIdeal p ∧
    (∀ i j, p.coeff i j = true → (i : Int) + (j : Int) = d) ∧
    ¬ InMaximalTimesIdeal p

theorem quotient_first_betti_supportZ_iff (d : Int) :
    QuotientFirstBettiSupportZ d ↔ d = 1 := by
  constructor
  · rintro ⟨p,hp,hd,hn⟩
    have hp0 := (ideal_iff_constant_zero p).mp hp
    cases hx : p.coeff 1 0 with
    | true => have h := hd 1 0 hx; omega
    | false =>
      cases hy : p.coeff 0 1 with
      | true => have h := hd 0 1 hy; omega
      | false => exact False.elim (hn ((maximal_times_ideal_iff p).mpr ⟨hp0,hx,hy⟩))
  · intro hd
    subst d
    refine ⟨X,X_in_ideal,?_,?_⟩
    · intro i j h
      have hh := X_homogeneous_one i j h
      omega
    · rw [maximal_times_ideal_iff]
      simp [X]

theorem quotient_first_betti_supportZ_isolated
    (isOpen : (Int → Prop) → Prop) (open_univ : isOpen (fun _ => True)) :
    IsolatedInSubset isOpen QuotientFirstBettiSupportZ 1 := by
  refine ⟨(quotient_first_betti_supportZ_iff 1).mpr rfl,
    (fun _ => True),open_univ,trivial,?_⟩
  intro k _ hk
  exact (quotient_first_betti_supportZ_iff k).mp hk

end TLMC506
