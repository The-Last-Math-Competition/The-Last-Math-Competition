import Mathlib.Analysis.Normed.Group.Constructions
import Mathlib.Data.Matrix.Notation
import Mathlib.Tactic

/-! A finite pure integer linear program and its genuine real relaxation.
Every finite input value, including the objective constant and variable bounds,
is included in `data`, and `delta` is its largest absolute value. -/
noncomputable section
namespace Proximity

structure Row (n : ℕ) where
  coeff : Fin n → ℤ
  rhs : ℤ

structure ILP (n : ℕ) where
  equalities : List (Row n)
  inequalities : List (Row n)
  lower : Fin n → Option ℤ
  upper : Fin n → Option ℤ
  cost : Fin n → ℤ
  constant : ℤ

def Row.eval {n : ℕ} (r : Row n) (x : Fin n → ℝ) : ℝ :=
  ∑ i, (r.coeff i : ℝ) * x i

def ILP.feasible {n : ℕ} (P : ILP n) (x : Fin n → ℝ) : Prop :=
  (∀ r ∈ P.equalities, r.eval x = (r.rhs : ℝ)) ∧
  (∀ r ∈ P.inequalities, r.eval x ≤ (r.rhs : ℝ)) ∧
  (∀ i b, P.lower i = some b → (b : ℝ) ≤ x i) ∧
  (∀ i b, P.upper i = some b → x i ≤ (b : ℝ))

def intCast {n : ℕ} (x : Fin n → ℤ) : Fin n → ℝ := fun i => x i

def ILP.intFeasible {n : ℕ} (P : ILP n) (x : Fin n → ℤ) : Prop :=
  P.feasible (intCast x)

def ILP.objective {n : ℕ} (P : ILP n) (x : Fin n → ℝ) : ℝ :=
  (∑ i, (P.cost i : ℝ) * x i) + P.constant

def ILP.realOptimal {n : ℕ} (P : ILP n) (x : Fin n → ℝ) : Prop :=
  P.feasible x ∧ ∀ y, P.feasible y → P.objective x ≤ P.objective y

def ILP.integerOptimal {n : ℕ} (P : ILP n) (x : Fin n → ℤ) : Prop :=
  P.intFeasible x ∧ ∀ y, P.intFeasible y →
    P.objective (intCast x) ≤ P.objective (intCast y)

def ILP.uniqueRealOptimal {n : ℕ} (P : ILP n) (x : Fin n → ℝ) : Prop :=
  P.realOptimal x ∧ ∀ y, P.realOptimal y → y = x

def ILP.uniqueIntegerOptimal {n : ℕ} (P : ILP n) (x : Fin n → ℤ) : Prop :=
  P.integerOptimal x ∧ ∀ y, P.integerOptimal y → y = x

/-- The usual extreme-point condition; our relaxation optimum is a vertex. -/
def ILP.vertex {n : ℕ} (P : ILP n) (x : Fin n → ℝ) : Prop :=
  P.feasible x ∧ ∀ y z : Fin n → ℝ, P.feasible y → P.feasible z →
    ∀ t : ℝ, 0 < t → t < 1 →
    x = t • y + (1 - t) • z → y = x ∧ z = x

def Row.data {n : ℕ} (r : Row n) : List ℤ := List.ofFn r.coeff ++ [r.rhs]

def ILP.data {n : ℕ} (P : ILP n) : List ℤ :=
  (P.equalities ++ P.inequalities).flatMap Row.data ++
  (List.ofFn P.lower).filterMap id ++ (List.ofFn P.upper).filterMap id ++
  List.ofFn P.cost ++ [P.constant]

def ILP.delta {n : ℕ} (P : ILP n) : ℕ :=
  (P.data.map Int.natAbs).foldl max 0

/-- Mixed equalities/inequalities with all three coordinates free. -/
def mixedFree : ILP 3 :=
  { equalities := [⟨![-10, 1, 0], 0⟩, ⟨![0, -10, 1], 0⟩]
    inequalities := [⟨![-2, 0, 0], -1⟩]
    lower := fun _ => none
    upper := fun _ => none
    cost := ![1, 0, 0]
    constant := 0 }

/-- Inequality-only standard form with free variables. -/
def inequalityFree : ILP 3 :=
  { equalities := []
    inequalities := [⟨![-2, 0, 0], -1⟩,
      ⟨![-10, 1, 0], 0⟩, ⟨![10, -1, 0], 0⟩,
      ⟨![0, -10, 1], 0⟩, ⟨![0, 10, -1], 0⟩]
    lower := fun _ => none
    upper := fun _ => none
    cost := ![1, 0, 0]
    constant := 0 }

/-- Inequality-only standard form with nonnegative variables. -/
def inequalityNonnegative : ILP 3 :=
  { inequalityFree with lower := fun _ => some 0 }

/-- Equality standard form with four nonnegative coordinates (x,y,z,s). -/
def equalityNonnegative : ILP 4 :=
  { equalities := [⟨![-10, 1, 0, 0], 0⟩,
      ⟨![0, -10, 1, 0], 0⟩, ⟨![2, 0, 0, -1], 1⟩]
    inequalities := []
    lower := fun _ => some 0
    upper := fun _ => none
    cost := ![1, 0, 0, 0]
    constant := 0 }

def ray3 (x : Fin 3 → ℝ) : Prop :=
  1 / 2 ≤ x 0 ∧ x 1 = 10 * x 0 ∧ x 2 = 100 * x 0

def ray4 (x : Fin 4 → ℝ) : Prop :=
  1 / 2 ≤ x 0 ∧ x 1 = 10 * x 0 ∧ x 2 = 100 * x 0 ∧ x 3 = 2 * x 0 - 1

def real3 : Fin 3 → ℝ := ![1/2, 5, 50]
def integer3 : Fin 3 → ℤ := ![1, 10, 100]
def real4 : Fin 4 → ℝ := ![1/2, 5, 50, 0]
def integer4 : Fin 4 → ℤ := ![1, 10, 100, 1]

lemma mixedFree_feasible (x : Fin 3 → ℝ) : mixedFree.feasible x ↔ ray3 x := by
  simp [ILP.feasible, mixedFree, Row.eval, Fin.sum_univ_succ, ray3]
  constructor
  · rintro ⟨⟨h₁, h₂⟩, h₃⟩
    exact ⟨by linarith, by linarith, by linarith⟩
  · rintro ⟨h₁, h₂, h₃⟩
    exact ⟨⟨by linarith, by linarith⟩, by linarith⟩

lemma inequalityFree_feasible (x : Fin 3 → ℝ) : inequalityFree.feasible x ↔ ray3 x := by
  simp [ILP.feasible, inequalityFree, Row.eval, Fin.sum_univ_succ, ray3]
  constructor
  · rintro ⟨h₁, h₂, h₃, h₄, h₅⟩
    exact ⟨by linarith, by linarith, by linarith⟩
  · rintro ⟨h₁, h₂, h₃⟩
    exact ⟨by linarith, by linarith, by linarith, by linarith, by linarith⟩

lemma inequalityNonnegative_feasible (x : Fin 3 → ℝ) :
    inequalityNonnegative.feasible x ↔ ray3 x := by
  simp [ILP.feasible, inequalityNonnegative, inequalityFree, Row.eval,
    Fin.sum_univ_succ, ray3]
  constructor
  · rintro ⟨⟨h₁, h₂, h₃, h₄, h₅⟩, _⟩
    exact ⟨by linarith, by linarith, by linarith⟩
  · rintro ⟨h₁, h₂, h₃⟩
    refine ⟨⟨by linarith, by linarith, by linarith, by linarith, by linarith⟩, ?_⟩
    intro i
    fin_cases i <;> dsimp <;> linarith

lemma equalityNonnegative_feasible (x : Fin 4 → ℝ) :
    equalityNonnegative.feasible x ↔ ray4 x := by
  simp [ILP.feasible, equalityNonnegative, Row.eval, Fin.sum_univ_succ, ray4]
  constructor
  · rintro ⟨⟨h₁, h₂, h₃⟩, h₄⟩
    have h := h₄ 3
    exact ⟨by linarith, by linarith, by linarith, by linarith⟩
  · rintro ⟨h₁, h₂, h₃, h₄⟩
    refine ⟨⟨by linarith, by linarith, by linarith⟩, ?_⟩
    intro i
    fin_cases i <;> dsimp <;> linarith

lemma mixedFree_objective (x : Fin 3 → ℝ) : mixedFree.objective x = x 0 := by
  simp [ILP.objective, mixedFree, Fin.sum_univ_succ]
lemma inequalityFree_objective (x : Fin 3 → ℝ) : inequalityFree.objective x = x 0 := by
  simp [ILP.objective, inequalityFree, Fin.sum_univ_succ]
lemma inequalityNonnegative_objective (x : Fin 3 → ℝ) :
    inequalityNonnegative.objective x = x 0 := by
  simp [ILP.objective, inequalityNonnegative, inequalityFree, Fin.sum_univ_succ]
lemma equalityNonnegative_objective (x : Fin 4 → ℝ) :
    equalityNonnegative.objective x = x 0 := by
  simp [ILP.objective, equalityNonnegative, Fin.sum_univ_succ]


lemma optimum3 (P : ILP 3)
    (hf : ∀ x, P.feasible x ↔ ray3 x)
    (hc : ∀ x, P.objective x = x 0) :
    P.uniqueRealOptimal real3 ∧ P.uniqueIntegerOptimal integer3 := by
  have hr : P.feasible real3 := (hf _).2 (by norm_num [ray3, real3, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail])
  have hi : P.intFeasible integer3 := (hf _).2 (by norm_num [ray3, intCast, integer3, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail])
  have hro : P.realOptimal real3 := by
    refine ⟨hr, ?_⟩
    intro y hy
    simpa [hc, real3] using ((hf y).1 hy).1
  have hio : P.integerOptimal integer3 := by
    refine ⟨hi, ?_⟩
    intro y hy
    have hy0 := ((hf _).1 hy).1
    have hp : (0 : ℝ) < (y 0 : ℝ) := by dsimp [intCast] at hy0; linarith
    have hpz : (0 : ℤ) < y 0 := by exact_mod_cast hp
    have hp1 : (1 : ℤ) ≤ y 0 := by omega
    simpa [hc, integer3, intCast] using (show (1 : ℝ) ≤ (y 0 : ℝ) by exact_mod_cast hp1)
  constructor
  · refine ⟨hro, ?_⟩
    intro y hy
    obtain ⟨h₀, h₁, h₂⟩ := (hf _).1 hy.1
    have hle := hy.2 real3 hr
    simp only [hc, real3, Matrix.cons_val_zero] at hle
    have he : y 0 = 1/2 := le_antisymm hle h₀
    ext i
    fin_cases i <;> simp [real3] <;> linarith
  · refine ⟨hio, ?_⟩
    intro y hy
    obtain ⟨h₀, h₁, h₂⟩ := (hf _).1 hy.1
    have hle := hy.2 integer3 hi
    simp [hc, intCast, integer3] at hle
    dsimp [intCast] at h₀ h₁ h₂
    have hp : (0 : ℝ) < (y 0 : ℝ) := by linarith
    have hpz : (0 : ℤ) < y 0 := by exact_mod_cast hp
    have hlez : y 0 ≤ (1 : ℤ) := by exact_mod_cast hle
    have he : y 0 = 1 := by omega
    have he1 : y 1 = 10 := by rw [he] at h₁; norm_num at h₁; exact_mod_cast h₁
    have he2 : y 2 = 100 := by rw [he] at h₂; norm_num at h₂; exact_mod_cast h₂
    ext i
    fin_cases i <;> simp [integer3, he, he1, he2]

lemma optimum4 (P : ILP 4)
    (hf : ∀ x, P.feasible x ↔ ray4 x)
    (hc : ∀ x, P.objective x = x 0) :
    P.uniqueRealOptimal real4 ∧ P.uniqueIntegerOptimal integer4 := by
  have hr : P.feasible real4 := (hf _).2 (by norm_num [ray4, real4, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.vecHead, Matrix.vecTail])
  have hi : P.intFeasible integer4 := (hf _).2 (by norm_num [ray4, intCast, integer4, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.vecHead, Matrix.vecTail])
  have hro : P.realOptimal real4 := by
    refine ⟨hr, ?_⟩
    intro y hy
    simpa [hc, real4] using ((hf y).1 hy).1
  have hio : P.integerOptimal integer4 := by
    refine ⟨hi, ?_⟩
    intro y hy
    have hy0 := ((hf _).1 hy).1
    have hp : (0 : ℝ) < (y 0 : ℝ) := by dsimp [intCast] at hy0; linarith
    have hpz : (0 : ℤ) < y 0 := by exact_mod_cast hp
    have hp1 : (1 : ℤ) ≤ y 0 := by omega
    simpa [hc, integer4, intCast] using (show (1 : ℝ) ≤ (y 0 : ℝ) by exact_mod_cast hp1)
  constructor
  · refine ⟨hro, ?_⟩
    intro y hy
    obtain ⟨h₀, h₁, h₂, h₃⟩ := (hf _).1 hy.1
    have hle := hy.2 real4 hr
    simp only [hc, real4, Matrix.cons_val_zero] at hle
    have he : y 0 = 1/2 := le_antisymm hle h₀
    ext i
    fin_cases i <;> simp [real4] <;> linarith
  · refine ⟨hio, ?_⟩
    intro y hy
    obtain ⟨h₀, h₁, h₂, h₃⟩ := (hf _).1 hy.1
    have hle := hy.2 integer4 hi
    simp [hc, intCast, integer4] at hle
    dsimp [intCast] at h₀ h₁ h₂ h₃
    have hp : (0 : ℝ) < (y 0 : ℝ) := by linarith
    have hpz : (0 : ℤ) < y 0 := by exact_mod_cast hp
    have hlez : y 0 ≤ (1 : ℤ) := by exact_mod_cast hle
    have he : y 0 = 1 := by omega
    have he1 : y 1 = 10 := by rw [he] at h₁; norm_num at h₁; exact_mod_cast h₁
    have he2 : y 2 = 100 := by rw [he] at h₂; norm_num at h₂; exact_mod_cast h₂
    have he3 : y 3 = 1 := by rw [he] at h₃; norm_num at h₃; exact_mod_cast h₃
    ext i
    fin_cases i <;> simp [integer4, he, he1, he2, he3]

lemma vertex_of_unique_coordinate_minimum {n : ℕ} (P : ILP n)
    (i : Fin n) (x : Fin n → ℝ)
    (hc : ∀ y, P.objective y = y i) (hu : P.uniqueRealOptimal x) :
    P.vertex x := by
  refine ⟨hu.1.1, ?_⟩
  intro y z hy hz t ht ht1 he
  have hymin := hu.1.2 y hy
  have hzmin := hu.1.2 z hz
  simp only [hc] at hymin hzmin
  have hei := congrFun he i
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hei
  have hyi : y i = x i := by nlinarith
  have hzi : z i = x i := by nlinarith
  constructor
  · apply hu.2 y
    refine ⟨hy, ?_⟩
    intro w hw
    have hwmin := hu.1.2 w hw
    simpa only [hc, hyi] using hwmin
  · apply hu.2 z
    refine ⟨hz, ?_⟩
    intro w hw
    have hwmin := hu.1.2 w hw
    simpa only [hc, hzi] using hwmin

lemma distance3 : ‖intCast integer3 - real3‖ = (50 : ℝ) := by
  apply le_antisymm
  · apply (pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 50)).2
    intro i
    fin_cases i <;> norm_num [intCast, integer3, real3, Real.norm_eq_abs]
  · have h := norm_le_pi_norm (intCast integer3 - real3) (2 : Fin 3)
    change ‖(100 : ℝ) - 50‖ ≤ ‖intCast integer3 - real3‖ at h
    norm_num at h
    exact h

lemma distance4 : ‖intCast integer4 - real4‖ = (50 : ℝ) := by
  apply le_antisymm
  · apply (pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 50)).2
    intro i
    fin_cases i <;> norm_num [intCast, integer4, real4, Real.norm_eq_abs]
  · have h := norm_le_pi_norm (intCast integer4 - real4) (2 : Fin 4)
    change ‖(100 : ℝ) - 50‖ ≤ ‖intCast integer4 - real4‖ at h
    norm_num at h
    exact h

lemma delta_mixedFree : mixedFree.delta = 10 := by decide
lemma delta_inequalityFree : inequalityFree.delta = 10 := by decide
lemma delta_inequalityNonnegative : inequalityNonnegative.delta = 10 := by decide
lemma delta_equalityNonnegative : equalityNonnegative.delta = 10 := by decide

/-- Exact, unique optima, vertex, full-data magnitude, norm, and strict violation. -/
def Certificate {n : ℕ} (P : ILP n) (xi : Fin n → ℤ) (xr : Fin n → ℝ) : Prop :=
  P.uniqueIntegerOptimal xi ∧ P.uniqueRealOptimal xr ∧ P.vertex xr ∧
  P.delta = 10 ∧ ‖intCast xi - xr‖ = 50 ∧
  (n : ℝ) * P.delta < ‖intCast xi - xr‖

theorem mixedFree_certificate : Certificate mixedFree integer3 real3 := by
  obtain ⟨hr, hi⟩ := optimum3 mixedFree mixedFree_feasible mixedFree_objective
  refine ⟨hi, hr, vertex_of_unique_coordinate_minimum _ 0 _ mixedFree_objective hr,
    delta_mixedFree, distance3, ?_⟩
  rw [delta_mixedFree, distance3]
  norm_num

theorem inequalityFree_certificate : Certificate inequalityFree integer3 real3 := by
  obtain ⟨hr, hi⟩ := optimum3 inequalityFree inequalityFree_feasible inequalityFree_objective
  refine ⟨hi, hr, vertex_of_unique_coordinate_minimum _ 0 _ inequalityFree_objective hr,
    delta_inequalityFree, distance3, ?_⟩
  rw [delta_inequalityFree, distance3]
  norm_num

theorem inequalityNonnegative_certificate : Certificate inequalityNonnegative integer3 real3 := by
  obtain ⟨hr, hi⟩ := optimum3 inequalityNonnegative inequalityNonnegative_feasible
    inequalityNonnegative_objective
  refine ⟨hi, hr, vertex_of_unique_coordinate_minimum _ 0 _ inequalityNonnegative_objective hr,
    delta_inequalityNonnegative, distance3, ?_⟩
  rw [delta_inequalityNonnegative, distance3]
  norm_num

theorem equalityNonnegative_certificate : Certificate equalityNonnegative integer4 real4 := by
  obtain ⟨hr, hi⟩ := optimum4 equalityNonnegative equalityNonnegative_feasible
    equalityNonnegative_objective
  refine ⟨hi, hr, vertex_of_unique_coordinate_minimum _ 0 _ equalityNonnegative_objective hr,
    delta_equalityNonnegative, distance4, ?_⟩
  rw [delta_equalityNonnegative, distance4]
  norm_num

/-- The explicit upper bound in the source, for finite pure integer linear programs. -/
def UniversalUpperBound : Prop :=
  ∀ (n : ℕ) (P : ILP n) (xi : Fin n → ℤ) (xr : Fin n → ℝ),
    P.integerOptimal xi → P.realOptimal xr →
    ‖intCast xi - xr‖ ≤ (n : ℝ) * P.delta

/-- Even restriction to unique optima and a relaxation vertex does not save the bound. -/
def UniqueVertexUpperBound : Prop :=
  ∀ (n : ℕ) (P : ILP n) (xi : Fin n → ℤ) (xr : Fin n → ℝ),
    P.uniqueIntegerOptimal xi → P.uniqueRealOptimal xr → P.vertex xr →
    ‖intCast xi - xr‖ ≤ (n : ℝ) * P.delta

theorem not_universalUpperBound : ¬ UniversalUpperBound := by
  intro h
  have hc := mixedFree_certificate
  exact (not_le_of_gt hc.2.2.2.2.2)
    (h 3 mixedFree integer3 real3 hc.1.1 hc.2.1.1)

theorem not_uniqueVertexUpperBound : ¬ UniqueVertexUpperBound := by
  intro h
  have hc := equalityNonnegative_certificate
  exact (not_le_of_gt hc.2.2.2.2.2)
    (h 4 equalityNonnegative integer4 real4 hc.1 hc.2.1 hc.2.2.1)

/-- Any conjunction with the explicit upper bound is false, regardless of how
one supplies the source's separate sharpness clause. -/
theorem not_source_conjunction (sharpnessClause : Prop) :
    ¬ (UniversalUpperBound ∧ sharpnessClause) := by
  rintro ⟨h, _⟩
  exact not_universalUpperBound h


/-- The explicit slack-variable map; it commutes with the integer embedding. -/
def addSlack (x : Fin 3 → ℝ) : Fin 4 → ℝ := ![x 0, x 1, x 2, 2 * x 0 - 1]
def addIntegerSlack (x : Fin 3 → ℤ) : Fin 4 → ℤ := ![x 0, x 1, x 2, 2 * x 0 - 1]
def dropSlack (x : Fin 4 → ℝ) : Fin 3 → ℝ := ![x 0, x 1, x 2]

lemma addSlack_cast (x : Fin 3 → ℤ) :
    intCast (addIntegerSlack x) = addSlack (intCast x) := by
  ext i
  fin_cases i <;> simp [addIntegerSlack, addSlack, intCast]

lemma slack_feasible_iff (x : Fin 3 → ℝ) :
    equalityNonnegative.feasible (addSlack x) ↔ mixedFree.feasible x := by
  rw [equalityNonnegative_feasible, mixedFree_feasible]
  simp [ray4, ray3, addSlack, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.vecHead, Matrix.vecTail]

lemma integer_slack_feasible_iff (x : Fin 3 → ℤ) :
    equalityNonnegative.intFeasible (addIntegerSlack x) ↔ mixedFree.intFeasible x := by
  simp only [ILP.intFeasible, addSlack_cast, slack_feasible_iff]

lemma dropSlack_feasible (x : Fin 4 → ℝ) (h : equalityNonnegative.feasible x) :
    mixedFree.feasible (dropSlack x) := by
  rw [mixedFree_feasible]
  have h' := equalityNonnegative_feasible x |>.1 h
  change 1/2 ≤ x 0 ∧ x 1 = 10 * x 0 ∧ x 2 = 100 * x 0
  exact ⟨h'.1, h'.2.1, h'.2.2.1⟩

lemma dropSlack_addSlack (x : Fin 3 → ℝ) : dropSlack (addSlack x) = x := by
  ext i
  fin_cases i <;> simp [dropSlack, addSlack]

lemma addSlack_dropSlack (x : Fin 4 → ℝ) (h : equalityNonnegative.feasible x) :
    addSlack (dropSlack x) = x := by
  have h' := equalityNonnegative_feasible x |>.1 h
  ext i
  fin_cases i <;> simp [dropSlack, addSlack]
  exact h'.2.2.2.symm

lemma slack_objective (x : Fin 3 → ℝ) :
    equalityNonnegative.objective (addSlack x) = mixedFree.objective x := by
  rw [equalityNonnegative_objective, mixedFree_objective]
  rfl

lemma three_coordinate_form_equivalence (x : Fin 3 → ℝ) :
    (mixedFree.feasible x ↔ inequalityFree.feasible x) ∧
    (mixedFree.feasible x ↔ inequalityNonnegative.feasible x) ∧
    mixedFree.objective x = inequalityFree.objective x ∧
    mixedFree.objective x = inequalityNonnegative.objective x := by
  simp [mixedFree_feasible, inequalityFree_feasible, inequalityNonnegative_feasible,
    mixedFree_objective, inequalityFree_objective, inequalityNonnegative_objective]

end Proximity
