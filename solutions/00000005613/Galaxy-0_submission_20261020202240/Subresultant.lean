import Std

/-!
# TLMC 00000005613: a vanishing coefficient minor with nonzero principal minor

The actual first subresultant construction for the monic polynomials
f = X^3 - 4 X and g = X^2 - 1 has M_{3,1} = 0 and M_{3,0} = -3.
Their rational roots strictly interlace and a Bezout identity certifies that
no common root exists. The matrix is generated from polynomial coefficients,
not assigned as a numerical table.
-/
namespace TLMC5613

/-- Coefficients in ascending powers. Only finite support is used below. -/
abbrev Polynomial := Nat → Rat
abbrev Matrix := Nat → Nat → Rat

def sum (n : Nat) (f : Nat → Rat) : Rat := ((List.range n).map f).sum

/-- Evaluation through degree `n`. -/
def evaluate (n : Nat) (f : Polynomial) (x : Rat) : Rat :=
  sum (n+1) (fun j => f j * x^j)

/-- Exact degree, expressed by a nonzero leading coefficient and zero tail. -/
def HasDegree (f : Polynomial) (n : Nat) : Prop :=
  f n ≠ 0 ∧ ∀ k, n < k → f k = 0

def monic (f : Polynomial) (n : Nat) : Prop := f n = 1

/-- Coefficient of X^e in X^s f. -/
def shiftedCoefficient (f : Polynomial) (s e : Nat) : Rat :=
  if s ≤ e then f (e-s) else 0

/-- The standard i-th Sylvester submatrix. Rows are the coefficient vectors of
X^(q-i-1) f,...,f, X^(p-i-1) g,...,g, in descending degree order.
For i < min(p,q), there are p+q-2i rows and p+q-i columns. -/
def sylvesterSubmatrix (p q i : Nat) (f g : Polynomial) : Matrix :=
  fun r c =>
    if r < p+q-2*i ∧ c < p+q-i then
      if r < q-i then
        shiftedCoefficient f (q-i-1-r) (p+q-i-1-c)
      else
        shiftedCoefficient g (p-i-1-(r-(q-i))) (p+q-i-1-c)
    else 0

/-- Laplace expansion along the first row, including det(empty)=1. -/
def det : Nat → Matrix → Rat
  | 0, _ => 1
  | n+1, A => sum (n+1) (fun j =>
      (if j % 2 = 0 then (1 : Rat) else -1) * A 0 j *
      det n (fun r c => A (r+1) (if c < j then c else c+1)))

/-- Standard M_{k,t}: first k rows, first k-1 columns and column k+t,
where the descriptive column numbers are one-based. -/
def coefficientMinor (A : Matrix) (k t : Nat) : Rat :=
  det k (fun r c => A r (if c < k-1 then c else k-1+t))

/-- Principal subresultant coefficient M_{p+q-2i,0}. -/
def principalSubresultant (p q i : Nat) (f g : Polynomial) : Rat :=
  coefficientMinor (sylvesterSubmatrix p q i f g) (p+q-2*i) 0

/-- Polynomial subresultant by its coefficient minors. -/
def subresultantValue (p q i : Nat) (f g : Polynomial) (x : Rat) : Rat :=
  sum (i+1) (fun j =>
    coefficientMinor (sylvesterSubmatrix p q i f g) (p+q-2*i) (i-j) * x^j)

def f : Polynomial := fun k =>
  if k = 3 then 1 else if k = 1 then -4 else 0

def g : Polynomial := fun k =>
  if k = 2 then 1 else if k = 0 then -1 else 0

def S : Matrix := sylvesterSubmatrix 3 2 1 f g

/-- The chosen inputs really have degrees 3 and 2 and are monic. -/
theorem input_degrees : HasDegree f 3 ∧ HasDegree g 2 ∧ monic f 3 ∧ monic g 2 := by
  refine ⟨⟨by decide, ?_⟩, ⟨by decide, ?_⟩, rfl, rfl⟩
  · intro k hk
    have h3 : k ≠ 3 := by omega
    have h1 : k ≠ 1 := by omega
    simp [f, h3, h1]
  · intro k hk
    have h2 : k ≠ 2 := by omega
    have h0 : k ≠ 0 := by omega
    simp [g, h2, h0]

theorem f_evaluation (x : Rat) : evaluate 3 f x = x^3 - 4*x := by
  simp [evaluate, sum, f, List.range_succ]
  grind

theorem g_evaluation (x : Rat) : evaluate 2 g x = x^2 - 1 := by
  simp [evaluate, sum, g, List.range_succ]
  grind

/-- Addition and multiplication of ascending finite coefficient lists. -/
def addCoefficients : List Rat → List Rat → List Rat
  | [], q => q
  | p, [] => p
  | a::p, b::q => (a+b)::addCoefficients p q

def multiplyCoefficients : List Rat → List Rat → List Rat
  | [], _ => []
  | [a], q => q.map (fun b => a*b)
  | a::p, q => addCoefficients (q.map (fun b => a*b))
      (0::multiplyCoefficients p q)

def linearCoefficients (a : Rat) : List Rat := [-a, 1]

def fromCoefficients (p : List Rat) : Polynomial := fun k => p[k]?.getD 0

/-- Coefficient-level product identities, valid under any field embedding. -/
theorem f_product_coefficients :
    multiplyCoefficients (multiplyCoefficients (linearCoefficients (-2))
      (linearCoefficients 0)) (linearCoefficients 2) = [0, -4, 0, 1] := by
  simp [multiplyCoefficients, addCoefficients, linearCoefficients]
  grind

theorem g_product_coefficients :
    multiplyCoefficients (linearCoefficients (-1)) (linearCoefficients 1) = [-1, 0, 1] := by
  simp [multiplyCoefficients, addCoefficients, linearCoefficients]
  grind

theorem f_coefficient_list : f = fromCoefficients [0, -4, 0, 1] := by
  funext k
  match k with
  | 0 | 1 | 2 | 3 => rfl
  | k+4 => simp [f, fromCoefficients]

theorem g_coefficient_list : g = fromCoefficients [-1, 0, 1] := by
  funext k
  match k with
  | 0 | 1 | 2 => rfl
  | k+3 => simp [g, fromCoefficients]

/-- Exact factorizations exhibit all roots, with no numerical approximations. -/
theorem f_factorization (x : Rat) : evaluate 3 f x = (x+2)*x*(x-2) := by
  rw [f_evaluation]
  grind

theorem g_factorization (x : Rat) : evaluate 2 g x = (x+1)*(x-1) := by
  rw [g_evaluation]
  grind

theorem f_roots (x : Rat) : evaluate 3 f x = 0 ↔ x = -2 ∨ x = 0 ∨ x = 2 := by
  rw [f_evaluation]
  grind

theorem g_roots (x : Rat) : evaluate 2 g x = 0 ↔ x = -1 ∨ x = 1 := by
  rw [g_evaluation]
  grind

/-- A factorization-based strict interlacing condition for a cubic and quadratic.
All five roots are distinct; the identities explicitly split both inputs. -/
def StrictlyInterlacing (F G : Polynomial) : Prop :=
  ∃ a b c d e : Rat, a < b ∧ b < c ∧ c < d ∧ d < e ∧
    (∀ x, evaluate 3 F x = (x-a)*(x-c)*(x-e)) ∧
    (∀ x, evaluate 2 G x = (x-b)*(x-d))

theorem strict_interlacing : StrictlyInterlacing f g := by
  refine ⟨-2, -1, 0, 1, 2, by decide, by decide, by decide, by decide, ?_, ?_⟩
  · intro x
    rw [f_evaluation]
    grind
  · intro x
    rw [g_evaluation]
    grind

/-- An explicit constant Bezout identity also proves coprimality. -/
theorem bezout_identity (x : Rat) :
    x * evaluate 3 f x + (3-x^2) * evaluate 2 g x = -3 := by
  rw [f_evaluation, g_evaluation]
  grind

/-- The same Bezout identity at the coefficient level, without evaluating x. -/
theorem bezout_coefficients :
    addCoefficients (multiplyCoefficients [0, 1] [0, -4, 0, 1])
      (multiplyCoefficients [3, 0, -1] [-1, 0, 1]) = [-3, 0, 0, 0, 0] := by
  simp [multiplyCoefficients, addCoefficients]
  grind

theorem no_common_root (x : Rat) : ¬ (evaluate 3 f x = 0 ∧ evaluate 2 g x = 0) := by
  intro ⟨hf, hg⟩
  have h := bezout_identity x
  rw [hf, hg] at h
  grind

/-- Entrywise display of the generated 3 by 4 Sylvester submatrix. -/
theorem generated_matrix :
    (List.range 3).map (fun r => (List.range 4).map (S r)) =
      [[1, 0, -4, 0], [1, 0, -1, 0], [0, 1, 0, -1]] := by
  decide

/-- The two relevant determinants come from different last-column selections. -/
theorem principal_minor_value : coefficientMinor S 3 0 = -3 := by
  simp [coefficientMinor, det, sum, S, sylvesterSubmatrix,
    shiftedCoefficient, f, g, List.range_succ]
  grind

theorem constant_minor_value : coefficientMinor S 3 1 = 0 := by
  simp [coefficientMinor, det, sum, S, sylvesterSubmatrix,
    shiftedCoefficient, f, g, List.range_succ]
  grind

theorem principal_coefficient_value : principalSubresultant 3 2 1 f g = -3 := by
  exact principal_minor_value

theorem first_subresultant_value (x : Rat) : subresultantValue 3 2 1 f g x = -3*x := by
  change sum 2 (fun j => coefficientMinor S 3 (1-j) * x^j) = -3*x
  simp [sum, List.range_succ, constant_minor_value, principal_minor_value]
  grind

/-- The disputed vanishing-equivalence clause, restricted to monic strictly
interlacing cubic/quadratic inputs and their actual order-three subresultant
coefficient minor and corresponding leading principal minor. -/
def VanishingEquivalence : Prop :=
  ∀ F G : Polynomial,
    HasDegree F 3 → HasDegree G 2 → monic F 3 → monic G 2 →
    StrictlyInterlacing F G →
    (coefficientMinor (sylvesterSubmatrix 3 2 1 F G) 3 1 = 0 ↔
      principalSubresultant 3 2 1 F G = 0)

/-- A genuine subresultant coefficient minor vanishes while its corresponding
principal minor is nonzero, even for strictly interlacing coprime inputs. -/
theorem counterexample :
    HasDegree f 3 ∧ HasDegree g 2 ∧ monic f 3 ∧ monic g 2 ∧
    StrictlyInterlacing f g ∧
    coefficientMinor S 3 1 = 0 ∧ principalSubresultant 3 2 1 f g ≠ 0 := by
  refine ⟨input_degrees.1, input_degrees.2.1, input_degrees.2.2.1,
    input_degrees.2.2.2, strict_interlacing, constant_minor_value, ?_⟩
  rw [principal_coefficient_value]
  decide

theorem conjecture_00000005613_false : ¬ VanishingEquivalence := by
  intro h
  have heq := h f g input_degrees.1 input_degrees.2.1 input_degrees.2.2.1
    input_degrees.2.2.2 strict_interlacing
  have hz := heq.mp constant_minor_value
  rw [principal_coefficient_value] at hz
  contradiction

#print axioms counterexample
#print axioms conjecture_00000005613_false
end TLMC5613
