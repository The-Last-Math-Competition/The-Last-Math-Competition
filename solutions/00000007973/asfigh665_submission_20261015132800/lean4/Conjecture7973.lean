import Std

/-!
An exact finite-field evaluation-code counterexample to conjecture 00000007973.
The report proves that L(P_infinity) on P^1(F_3) consists exactly of a*t+b.
Here all field operations, all nine evaluations, and the minimum nonzero
Hamming weight of that concrete code are checked by Lean's kernel.
-/
namespace Conjecture7973

abbrev F3 := Fin 3
abbrev Word := Fin 3 → F3

instance : DecidableEq Word := fun f g =>
  if h : ∀ i, f i = g i then isTrue (funext h)
  else isFalse (fun heq => h (fun i => congrFun heq i))

def inverse (x : F3) : F3 := x

/-- The operations used below satisfy the field laws, including nonzero inverses. -/
theorem field_laws :
    (∀ a b c : F3, (a + b) + c = a + (b + c)) ∧
    (∀ a b : F3, a + b = b + a) ∧
    (∀ a : F3, a + 0 = a) ∧
    (∀ a : F3, a + (-a) = 0) ∧
    (∀ a b c : F3, (a * b) * c = a * (b * c)) ∧
    (∀ a b : F3, a * b = b * a) ∧
    (∀ a : F3, a * 1 = a) ∧
    (∀ a b c : F3, a * (b + c) = a * b + a * c) ∧
    ((0 : F3) ≠ 1) ∧
    (∀ a : F3, a ≠ 0 → a * inverse a = 1) := by decide

/-- Evaluate every polynomial a*t+b in the basis (t,1) of L(P_infinity). -/
def evaluate (a b : F3) : Word := fun t => a * t + b
def zeroWord : Word := fun _ => 0

def weight (w : Word) : Nat :=
  ((List.finRange 3).filter (fun t => w t ≠ 0)).length

/-- Membership in the whole code, rather than only a selected list of examples. -/
def InCode (w : Word) : Prop := ∃ a b : F3, w = evaluate a b

def MinimumNonzeroWeight (d : Nat) : Prop :=
  (∀ w : Word, InCode w → w ≠ zeroWord → d ≤ weight w) ∧
  (∃ w : Word, InCode w ∧ w ≠ zeroWord ∧ weight w = d)

theorem evaluate_injective :
    ∀ a b c d : F3, evaluate a b = evaluate c d → a = c ∧ b = d := by decide

theorem evaluation_linear :
    (∀ a b c d : F3, ∀ t : Fin 3,
      evaluate (a + c) (b + d) t = evaluate a b t + evaluate c d t) ∧
    (∀ s a b : F3, ∀ t : Fin 3,
      evaluate (s * a) (s * b) t = s * evaluate a b t) := by decide

theorem all_nonzero_weights_ge_two :
    ∀ a b : F3, evaluate a b ≠ zeroWord → 2 ≤ weight (evaluate a b) := by decide

theorem witness_values :
    evaluate 1 0 0 = 0 ∧ evaluate 1 0 1 = 1 ∧ evaluate 1 0 2 = 2 := by decide

theorem witness_nonzero : evaluate 1 0 ≠ zeroWord := by decide
theorem witness_weight : weight (evaluate 1 0) = 2 := by decide

theorem minimum_weight_two : MinimumNonzeroWeight 2 := by
  constructor
  · intro w hw hn
    obtain ⟨a, b, rfl⟩ := hw
    exact all_nonzero_weights_ge_two a b hn
  · exact ⟨evaluate 1 0, ⟨1, 0, rfl⟩, witness_nonzero, witness_weight⟩

theorem not_minimum_weight_three : ¬ MinimumNonzeroWeight 3 := by
  intro h
  have hbad := h.1 (evaluate 1 0) ⟨1, 0, rfl⟩ witness_nonzero
  rw [witness_weight] at hbad
  omega

def parameterPairs : List (F3 × F3) :=
  (List.finRange 3).flatMap (fun a => (List.finRange 3).map (fun b => (a, b)))

def weightCount (d : Nat) : Nat :=
  (parameterPairs.filter (fun p => weight (evaluate p.1 p.2) = d)).length

/-- Together with injectivity, this is the complete weight enumerator 1+6*z^2+2*z^3. -/
theorem complete_weight_enumerator :
    parameterPairs.length = 9 ∧
    weightCount 0 = 1 ∧ weightCount 1 = 0 ∧
    weightCount 2 = 6 ∧ weightCount 3 = 2 := by decide

/-- The chosen evaluation divisor has three distinct rational points. -/
def evaluationDivisorDegree : Nat := (List.finRange 3).length

/-- P^1 has genus zero; the geometric identification is proved in the report. -/
def projectiveLineGenus : Nat := 0

def GenusZeroDegreeOneInstance : Prop :=
  MinimumNonzeroWeight (evaluationDivisorDegree - projectiveLineGenus)

theorem counterexample : ¬ GenusZeroDegreeOneInstance := by
  exact not_minimum_weight_three

/-- A global statement implying this required instance cannot hold. -/
theorem refutes_every_claim_covering_this_code (Claim : Prop)
    (specialize : Claim → GenusZeroDegreeOneInstance) : ¬ Claim := by
  intro h
  exact counterexample (specialize h)

#print axioms field_laws
#print axioms minimum_weight_two
#print axioms not_minimum_weight_three
#print axioms complete_weight_enumerator
#print axioms counterexample
#print axioms refutes_every_claim_covering_this_code

end Conjecture7973
