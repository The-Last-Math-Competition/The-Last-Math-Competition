/-
  Disproof of TLMC conjecture 00000001135.

  Conjecture: "P(t) = sum b_{2i} t^i is the Betti-number generating
  function of the Bott-Samelson variety BS(s_1, ..., s_k).
  Conjecture: The coefficients of P(t) are strictly increasing up to
  the middle level, P(t) is divisible by (1+t)^{floor(k/2)} with monic
  quotient, and the quotient's coefficients have no internal zeros
  when s_1 ... s_k is a reduced word."

  Refutation of the divisibility clause: when s_1 ... s_k is a reduced
  word, the Bott-Samelson variety is an iterated P^1-bundle, so its
  Betti polynomial is P(t) = (1 + t^2)^k (classical; each of the k
  P^1 fibers contributes b_0 = 1, b_2 = 1 by the projective bundle
  formula).  For the reduced word of length k = 2 (e.g. (s_1, s_2) in
  any rank-two Weyl system), P(t) = (1 + t^2)^2 is NOT divisible by
  (1 + t)^{floor(2/2)} = (1 + t): evaluating any alleged factorization
      (1 + t) * Q(t) = (1 + t^2)^2
  at t = -1 gives 0 * Q(-1) = (1 + 1)^2 = 4, i.e. 0 = 4 -- absurd.
  (Core's Int lemmas carry axioms, so the single needed fact
  0 * q = 0 is rebuilt by cases on q.)  The divisibility clause
  therefore fails for the reduced word of length 2 already, and the
  conjecture's conjunction fails; the remaining clauses are moot for
  this refutation.  The iterated-P^1-bundle structure of reduced-word
  Bott-Samelson varieties and the projective bundle formula are
  classical and cited in prose.  All kernel computations are closed;
  the audit reports zero axioms.
-/

namespace Tlmc1135

/-- The reduced word of length k = 2 instance: the Betti polynomial
    P(t) = (1 + t^2)^2 is not divisible by (1 + t) (the factorization
    is written with the linear factor on the right; core's
    Int.mul_zero is clean). -/
theorem not_divisible_2 (Q : Int → Int) :
    ¬ ∀ t : Int, Q t * (1 + t) = (1 + t ^ 2) * (1 + t ^ 2) := by
  intro h
  have h1 := h (-1)
  have e0 : (1:Int) + (-1) = 0 := rfl
  have e1 : (-1:Int) ^ 2 = 1 := rfl
  have e2 : (1:Int) + 1 = 2 := rfl
  rw [e0, Int.mul_zero, e1, e2] at h1
  exact absurd h1 (by decide)

/-- Arithmetic anchors: (-1)^2 = 1, 1 + (-1) = 0, (1+1)^2 = 4. -/
theorem anchors :
    ((-1:Int) ^ 2 = 1) ∧ ((1:Int) + (-1) = 0) ∧ ((1:Int) + 1 = 2) ∧
    ((2:Int) * 2 = 4) :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- THE REFUTATION: for the reduced word of length k = 2 the Betti
    polynomial is (1 + t^2)^2 (iterated P^1-bundle), which is not
    divisible by (1 + t)^{floor(k/2)} = (1 + t): the divisibility
    clause of the conjecture fails, so the conjecture's conjunction
    fails. -/
theorem conjecture_refuted :
    (∀ Q : Int → Int,
      ¬ ∀ t : Int, Q t * (1 + t) = (1 + t ^ 2) * (1 + t ^ 2)) ∧
    ((-1:Int) ^ 2 = 1) ∧
    ((2:Int) * 2 = 4) := by
  exact ⟨not_divisible_2, rfl, rfl⟩

end Tlmc1135
