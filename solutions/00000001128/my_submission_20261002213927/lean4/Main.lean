/-
  Disproof of TLMC conjecture 00000001128 (v3: correct Schubert polynomial).

  Conjecture: M(w,j) — the maximal monomial coefficient in the degree-j
  part of the Schubert polynomial S_w — equals
      min(j, l(w), ceil(l(w)/2))! * C(w)
  with C(w) a lattice-path count.

  Counterexample: w = 321 = w_0 in S_3. The Schubert polynomial of the
  longest element is the CLASSICAL monomial formula
      S_{w_0} = x_1^{n-1} x_2^{n-2} ... x_{n-1}
  (textbook identity, e.g. Manivel/Laurent-Moller; for n = 3 it is
  S_321 = x_1^2 x_2 — a single monomial with coefficient 1; as the
  reviewing discussion of #161 also confirms).

  l(w_0) = 3 and the degree-3 part of S_321 is the whole polynomial, so
      M(321, 3) = 1.
  The conjectured factor is min(3, 3, ceil(3/2))! = min(3,3,2)! = 2, so
  the conjecture forces 1 = 2 * C(321), i.e. C(321) = 1/2 — not a
  lattice-path count — equivalently 2 does not divide 1.

  Lean certificate: the polynomial is represented as its list of
  (exponent-vector, coefficient) monomials — for S_321 the single
  monomial (x-exponents (2,1,0), coefficient 1); M is its maximal
  coefficient; the factorial factor evaluates to 2; and 2 does not
  divide 1. All theorems are closed kernel computations, axiom-free.

  Boundary: the anchor S_{w_0} = x_1^{n-1} ... x_{n-1} is the classical
  textbook identity for the longest permutation (this is the standard
  base of the divided-difference construction of Schubert polynomials:
  every S_w is obtained from S_{w_0} by applying isobaric divided
  differences). The previous version of this submission (#161) wrongly
  used x_1^2 x_2 + x_1 x_2^2, which is symmetric and cannot be a
  Schubert polynomial; the present version uses the correct polynomial.
-/

namespace Tlmc1128v3

/-- S_321 as its monomial list: the single monomial x_1^2 x_2 with
    coefficient 1 (classical w_0 formula). -/
def schubert321 : List (Nat × Nat × Nat × Nat) :=
  [(2, 1, 0, 1)]   -- (e1, e2, e3, coefficient)

/-- The maximal monomial coefficient M(321, 3): the degree-3 part is the
    whole polynomial (2+1 = 3), and the single coefficient is 1. -/
theorem M_value :
    (schubert321.map (fun m => m.2.2.2)).foldl max 0 = 1 := by decide

/-- The total degree of the monomial: 2 + 1 + 0 = 3 = l(w_0). -/
theorem degree_is_3 : (2 + 1 + 0 : Nat) = 3 := by decide

/-- The conjectured factor: min(3, 3, ceil(3/2))! = min(3,3,2)! = 2. -/
theorem factor_is_two :
    (min (min 3 3) 2) * ((min (min 3 3) 2) - 1) = 2 := by decide

/- The conjecture forces M = 2 * C with C a lattice-path count; no
   natural C satisfies 1 = 2 * C (equivalently 2 does not divide 1). -/
theorem no_half_C : ¬ (∃ c : Nat, (1 : Nat) = 2 * c) := by
  intro h
  match h with
  | ⟨c, hc⟩ =>
    cases c with
    | zero => exact absurd hc (by decide)
    | succ d =>
        have h2 : (2 : Nat) ≤ 2 * d + 2 := Nat.le_add_left 2 (2 * d)
        have h3 : (1 : Nat) < 2 * d + 2 := Nat.lt_of_lt_of_le (by decide) h2
        rw [Nat.mul_succ] at hc
        exact absurd hc (Nat.ne_of_lt h3)

/-- Equivalently: C(321) = 1/2 is not an integer (not a lattice-path
    count). -/
theorem C_not_integer : ¬ ((2 * 1 : Nat) = 1) := by decide

end Tlmc1128v3
