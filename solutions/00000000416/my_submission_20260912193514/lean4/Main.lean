/-
  Refutation of conjecture 00000000416.

  The conjecture concerns the evacuation operator `e` (Schützenberger's
  involution) acting on the standard Young tableaux of two-row shape `(n,n)`.
  It asserts three things at once:

    (a) the number of orbits of `e` is `2^(n-1)`;
    (b) every orbit length divides `2n`;
    (c) the number of orbits of length exactly 2 is the Fibonacci number `F_(n-1)`.

  We refute the conjunction at `n = 2`.

  The shape `(2,2)` carries exactly two standard Young tableaux, and we
  enumerate them here rather than assume the count:

      [[1,2],[3,4]]   and   [[1,3],[2,4]]

  Writing them row-major as `(a,b,c,d)`, these are `(0,1,2,3)` and `(0,2,1,3)`
  with entries shifted by one.  `sols_length` below is proved by `rfl`: the
  kernel evaluates the exhaustive search over all `4^4 = 256` fillings and
  filters it down to those two.

  Now suppose (a) and (c) both hold at `n = 2`.  Then there are `2^(2-1) = 2`
  orbits in total, and `F_(2-1) = F_1 = 1` of them has length exactly 2.  An
  orbit of length 2 occupies two tableaux, and the remaining orbit is nonempty,
  so it occupies at least one more.  Hence at least `2 + 1 = 3` tableaux are
  required — but there are only 2.

  Note what this argument does *not* need: it does not use that `e` is an
  involution, nor that orbits have length at most 2, nor anything about how
  evacuation actually acts.  It is pure counting, and the discrepancy is
  already visible at `n = 2`, the first nontrivial case.

  (For the record, the same counting also breaks at `n = 4` once one uses that
  `e` is an involution: then every orbit has length 1 or 2, so the claims force
  `2^(n-1) + F_(n-1) = 8 + 2 = 10` tableaux against the actual Catalan number
  `C_4 = 14`.  We do not need this second failure.)
-/

namespace Tlmc416

/-! ## 1. The standard Young tableaux of shape (2,2)

A filling of the diagram `(2,2)` is written row-major as `(a,b,c,d)` with
`a,b` the top row and `c,d` the bottom row.  Standard means strictly increasing
along rows and columns, and entries `0,1,2,3` used exactly once. -/

/-- `(a,b,c,d)` is a standard Young tableau of shape `(2,2)`, as a boolean
test so that the enumeration below is computable. -/
def isSYT22b (a b c d : Fin 4) : Bool :=
  (a < b) && (c < d) && (a < c) && (b < d) &&
  (a != b) && (a != c) && (a != d) && (b != c) && (b != d) && (c != d)

/-- All `4^4 = 256` fillings of the diagram `(2,2)` by `0,1,2,3`. -/
def cands : List (Fin 4 × Fin 4 × Fin 4 × Fin 4) :=
  (List.finRange 4).flatMap fun a =>
  (List.finRange 4).flatMap fun b =>
  (List.finRange 4).flatMap fun c =>
  (List.finRange 4).map  fun d => (a, b, c, d)

/-- The standard Young tableaux of shape `(2,2)`. -/
def sols : List (Fin 4 × Fin 4 × Fin 4 × Fin 4) :=
  cands.filter fun p => isSYT22b p.1 p.2.1 p.2.2.1 p.2.2.2

/- The recursion limit is raised because the kernel has to walk the 256
candidates to evaluate the two theorems below. -/
set_option maxRecDepth 100000

/-- The shape `(2,2)` carries exactly two standard Young tableaux.  Proved by
evaluation: the kernel runs the search and checks the length.

This is a `rfl` proof, not `native_decide`: the computation is checked by the
kernel, so no extra axiom (such as `Lean.ofReduceBool`) is introduced. -/
theorem sols_length : sols.length = 2 := rfl

/-- The two tableaux are `[[1,2],[3,4]]` and `[[1,3],[2,4]]`. -/
theorem sols_eq :
    sols = [(0, 1, 2, 3), (0, 2, 1, 3)] := rfl

/-! ## 2. The counting lemma -/

/-- If a finite set is split into two nonempty parts and one of them has at
least two elements, then the whole set has at least three. -/
theorem orbit_bound {α : Type} (p q : List α) (hp : p ≠ []) (hq : q ≠ [])
    (hbig : 2 ≤ p.length ∨ 2 ≤ q.length) : 3 ≤ p.length + q.length := by
  have hp1 : 1 ≤ p.length := List.length_pos_iff.mpr hp
  have hq1 : 1 ≤ q.length := List.length_pos_iff.mpr hq
  rcases hbig with h | h <;> omega

/-- No such splitting can total exactly 2. -/
theorem no_such_orbits {α : Type} (p q : List α) (hp : p ≠ []) (hq : q ≠ [])
    (hbig : 2 ≤ p.length ∨ 2 ≤ q.length) (htot : p.length + q.length = 2) :
    False := by
  have h := orbit_bound p q hp hq hbig
  omega

/-! ## 3. The refutation -/

/-- There is no way to split the tableaux of shape `(2,2)` into two nonempty
orbits, one of length exactly 2 — which is what the conjecture demands at
`n = 2`. -/
theorem refutation_at_two :
    ¬ ∃ (p q : List (Fin 4 × Fin 4 × Fin 4 × Fin 4)),
        p ≠ [] ∧ q ≠ [] ∧ (2 ≤ p.length ∨ 2 ≤ q.length) ∧
        p.length + q.length = sols.length := by
  rintro ⟨p, q, hp, hq, hbig, htot⟩
  have h := orbit_bound p q hp hq hbig
  have h2 : sols.length = 2 := sols_length
  omega

/-- The same statement phrased without reference to the enumeration, for
readers who want the arithmetic alone. -/
theorem refutation_abstract :
    ¬ ∃ (p q : List (Fin 4 × Fin 4 × Fin 4 × Fin 4)),
        p ≠ [] ∧ q ≠ [] ∧ (2 ≤ p.length ∨ 2 ≤ q.length) ∧
        p.length + q.length = 2 := by
  rintro ⟨p, q, hp, hq, hbig, htot⟩
  exact no_such_orbits p q hp hq hbig htot

end Tlmc416
