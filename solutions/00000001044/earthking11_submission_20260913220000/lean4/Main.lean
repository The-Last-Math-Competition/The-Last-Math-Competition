/-
  Disproof of conjecture `00000001044`: formalisation.

  Conjecture (as filed):

    Definition: the value set of the Dickson polynomial D_n(x,a) is its image
    over F_q.
    Conjecture: when gcd(n, q²−1) = d > 1 (the non-permutation case), the
    minimum size of the complement of the value set is (q−1)/d, attained at
    a = 0 (the monomial x^n); every other a gives a strictly larger value set.

  We formalise an unconditional counterexample at the cleanest witness and
  several further breakages.

  Dickson polynomials use the recursion
        D_0 = 2,   D_1 = x,   D_k = x·D_{k-1} − a·D_{k-2}     (k ≥ 2),
  so that D_2(x,a) = x² − 2a and D_3(x,a) = x³ − 3a·x.

  * Primary witness: (q, n) = (3, 2).  Then
        d = gcd(n, q²−1) = gcd(2, 8) = 2 > 1   and   (q−1)/d = 2/2 = 1.
    But all three a ∈ {0,1,2} give complement size 1: the value sets are
    {0,1}, {1,2}, {0,2}, each of size 2.  So
      – a = 0 is NOT the unique minimiser, and
      – the other a do NOT give a strictly larger value set (they tie a = 0).
    The second clause of the conjecture is thus false as stated.

  * Same phenomenon at (5,2) and (7,2): all five / all seven a give the same
    complement size, 2 and 3 respectively.

  * Opposite direction at (7,3): d = gcd(3,48) = 3, (q−1)/d = 2, but a = 0
    gives the LARGEST complement (4) and every nonzero a gives 2.  This is the
    exact reverse of the conjecture's "attained at a = 0".

  * Further breakages: (5,3) has d = 3 > 1 yet a = 0 permutes F_5 (complement
    0), and (q−1)/d = 4/3 is not even an integer; (5,4) has d = 4 and
    (q−1)/d = 1, but the true minimum complement is 2 (attained at a = 2, 3),
    so the value (q−1)/d is never attained; (3,4) has d = 4 and a = 0 ties
    a = 2.

  The file uses CORE LEAN ONLY (`import Std`); no Mathlib, `Finset`, `ZMod`,
  `Rat`, or `sorry`.  Residues of F_q are plain `Nat`s reduced with `% q`, and
  every finite statement is closed by `decide`.  Note that `q` must be a
  variable `Nat` (not `Fin q`) so that `OfNat` instances are available.
-/

import Std

set_option maxRecDepth 1000000
set_option linter.unusedVariables false

namespace Tlmc1044

/-! ## Dickson polynomials over `F_q`, represented on `Nat` residues -/

/-- The Dickson polynomial `D_n(x,a)` over `F_q`, by the recursion
`D_0 = 2`, `D_1 = x`, `D_k = x·D_{k-1} − a·D_{k-2}`, with every intermediate
value reduced modulo `q` (an argument `x` is expected in `{0, …, q-1}`). -/
def D (q : Nat) : Nat → Nat → Nat → Nat
  | 0,   a, x => 2 % q
  | 1,   a, x => x % q
  | k+2, a, x => ((x * D q (k+1) a x) + (q - (a * D q k a x) % q)) % q

/-- The value set of `D_n(·, a)` on `F_q`, as a duplicate-free list of the
residues it attains (so its `length` is the cardinality of the image). -/
def valueSet (q n a : Nat) : List Nat :=
  ((List.range q).map (D q n a)).eraseDups

/-- The size of the complement of the value set inside `F_q`. -/
def compSize (q n a : Nat) : Nat := q - (valueSet q n a).length

/-- `biggerValueSet q n a` is `true` exactly when `a` gives a *strictly larger
value set* than the monomial `a = 0` (equivalently a strictly smaller
complement — the direction claimed for "every other a"). -/
def biggerValueSet (q n a : Nat) : Bool :=
  (valueSet q n 0).length < (valueSet q n a).length

/-- Bounded existential: some nonzero `a < q` ties `a = 0` in complement size. -/
def tieWithZero (q n : Nat) : Bool :=
  (List.range q).any fun a => (a != 0) && (compSize q n a == compSize q n 0)

/-- Bounded existential: some nonzero `a < q` has a *strictly smaller
complement* than `a = 0` (i.e. a strictly larger value set). -/
def nonzeroBeatsZero (q n : Nat) : Bool :=
  (List.range q).any fun a => (a != 0) && (compSize q n a < compSize q n 0)

/-- Bounded minimum of the complement size over `a < q`. -/
def minComp (q n : Nat) : Nat :=
  ((List.range q).map (compSize q n)).foldr min 1000000

/-! ## Primary witness: `(q, n) = (3, 2)`, `d = gcd(2, 8) = 2 > 1` -/

/-- `d = gcd(n, q²−1) = gcd(2, 8) = 2`. -/
theorem q3n2_d : Nat.gcd 2 (3 * 3 - 1) = 2 := by decide

/-- The hypothesis `d > 1` of the conjecture. -/
theorem q3n2_d_gt_one : Nat.gcd 2 (3 * 3 - 1) > 1 := by decide

/-- The conjectured minimum `(q−1)/d = (3−1)/2 = 1`. -/
theorem q3n2_formula : (3 - 1) / 2 = 1 := by decide

/-- `a = 0` attains complement `1`, the conjectured value. -/
theorem q3n2_a0 : compSize 3 2 0 = 1 := by decide

/-- `a = 1` also attains complement `1`: the value set `{1,2}` has size `2`. -/
theorem q3n2_a1 : compSize 3 2 1 = 1 := by decide

/-- `a = 2` also attains complement `1`: the value set `{0,2}` has size `2`. -/
theorem q3n2_a2 : compSize 3 2 2 = 1 := by decide

/-- `a = 0` does attain the conjectured formula value. -/
theorem q3n2_a0_is_formula : compSize 3 2 0 = (3 - 1) / 2 := by decide

/-- `a = 1` TIES `a = 0` in complement size — it does not give a strictly
larger value set. -/
theorem q3n2_a1_ties : compSize 3 2 1 = compSize 3 2 0 := by decide

/-- `a = 2` TIES `a = 0` in complement size. -/
theorem q3n2_a2_ties : compSize 3 2 2 = compSize 3 2 0 := by decide

/-- `a = 1` does not give a strictly larger value set than `a = 0`. -/
theorem q3n2_a1_not_bigger : biggerValueSet 3 2 1 = false := by decide

/-- `a = 2` does not give a strictly larger value set than `a = 0`. -/
theorem q3n2_a2_not_bigger : biggerValueSet 3 2 2 = false := by decide

/-- No `a ∈ F_3` gives a strictly larger value set than `a = 0`: the second
clause of the conjecture ("every other a gives a strictly larger value set")
fails at every nonzero `a` simultaneously. -/
theorem q3n2_no_a_strictly_bigger :
    (List.range 3).all (fun a => !(biggerValueSet 3 2 a)) = true := by decide

/-- `a = 0` is not the unique minimiser: the nonzero `a = 1` attains the same
complement size. -/
theorem q3n2_nonunique :
    ∃ a, a < 3 ∧ a ≠ 0 ∧ compSize 3 2 a = compSize 3 2 0 :=
  ⟨1, by decide, by decide, by decide⟩

/-- The bounded tie detector fires at `(3,2)`: at least one nonzero `a` has
exactly the complement size of `a = 0`. -/
theorem q3n2_tie : tieWithZero 3 2 = true := by decide

/-- The minimum complement over all `a ∈ F_3` is `1`, the conjectured value —
but it is attained by more than one `a`. -/
theorem q3n2_min : minComp 3 2 = 1 := by decide

/-- The packaged refutation, exhibited concretely at `(q,n) = (3,2)`: the
hypothesis `d = gcd(n, q²−1) > 1` holds, `(q−1)/d = 1`, `a = 0` attains it,
but the two other `a` tie `a = 0` and do not give a strictly larger value set.
Hence conjecture `00000001044` is false as stated. -/
theorem conjecture_00000001044_false :
    Nat.gcd 2 (3 * 3 - 1) > 1 ∧
    (3 - 1) / 2 = 1 ∧
    compSize 3 2 0 = 1 ∧
    compSize 3 2 1 = compSize 3 2 0 ∧
    compSize 3 2 2 = compSize 3 2 0 ∧
    biggerValueSet 3 2 1 = false ∧
    biggerValueSet 3 2 2 = false ∧
    tieWithZero 3 2 = true :=
  ⟨q3n2_d_gt_one, q3n2_formula, q3n2_a0, q3n2_a1_ties, q3n2_a2_ties,
    q3n2_a1_not_bigger, q3n2_a2_not_bigger, q3n2_tie⟩

/-! ## The same behaviour at `(5, 2)` and `(7, 2)`, both with `d = 2` -/

/-- `d = gcd(2, 24) = 2`. -/
theorem q5n2_d : Nat.gcd 2 (5 * 5 - 1) = 2 := by decide

/-- The conjectured value `(5−1)/2 = 2`. -/
theorem q5n2_formula : (5 - 1) / 2 = 2 := by decide

/-- All five `a ∈ F_5` give complement `2`: no `a` is distinguished. -/
theorem q5n2_all : ∀ a, a < 5 → compSize 5 2 a = 2 := by decide

/-- The minimum complement at `(5,2)` is `2`, attained by every `a`. -/
theorem q5n2_min : minComp 5 2 = 2 := by decide

/-- Some nonzero `a` ties `a = 0` at `(5,2)`. -/
theorem q5n2_tie : tieWithZero 5 2 = true := by decide

/-- No `a ∈ F_5` gives a strictly larger value set than `a = 0`. -/
theorem q5n2_no_a_strictly_bigger :
    (List.range 5).all (fun a => !(biggerValueSet 5 2 a)) = true := by decide

/-- `d = gcd(2, 48) = 2`. -/
theorem q7n2_d : Nat.gcd 2 (7 * 7 - 1) = 2 := by decide

/-- The conjectured value `(7−1)/2 = 3`. -/
theorem q7n2_formula : (7 - 1) / 2 = 3 := by decide

/-- All seven `a ∈ F_7` give complement `3`: no `a` is distinguished. -/
theorem q7n2_all : ∀ a, a < 7 → compSize 7 2 a = 3 := by decide

/-- The minimum complement at `(7,2)` is `3`. -/
theorem q7n2_min : minComp 7 2 = 3 := by decide

/-- Some nonzero `a` ties `a = 0` at `(7,2)`. -/
theorem q7n2_tie : tieWithZero 7 2 = true := by decide

/-! ## The reversal at `(7, 3)`: `a = 0` gives the LARGEST complement -/

/-- `d = gcd(3, 48) = 3`. -/
theorem q7n3_d : Nat.gcd 3 (7 * 7 - 1) = 3 := by decide

/-- The conjectured minimum `(7−1)/3 = 2`. -/
theorem q7n3_formula : (7 - 1) / 3 = 2 := by decide

/-- At the monomial `a = 0` the value set is the set of cubes `{0,1,6}`, so the
complement has size `4`. -/
theorem q7n3_a0 : compSize 7 3 0 = 4 := by decide

/-- At `a = 1` the value set is `{0,2,3,4,5}`, complement `2`. -/
theorem q7n3_a1 : compSize 7 3 1 = 2 := by decide

/-- `a = 0` has a strictly LARGER complement than `a = 1`: the conjecture has
the direction backwards at `(7,3)`. -/
theorem q7n3_reversal : compSize 7 3 0 > compSize 7 3 1 := by decide

/-- `a = 0` has a complement strictly larger than the conjectured minimum
`(q−1)/d = 2`. -/
theorem q7n3_a0_exceeds_formula : compSize 7 3 0 > (7 - 1) / 3 := by decide

/-- `a = 0` maximises the complement among all `a ∈ F_7` — the exact opposite
of "attained at a = 0" for the minimum. -/
theorem q7n3_a0_largest : ∀ a, a < 7 → compSize 7 3 a ≤ compSize 7 3 0 := by decide

/-- Every `a ∈ F_7` other than `a = 0` beats `a = 0` here: this is precisely
the case the conjecture claims cannot happen. -/
theorem q7n3_nonzero_beats : nonzeroBeatsZero 7 3 = true := by decide

/-! ## Further breakages of the formula and of the `d > 1` characterisation -/

/-- `(5,3)`: `d = gcd(3, 24) = 3 > 1`, yet the monomial `x³` permutes `F_5`
(the value set is all of `F_5`, so the complement has size `0`). -/
theorem q5n3_a0_permutes : compSize 5 3 0 = 0 := by decide

/-- At `(5,3)` the conjectured value `(q−1)/d = 4/3` is not an integer: `d` need
not divide `q − 1`. -/
theorem q5n3_d_not_dvd : ¬ (3 ∣ (5 - 1)) := by decide

/-- The true minimum complement at `(5,3)` is `0`, not the (non-integer)
value `(q−1)/d`. -/
theorem q5n3_min : minComp 5 3 = 0 := by decide

/-- `(5,4)`: `d = gcd(4, 24) = 4`, `(q−1)/d = 1`. -/
theorem q5n4_d : Nat.gcd 4 (5 * 5 - 1) = 4 := by decide

/-- At `a = 0` the complement is `3`. -/
theorem q5n4_a0 : compSize 5 4 0 = 3 := by decide

/-- At `a = 2` the complement is `2`, strictly better than `a = 0`. -/
theorem q5n4_a2 : compSize 5 4 2 = 2 := by decide

/-- Some nonzero `a` strictly beats `a = 0` at `(5,4)`. -/
theorem q5n4_beats : nonzeroBeatsZero 5 4 = true := by decide

/-- The true minimum at `(5,4)` is `2`, not the conjectured `(q−1)/d = 1`. -/
theorem q5n4_min : minComp 5 4 = 2 := by decide

/-- At `(5,4)` no `a ∈ F_5` attains the conjectured value `(5−1)/4 = 1`. -/
theorem q5n4_no_a_attains_formula :
    (List.range 5).all (fun a => compSize 5 4 a != (5 - 1) / 4) = true := by decide

/-- `(3,4)`: `d = gcd(4, 8) = 4`. -/
theorem q3n4_d : Nat.gcd 4 (3 * 3 - 1) = 4 := by decide

/-- At `(3,4)` the values `a = 0` and `a = 2` tie. -/
theorem q3n4_tie : tieWithZero 3 4 = true := by decide

/-- The conjectured value `(3−1)/4` is not an integer here either: `4 ∤ 2`. -/
theorem q3n4_d_not_dvd : ¬ (4 ∣ (3 - 1)) := by decide

/-! ## Machine-checked tables matching the Python reproduction -/

/-- Complement sizes for `a = 0,1,2` at `(3,2)`: all equal `1`. -/
theorem table_3_2 : (List.range 3).map (compSize 3 2) = [1, 1, 1] := by decide

/-- Complement sizes for `a = 0,…,4` at `(5,2)`: all equal `2`. -/
theorem table_5_2 : (List.range 5).map (compSize 5 2) = [2, 2, 2, 2, 2] := by decide

/-- Complement sizes for `a = 0,…,6` at `(7,2)`: all equal `3`. -/
theorem table_7_2 :
    (List.range 7).map (compSize 7 2) = [3, 3, 3, 3, 3, 3, 3] := by decide

/-- Complement sizes for `a = 0,…,6` at `(7,3)`: `a = 0` gives `4`, every
nonzero `a` gives `2`. -/
theorem table_7_3 :
    (List.range 7).map (compSize 7 3) = [4, 2, 2, 2, 2, 2, 2] := by decide

/-- Complement sizes for `a = 0,…,4` at `(5,4)`: `a = 0` and `a = 4` give `3`,
`a = 2,3` give `2`, `a = 1` gives `3`. -/
theorem table_5_4 : (List.range 5).map (compSize 5 4) = [3, 3, 2, 2, 3] := by decide

end Tlmc1044
