import Std

/-!
# Disproof of conjecture `00000001752` (core Lean formalisation)

Conjecture `00000001752` (auto-generated) reads: the Mark values of primitive
permutation characters of `S_n` are the averages of fixed points by subset size,
and in the 2-transitive case they satisfy the closed form

    M_k = k! * S(n,k) / |G|,

"given by the Burnside average of subset counts", where `S(n,k)` is a Stirling
number of the second kind and `|G| = n!` is the order of `S_n`.

The file itself specifies the right-hand side via a *Burnside average*, so we
take the asserted equation literally:

    (1/|S_n|) * sum_{g in S_n} #{k-subsets fixed by g}  =  k! * S(n,k) / n!.

For `S_n` acting on `k`-subsets the action is transitive (for `1 ≤ k ≤ n-1`), so
by Burnside's lemma the left-hand side is the number of orbits, which is `1`.
For `n = 3`, `k = 1` (the natural sharply 2-transitive action on three points)
both sides share the denominator `|S_3| = 6`, so the equation is the integer
statement

    sum_{g in S_3} #{singletons fixed by g}  =  1! * S(3,1),

i.e. `6 = 1`, which is false.  This file formalises exactly that.

Core Lean only (`import Std`), no Mathlib, no `Finset`, no `sorry`, and no
`native_decide` (the concrete evaluations below are `rfl`, so the audit reports
only `propext`).
-/

namespace Tlmc1752

/-- Boolean test "`f` is a permutation of `Fin 3`": its image has three distinct
elements.  (`Finset` is not available under `import Std`, so we work with
`List`.) -/
def isPerm (f : Fin 3 → Fin 3) : Bool :=
  ((List.finRange 3).map f).eraseDups.length == 3

/-- All `3^3 = 27` functions `Fin 3 → Fin 3`, enumerated by their value table. -/
def allFuns : List (Fin 3 → Fin 3) :=
  List.flatMap (fun a =>
    List.flatMap (fun b =>
      List.map (fun c =>
        fun i => if i = 0 then a else if i = 1 then b else c)
        (List.finRange 3))
      (List.finRange 3))
    (List.finRange 3)

/-- The six permutations of `Fin 3`, i.e. the elements of `S_3`. -/
def perms : List (Fin 3 → Fin 3) := allFuns.filter isPerm

/-- For `k = 1`, a permutation fixes the singleton `{s}` iff it fixes `s`, so
the number of fixed `1`-subsets of `f` is the number of fixed points of `f`. -/
def fixCount (f : Fin 3 → Fin 3) : Nat :=
  List.countP (fun s => f s == s) (List.finRange 3)

/-- Numerator of the Burnside average over `S_3` acting on `1`-subsets:
`sum_{g in S_3} Fix_1(g)`.  The Burnside average itself is this divided by
`perms.length = |S_3| = 6`. -/
def burnsideSum : Nat := (perms.map fixCount).sum

/-- Factorial, defined by hand (`Nat.factorial` is not available under
`import Std`). -/
def fact : Nat → Nat
  | 0 => 1
  | n + 1 => (n + 1) * fact n

/-- Stirling numbers of the second kind, by the standard recurrence
(`S(0,0) = 1`, `S(0,k+1) = 0`, `S(n+1,0) = 0`,
`S(n+1,k+1) = (k+1) * S(n,k+1) + S(n,k)`). -/
def stirling2 : Nat → Nat → Nat
  | 0, 0 => 1
  | 0, _ + 1 => 0
  | _ + 1, 0 => 0
  | n + 1, k + 1 => (k + 1) * stirling2 n (k + 1) + stirling2 n k

/-! ## Concrete evaluations (`rfl`, i.e. kernel computation, no axioms) -/

/-- `S_3` has `6` elements. -/
theorem perms_length : perms.length = 6 := rfl

/-- The Burnside numerator at `k = 1` is `6`: the fixed-point counts of the six
permutations of `Fin 3` are `3, 1, 1, 1, 0, 0`, whose sum is `6`. -/
theorem burnsideSum_eq : burnsideSum = 6 := rfl

/-- The conjecture's right-hand numerator is `1! * S(3,1) = 1 * 1 = 1`. -/
theorem formula_val : fact 1 * stirling2 3 1 = 1 := rfl

/-- Burnside's average equals the number of orbits, here `1`: the numerator
`burnsideSum` equals the group order `perms.length`. -/
theorem burnside_average_is_one : burnsideSum = perms.length := by
  rw [perms_length, burnsideSum_eq]

/-- **The claimed closed form fails.**  The Burnside numerator is `6`, while the
conjectured formula gives `1! * S(3,1) = 1`; equivalently the Burnside average
is `6/6 = 1` whereas the formula is `1/6`.  Since `6 ≠ 1` (and both sides share
the denominator `6`), `1 ≠ 1/6`. -/
theorem mismatch : burnsideSum ≠ fact 1 * stirling2 3 1 := by
  rw [burnsideSum_eq, formula_val]
  decide

/-- The same mismatch in the unit-fraction form `1 ≠ 1/6`, cross-multiplied:
`1 * 6 = 6` while `1 * 1 = 1`, and `6 ≠ 1`.  (The Burnside average is
`burnsideSum / 6 = 6 / 6 = 1`, i.e. `1/1`; the conjectured formula is
`(1! * S(3,1)) / 6 = 1/6`.) -/
theorem one_ne_one_sixth_cross : (1 : Nat) * 6 ≠ (1 : Nat) * 1 := by
  decide

end Tlmc1752
