set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

/-!
# Disproof of TLMC conjecture 00000008420 (transitive-KTS clause)

We construct an explicit point-transitive Kirkman triple system of order 9,
namely the line system of the affine plane `AG(2,3)`.  Since `9 < 15`, the
conjecture clause "the smallest order of a KTS with a transitive automorphism
is the point-transitive type of order 15" is false.

Everything is a finite computation over the 9 points and 12 lines, so every
theorem below is proved by `decide` from a single closed Boolean expression.
No axioms, no `sorry`, and no dependency beyond the Lean 4 core.
-/

namespace Tlmc8420

/-! ## The affine plane AG(2,3)

The field `F_3` is modelled as `Fin 3` with wrapping (mod 3) arithmetic, which
carries exactly the additive structure of `ZMod 3` used here.  A point of the
affine plane is a pair in `Fin 3 x Fin 3`; there are 9 points. -/

/-- Points of the affine plane `AG(2,3)`, i.e. elements of `F_3^2`. -/
def Point := Fin 3 × Fin 3

instance : BEq Point := ⟨fun a b => a.1 == b.1 && a.2 == b.2⟩

/-- The nine points, listed explicitly: `(x, y)` with `x, y in F_3`.
(Built from `List.finRange` rather than numeral literals so that every
definition below is axiom-free: the core `OfNat (Fin n)` instances are
elaborated with `propext`, while `List.finRange` is not.) -/
def points : List Point :=
  (List.finRange 3).flatMap (fun x => (List.finRange 3).map (fun y => (x, y)))

/-- The 12 lines, indexed by `k : Nat` with the encoding
* `k = 3*m + b` for `k < 9`:  the graph `{(x, m*x + b) : x in F_3}` (slope `m`, intercept `b`);
* `k = 9 + c` for `k <= 11`: the vertical line `{(c, y) : y in F_3}`.

`lineMem k p` says that point `p` lies on line `k`. -/
def lineMem (k : Nat) (p : Point) : Bool :=
  if k < 9 then
    (k / 3 * p.1.val + k % 3) % 3 == p.2.val
  else
    p.1.val == (k - 9) % 3

/-- All 12 line indices. -/
def lines : List Nat := List.range 12

/-! ## (a) Steiner triple system

Every pair of distinct points lies on exactly one line: with 36 unordered
pairs and 12 lines of 3 points each, the 12 lines contain `12 * 3 = 36`
point-pairs, so "at most one" plus "at least one" forces a decomposition.
We enumerate all `9 * 9 = 81` ordered pairs (the diagonal `p = q` is
vacuous). -/

/-- Number of lines containing both `p` and `q`. -/
def pairCount (p q : Point) : Nat :=
  (lines.filter (fun k => lineMem k p && lineMem k q)).length

/-- (a) The line system is a Steiner triple system on 9 points:
each of the 81 ordered pairs `(p, q)` with `p != q` lies on exactly one line. -/
def stsBool : Bool :=
  points.all fun p =>
    points.all fun q =>
      p == q || (pairCount p q == 1)

theorem sts_property : stsBool = true := by decide

/-! ## (b) Resolvability (the "Kirkman" part)

The 12 lines split into 4 parallel classes `C_0 = [0,1,2]`, `C_1 = [3,4,5]`,
`C_2 = [6,7,8]` (slopes `m = 0,1,2`) and `C_3 = [9,10,11]` (vertical).  Each
class consists of 3 lines; disjointness plus coverage of the 9 points is the
statement that every point lies on exactly one line of the class, and the
classes partition the set of 12 lines.  Note `4 = (9-1)/2`, so this clause of
the conjecture is consistent with the counterexample. -/

/-- The four parallel classes as lists of line indices. -/
def parallelClasses : List (List Nat) := [[0, 1, 2], [3, 4, 5], [6, 7, 8], [9, 10, 11]]

/-- (b) Resolvability: 4 parallel classes, each of 3 lines, pairwise disjoint
lines covering all 9 points, and the classes partition the 12 lines. -/
def resolvableBool : Bool :=
  parallelClasses.length == 4 &&
    (parallelClasses.all fun cls =>
      cls.length == 3 &&
        (points.all fun p => cls.countP (fun k => lineMem k p) == 1)) &&
    ((List.range 12).all fun k =>
      parallelClasses.countP (fun cls => cls.contains k) == 1)

theorem resolvable : resolvableBool = true := by decide

/-! ## (c) Translations are automorphisms

For `v : Point` the translation `t_v(p) = p + v` (componentwise addition in
`Fin 3`, i.e. addition in `F_3^2`) maps lines to lines: for every line index
`k` there is a line index `k'` with, for every point `p`,
`p` on line `k` iff `p + v` on line `k'`.  Since translations are bijections
of the point set, this says the image of each line is again a line. -/

/-- Translation by `v`: `p |-> p + v` componentwise in `F_3^2`. -/
def translate (v p : Point) : Point := (p.1 + v.1, p.2 + v.2)

/-- (c) Every one of the 9 translations maps the line system to itself:
for all `v` and all lines `k` there is a line `k'` such that
`lineMem k p = lineMem k' (translate v p)` for all `p`. -/
def translationInvariantBool : Bool :=
  points.all fun v =>
    (List.range 12).all fun k =>
      (List.range 12).any fun k' =>
        points.all fun p => lineMem k p == lineMem k' (translate v p)

theorem translation_invariant : translationInvariantBool = true := by decide

/-! ## (d) Transitivity of the translation group

For all points `p, q` there exists `v` with `p + v = q` (namely the
componentwise difference `q - p` in `F_3^2`).  Hence the translation group
`F_3^2` of order 9 acts transitively on the 9 points. -/

/-- (d) The translation group `F_3^2` acts transitively on the 9 points. -/
def transitiveBool : Bool :=
  points.all fun p =>
    points.all fun q =>
      points.any fun v => translate p v == q

theorem transitive : transitiveBool = true := by decide

/-! ## Conclusion

There exists a point-transitive Kirkman triple system of order 9, so the
smallest order of a KTS with a transitive automorphism is at most 9, which is
strictly smaller than 15.  This refutes the clause of conjecture 00000008420
asserting that the smallest such order is 15. -/

/-- `9 < 15`: the counterexample order is strictly below the claimed minimum. -/
theorem refute : 9 < 15 := by decide

end Tlmc8420
