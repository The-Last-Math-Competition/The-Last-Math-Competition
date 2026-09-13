/-
  Disproof of conjecture `00000001006`: formalisation.

  Conjecture (as filed):

    Definition: An m-ovoid (meeting every generating line in exactly m points).
    Conjecture: m-ovoids of Q(4,q) exist only when m | (q+1) (an existence
    criterion for m-ovoids).

    定义：m-ovoid(每条生成线恰交 m 点)。猜想：Q(4, q) 的 m-ovoid 仅在
    m | (q+1) 存在(m-ovoid 存在判据)。

  We disprove it at the smallest case `q = 2`, `m = 2`.

  * `Q(4,2)` is the parabolic quadric in `PG(4,2)`.  Points are modelled as the
    nonzero vectors `x : Fin 5 → Bool` with `Q(x) = x0 + x1*x2 + x3*x4 = 0`
    over `F_2`; there are 15 of them, and 15 generating lines, each with 3
    points.

  * `Q(4,2)` has an ovoid `O` (a 1-ovoid): a 5-element point set meeting every
    line in exactly 1 point.  One explicit ovoid is
        O = {(0,1,0,0,0), (0,0,1,0,0), (1,1,1,1,0), (1,1,1,0,1), (0,1,1,1,1)}.

  * Its complement `O^c` has 10 points and meets every line in exactly
    (q+1) - 1 = 3 - 1 = 2 points, so `O^c` is a 2-ovoid.

  * But `m = 2` does not divide `q + 1 = 3`, so the claimed necessary condition
    is violated by an m-ovoid that provably exists.

  The file uses CORE LEAN ONLY (`import Std`); no Mathlib, no `Finset`, no
  `sorry`.  All finite facts are closed by `decide`; the whole formalisation
  compiles and is audited by `Check.lean`.
-/

import Std

set_option maxRecDepth 1000000
set_option maxHeartbeats 8000000

namespace Tlmc1006

/-! ## The vector model of `Q(4,2)` -/

/-- Points of `PG(4,2)` are the 32 vectors `Fin 5 → Bool`. -/
abbrev Point := Fin 5 → Bool

/-- The quadratic form `Q(x) = x0^2 + x1*x2 + x3*x4 = x0 + x1*x2 + x3*x4`
over `F_2`. -/
def Q (x : Point) : Bool :=
  x 0 != ((x 1 && x 2) != (x 3 && x 4))

/-- `x` is a nonzero vector. -/
def Nonzero (x : Point) : Bool :=
  x 0 || x 1 || x 2 || x 3 || x 4

/-- The point set of `Q(4,2)`: nonzero vectors with `Q(x) = 0`. -/
def IsPoint (x : Point) : Bool :=
  Nonzero x && !Q x

/-- The polar bilinear form `B(a,b) = a1*b2 + a2*b1 + a3*b4 + a4*b3` over `F_2`,
so that `Q(a+b) = Q(a) + Q(b) + B(a,b)`. -/
def B (a b : Point) : Bool :=
  ((a 1 && b 2) != (a 2 && b 1)) != ((a 3 && b 4) != (a 4 && b 3))

/-- Coordinatewise sum of two vectors (addition in `F_2^5`). -/
def addP (a b : Point) : Point := fun i => a i != b i

/-! ## Encoding vectors by naturals, for decidable finite computation -/

/-- The binary encoding `n = Σ x_i * 2^i` of a vector. -/
def enc (x : Point) : Nat :=
  (if x 0 then 1 else 0) + (if x 1 then 2 else 0) + (if x 2 then 4 else 0)
    + (if x 3 then 8 else 0) + (if x 4 then 16 else 0)

/-- The vector whose `i`-th coordinate is bit `i` of `n`. -/
def mk (n : Nat) : Point := fun i => (n / 2 ^ (i : Nat)) % 2 == 1

/-- `n` encodes a point of `Q(4,2)`. -/
def IsPointE (n : Nat) : Bool := n < 32 && IsPoint (mk n)

/-- The encodings of the 15 points of `Q(4,2)`. -/
def pointsE : List Nat := (List.range 32).filter IsPointE

/-! ## The generating lines -/

/-- `a`, `b` encode two distinct points with `B(a,b) = 0`, so they span a
generating line. -/
def IsLinePairE (a b : Nat) : Bool :=
  IsPointE a && IsPointE b && a != b && !B (mk a) (mk b)

/-- The line through the points encoded by `a` and `b` is `{a, b, a+b}`; written
as a sorted triple `(a,b,c)` with `a < b < c`, its normal form is `c = a + b`. -/
def IsLineE (a b c : Nat) : Bool :=
  IsLinePairE a b && c == enc (addP (mk a) (mk b))

/-- Candidate sorted triples of the 15 points. -/
def cand : List (List Nat) :=
  pointsE.flatMap fun a =>
    pointsE.flatMap fun b =>
      pointsE.flatMap fun c =>
        if decide (a < b) && decide (b < c) then [[a, b, c]] else []

/-- All 15 generating lines of `Q(4,2)`, computed from the definitions, as
sorted encoding triples. -/
def allLinesE : List (List Nat) :=
  cand.filter fun L =>
    match L with
    | [a, b, c] => IsLineE a b c
    | _ => false

/-- The same 15 lines, listed explicitly. -/
def lines15 : List (List Nat) :=
  [[2, 8, 10], [2, 16, 18], [2, 25, 27],
   [4, 8, 12], [4, 16, 20], [4, 25, 29],
   [7, 8, 15], [7, 16, 23], [7, 25, 30],
   [10, 20, 30], [10, 23, 29],
   [12, 18, 30], [12, 23, 27],
   [15, 18, 29], [15, 20, 27]]

/-- The 15 lines as lists of points. -/
def linesP : List (List Point) := lines15.map (fun L => L.map mk)

/-! ## The explicit ovoid and its complement -/

/-- An explicit ovoid of `Q(4,2)` (5 points). -/
def O : List Point := [mk 2, mk 4, mk 15, mk 23, mk 30]

/-- The encodings of the ovoid `O`. -/
def OE : List Nat := [2, 4, 15, 23, 30]

/-- The complement of `O` among the 15 points of `Q(4,2)`. -/
def compE : List Nat := pointsE.filter fun n => !OE.contains n

/-- The complement of `O`, as points. -/
def Ocomp : List Point := compE.map mk

/-- Membership up to the encoding (no `DecidableEq` on function types is
needed). -/
def memP (S : List Point) (x : Point) : Bool := S.any fun y => enc y == enc x

/-- Number of points of the line `L` lying in the point set `S`. -/
def hitP (S L : List Point) : Nat := (L.filter fun x => memP S x).length

/-- `S` is an `m`-ovoid: it meets every generating line in exactly `m` points. -/
def IsMOvoid (m : Nat) (S : List Point) : Bool := linesP.all fun L => hitP S L == m

/-! ## Finite verifications -/

/-- `Q(4,2)` has 15 points. -/
theorem pointsE_length : pointsE.length = 15 := by decide

/-- The point list equals the canonical list. -/
theorem pointsE_eq :
    pointsE = [2, 4, 7, 8, 10, 12, 15, 16, 18, 20, 23, 25, 27, 29, 30] := by
  decide

/-- The computed line set is exactly the explicit list of 15 lines, so the list
is complete and contains no non-lines. -/
theorem lines15_is_all_lines : allLinesE = lines15 := by decide

/-- `Q(4,2)` has 15 lines. -/
theorem allLinesE_length : allLinesE.length = 15 := by decide

/-- Every line has exactly 3 points (`= q+1`). -/
theorem lines15_size : lines15.all (fun L => L.length == 3) = true := by decide

/-- `linesP` is a list of 15 lines of 3 points each. -/
theorem linesP_shape : linesP.length = 15 ∧ linesP.all (fun L => L.length == 3) = true :=
  ⟨by decide, by decide⟩

/-- The encoding round-trips on `{0,…,31}`. -/
theorem enc_mk_range : (List.range 32).all (fun n => enc (mk n) == n) = true := by
  decide

/-- The encoding round-trips on the points. -/
theorem mk_enc_points : pointsE.all (fun n => enc (mk n) == n) = true := by decide

/-- `O` is an explicit 5-element list of points. -/
theorem O_card : O.length = 5 ∧ O.all IsPoint = true := ⟨by decide, by decide⟩

/-- The encodings of `O` are `{2,4,15,23,30}`. -/
theorem O_map_enc : O.map enc = OE := by decide

/-- `O` is a 1-ovoid (an ovoid): every line meets it in exactly one point. -/
theorem O_is_ovoid : IsMOvoid 1 O = true := by decide

/-- The complement `O^c` has 10 points. -/
theorem Ocomp_card : Ocomp.length = 10 ∧ Ocomp.all IsPoint = true :=
  ⟨by decide, by decide⟩

/-- The encodings of `O^c` are the canonical complement list. -/
theorem Ocomp_map_enc : Ocomp.map enc = compE := by decide

/-- `O^c` is a 2-ovoid: every line meets it in exactly two points. -/
theorem Ocomp_is_2ovoid : IsMOvoid 2 Ocomp = true := by decide

/-- `O` and `O^c` partition the 15 points: together they have 15 entries and
`O^c` is disjoint from `O`. -/
theorem O_and_Ocomp_partition :
    (O ++ Ocomp).length = 15 ∧ Ocomp.all (fun x => !memP O x) = true := by
  decide

/-- The arithmetic heart of the disproof: `2` does not divide `q+1 = 3`. -/
theorem two_not_dvd_three : ¬ (2 ∣ 3) := by decide

/-- A 2-ovoid of `Q(4,2)` exists. -/
theorem two_ovoid_exists : ∃ S : List Point, IsMOvoid 2 S = true :=
  ⟨Ocomp, Ocomp_is_2ovoid⟩

/-- The conjecture is false: there is a 2-ovoid of `Q(4,2)`, yet `2 ∤ q+1`. -/
theorem conjecture_00000001006_false :
    (∃ S : List Point, IsMOvoid 2 S = true) ∧ ¬ (2 ∣ 3) :=
  ⟨two_ovoid_exists, two_not_dvd_three⟩

end Tlmc1006
