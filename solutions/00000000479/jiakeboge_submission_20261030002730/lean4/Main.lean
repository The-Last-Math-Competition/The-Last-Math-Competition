namespace Tlmc479

/-- A unit cell, identified by its lower-left lattice coordinate. -/
abbrev Cell := Int × Int

/-- A domino, stored as an ordered pair of adjacent cells. -/
abbrev Domino := Cell × Cell

/-- The order-1 Aztec diamond: cells `(i,j)` with `|i+1/2| + |j+1/2| <= 1`. -/
def region1 : List Cell :=
  [(-1, -1), (-1, 0), (0, -1), (0, 0)]

/-- The order-2 Aztec diamond: cells `(i,j)` with `|i+1/2| + |j+1/2| <= 2`. -/
def region2 : List Cell :=
  [(-2, -1), (-2, 0), (-1, -2), (-1, -1), (-1, 0), (-1, 1),
   (0, -2), (0, -1), (0, 0), (0, 1), (1, -1), (1, 0)]

/-- A domino is horizontal when its two cells share the second coordinate. -/
def isHoriz (d : Domino) : Bool := d.1.2 == d.2.2

/-- Number of horizontal dominoes in a matching. -/
def hcount (L : List Domino) : Nat := (L.filter isHoriz).length

/-- The two neighbours of `c` that still lie in the uncovered set `rem`. -/
def nbrs (rem : List Cell) (c : Cell) : List Cell :=
  ([(c.1 + 1, c.2), (c.1, c.2 + 1)]).filter (fun d => rem.contains d)

/-- Remove one cell from a list. -/
def erase (rem : List Cell) (c : Cell) : List Cell :=
  rem.filter (fun x => x != c)

/-- Enumerate all matchings of a region by repeatedly covering the
lexicographically least uncovered cell with one of its two possible dominoes. -/
def search : Nat → List Cell → List Domino → List (List Domino)
  | 0, _, _ => []
  | _fuel + 1, [], acc => [acc.reverse]
  | fuel + 1, c :: rest, acc =>
      let rem := c :: rest
      (nbrs rem c).flatMap (fun d =>
        search fuel (erase (erase rem c) d) ((c, d) :: acc))

/-- All matchings of the order-1 Aztec diamond. -/
def matchings1 : List (List Domino) := search 4 region1 []

/-- All matchings of the order-2 Aztec diamond. -/
def matchings2 : List (List Domino) := search 12 region2 []

theorem matchings1_card : matchings1.length = 2 := by decide

theorem matchings2_card : matchings2.length = 8 := by decide

/-- The stratum of order 1 with exactly two horizontal dominoes. -/
theorem stratum2_order1 :
    (matchings1.filter (fun L => hcount L == 2)).length = 1 := by decide

/-- The stratum of order 2 with exactly two horizontal dominoes. -/
theorem stratum2_order2 :
    (matchings2.filter (fun L => hcount L == 2)).length = 3 := by decide

/-- The stratum of order 2 with exactly six horizontal dominoes. -/
theorem stratum6_order2 :
    (matchings2.filter (fun L => hcount L == 6)).length = 1 := by decide

/-- The stratum of order 2 with exactly four horizontal dominoes. -/
theorem stratum4_order2 :
    (matchings2.filter (fun L => hcount L == 4)).length = 3 := by decide

/-- The stratum of order 2 with no horizontal dominoes. -/
theorem stratum0_order2 :
    (matchings2.filter (fun L => hcount L == 0)).length = 1 := by decide

theorem three_is_odd : ¬ (2 ∣ 3) := by decide

theorem one_is_odd : ¬ (2 ∣ 1) := by decide

/-- The conjecture demands `v_2(N_2) = 1` for `k = 2`, i.e. that the stratum
size be twice an odd number.  At order 2 that size is `3`, which is odd. -/
theorem refutation_order2 :
    (matchings2.filter (fun L => hcount L == 2)).length = 3 ∧ ¬ (2 ∣ 3) :=
  ⟨stratum2_order2, three_is_odd⟩

/-- The same failure at order 1. -/
theorem refutation_order1 :
    (matchings1.filter (fun L => hcount L == 2)).length = 1 ∧ ¬ (2 ∣ 1) :=
  ⟨stratum2_order1, one_is_odd⟩

/-- The four strata at order 2 sum to the total number of matchings. -/
theorem strata_partition :
    (matchings2.filter (fun L => hcount L == 0)).length
      + (matchings2.filter (fun L => hcount L == 2)).length
      + (matchings2.filter (fun L => hcount L == 4)).length
      + (matchings2.filter (fun L => hcount L == 6)).length = 8 := by decide

end Tlmc479
