/-
  Disproof of TLMC conjecture 00000001031 (core Lean 4, no Mathlib).

  Conjecture: the multiplier group {tau : tauD = D} of a Singer difference set
  D in F_{q^3}^* equals the norm-image subgroup N(F_{q^3}/F_q) of F_{q^3}^*,
  which has order q-1 and index q^2+q+1.

  Counterexample q = 2.  F_8^* is cyclic of order 7; writing exponents as
  elements of Z_7, the classical Singer difference set (nonzero trace-zero
  elements of F_8) is D = {1, 2, 4}.  All numeric claims below are proved by
  pure computation (`rfl`), and the whole file is axiom-free (see Check.lean):

    multiplier group of D   = [1, 2, 4]   (order 3)
    norm subgroup           = [1]         (order q-1 = 1, index 7 = q^2+q+1)
    [1,2,4] != [1]                        =>  conjecture FALSE
-/

set_option maxHeartbeats 1000000

/-- The Singer difference set for `q = 2`, in the cyclic group `Z_7`. -/
def D : List Nat := [1, 2, 4]

/-- The image of multiplier `t` acting on `D` (`tD` inside `Z_7`). -/
def act (t : Nat) : List Nat := D.map (fun d => (t * d) % 7)

/-- `t` is a multiplier of `D` iff `tD = D` (mutual containment of the two lists). -/
def isMult (t : Nat) : Bool :=
  (act t).all (fun d => D.contains d) && D.all (fun d => (act t).contains d)

/-- The full multiplier group of `D`, enumerated over the units of `Z_7`. -/
def multGroup : List Nat := [1, 2, 3, 4, 5, 6].filter isMult

/-- The conjectured multiplier group: the norm image `N(F_8/F_2) = F_2^* = {1}`
(order `q-1 = 1`, index `7 = q^2+q+1`). -/
def normSub : List Nat := [1]

/-- Ordered differences of distinct elements of `D`, reduced mod 7. -/
def diffs : List Nat :=
  D.flatMap (fun a => D.filterMap (fun b =>
    if a == b then none else some ((a + 7 - b) % 7)))

/-! ### Difference-set property: each nonzero residue covered exactly once -/

theorem diffs_len : diffs.length = 6 := rfl

theorem diffs_cover_1 : (diffs.filter (fun x => x == 1)).length = 1 := rfl
theorem diffs_cover_2 : (diffs.filter (fun x => x == 2)).length = 1 := rfl
theorem diffs_cover_3 : (diffs.filter (fun x => x == 3)).length = 1 := rfl
theorem diffs_cover_4 : (diffs.filter (fun x => x == 4)).length = 1 := rfl
theorem diffs_cover_5 : (diffs.filter (fun x => x == 5)).length = 1 := rfl
theorem diffs_cover_6 : (diffs.filter (fun x => x == 6)).length = 1 := rfl

/-! ### Multiplier enumeration -/

theorem mult_1 : isMult 1 = true := rfl
theorem mult_2 : isMult 2 = true := rfl
theorem mult_4 : isMult 4 = true := rfl
theorem mult_3 : isMult 3 = false := rfl
theorem mult_5 : isMult 5 = false := rfl
theorem mult_6 : isMult 6 = false := rfl

/-- The multiplier group of `D` is exactly `{1, 2, 4}`. -/
theorem multGroup_value : multGroup = [1, 2, 4] := rfl

/-- Its order is `3`. -/
theorem multGroup_order : multGroup.length = 3 := rfl

/-! ### The norm subgroup -/

/-- Order of the norm image `N(F_8/F_2) = F_2^*` is `q - 1 = 1`. -/
theorem normSub_order : normSub.length = 2 - 1 := rfl

/-- Its index in `F_8^*` (`Z_7`) is `q^2+q+1 = 7`. -/
theorem normSub_index : 7 / normSub.length = 2 * 2 + 2 + 1 := rfl

/-! ### The conjecture fails -/

/-- The conjectured equality `multiplier group = norm subgroup` evaluates to false. -/
theorem conjecture_claim_bool : (multGroup == normSub) = false := rfl

/-- Main result: the multiplier group is *not* the norm subgroup
(orders 3 and q-1 = 1 differ). -/
theorem multGroup_ne_normSub : ¬ (multGroup = normSub) :=
  fun h => absurd (congrArg List.length h) (by decide)

/-- The clause "no other multipliers" also fails: 2 and 4 are multipliers
outside the norm subgroup `{1}`. -/
theorem other_multipliers_exist : isMult 2 && isMult 4 = true := rfl
