/-
  Disproof of TLMC conjecture 00000000427 (n = 1 and n = 2 counterexamples).

  A plane partition in an n x n x n cubic box is an order ideal of
  [n]x[n]x[n], equivalently a monotone non-decreasing {0,1}-valued height
  function h : {0,...,n-1}^3 -> {0,1}.  MacMahon's product formula counts all
  of them: M(1) = 2, M(2) = 20.  Below we enumerate ALL height functions of
  the 2x2x2 cube (2^8 = 256) and the 1x1x1 cube (2), filter the monotone ones
  (recovering MacMahon's 2 and 20), then count the diagonally symmetric ones
  under both natural readings of "diagonal":

    * mirror reading:  invariant under every transposition of coordinates,
                       h(i,j,k) = h(j,i,k) = h(k,j,i);
    * cyclic reading:  invariant under the 3-cycle, h(i,j,k) = h(j,k,i).

  True symmetric counts: 5 and 5 at n = 2; 2 and 2 at n = 1.
  Conjectured formula 2^{floor(n^2/4)} * prod (2i-1)!!/i! at t = 1:
  3 at n = 2 and 1 at n = 1.  Both readings refute the formula.
-/

namespace Tlmc0427

/-! ## Encoding of height functions on the 2x2x2 cube

A height function `h : {0,1}^3 -> {0,1}` is stored as a list of 8 naturals
(values 0 or 1); the cell `(i, j, k)` with `i, j, k ∈ {0,1}` is stored at
index `4*i + 2*j + k`. -/

/-- Structural-recursion indexing.  (Core `List.getD` carries `propext` in
its reduction, which would pollute `#print axioms`; `idx` is axiom-free.) -/
def idx : List Nat → Nat → Nat
  | [],      _     => 0
  | a :: _,  0     => a
  | _ :: as, n + 1 => idx as n

def val (t : List Nat) (i j k : Nat) : Nat := idx t (4*i + 2*j + k)

def bLe (a b : Nat) : Bool := decide (a ≤ b)

def bEq (a b : Nat) : Bool := decide (a = b)

/- Monotonicity: the 12 cover inequalities of the cube poset. -/
def monoB (t : List Nat) : Bool :=
  bLe (val t 0 0 0) (val t 1 0 0) && bLe (val t 0 1 0) (val t 1 1 0) &&
  bLe (val t 0 0 1) (val t 1 0 1) && bLe (val t 0 1 1) (val t 1 1 1) &&
  bLe (val t 0 0 0) (val t 0 1 0) && bLe (val t 1 0 0) (val t 1 1 0) &&
  bLe (val t 0 0 1) (val t 0 1 1) && bLe (val t 1 0 1) (val t 1 1 1) &&
  bLe (val t 0 0 0) (val t 0 0 1) && bLe (val t 1 0 0) (val t 1 0 1) &&
  bLe (val t 0 1 0) (val t 0 1 1) && bLe (val t 1 1 0) (val t 1 1 1)

/-! Mirror reading: `h(i,j,k) = h(j,i,k)` and `h(i,j,k) = h(k,j,i)` for every
one of the 8 cells (equalities on the two diagonal cells `(0,0,0)`, `(1,1,1)`
are trivial but listed for faithfulness). -/

def symB (t : List Nat) : Bool :=
  bEq (val t 0 0 0) (val t 0 0 0) && bEq (val t 0 0 0) (val t 0 0 0) &&
  bEq (val t 0 0 1) (val t 0 1 0) && bEq (val t 0 0 1) (val t 1 0 0) &&
  bEq (val t 0 1 0) (val t 1 0 0) && bEq (val t 0 1 0) (val t 0 1 0) &&
  bEq (val t 0 1 1) (val t 1 0 1) && bEq (val t 0 1 1) (val t 1 1 0) &&
  bEq (val t 1 0 0) (val t 0 1 0) && bEq (val t 1 0 0) (val t 0 0 1) &&
  bEq (val t 1 0 1) (val t 0 1 1) && bEq (val t 1 0 1) (val t 1 0 1) &&
  bEq (val t 1 1 0) (val t 1 1 0) && bEq (val t 1 1 0) (val t 0 1 1) &&
  bEq (val t 1 1 1) (val t 1 1 1) && bEq (val t 1 1 1) (val t 1 1 1)

/-! Cyclic reading: `h(i,j,k) = h(j,k,i)` for every one of the 8 cells. -/

def cycB (t : List Nat) : Bool :=
  bEq (val t 0 0 0) (val t 0 0 0) &&
  bEq (val t 0 0 1) (val t 0 1 0) &&
  bEq (val t 0 1 0) (val t 1 0 0) &&
  bEq (val t 0 1 1) (val t 1 1 0) &&
  bEq (val t 1 0 0) (val t 0 0 1) &&
  bEq (val t 1 0 1) (val t 0 1 1) &&
  bEq (val t 1 1 0) (val t 1 0 1) &&
  bEq (val t 1 1 1) (val t 1 1 1)

/-! All `2^8 = 256` height functions, as lists of 8 values. -/

def step2 (acc : List (List Nat)) : List (List Nat) :=
  acc.flatMap (fun l => ((0 : Nat) :: l) :: ((1 : Nat) :: l) :: [])

def allTuples : List (List Nat) :=
  (List.range 8).foldl (fun acc _ => step2 acc) [[]]

def planes : List (List Nat) := allTuples

/-! ## The n = 2 counterexample -/

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 100000 in
theorem allTuplesLen2 : allTuples.length = 256 := by decide

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 100000 in
theorem macMahon2 : (planes.filter monoB).length = 20 := by decide

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 100000 in
theorem symCount2 :
    (planes.filter (fun t => monoB t && symB t)).length = 5 := by decide

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 100000 in
theorem cycSymCount2 :
    (planes.filter (fun t => monoB t && cycB t)).length = 5 := by decide

/-! The conjectured formula at n = 2:
`2^{floor(4/4)} * prod (2i-1)!! = 2 * (1 * 3)` and `prod i! = 1 * 2`,
so the formula value is `2 * (1 * 3) / (1 * 2) = 6 / 2 = 3` (exact division;
stated over Nat because core Lean's `Rat` operations do not kernel-reduce for
`decide`/`rfl`, and the value is an exact integer here). -/

theorem formula2 : 2^(4/4) * (1 * 3) / (1 * 2) = 3 := by rfl

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 100000 in
theorem refute2 :
    (planes.filter monoB).length = 20 ∧
    (planes.filter (fun t => monoB t && symB t)).length = 5 ∧
    (planes.filter (fun t => monoB t && cycB t)).length = 5 ∧
    (2^(4/4) * (1 * 3) / (1 * 2) = 3) ∧
    (planes.filter (fun t => monoB t && symB t)).length ≠ 3 ∧
    (planes.filter (fun t => monoB t && cycB t)).length ≠ 3 := by decide

/-! ## The n = 1 counterexample

The 1x1x1 cube has a single cell and height values in `{0,1}`: exactly two
plane partitions (empty and full), both trivially monotone and symmetric. -/

def planes1 : List (List Nat) := [[0], [1]]

def trivialB (_t : List Nat) : Bool := true

theorem macMahon1 : (planes1.filter trivialB).length = 2 := by decide

theorem symCount1 :
    (planes1.filter (fun t => trivialB t && trivialB t)).length = 2 := by decide

/-! The conjectured formula at n = 1:
`2^{floor(1/4)} * (1!!) / (1!) = 2^0 * 1 / 1 = 1`. -/

theorem formula1 : 2^(1/4) * 1 / 1 = 1 := by rfl

theorem refute1 :
    (planes1.filter (fun t => trivialB t && trivialB t)).length = 2 ∧
    (2^(1/4) * 1 / 1 = 1) ∧
    (planes1.filter (fun t => trivialB t && trivialB t)).length ≠ 1 := by decide

end Tlmc0427
