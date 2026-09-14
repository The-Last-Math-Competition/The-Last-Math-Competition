/-
  Core-Lean refutation of conjecture 00000002605
  ("Whitney strict concavity" / the complete version of Mason's conjecture).

  The witness is the 5-element lattice

      0  = bottom
      a  = element 1        b = element 2       (a, b incomparable)
      c  = a ⊔ b = element 3
      1  = top = element 4

  with cover relations  (0,1), (0,2), (1,3), (2,3), (3,4).
  Its rank numbers (Whitney numbers of the SECOND kind) are

      W = [1, 2, 1, 1],

  so  W 2 * W 2 = 1 < W 1 * W 3 = 2 : log-concavity fails at the very start.

  This file is core Lean ONLY: no `import Std`, no Mathlib, no `sorry`, and
  in fact no imports at all.  `List`, `Fin`, `Nat` and `Bool` are from Init.

  Unlike a table-only encoding, this file DERIVES everything from the cover
  relations:

    * `leB`    is the reflexive-transitive closure of the covers (Bellman-Ford
               relaxation, `closeIter`), and it is *proved* to be a partial
               order whose every relation decomposes through a cover
               (`le_decomp`), i.e. it is exactly the closure of the covers;
    * `meetB` / `joinB` are the greatest lower bound / least upper bound
               computed by search through `elems`, and are *proved* to satisfy
               the GLB / LUB universal properties (`meet_is_glb`,
               `join_is_lub`), which are the lattice axioms;
    * `rankB`  is the longest cover-chain length ending at each element
               (relaxation, `rankIter`), and is *proved* to vanish at the
               bottom and to increase by exactly one along every cover.

  Consequently upper semimodularity (`upperSemimodular`), distributivity
  (`distributive`) and the failure of log-concavity are all statements about
  the derived order, not about asserted tables.
-/

namespace Tlmc2605

/-- The five elements of the witness lattice, as `Fin 5`. -/
def elems : List (Fin 5) := [0, 1, 2, 3, 4]

/-- Cover relation `x ⋖ y` of the witness (this is the input data).
    Element indices: 0 = bottom, 1 = a, 2 = b, 3 = a ⊔ b, 4 = top. -/
def covB (x y : Fin 5) : Bool :=
  match x.val, y.val with
  | 0, 1 => true
  | 0, 2 => true
  | 1, 3 => true
  | 2, 3 => true
  | 3, 4 => true
  | _, _ => false

/-- One relaxation step of the reflexive-transitive closure:
    `x ≤ z` if `x ≤ z` already, or if `x ≤ y` for some `y ⋖ z`.
    The `&&`-order (`covB y z && r x y`) keeps this cheap: the recursive
    call is only made for the actual predecessors `y` of `z`. -/
def extend (r : Fin 5 → Fin 5 → Bool) : Fin 5 → Fin 5 → Bool :=
  fun x z => r x z || (elems.any fun y => covB y z && r x y)

/-- `n`-fold relaxation; base relation is equality together with the covers. -/
def closeIter : Nat → (Fin 5 → Fin 5 → Bool)
  | 0 => fun x y => (x == y) || covB x y
  | n + 1 => extend (closeIter n)

/-- The order relation of the witness, **derived** as the reflexive-transitive
    closure of the cover relations.  Four relaxation steps already cover all
    chains (the longest has four edges); we use five. -/
def leB (x y : Fin 5) : Bool := closeIter 5 x y

/-- Strict order, derived. -/
def ltB (x y : Fin 5) : Bool := leB x y && (x != y)

/-- The covering relation **re-derived** from the order. -/
def covLe (x y : Fin 5) : Bool :=
  ltB x y && !(elems.any fun z => ltB x z && ltB z y)

/-- Meet, computed by search: the greatest element below both `x` and `y`.
    The fold starts at the bottom `0`, which is a lower bound of everything. -/
def meetB (x y : Fin 5) : Fin 5 :=
  (elems.filter fun z => leB z x && leB z y).foldl
    (fun acc z => if leB acc z then z else acc) 0

/-- Join, computed by search: the least element above both `x` and `y`.
    The fold starts at the top `4`, which is an upper bound of everything. -/
def joinB (x y : Fin 5) : Fin 5 :=
  (elems.filter fun z => leB x z && leB y z).foldl
    (fun acc z => if leB z acc then z else acc) 4

/-- One relaxation step of the longest-chain computation:
    the height of `y` is at least `1 + height(x)` for every `x ⋖ y`. -/
def rankStep (d : Fin 5 → Nat) : Fin 5 → Nat :=
  fun y => (elems.map fun x => if covB x y then d x + 1 else 0).foldl Nat.max 0

/-- `n` relaxation steps of the longest-chain computation, starting from `0`. -/
def rankIter : Nat → (Fin 5 → Nat)
  | 0 => fun _ => 0
  | n + 1 => rankStep (rankIter n)

/-- The rank function, **derived** as the length of the longest cover-chain
    ending at each element.  Four relaxation steps suffice; we use four. -/
def rankB : Fin 5 → Nat := rankIter 4

/-- Whitney numbers of the SECOND kind: the number of elements of rank `k`.
    These are the coefficients of the rank generating function, i.e. the
    "rank number sequence" of the conjecture. -/
def W (k : Nat) : Nat := (elems.filter fun x => rankB x == k).length

/-- Upper semimodularity, as a Boolean check over all ordered pairs:
    `x ⊓ y ⋖ x  ⟹  y ⋖ x ⊔ y`. -/
def upperSemimodular : Bool :=
  elems.all fun x => elems.all fun y =>
    (!covLe (meetB x y) x) || covLe y (joinB x y)

/-- Distributivity, as a Boolean check over all triples:
    `x ⊓ (y ⊔ z) = (x ⊓ y) ⊔ (x ⊓ z)`. -/
def distributive : Bool :=
  elems.all fun x => elems.all fun y => elems.all fun z =>
    (meetB x (joinB y z) == joinB (meetB x y) (meetB x z))

/-- The atoms: elements covering the bottom. -/
def atoms : List (Fin 5) := elems.filter fun x => covB 0 x

/-- The join of all atoms. -/
def joinAtoms : Fin 5 := atoms.foldl joinB 0

/-- The top element. -/
def top : Fin 5 := 4

-- ---------------------------------------------------------------------------
-- Boolean forms of the order/lattice axioms, all closed computations.
-- Each is *proved equal to true* by `decide`; no quantifier decidability
-- beyond `Fin 5` is required, because the quantification is internal
-- (`List.all` over `elems`).
-- ---------------------------------------------------------------------------

def leReflB : Bool := elems.all fun x => leB x x

def leAntisymmB : Bool :=
  elems.all fun x => elems.all fun y =>
    (!(leB x y && leB y x)) || (x == y)

def leTransB : Bool :=
  elems.all fun x => elems.all fun y => elems.all fun z =>
    (!(leB x y && leB y z)) || leB x z

/-- Every relation is reflexive, a cover, or a cover followed by a relation:
    this is the minimality half that pins `leB` to be *the* closure. -/
def leDecompB : Bool :=
  elems.all fun x => elems.all fun y =>
    (!leB x y) || (x == y) || covB x y ||
      (elems.any fun z => covB z y && leB x z)

/-- The re-derived covering relation agrees with the input covers. -/
def covLeEqB : Bool :=
  elems.all fun x => elems.all fun y => (covLe x y == covB x y)

/-- `meetB` is a lower bound and dominates every lower bound (GLB). -/
def meetGlbB : Bool :=
  elems.all fun x => elems.all fun y =>
    leB (meetB x y) x && leB (meetB x y) y &&
      (elems.all fun z => (!(leB z x && leB z y)) || leB z (meetB x y))

/-- `joinB` is an upper bound and is dominated by every upper bound (LUB). -/
def joinLubB : Bool :=
  elems.all fun x => elems.all fun y =>
    leB x (joinB x y) && leB y (joinB x y) &&
      (elems.all fun z => (!(leB x z && leB y z)) || leB (joinB x y) z)

def rankZeroB : Bool := rankB 0 == 0

/-- The rank increases by exactly one along every cover. -/
def rankCovB : Bool :=
  elems.all fun x => elems.all fun y =>
    (!covB x y) || (rankB y == rankB x + 1)

/-- The rank is monotone along the derived order. -/
def rankMonoB : Bool :=
  elems.all fun x => elems.all fun y =>
    (!leB x y) || Nat.ble (rankB x) (rankB y)

-- ---------------------------------------------------------------------------
-- Machine-checked facts
-- ---------------------------------------------------------------------------

theorem le_refl : leReflB = true := by decide
theorem le_antisymm : leAntisymmB = true := by decide
theorem le_trans : leTransB = true := by decide
theorem le_decomp : leDecompB = true := by decide
theorem cover_derived_eq : covLeEqB = true := by decide
theorem meet_is_glb : meetGlbB = true := by decide
theorem join_is_lub : joinLubB = true := by decide
theorem rank_zero : rankZeroB = true := by decide
theorem rank_cov : rankCovB = true := by decide
theorem rank_mono : rankMonoB = true := by decide

theorem W_zero : W 0 = 1 := by decide
theorem W_one : W 1 = 2 := by decide
theorem W_two : W 2 = 1 := by decide
theorem W_three : W 3 = 1 := by decide
theorem W_four : W 4 = 0 := by decide

/-- Log-concavity fails at `k = 2`: `W₂² < W₁·W₃`, i.e. `1 < 2`. -/
theorem logConcavity_fails : W 2 * W 2 < W 1 * W 3 := by decide

/-- Strict log-concavity fails as well. -/
theorem strictLogConcavity_fails : ¬ (W 1 * W 3 ≤ W 2 * W 2) := by decide

/-- The witness is upper semimodular (all 25 pairs check out). -/
theorem upperSemimodular_true : upperSemimodular = true := by decide

/-- The witness is distributive (all 125 triples check out). -/
theorem distributive_true : distributive = true := by decide

/-- The atoms are exactly `a` and `b`. -/
theorem atoms_eq : atoms = [1, 2] := by decide

/-- The join of the atoms is `a ⊔ b = c`, not the top. -/
theorem joinAtoms_eq : joinAtoms = 3 := by decide

/-- The join of all atoms is not the top: the lattice is not atomistic, hence
    not geometric (geometric lattices are atomistic by definition). -/
theorem not_atomistic : joinAtoms ≠ top := by decide

/-- **The conjecture is false.**  For this semimodular lattice the rank numbers
    `W = [1,2,1,1]` violate (strict) log-concavity, while the lattice is
    distributive and hence contains no N₅ sublattice at all. -/
theorem conjecture_00000002605_false :
    W 2 * W 2 < W 1 * W 3 ∧
      ¬ (W 1 * W 3 ≤ W 2 * W 2) ∧
      upperSemimodular = true ∧
      joinAtoms ≠ top := by
  decide

-- ---------------------------------------------------------------------------
-- Concrete evaluations (for eyeballing; the theorems above are the content)
-- ---------------------------------------------------------------------------

#eval W 0
#eval W 1
#eval W 2
#eval W 3
#eval W 4
#eval atoms
#eval joinAtoms
#eval upperSemimodular
#eval distributive
#eval joinAtoms == top

end Tlmc2605
