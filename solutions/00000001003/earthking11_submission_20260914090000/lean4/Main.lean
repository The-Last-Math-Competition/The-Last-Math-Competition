/-
  Disproof of conjecture 00000001003 (maximal caps in PG(4,q)).

  Conjecture (verbatim): "The maximal cap size in PG(4,q) is
  q^2+q+1+floor((q+1)/3) for all odd q, attained by an elliptic quadric with
  an explicit three-point augmentation; for even q the value increases by 2."

  This file formalises the refutation at q = 3.  The conjecture predicts
      3^2 + 3 + 1 + floor(4/3) = 9 + 3 + 1 + 1 = 14,
  but PG(4,3) contains an explicit 20-point cap (no three collinear).  Hence
  the maximum is at least 20 > 14 and the q = 3 instance of "for all odd q"
  is false.

  Core Lean only: `import Std`, no Mathlib, no `sorry`, no `native_decide`.
  Every theorem below is proved by `decide` and is axiom-free.

  PITFALLS handled here:
  * `ZMod`, `Finset`, `Fintype` are NOT in `import Std`; arithmetic is done
    with `Nat % 3`.
  * There is no `DecidableEq` instance for function types such as
    `Fin 5 -> Fin 3`, so a point is a small `structure Pt` with five `Nat`
    fields and `deriving DecidableEq, Repr, BEq`.
  * `decide` cannot reduce `Rat`, so only `Nat` arithmetic is used.
-/

import Std

/-- A point of PG(4,3) represented by integer coordinates (reduced mod 3). -/
structure Pt where
  x0 : Nat
  x1 : Nat
  x2 : Nat
  x3 : Nat
  x4 : Nat
deriving DecidableEq, Repr, BEq

namespace Pt

def coords (p : Pt) : List Nat := [p.x0, p.x1, p.x2, p.x3, p.x4]

/-- componentwise addition mod 3 -/
def add (p q : Pt) : Pt :=
  ⟨(p.x0 + q.x0) % 3, (p.x1 + q.x1) % 3, (p.x2 + q.x2) % 3,
   (p.x3 + q.x3) % 3, (p.x4 + q.x4) % 3⟩

/-- scalar multiplication mod 3 -/
def smul (t : Nat) (p : Pt) : Pt :=
  ⟨(t * p.x0) % 3, (t * p.x1) % 3, (t * p.x2) % 3,
   (t * p.x3) % 3, (t * p.x4) % 3⟩

/-- first nonzero coordinate (0 if the vector is zero) -/
def firstNonzero (p : Pt) : Nat :=
  (p.coords.find? (fun a => a % 3 != 0)).getD 0

/-- projective normalisation: first nonzero coordinate becomes 1 (inv(2)=2 mod 3) -/
def normalize (p : Pt) : Pt := p.smul p.firstNonzero

end Pt

open Pt

/-- `r` is one of the two "new" points on the line through `p`, `q`:
    for q = 3 the projective line through two distinct points is
    {p, q, normalize(p+q), normalize(p+2q)}, so this test is complete. -/
def bad (p q r : Pt) : Bool :=
  (p != q) && (q != r) && (p != r) &&
  (((p.add q).normalize == r) || ((p.add (q.smul 2)).normalize == r))

/-- Executable cap test: no three distinct points of `S` are collinear. -/
def isCap (S : List Pt) : Bool :=
  !(S.any (fun p => S.any (fun q => S.any (fun r => bad p q r))))

/-- The explicit 20-point cap in PG(4,3), all vectors normalised
    (first nonzero coordinate = 1). -/
def pts20 : List Pt :=
  [ ⟨1,0,0,0,2⟩, ⟨0,0,0,1,2⟩, ⟨1,2,2,1,1⟩, ⟨0,1,0,0,0⟩, ⟨1,0,2,1,2⟩
  , ⟨1,0,1,2,0⟩, ⟨0,1,0,1,0⟩, ⟨1,2,1,2,1⟩, ⟨1,1,2,2,0⟩, ⟨1,2,0,1,2⟩
  , ⟨1,2,0,1,0⟩, ⟨1,2,1,0,2⟩, ⟨1,0,1,1,0⟩, ⟨0,1,1,1,2⟩, ⟨0,0,1,0,0⟩
  , ⟨0,1,2,2,0⟩, ⟨1,0,2,2,2⟩, ⟨1,2,1,2,2⟩, ⟨0,1,2,2,2⟩, ⟨1,1,0,1,1⟩ ]

/-- The conjecture's formula at a prime power `q`:
    `q^2 + q + 1 + floor((q+1)/3)`. -/
def formula (q : Nat) : Nat := q * q + q + 1 + (q + 1) / 3

/-! ### Non-vacuity sanity checks for `isCap` -/

/-- A genuinely collinear triple of distinct points. -/
def collinearTriple : List Pt :=
  [⟨1,0,0,0,0⟩, ⟨0,1,0,0,0⟩, ⟨1,1,0,0,0⟩]

/-- A genuinely non-collinear triple of distinct points. -/
def independentTriple : List Pt :=
  [⟨1,0,0,0,0⟩, ⟨0,1,0,0,0⟩, ⟨1,0,1,0,0⟩]

/-- `isCap` correctly rejects a collinear triple. -/
theorem isCap_collinear_false : isCap collinearTriple = false := by decide

/-- `isCap` correctly accepts a non-collinear triple. -/
theorem isCap_independent_true : isCap independentTriple = true := by decide

/-- Direct witness of `bad` on the collinear triple. -/
theorem bad_witness :
    bad ⟨1,0,0,0,0⟩ ⟨0,1,0,0,0⟩ ⟨1,1,0,0,0⟩ = true := by decide

/-! ### The 20-point cap and the refutation -/

/-- The 20 points are pairwise distinct (they are 20 distinct projective points). -/
theorem pts20_nodup : pts20.Nodup := by decide

/-- The cap has exactly 20 points. -/
theorem pts20_length : pts20.length = 20 := by decide

/-- The executable cap check returns `true` on those 20 points:
    no three of the C(20,3) = 1140 triples are collinear. -/
theorem pts20_isCap : isCap pts20 = true := by decide

/-- The conjecture's value at q = 3 is 9 + 3 + 1 + 1 = 14. -/
theorem formula_three : formula 3 = 14 := by decide

/-- 20 > 14, the arithmetic content of the refutation. -/
theorem twenty_gt_fourteen : (20 : Nat) > 14 := by decide

/-- The formula at q = 3 is strictly smaller than the explicit cap. -/
theorem formula_three_lt_length : formula 3 < pts20.length := by decide

/-- REFUTATION.  There is a valid cap in PG(4,3) whose size is 20, and the
    conjecture's value `formula 3 = 14` is strictly smaller.  Hence the
    maximum cap size in PG(4,3) is at least 20 > 14, contradicting the
    conjecture at q = 3 (an odd prime power). -/
theorem refutes_conjecture :
    ∃ S : List Pt, S.length = 20 ∧ isCap S = true ∧ formula 3 < S.length :=
  ⟨pts20, by decide, by decide, by decide⟩

/-- Same statement phrased with the explicit numbers: a cap of size 20 exists
    while the conjecture predicts 14. -/
theorem conjecture_00000001003_false :
    ∃ S : List Pt, isCap S = true ∧ S.length = 20 ∧ formula 3 = 14 ∧ (20 : Nat) > 14 :=
  ⟨pts20, by decide, by decide, by decide, by decide⟩
