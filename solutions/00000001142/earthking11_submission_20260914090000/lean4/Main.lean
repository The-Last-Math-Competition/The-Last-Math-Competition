/-
  Disproof of conjecture `00000001142`.

  Conjecture (as filed):
    The order of the automorphism group of the mod-p Witt algebra W(1; 1)
    is p(p-1) (Witt automorphisms).

  The conjecture is FALSE.  W(1;1) = Der(F_p[x]/(x^p)) has the p basis
  elements b_k = x^k d/dx (k = 0, ..., p-1), and

      [b_k, b_l] = (l - k) b_{k+l-1}   if 1 <= k+l <= p,   else 0.

  At p = 3 the algebra is 3-dimensional (basis b_0, b_1, b_2) and we compute
  |Aut(W(1;1))| by exhaustive search over all 3^9 = 19683 matrices over F_3:
  exactly 24 matrices are invertible and bracket-preserving, whereas the
  conjecture predicts p(p-1) = 6.  (Indeed W(1;1) = sl(2, F_3) for p = 3, so
  |Aut| = |PGL(2,3)| = |S_4| = 24.)

  The computation below is faithful, not hardcoded: only the nine structure
  constants of the 3-dimensional algebra are written down (that is the
  definition of the algebra); the 24 automorphisms are found by enumerating
  all 19683 matrices and testing invertibility + bracket preservation.

  Everything is Nat arithmetic mod 3 (no ZMod / Matrix / Finset / Fintype,
  which are not available in `import Std`).  Core Lean only, no `sorry`.

  The enumeration is discharged by the KERNEL `decide` tactic (defeq
  reduction), NOT by `native_decide`: no `Lean.ofReduceBool` axiom is used.
  The inner predicate was optimised (base-3 `Nat` codes, inlined structure
  constants, `Bool` predicate on basis pairs) so that the kernel reduction
  finishes in about one minute; see `lean4/README.md` for the measured time.

  NOTE: p = 5 is out of scope here (the analogue would require 5^25 matrices);
  it is treated in the LaTeX write-up and in `reproduce.py`.
-/

import Std

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Tlmc1142
namespace Witt3

/-! ## Modular arithmetic helpers (all operands are already reduced mod 3) -/

/-- Product mod 3. -/
def m3 (x y : Nat) : Nat := (x * y) % 3

/-- Difference mod 3, for `x, y < 3` (the `+3` keeps the subtraction in `Nat`). -/
def s3 (x y : Nat) : Nat := (x + 3 - y) % 3

/-- Determinant mod 3 of the matrix with entries `a b c / d e f / g h i`
    (row-major), by the cofactor rule, using `-x = 2x` in F_3. -/
def detG (a b c d e f g h i : Nat) : Nat :=
  (a * s3 (m3 e i) (m3 f h)
    + (2 * b) * s3 (m3 d i) (m3 f g)
    + c * s3 (m3 d h) (m3 e g)) % 3

/-! ## The structure constants of W(1;1) at p = 3

    The bracket is bilinear, so it is determined by its values on the basis.
    From [b_k,b_l] = (l-k) b_{k+l-1} (with b_{k+l-1} = 0 when k+l > 3) the
    nine brackets are

      [b_0,b_0]=0, [b_0,b_1]=b_0,   [b_0,b_2]=2 b_1,
      [b_1,b_0]=2 b_0, [b_1,b_1]=0, [b_1,b_2]=b_2,
      [b_2,b_0]=b_1,   [b_2,b_1]=2 b_2, [b_2,b_2]=0.

    Hence for `X = x0 b_0 + x1 b_1 + x2 b_2` and `Y = y0 b_0 + y1 b_1 + y2 b_2`
    bilinearity gives the three coordinates of `[X,Y]` as

      [X,Y]_0 = x0*y1 + 2*x1*y0
      [X,Y]_1 = 2*x0*y2 + x2*y0
      [X,Y]_2 = x1*y2 + 2*x2*y1      (all mod 3).
-/

/-- Zeroth coordinate of `[X,Y]`. -/
def b0 (x0 x1 y0 y1 : Nat) : Nat := (x0 * y1 + 2 * (x1 * y0)) % 3

/-- First coordinate of `[X,Y]`. -/
def b1 (x0 x2 y0 y2 : Nat) : Nat := (2 * (x0 * y2) + x2 * y0) % 3

/-- Second coordinate of `[X,Y]`. -/
def b2 (x1 x2 y1 y2 : Nat) : Nat := (x1 * y2 + 2 * (x2 * y1)) % 3

/-- Componentwise equality test of two computed vectors with an expected one. -/
def eqc (z0 z1 z2 e0 e1 e2 : Nat) : Bool :=
  (z0 == e0) && (z1 == e1) && (z2 == e2)

/-- Bracket preservation for the linear map whose columns are the images of
    the basis: column 0 is `(a,d,g)`, column 1 is `(b,e,h)`, column 2 is
    `(c,f,i)`.  The nine checks are exactly `phi([b_k,b_l]) = [phi b_k, phi b_l]`
    read off the table of structure constants above. -/
def presG (a b c d e f g h i : Nat) : Bool :=
  eqc (b0 a d a d) (b1 a g a g) (b2 d g d g) 0 0 0 &&
  eqc (b0 a d b e) (b1 a g b h) (b2 d g e h) a d g &&
  eqc (b0 a d c f) (b1 a g c i) (b2 d g f i) (2 * b % 3) (2 * e % 3) (2 * h % 3) &&
  eqc (b0 b e a d) (b1 b h a g) (b2 e h d g) (2 * a % 3) (2 * d % 3) (2 * g % 3) &&
  eqc (b0 b e b e) (b1 b h b h) (b2 e h e h) 0 0 0 &&
  eqc (b0 b e c f) (b1 b h c i) (b2 e h f i) c f i &&
  eqc (b0 c f a d) (b1 c i a g) (b2 f i d g) b e h &&
  eqc (b0 c f b e) (b1 c i b h) (b2 f i e h) (2 * c % 3) (2 * f % 3) (2 * i % 3) &&
  eqc (b0 c f c f) (b1 c i c i) (b2 f i f i) 0 0 0

/-! ## Enumerating the matrices -/

/-- A matrix is coded by an integer `m < 3^9` whose base-3 digits, from least
    significant, are the entries `g0,...,g8` in row-major order.  `isAut m`
    holds iff the matrix is invertible and preserves the bracket. -/
def isAut (m : Nat) : Bool :=
  let a := m % 3
  let b := m / 3 % 3
  let c := m / 9 % 3
  let d := m / 27 % 3
  let e := m / 81 % 3
  let f := m / 243 % 3
  let g := m / 729 % 3
  let h := m / 2187 % 3
  let i := m / 6561 % 3
  (detG a b c d e f g h i != 0) && presG a b c d e f g h i

/-- All candidate matrices: the 3^9 = 19683 codes. -/
def allMats : List Nat := List.range (3 ^ 9)

/-- The automorphisms of W(1;1) at p = 3, found by exhaustive search. -/
def auts3 : List Nat := allMats.filter isAut

/-! ## The computation -/

/-- Sanity check: there are indeed 3^9 candidate matrices. -/
theorem num_mats : allMats.length = 3 ^ 9 := by decide

/-- **Refutation.** `|Aut(W(1;1))| = 24` at `p = 3`, while the conjecture
    claims `p(p-1) = 3*2 = 6`. -/
theorem aut_count_3 : auts3.length = 24 := by decide

/-- The conjectured value `p(p-1) = 6` does not occur. -/
theorem claim_false_3 : auts3.length ≠ 3 * (3 - 1) := by decide

end Witt3
end Tlmc1142

/-!
  Summary of the formalised refutation at `p = 3`:

  * `3^9 = 19683` matrices are enumerated (coding `m : Nat`, base-3 digits);
  * `11232 = |GL(3,F_3)|` of them are invertible;
  * exactly `24` of those preserve the bracket `[b_k,b_l] = (l-k) b_{k+l-1}`;
  * the conjecture predicts `p(p-1) = 6`, so it is false at `p = 3`.

  Discharged by the kernel `decide` tactic, not by `native_decide`.
-/
