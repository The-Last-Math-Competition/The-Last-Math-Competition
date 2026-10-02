/-
  Disproof of TLMC conjecture 00000001581.

  Conjecture: "The count of Q-points of the PVI monodromy manifold is
  N_p = p^2 + a*p + 1 with a in {-1, 0, 1}."

  The PVI monodromy manifold is the Fricke surface
      M_kappa : x^2 + y^2 + z^2 - x*y*z = kappa,
  where kappa is fixed by the local monodromy data (for the standard
  specializations, e.g. (p,q,r) = (1,1,1) one gets kappa = 0; the
  generic once-punctured-torus family runs over all integer kappa).

  Kernel-certified: the COMPLETE enumeration of M_kappa(F_5) for every
  kappa in F_5 (all 125 triples checked), giving

      kappa :  0   1   2   3   4
      N_5  :  41   6  16  36  26

  The claimed pattern allows only N_5 in {21, 26, 31}.  The actual
  counts 41, 6, 16, 36 (for kappa = 0, 1, 2, 3 — including the two most
  standard normalizations kappa = 0 and kappa = 1) all fall outside the
  claimed set; only kappa = 4 = -1 coincidentally matches 26.  The
  count is not even well-defined without fixing kappa (it varies), so
  "N_p = p^2 + a p + 1" fails as a statement about the monodromy
  manifold family, and for each standard choice of kappa it fails
  numerically.

  All counts are closed kernel computations over Int arithmetic (no
  truncation errors), axiom-free.
-/

namespace Tlmc1581

/-! ## The Fricke surface and its F_5-point counter. -/

/-- The Fricke surface equation at p = 5: is (x,y,z) on M_kappa? -/
def onep (k x y z : Nat) : Bool :=
  ((x*x + y*y + z*z : Int) - ((x*y*z : Int)) - ((k : Int))) % 5 == 0

/-- Count over z. -/
def cntZ (k x y : Nat) : Nat → Nat
  | 0 => 0
  | z + 1 => (if onep k x y z then 1 else 0) + cntZ k x y z

/-- Count over (y, z). -/
def cntY (k x : Nat) : Nat → Nat
  | 0 => 0
  | y + 1 => cntZ k x y 5 + cntY k x y

/-- Count over (x, y, z): the total F_5-point count of M_kappa. -/
def cntX (k : Nat) : Nat → Nat
  | 0 => 0
  | x + 1 => cntY k x 5 + cntX k x

/-- THE FULL TABLE, kernel-certified (all 125 triples per row). -/
theorem table_0 : cntX 0 5 = 41 := by decide
theorem table_1 : cntX 1 5 = 6 := by decide
theorem table_2 : cntX 2 5 = 16 := by decide
theorem table_3 : cntX 3 5 = 36 := by decide
theorem table_4 : cntX 4 5 = 26 := by decide

/-! ## The refutation. -/

/-- The claimed pattern at p = 5 allows only {21, 26, 31}. -/
theorem claimed : (31 : Nat) = 5 * 5 + 5 + 1 ∧ (26 : Nat) = 5 * 5 + 1 ∧
    (21 : Nat) = 5 * 5 - 5 + 1 := by decide

/-- The standard normalization kappa = 0 gives 41, outside {21, 26, 31}. -/
theorem kappa0_fails : cntX 0 5 = 41 ∧ 41 ≠ 21 ∧ 41 ≠ 26 ∧ 41 ≠ 31 := by
  decide

/-- The kappa = 1 normalization gives 6, outside {21, 26, 31}. -/
theorem kappa1_fails : cntX 1 5 = 6 ∧ 6 ≠ 21 ∧ 6 ≠ 26 ∧ 6 ≠ 31 := by
  decide

/-- The kappa = 2 normalization gives 16, outside {21, 26, 31}. -/
theorem kappa2_fails : cntX 2 5 = 16 ∧ 16 ≠ 21 ∧ 16 ≠ 26 ∧ 16 ≠ 31 := by
  decide

/-- The kappa = 3 normalization gives 36, outside {21, 26, 31}. -/
theorem kappa3_fails : cntX 3 5 = 36 ∧ 36 ≠ 21 ∧ 36 ≠ 26 ∧ 36 ≠ 31 := by
  decide

/-- The count varies with kappa, so "the count N_p" is not even
    well-defined over the monodromy-manifold family. -/
theorem counts_differ : cntX 0 5 ≠ cntX 1 5 := by decide

end Tlmc1581
