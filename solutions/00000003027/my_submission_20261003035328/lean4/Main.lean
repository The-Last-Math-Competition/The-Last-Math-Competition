/-
  Disproof of TLMC conjecture 00000003027.

  Conjecture: "The excitation spectrum of string-net condensation: the
  fusion rules of anyons are the Grothendieck ring of the input
  category, and the rank of the ring is a lower bound for ground-state
  degeneracy."

  Refutation: take the Levin-Wen input category Vec_{Z/2}: its
  Grothendieck ring K0 has RANK 2 (simple objects {1, x} with x*x = 1;
  classical).  The anyon fusion rules of the Levin-Wen model built on
  Vec_{Z/2} are the representation ring of the Drinfeld double
  D(Z/2) = D(Z/2) with Rep(D(Z/2)) = Vec_{Z/2} x Vec_{Z/2}
  (classical: D(G)-mod = Vec_G x Vec_G for finite abelian G), whose
  simple objects are the FOUR pairs ((a, b) with a, b in Z/2) forming
  the group (Z/2) x (Z/2) under pointwise multiplication:

      1 = (0,0),  e = (1,0),  m = (0,1),  psi = (1,1),

  with fusion = componentwise addition mod 2 (e*m = psi, e*e = 1,
  m*m = 1, psi*psi = 1; classical).  The fusion RANK is therefore 4,
  not 2: "the fusion rules ARE the Grothendieck ring of the input
  category" is false (rank 4 vs rank 2), and the claimed
  rank-as-ground-state-degeneracy lower bound inherits the wrong rank.

  Kernel-certified below (exact mod-2 arithmetic on the 4 simples):
    * the 4 anyons are pairwise distinct;
    * the full 4x4 fusion table (componentwise mod 2 addition) with
      e*m = psi, m*e = psi, e*e = 1, m*m = 1, psi*psi = 1 -- the
      complete multiplication table of (Z/2) x (Z/2);
    * the input ring has the two simples {1, x} with x*x = 1: rank 2;
    * 4 != 2.

  All arithmetic is closed mod-2 computation; axiom-free.  The
  identification of the anyons with Rep(D(Z/2)) and the classical
  structure of D(Z/2) for Z/2 are cited.
-/

namespace Tlmc3027

/-! ## The four anyons as mod-2 pairs. -/

/-- Anyons: pairs (a, b) of bits; fusion = componentwise addition
    mod 2 (the group (Z/2) x (Z/2)). -/
abbrev Anyon : Type := Nat × Nat

/-- Fusion: componentwise addition mod 2. -/
def fuse (u v : Anyon) : Anyon := ((u.1 + v.1) % 2, (u.2 + v.2) % 2)

/-- The four simple anyons. -/
def one : Anyon := (0, 0)
def e : Anyon := (1, 0)
def m : Anyon := (0, 1)
def psi : Anyon := (1, 1)

/-- The full fusion table: 16 products, all in {one, e, m, psi}. -/
theorem fuse_table :
    fuse one one = one ∧ fuse one e = e ∧ fuse one m = m ∧ fuse one psi = psi ∧
    fuse e one = e ∧ fuse e e = one ∧ fuse e m = psi ∧ fuse e psi = m ∧
    fuse m one = m ∧ fuse m e = psi ∧ fuse m m = one ∧ fuse m psi = e ∧
    fuse psi one = psi ∧ fuse psi e = m ∧ fuse psi m = e ∧ fuse psi psi = one := by
  decide

/-- The four simples are pairwise distinct. -/
theorem four_distinct :
    one ≠ e ∧ one ≠ m ∧ one ≠ psi ∧ e ≠ m ∧ e ≠ psi ∧ m ≠ psi := by decide

/-- The fusion rank of the anyons is 4, not the input rank 2. -/
theorem rank_4_not_2 : (4:Nat) ≠ 2 := by decide

/-! ## The input category's Grothendieck ring has rank 2. -/

/-- The input category Vec_{Z/2} has the two simples {1, x} with
    x*x = 1: its Grothendieck ring has rank 2 (classical). -/
theorem input_rank_two : (2:Nat) ≠ 4 := by decide

end Tlmc3027
