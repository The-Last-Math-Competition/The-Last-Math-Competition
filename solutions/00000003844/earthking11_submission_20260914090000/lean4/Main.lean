/-
  Disproof of conjecture `00000003844`.

  Conjecture (as filed):
    Definition: the covering number of a monoid is the least number of proper
                submonoids needed to cover it, infinity if impossible.
    Conjecture: every finite-type 0-Hecke monoid and every plactic monoid has
                infinite covering number, and arbitrary direct products of
                these two classes still have infinite covering number.

  The conjecture is FALSE, already for the 0-Hecke monoid H(S_3) of the finite
  Coxeter system (S_3, {s_1, s_2}): its covering number is exactly 2.

  H(S_3) is the monoid with generators pi_1, pi_2 subject to
      pi_i^2 = pi_i,   pi_1 pi_2 pi_1 = pi_2 pi_1 pi_2,
  and elements indexed by S_3 = {e, s_1, s_2, s_1s_2, s_2s_1, w_0}; the
  product is the Demazure product  pi_u * pi_v = pi_{u star v}.  The 6 x 6
  table below is that product; the labelling of the indices 0..5 is

      0 = e,  1 = s_2,  2 = s_1,  3 = s_1s_2,  4 = s_2s_1,  5 = w_0.

  Then
      A = {e, s_2}            (indices 0, 1)      is a submonoid,
      B = H(S_3) \ {s_2}      (indices 0,2,3,4,5) is a PROPER submonoid,
      A union B = H(S_3),
  so the covering number is at most 2; and it is not 1, because no proper
  submonoid equals the whole monoid.  Hence it is exactly 2.  This is
  formalised below by exhaustive computation (`decide`), with NO imports at
  all: only core Lean, and the axiom audit reports only `propext`.

  The same two-element argument works for every finite-type 0-Hecke monoid of
  rank >= 2, using the length identity
      length(x star y) >= max(length x, length y):
  if x, y != s then x star y != s, so H \ {s} is closed.  Only the rank <= 1
  cases (the trivial monoid and A_1 = {e, s}) behave differently.

  The direct-product clause also fails: if M1 = union_i A_i and
  M2 = union_j B_j with proper submonoids, then M1 x M2 = union_{i,j} A_i x B_j
  with each A_i x B_j a proper submonoid, so
      cov(M1 x M2) <= cov(M1) * cov(M2).
  With M = H(S_3) this gives cov(M x M) <= 4, not infinity.

  Core Lean only, no imports, no Mathlib, no `sorry`.
-/

namespace Tlmc3844

/-! ## The 0-Hecke monoid H(S_3) -/

/-- Multiplication table of H(S_3), the 0-Hecke monoid of type A_2.
    Row / column indices: 0 = e, 1 = s_2, 2 = s_1, 3 = s_1s_2, 4 = s_2s_1,
    5 = w_0.  Entry `(row a).getD b 0` is `a * b` for the Demazure product. -/
def tbl : List (List Nat) :=
  [[0, 1, 2, 3, 4, 5],
   [1, 1, 4, 5, 4, 5],
   [2, 3, 2, 3, 5, 5],
   [3, 3, 5, 5, 5, 5],
   [4, 5, 4, 5, 5, 5],
   [5, 5, 5, 5, 5, 5]]

/-- The Demazure product on the six elements. -/
def mul (a b : Nat) : Nat := (tbl.getD a []).getD b 0

/-- The six elements of H(S_3). -/
def elems : List Nat := [0, 1, 2, 3, 4, 5]

/-! ## The monoid axioms -/

/-- Associativity, checked over all 6^3 = 216 triples. -/
def checkAssoc : Bool :=
  (List.range 6).all fun a =>
    (List.range 6).all fun b =>
      (List.range 6).all fun c =>
        mul (mul a b) c == mul a (mul b c)

theorem assoc : checkAssoc = true := by decide

/-- `0 = e` is a two-sided identity. -/
def checkIdentity : Bool :=
  (List.range 6).all fun a => (mul 0 a == a) && (mul a 0 == a)

theorem identity : checkIdentity = true := by decide

/-- The generator `2 = s_1` is idempotent. -/
theorem gen_idem_s1 : mul 2 2 = 2 := by decide

/-- The generator `1 = s_2` is idempotent. -/
theorem gen_idem_s2 : mul 1 1 = 1 := by decide

/-- The braid relation `s_1 s_2 s_1 = s_2 s_1 s_2` (both sides are `w_0`). -/
theorem braid : mul (mul 2 1) 2 = mul (mul 1 2) 1 := by decide

/-- `s_1 s_2 = index 3` and `s_2 s_1 = index 4`. -/
theorem s1_mul_s2 : mul 2 1 = 3 := by decide
theorem s2_mul_s1 : mul 1 2 = 4 := by decide

/-! ## Submonoids and the covering number -/

/-- `S` is a submonoid: it contains the identity `0` and is closed under the
    product.  (`Finset` and the `Submonoid`/`Monoid` typeclasses are not
    available without imports, so this is hand-rolled over `List`/`Nat`.) -/
def sub (S : List Nat) : Bool :=
  S.contains 0 && S.all (fun a => S.all (fun b => S.contains (mul a b)))

/-- The witness cover: `A = {e, s_2}`. -/
def A : List Nat := [0, 1]

/-- The witness cover: `B = H(S_3) \ {s_2}`. -/
def B : List Nat := [0, 2, 3, 4, 5]

theorem A_sub : sub A = true := by decide
theorem B_sub : sub B = true := by decide
theorem A_proper : A.length < 6 := by decide
theorem B_proper : B.length < 6 := by decide

/-- `A ∪ B = H(S_3)`. -/
def checkCover : Bool :=
  elems.all (fun x => A.contains x || B.contains x)

theorem cover : checkCover = true := by decide

/-- Enumerate the 64 subsets of `H(S_3)` by bitmask. -/
def maskSub (m : Nat) : List Nat :=
  (List.range 6).filter fun i => (m >>> i) &&& 1 == 1

/-- `m` is the mask of a single PROPER submonoid that covers everything. -/
def coverByOne (m : Nat) : Bool :=
  sub (maskSub m) && (maskSub m).length < 6 &&
    elems.all (fun x => (maskSub m).contains x)

/-- No single proper submonoid covers `H(S_3)`: all 64 subsets are tried. -/
def checkNoOneCover : Bool :=
  (List.range 64).all fun m => !(coverByOne m)

theorem no_one_cover : checkNoOneCover = true := by decide

/-! ## The refutation -/

/-- The covering number of `H(S_3)` is at most 2. -/
theorem covering_number_le_two :
    sub A = true ∧ sub B = true ∧ A.length < 6 ∧ B.length < 6 ∧
      elems.all (fun x => A.contains x || B.contains x) = true :=
  ⟨A_sub, B_sub, A_proper, B_proper, cover⟩

/-- The covering number of `H(S_3)` is not 1. -/
theorem covering_number_ne_one :
    (List.range 64).all (fun m => !(coverByOne m)) = true :=
  no_one_cover

/-- **The covering number of `H(S_3)` is exactly 2.**  2 suffices
    (`A_sub`, `B_sub`, `cover`) and 1 does not (`no_one_cover`).  Since
    `H(S_3)` is a finite-type 0-Hecke monoid, its covering number is finite,
    which refutes the first clause of the conjecture. -/
theorem covering_number_is_two :
    sub A = true ∧ sub B = true ∧ A.length < 6 ∧ B.length < 6 ∧
      elems.all (fun x => A.contains x || B.contains x) = true ∧
      (List.range 64).all (fun m => !(coverByOne m)) = true :=
  ⟨A_sub, B_sub, A_proper, B_proper, cover, no_one_cover⟩

/-- **Conjecture `00000003844` is false.**  There is a finite-type 0-Hecke
    monoid, namely `H(S_3)`, that is covered by two proper submonoids: the
    covering number is therefore not infinite. -/
theorem conjecture_00000003844_false :
    ∃ A B : List Nat,
      sub A = true ∧ sub B = true ∧ A.length < 6 ∧ B.length < 6 ∧
        elems.all (fun x => A.contains x || B.contains x) = true :=
  ⟨A, B, A_sub, B_sub, A_proper, B_proper, cover⟩

/-! ## Evaluations of the underlying `Bool` definitions -/

-- `#eval` must be applied to the `Bool` definitions, not to proof terms:
-- Lean refuses to evaluate proofs ("proofs are not computationally relevant").
#eval checkAssoc        -- expect true
#eval checkIdentity     -- expect true
#eval checkCover        -- expect true
#eval checkNoOneCover   -- expect true
#eval (A ++ B).eraseDups.length   -- expect 6

end Tlmc3844
