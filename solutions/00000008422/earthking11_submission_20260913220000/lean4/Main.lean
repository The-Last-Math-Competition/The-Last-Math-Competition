/-
  Disproof of conjecture `00000008422`: formalisation.

  Conjecture as filed (verbatim):

    Definition: The lambda spectrum of block designs: the set of realizable
    lambda values for given (v,k).  Conjecture: lambda is attainable if and
    only if lambda binom(v,t)/binom(k,t) is an integer (with t = k-1) and
    lambda is at most binom(v-2,k-2), so the spectrum is complete; the
    complement of the spectrum is a finite explicit exceptional set with at
    most k^2 exceptions.

  What this file formalises.

  * (v,k) = (6,3), t = k-1 = 2.  Here binom(6,2)/binom(3,2) = 15/3 = 5, so
    `5 * lambda` is an integer for every lambda, and the bound is
    lambda <= binom(4,1) = 4.  Hence the criterion predicts
    lambda in {1,2,3,4}.  A 2-(6,3,lambda) design is encoded as a sublist of
    the twenty 3-subsets of `Fin 6` (each written as a 6-bit mask).

      - `design2` and the complete design `triples` are explicit 2-(6,3,2)
        and 2-(6,3,4) designs, verified by `decide`;
      - exhaustive `decide` over all C(20,5) = 15504 five-element sublists
        shows no 2-(6,3,1) design exists (`no_design_1`);
      - by complementation inside the twenty triples (the complete design has
        lambda = 4, so complementing interchanges lambda and 4 - lambda),
        the same enumeration over the 15504 complements shows no 2-(6,3,3)
        design exists (`no_design_3`).

    So the (6,3) spectrum is exactly {2,4}, while the criterion predicts
    {1,2,3,4}: two "exceptions".  Since 2 <= k^2 = 9, this is consistent with
    the conjecture's own clause that the complement is exceptional with at
    most k^2 elements -- the (6,3) case refutes only the strict
    "spectrum is complete / if and only if" reading.

  * (v,k) = (22,3), the decisive case.  Here binom(22,2)/binom(3,2) = 231/3 =
    77, so the criterion predicts EVERY lambda in {1,...,binom(20,1)} =
    {1,...,20}.  But in any 2-(v,k,lambda) design the replication number
    r = lambda*(v-1)/(k-1) is a count and hence an integer; for k = 3 this
    counting gives 2*r = (v-1)*lambda, i.e. 2*r = 21*lambda at v = 22, which
    forces lambda even.  The ten odd values in {1,...,20} are therefore
    unattainable although predicted, and 10 > k^2 = 9.  This violates the
    exception clause itself, so it refutes the conjecture under BOTH readings
    (strict iff and "at most k^2 exceptions").

    The counting identity 2*r = (v-1)*lambda is the standard double count
    (each block through a point contains k-1 = 2 further points, and each of
    the v-1 pairs at that point is covered lambda times).  It is stated and
    proved on paper in `main.tex`; here `parity_22_3` formalises the final
    arithmetic step `2*r = 21*lambda -> 2 | lambda`, and the counting identity
    is kept as an explicit hypothesis.  See `lean4/README.md` for the scope
    note.

  Core Lean only (`import Std`); no Mathlib, no `Finset`, no `ZMod`, no
  `sorry`, no `native_decide`.
-/

import Std

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Tlmc8422

/-! ## Encoding of a 2-(6,3,lambda) design -/

/-- Number of 1-bits among the low six bits of `m`, i.e. the size of the
subset of `Fin 6` encoded by the 6-bit mask `m`. -/
def popcount6 (m : Nat) : Nat :=
  (List.range 6).foldl (fun a i => a + ((m >>> i) &&& 1)) 0

/-- The twenty 3-element subsets of `Fin 6`, as 6-bit masks. -/
def triples : List Nat := (List.range 64).filter (fun m => popcount6 m == 3)

/-- The fifteen 2-element subsets of `Fin 6`, as 6-bit masks. -/
def pairs : List Nat := (List.range 64).filter (fun m => popcount6 m == 2)

/-- `isDesign blocks lam` is true exactly when every one of the fifteen pairs
of points is contained in exactly `lam` of the 3-subsets listed in `blocks`.
This is the pair-covering condition of a 2-(6,3,lam) design. -/
def isDesign (blocks : List Nat) (lam : Nat) : Bool :=
  pairs.all (fun pm => (blocks.filter (fun b => (b &&& pm) == pm)).length == lam)

/-- All sublists of `xs` of length `n`.  The recursion is structural on the
list, so the kernel can evaluate it inside `decide`. -/
def sublistsLen : Nat → List α → List (List α)
  | 0, _ => [[]]
  | _, [] => []
  | n + 1, x :: xs => (sublistsLen n xs).map (x :: ·) ++ sublistsLen (n + 1) xs

/-- The complement of a set of triples inside all twenty triples. -/
def complement (c : List Nat) : List Nat :=
  triples.filter (fun b => !(c.contains b))

/-! ## Cardinalities -/

/-- There are C(6,3) = 20 triples. -/
theorem triples_len : triples.length = 20 := by decide

/-- There are C(6,2) = 15 pairs. -/
theorem pairs_len : pairs.length = 15 := by decide

/-! ## Existence for lambda = 2 and lambda = 4 -/

/-- An explicit 2-(6,3,2) design: ten triples, each pair covered exactly twice.
The masks encode (0,1,2), (0,1,3), (0,2,4), (0,3,5), (0,4,5), (1,2,5),
(1,3,4), (1,4,5), (2,3,4), (2,3,5). -/
def design2 : List Nat := [7, 11, 21, 41, 49, 38, 26, 50, 28, 44]

/-- `design2` is a genuine 2-(6,3,2) design. -/
theorem design2_is : isDesign design2 2 = true := by decide

/-- It has the expected number b = lambda*v*(v-1)/(k*(k-1)) = 10 of blocks. -/
theorem design2_len : design2.length = 10 := by decide

/-- The complete design (all twenty triples) is a 2-(6,3,4) design: each pair
lies in binom(4,1) = 4 triples. -/
theorem design4_is : isDesign triples 4 = true := by decide

/-- It has b = 20 blocks. -/
theorem design4_len : triples.length = 20 := triples_len

/-! ## Non-existence for lambda = 1 and lambda = 3 -/

/-- No 2-(6,3,1) design exists.  A 2-(6,3,1) design would have
b = 1*6*5/(3*2) = 5 blocks; the exhaustive `decide` below searches all
C(20,5) = 15504 five-element sublists of the twenty triples, and none covers
every pair exactly once.  (Equivalently, a Steiner triple system on 6 points
does not exist since 6 is neither 1 nor 3 mod 6.) -/
theorem no_design_1 :
    (sublistsLen 5 triples).all (fun c => !(isDesign c 1)) = true := by decide

/-- No 2-(6,3,3) design exists.  A 2-(6,3,3) design would have 15 blocks; its
complement among the twenty triples has 5 blocks and, since the complete
design has lambda = 4, each pair is covered 4 - 3 = 1 time.  Complementing is
a bijection between 5- and 15-element sublists, so the same enumeration of all
15504 five-element sublists rules out a 3-design as well. -/
theorem no_design_3 :
    (sublistsLen 5 triples).all (fun c => !(isDesign (complement c) 3)) = true :=
  by decide

/-- The (6,3) spectrum is not the criterion set: lambda = 2 and lambda = 4 are
attainable, while lambda = 1 and lambda = 3 are not, even though the criterion
`5 * lambda integral, lambda <= 4` predicts all four values. -/
theorem spectrum_6_3 :
    isDesign design2 2 = true ∧ isDesign triples 4 = true ∧
    (sublistsLen 5 triples).all (fun c => !(isDesign c 1)) = true ∧
    (sublistsLen 5 triples).all (fun c => !(isDesign (complement c) 3)) = true :=
  ⟨design2_is, design4_is, no_design_1, no_design_3⟩

/-! ## The criterion and the exception budget -/

/-- The criterion's predicted set at (6,3): lambda in {1,2,3,4}. -/
def predicted6 : List Nat := (List.range 4).map (· + 1)

/-- The criterion's predicted set at (22,3): lambda in {1,...,20}. -/
def predicted22 : List Nat := (List.range 20).map (· + 1)

/-- At (6,3) the criterion reads binom(6,2)/binom(3,2) = 5, an integer: every
lambda is predicted. -/
theorem criterion_6_3 : predicted6.all (fun l => (15 * l) % 3 == 0) = true := by decide

/-- At (22,3) the criterion reads binom(22,2)/binom(3,2) = 231/3 = 77: again
every lambda in {1,...,20} is predicted. -/
theorem criterion_22_3 : predicted22.all (fun l => (231 * l) % 3 == 0) = true := by decide

/-- The values at (6,3) that the necessary replication condition
2*r = 5*lambda rules out: exactly {1,3}. -/
theorem forced_out_6_3 : (predicted6.filter (fun l => (5 * l) % 2 != 0)) = [1, 3] := by decide

/-- At (6,3) there are 2 such forced-out values, which is within the
conjecture's budget k^2 = 9: the (6,3) case is absorbed by the exception
clause. -/
theorem budget_6_3 : (predicted6.filter (fun l => (5 * l) % 2 != 0)).length ≤ 3 ^ 2 :=
  by decide

/-- The ten odd values in {1,...,20} are forced out at (22,3) by
2*r = 21*lambda. -/
theorem forced_out_22_3 : (predicted22.filter (fun l => (21 * l) % 2 != 0)).length = 10 :=
  by decide

/-- 10 > k^2 = 9: at (22,3) the number of criterion-predicted values that are
forced to be unattainable exceeds the exception budget. -/
theorem budget_22_3 : 3 ^ 2 < (predicted22.filter (fun l => (21 * l) % 2 != 0)).length :=
  by decide

/-! ## The final arithmetic step of the divisibility argument -/

/-- (6,3): the counting identity 2*r = (v-1)*lambda = 5*lambda forces lambda
even. -/
theorem parity_6_3 (r lam : Nat) (h : 2 * r = 5 * lam) : 2 ∣ lam := by omega

/-- (22,3): the counting identity 2*r = (v-1)*lambda = 21*lambda forces lambda
even. -/
theorem parity_22_3 (r lam : Nat) (h : 2 * r = 21 * lam) : 2 ∣ lam := by omega

/-- (22,3), contrapositive form: an odd lambda admits no replication number
r, i.e. no 2-(22,3,lambda) design. -/
theorem no_odd_lambda_22_3 (lam : Nat) (hodd : lam % 2 = 1) :
    ¬ ∃ r, 2 * r = 21 * lam := by
  rintro ⟨r, hr⟩
  have h2 : 2 ∣ lam := parity_22_3 r lam hr
  omega

/-! ## The decisive package at (22,3) -/

/-- The two facts that make (22,3) decisive: the criterion predicts all twenty
values in {1,...,20}, and ten of them (the odd ones) are forced to be
unattainable by the replication identity, exceeding the k^2 = 9 budget. -/
theorem decisive_22_3 :
    predicted22.all (fun l => (231 * l) % 3 == 0) = true ∧
    (predicted22.filter (fun l => (21 * l) % 2 != 0)).length = 10 ∧
    3 ^ 2 < (predicted22.filter (fun l => (21 * l) % 2 != 0)).length :=
  ⟨criterion_22_3, forced_out_22_3, budget_22_3⟩

end Tlmc8422
