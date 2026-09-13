/-
  Disproof of conjecture `00000001260`.

  The conjecture asserts the *universal* upper bound

      p(n) ≤ n + 2     for the factor complexity of every primitive substitution

  within the "purely substitutive class" (纯替换类).  The filed text imposes no
  alphabet restriction and does not exclude constant-length substitutions.

  The Thue–Morse word is the fixed point of the primitive substitution

      0 ↦ 01,   1 ↦ 10,

  whose incidence matrix is [[1,1],[1,1]] — positive, hence primitive.  It has
  six distinct factors of length 3, so `p(3) = 6 > 5 = 3 + 2` and the asserted
  universal bound fails already at `n = 3`.

  What is formalised below is exactly the required LOWER bound `p(3) ≥ 6`: each
  of the six triples is a genuine factor of the Thue–Morse word by construction
  (it starts at an explicit position), so the number of distinct triples
  produced is a lower bound for `p(3)`.  Refuting a universal *upper* bound
  needs only such a lower bound; no completeness (upper-bound) argument and no
  enumeration of all length-3 factors is required.
-/

import Std

namespace Tlmc1260

/-- The substitution `0 ↦ 01, 1 ↦ 10`, as a morphism on `Bool` lists.

`false` is `0` and `true` is `1`.  Structural recursion, so `gen` below reduces
under `decide` (a well-founded definition would get stuck at `WellFounded.fix`). -/
def step : List Bool → List Bool
  | [] => []
  | b :: t => (if b then [true, false] else [false, true]) ++ step t

/-- `gen k = σ^k(0)`: explicit finite prefixes of the Thue–Morse fixed point. -/
def gen : Nat → List Bool
  | 0 => [false]
  | k + 1 => step (gen k)

/-- The Thue–Morse word: `tm n` is the parity of the binary digit sum of `n`.
This is the standard closed form of the fixed point of `0 ↦ 01, 1 ↦ 10`. -/
def tm (n : Nat) : Bool :=
  (List.range (n + 1)).foldl (fun a i => if Nat.testBit n i then !a else a) false

/-- Sanity check: the closed form agrees with the substitution on a prefix. -/
theorem tm_prefix_agrees : (List.range 64).map tm = gen 6 := by decide

/-- The length-3 factors of `tm` starting at positions `0, …, 61`.

Every entry of this list is a genuine factor of the Thue–Morse word (it is the
length-3 block beginning at the recorded position), so `fac3.eraseDups.length`
is a lower bound for the true complexity `p(3)`. -/
def fac3 : List (List Bool) :=
  (List.range 62).map (fun i => [tm i, tm (i + 1), tm (i + 2)])

/-- `p(3) ≥ 6`: six distinct length-3 factors of the Thue–Morse word occur. -/
theorem tm_p3_ge_6 : 6 ≤ fac3.eraseDups.length := by decide

/-- The six distinct length-3 factors, listed explicitly. -/
theorem tm_six_factors :
    fac3.eraseDups =
      [[false, true, true], [true, true, false], [true, false, true],
       [false, true, false], [true, false, false], [false, false, true]] := by
  decide

/-- The number of distinct factors found is exactly `6`. -/
theorem tm_p3_eq_6 : fac3.eraseDups.length = 6 := by decide

/-- `p(3) = 6 > 5 = 3 + 2`: the asserted universal bound fails at `n = 3`. -/
theorem tm_refutes_bound : fac3.eraseDups.length > 3 + 2 := by decide

/-- The incidence matrix of the substitution `0 ↦ 01, 1 ↦ 10`. -/
def incidence : List (List Nat) := [[1, 1], [1, 1]]

/-- Every entry of the incidence matrix is positive, which is the standard
witness that the substitution is primitive. -/
theorem incidence_positive : ∀ r ∈ incidence, ∀ c ∈ r, 0 < c := by decide

/-- Packaged refutation of the literal universal reading: at `n = 3` the
complexity is `6`, and `6 ≤ 3 + 2` is false. -/
theorem conjecture_00000001260_false :
    fac3.eraseDups.length = 6 ∧ ¬ (fac3.eraseDups.length ≤ 3 + 2) := by
  decide

end Tlmc1260
