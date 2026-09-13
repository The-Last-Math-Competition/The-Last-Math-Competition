import Std

/-!
# Disproof of conjecture 00000000155

The conjecture states that the only Bell primes are `B_2 = 2` and `B_3 = 5`.
We refute this by exhibiting two further Bell primes using the *same* 0-indexed
convention that the conjecture file uses (which pins `B_2 = 2`, `B_3 = 5`):

* `B_7  = 877`      is prime,
* `B_13 = 27644437` is prime.

Hence `{2, 5}` is not the complete list of Bell primes.

Everything is proved in core Lean 4 (only `import Std`, no Mathlib, no `sorry`,
no `axiom`, and no `native_decide` / `ofReduceBool`).
-/

set_option maxRecDepth 100000

namespace Tlmc155

/-- One step of the Bell triangle (Aitken's array).

Given the previous row `row`, produce the next row.  The first entry of the
next row is the last entry of `row`, and every following entry is the sum of
the entry to its left and the entry above-left.  The head of the `n`-th row is
the `n`-th Bell number. -/
def bellStep : List Nat → List Nat → List Nat
  | [], acc => acc.reverse
  | x :: rest, acc => bellStep rest ((acc.headD 0 + x) :: acc)

/-- The next row of the Bell triangle. -/
def nextBellRow (row : List Nat) : List Nat :=
  match row with
  | [] => [1]
  | _ => bellStep row [row.foldl (fun _ x => x) 0]

/-- `bellRows n` is the `n`-th row of the Bell triangle. -/
def bellRows : Nat → List Nat
  | 0 => [1]
  | n + 1 => nextBellRow (bellRows n)

/-- The `n`-th Bell number (0-indexed): `B_0 = 1, B_1 = 1, B_2 = 2, …` -/
def bell (n : Nat) : Nat :=
  (bellRows n).headD 0

/-- Trial division for odd candidate divisors `d`, with fuel so that the
recursion is structural and kernel-reducible.  It returns `true` once
`d * d > n`, i.e. no divisor has been found. -/
def trialDiv (n : Nat) : Nat → Nat → Bool
  | _, 0 => true
  | d, fuel + 1 =>
      if d * d > n then true
      else if n % d == 0 then false
      else trialDiv n (d + 2) fuel

/-- A computable primality predicate (trial division).  For `n ≥ 3` it tests
all odd divisors starting from `3`, stopping at `√n`. -/
def isPrimeB (n : Nat) : Bool :=
  if n < 2 then false
  else if n == 2 then true
  else if n % 2 == 0 then false
  else trialDiv n 3 (n + 1)

/-! ### Bell-number values (the file's own indexing) -/

theorem bell_zero : bell 0 = 1 := by decide

theorem bell_one : bell 1 = 1 := by decide

theorem bell_two : bell 2 = 2 := by decide

theorem bell_three : bell 3 = 5 := by decide

theorem bell_four : bell 4 = 15 := by decide

theorem bell_five : bell 5 = 52 := by decide

theorem bell_six : bell 6 = 203 := by decide

theorem bell_seven : bell 7 = 877 := by decide

theorem bell_thirteen : bell 13 = 27644437 := by decide

/-! ### Primality of the two extra Bell primes -/

theorem prime_877 : isPrimeB 877 = true := by decide

theorem prime_27644437 : isPrimeB 27644437 = true := by decide

/-! ### The conjecture is false -/

/-- Refutation: `B_7 = 877` and `B_13 = 27644437` are both prime, and neither
equals `B_2 = 2` nor `B_3 = 5`.  Therefore the Bell primes are not exactly
`{2, 5}`. -/
theorem conjecture_00000000155_false :
    bell 2 = 2 ∧
    bell 3 = 5 ∧
    isPrimeB (bell 7) = true ∧
    isPrimeB (bell 13) = true ∧
    bell 7 ≠ bell 2 ∧
    bell 7 ≠ bell 3 ∧
    bell 13 ≠ bell 2 ∧
    bell 13 ≠ bell 3 := by
  decide

end Tlmc155
