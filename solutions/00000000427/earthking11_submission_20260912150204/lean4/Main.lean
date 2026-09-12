/-
  Disproof of conjecture 00000000427.

  The conjecture: the count of "spin symmetric plane partitions" at `t = 1`
  equals

      F(n) = 2^{floor(n^2/4)} * prod_{i=1..n} (2i-1)!! / i! .

  Refutation strategy.  A count at `t = 1` is a cardinality, hence a natural
  number; but the formula is not always a natural number.  Each odd double
  factorial (2i-1)!! is a product of odd integers, so `v2((2i-1)!!) = 0`, while
  the denominators `i!` contribute.  The resulting 2-adic valuation is

      v2(F(n)) = floor(n^2/4) - sum_{i=1..n} v2(i!) ,

  and this is `-1` already at `n = 4`; in fact it is `< 0` for every `n >= 4`.
  Hence `F(4) = 525 / 2` is not an integer, and no natural number (no
  cardinality) can equal it.  The formalisation below makes this concrete: it
  defines `F : Nat -> Rat`, proves the closed value `F 4 = 525 / 2`, and proves
  `conjecture_00000000427_false : forall m : Nat, (m : Rat) != F 4` by comparing
  denominators: a natural number has denominator `1` when cast to `Rat`, whereas
  `525/2` has denominator `2`.

  Design note: `F` is defined through the core primitive `mkRat` with an
  explicit integer numerator and natural denominator.  The irreducible core
  operations `Rat.mul` / `Rat.inv` do not reduce under `decide`, but `mkRat`
  does, so every closed value below is checked by the kernel without any
  arithmetic tactic beyond `decide`.

  Lean 4, core only -- no Mathlib dependency.
-/

namespace Tlmc427

/-! ## The odd double factorial and the conjectured formula -/

/-- The odd double factorial `(2i-1)!! = 1 * 3 * ... * (2i-1)`, with
`oddDF 0 = 1` (the empty product). -/
def oddDF : Nat → Nat
  | 0 => 1
  | n + 1 => (2 * n + 1) * oddDF n

/-- `oddDFProd n = prod_{i=1..n} (2i-1)!!`. -/
def oddDFProd : Nat → Nat
  | 0 => 1
  | n + 1 => oddDFProd n * oddDF (n + 1)

/-- The factorial. -/
def fact : Nat → Nat
  | 0 => 1
  | n + 1 => (n + 1) * fact n

/-- `factProd n = prod_{i=1..n} i!`. -/
def factProd : Nat → Nat
  | 0 => 1
  | n + 1 => factProd n * fact (n + 1)

/-- The conjectured count at `t = 1`, as an exact rational number.  Since
`prod_{i=1..n} (2i-1)!!/i! = (prod_{i=1..n} (2i-1)!!) / (prod_{i=1..n} i!)`,
the formula is represented as the single quotient

`F n = 2^{floor(n^2/4)} * (prod_{i=1..n} (2i-1)!!) / (prod_{i=1..n} i!)`,

built with `mkRat` from an explicit integer numerator and natural
denominator. -/
def F (n : Nat) : Rat :=
  mkRat ((2 : Int) ^ (n * n / 4) * (oddDFProd n : Int)) (factProd n)

/-! ## Closed values -/

/-- The first odd double factorial values needed for `n = 4`. -/
theorem oddDF_four : oddDF 4 = 105 := by decide
theorem oddDFProd_four : oddDFProd 4 = 4725 := by decide
theorem factProd_four : factProd 4 = 288 := by decide

/-- The formula is integral for the first three values, which is presumably why
the claim looked plausible. -/
theorem F_one : F 1 = 1 := by decide
theorem F_two : F 2 = 3 := by decide
theorem F_three : F 3 = 15 := by decide

/-- **The counterexample.** `F(4) = 525/2`, a rational that is not an
integer.

The left side is `mkRat 75600 288`; the right side is rewritten past the
irreducible `Rat.mul` / `Rat.inv` using `Rat.div_def`, `Rat.num_mul`,
`Rat.den_mul`, `Rat.num_inv`, `Rat.den_inv`, after which both sides are closed
`Int` / `Nat` expressions that `decide` evaluates.  The `Rat.ext` splits the
proof into numerator and denominator. -/
theorem F_four : F 4 = 525 / 2 := by
  apply Rat.ext
  · rw [Rat.div_def, Rat.num_mul]
    simp only [Rat.num_inv, Rat.den_inv, Rat.num_ofNat, Rat.den_ofNat]
    decide
  · rw [Rat.div_def, Rat.den_mul]
    simp only [Rat.num_inv, Rat.den_inv, Rat.num_ofNat, Rat.den_ofNat]
    decide

/-- The denominator of `F 4` in lowest terms is `2`. -/
theorem F_four_den : (F 4).den = 2 := by decide

/-- Consequently `F 4` is not an integer. -/
theorem F_four_not_integer : (F 4).den ≠ 1 := by
  rw [F_four_den]
  decide

/-! ## The refutation -/

/-- A natural number has denominator `1` when cast to `Rat`. -/
theorem nat_cast_den (m : Nat) : (m : Rat).den = 1 := Rat.den_natCast m

/-- **Conjecture 00000000427 is false.** No natural number equals
`F 4 = 525/2`. Since a count at `t = 1` is a natural number, the conjectured
equality already fails at `n = 4`.

Proof: apply `Rat.den` to a hypothetical equality `(m : Rat) = F 4`.  The left
side has denominator `1` (`nat_cast_den`), the right side has denominator `2`
(`F_four_den`), giving `1 = 2`, a contradiction. -/
theorem conjecture_00000000427_false : ∀ m : Nat, (m : Rat) ≠ F 4 := by
  intro m h
  have hden : (m : Rat).den = (F 4).den := congrArg Rat.den h
  rw [nat_cast_den m, F_four_den] at hden
  exact (by decide : (1 : Nat) ≠ 2) hden

/-- Contrapositive packaging: there is no natural number equal to `F 4`. -/
theorem no_nat_eq_F_four : ¬ ∃ m : Nat, (m : Rat) = F 4 := by
  rintro ⟨m, hm⟩
  exact conjecture_00000000427_false m hm

end Tlmc427
