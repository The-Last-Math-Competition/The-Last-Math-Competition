import Init.Data.Rat

set_option maxRecDepth 100000

/-!
# Disproof of TLMC conjecture 00000001042

Original conjecture: "The variance of the value-set size of a random polynomial f uniform
of degree <= d is asymptotically q*(1 - 1/e)/d (value-set variance)."

Attack point (from the verify queue): d = 1, q = 101, exact enumeration.

Object discipline: "uniform of degree <= d" means f is uniform over ALL coefficient tuples,
so for d = 1 the polynomial f(x) = a*x + b has (a, b) uniform over F_101 x F_101 (10201
polynomials, including the constant ones a = 0).  The value set is {f(x) : x in F_101}.

* If a != 0, x -> a*x + b is a bijection F_101 -> F_101, so the value-set size is 101.
* If a = 0, f is constant and the value-set size is 1.

Exact enumeration gives E[V] = 10101/101, E[V^2] = 1020101/101 and

    Var = E[V^2] - E[V]^2 = 1000000/10201 ~= 98.0296,

whereas the conjecture predicts q(1 - 1/e)/d = 101(1 - 1/e) ~= 63.8442
(Euler's number e = 2.718281828...).  Moreover Var = (q-1)^3/q^2 -> q as q -> infinity,
so the true asymptotic constant at d = 1 is 1, not 1 - 1/e ~= 0.6321.

Everything below is proved inside Lean 4 core (no Mathlib) using only `decide` and
hand-built elementary arithmetic lemmas (pure structural inductions); `lean4/Check.lean`
audits that every theorem is axiom-free.  In particular the attack theorems avoid
`omega`/`simp`-generated classical reasoning and avoid truncated subtraction entirely:
a candidate value e = n/d of Euler's number with 1 < e <= 68/25 is represented by the
pair (m, d) with m = n - d > 0, i.e. n = m + d.
-/

namespace TLMC01042

/-! ### Small axiom-free arithmetic toolkit (structural inductions) -/

theorem mul_assoc' : ∀ a b c : Nat, a * b * c = a * (b * c)
  | _, _, 0 => rfl
  | a, b, c + 1 => by
      show (a * b) * c + a * b = a * (b * c + b)
      rw [mul_assoc' a b c, Nat.mul_add a (b * c) b]

theorem mul_left_comm' (a b c : Nat) : a * b * c = b * a * c := by
  rw [Nat.mul_comm a b]

/-- "Swap the outer factors": a * (b * c) = b * (a * c). -/
theorem mul_swap (a b c : Nat) : a * (b * c) = b * (a * c) := by
  rw [← mul_assoc', Nat.mul_comm a b, mul_assoc']

theorem add_le_add_right_cancel' : ∀ (k a b : Nat), a + k ≤ b + k → a ≤ b
  | 0, _, _, h => h
  | k + 1, a, b, h => add_le_add_right_cancel' k a b (Nat.le_of_succ_le_succ h)

/-- Right-distributivity, built from the axiom-free `Nat.mul_comm` / `Nat.mul_add`
(core's `Nat.add_mul` drags in `propext`). -/
theorem add_mul' (a b c : Nat) : (a + b) * c = a * c + b * c := by
  rw [Nat.mul_comm (a + b) c, Nat.mul_add c a b, Nat.mul_comm c a, Nat.mul_comm c b]

/-! ### The enumeration (q = 101, d = 1) -/

/-- Value-set size over F_101 of f(x) = a*x + b: the linear map is bijective when a != 0
(size 101), otherwise f is constant (size 1). -/
def V (a : Nat) (_b : Nat) : Nat := if a = 0 then 1 else 101

/-- `sumTo f k = f 0 + f 1 + ... + f k` (k+1 terms). -/
def sumToAux (f : Nat → Nat) : Nat → Nat → Nat
  | acc, 0 => acc + f 0
  | acc, k + 1 => sumToAux f (acc + f (k + 1)) k

def sumTo (f : Nat → Nat) (k : Nat) : Nat := sumToAux f 0 k

/-- Total of V over all (a, b) in F_101 x F_101 (all 10201 polynomials of degree <= 1). -/
def totalV : Nat := sumTo (fun a => sumTo (fun b => V a b) 100) 100

/-- Total of V^2 over all (a, b) in F_101 x F_101. -/
def totalV2 : Nat := sumTo (fun a => sumTo (fun b => (V a b) ^ 2) 100) 100

/-- Exact enumeration of the first moment: 100 * 101 * 101 + 101 * 1. -/
theorem totalV_eq : totalV = 1020201 := by decide

/-- Exact enumeration of the second moment: 100 * 101 * 101^2 + 101 * 1. -/
theorem totalV2_eq : totalV2 = 103030201 := by decide

/-- Scaled exact variance.  With N = 101^2 = 10201 pairs, Var = totalV2/N - (totalV/N)^2,
so Var * N^2 = totalV2 * N - totalV^2 = 10201000000 = 1000000 * 10201, i.e.
Var = 1000000/10201 = 98.0296... -/
theorem scaledVar_eq : totalV2 * 10201 - totalV * totalV = 10201000000 := by decide

/-- The arithmetic kernel of the gap: 4343/68 < 1000000/10201 (cross-multiplied by 101^4):
the conjectured value 101(1 - 1/e) < 4343/68 (given e <= 68/25, see `attack`) is strictly
below the true variance 1000000/10201. -/
theorem gap : 4343 * 104060401 < 68 * 10201000000 := by decide

/-- Boundary reading: if one instead samples uniformly over degree-EXACTLY-1 polynomials
(a != 0: 100 choices for a, 101 for b, N = 10100 pairs), then every value set has size 101
(`deg1_deterministic`), the variance is exactly 0, and the conjecture fails as well. -/
def totalW : Nat := sumTo (fun a => sumTo (fun b => V (a + 1) b) 100) 99

def totalW2 : Nat := sumTo (fun a => sumTo (fun b => (V (a + 1) b) ^ 2) 100) 99

theorem scaledVar1_eq : totalW2 * 10100 - totalW * totalW = 0 := by decide

theorem deg1_deterministic (a b : Nat) (ha : 0 < a) : V a b = 101 := by
  show (if a = 0 then 1 else 101) = 101
  exact if_neg (Nat.ne_of_gt ha)

/-! ### The attack -/

/-- **ATTACK** (degree <= d reading; d = 1, q = 101).  A candidate value e = n/d of Euler's
number with 1 < e <= 68/25 is represented by (m, d) with n = m + d and m > 0 (Euler's
number satisfies this: e = sum 1/k! < 11743/4320 < 68/25 = 2.72, and e > 1).  The
conjectured variance q(1 - 1/e)/d = 101 * m/(m + d) would satisfy

    (totalV2 * 10201 - totalV * totalV) * (m + d) = 101 * m * 101^2

after scaling by 101^4 (the left side is Var * 101^4 * n, the right side is the conjectured
value 101 * m/n times 101^4 * n).  This theorem refutes that equation for every such (m, d).

Proof sketch: 25 * (m + d) <= 68 * d gives 25 * m <= 43 * d, hence 68 * m <= 43 * (m + d).
Scaling both the equation and the inequality by 101 * 101^4 and combining yields
68 * 10201000000 * (m + d) <= 4343 * 101^4 * (m + d), and cancelling the positive factor
(m + d) contradicts `gap` (693668000000 > 451934321543). -/
theorem attack (m d : Nat) (hm : 0 < m) (hnd : 25 * (m + d) ≤ 68 * d) :
    ¬ (totalV2 * 10201 - totalV * totalV) * (m + d) = 101 * m * (10201 * 10201) := by
  intro hEq
  rw [scaledVar_eq] at hEq
  have hN : (10201 * 10201 : Nat) = 104060401 := by decide
  rw [hN] at hEq
  -- hEq : 10201000000 * (m + d) = 101 * m * 104060401
  have h1 : 25 * m + 25 * d ≤ 68 * d := by
    rw [← Nat.mul_add 25 m d]
    exact hnd
  have h2 : 25 * m ≤ 43 * d := by
    have e : 68 * d = 43 * d + 25 * d := add_mul' 43 25 d
    rw [e] at h1
    exact add_le_add_right_cancel' (25 * d) (25 * m) (43 * d) h1
  have h3 : 68 * m ≤ 43 * (m + d) := by
    calc 68 * m = 43 * m + 25 * m := add_mul' 43 25 m
      _ ≤ 43 * m + 43 * d := Nat.add_le_add_left h2 (43 * m)
      _ = 43 * (m + d) := (Nat.mul_add 43 m d).symm
  have h4 : (101 * 104060401) * (68 * m) ≤ (101 * 104060401) * (43 * (m + d)) :=
    Nat.mul_le_mul_left (101 * 104060401) h3
  -- rewrite both sides of h4 into the shapes dictated by hEq
  have h5 : (101 * 104060401) * (68 * m) = 68 * (101 * m * 104060401) := by
    calc (101 * 104060401) * (68 * m)
        = 101 * (104060401 * (68 * m)) := mul_assoc' 101 104060401 (68 * m)
      _ = 101 * (68 * (104060401 * m)) := by rw [mul_swap 104060401 68 m]
      _ = (101 * 68) * (104060401 * m) := (mul_assoc' 101 68 (104060401 * m)).symm
      _ = (68 * 101) * (104060401 * m) := by rw [Nat.mul_comm 101 68]
      _ = 68 * (101 * (104060401 * m)) := mul_assoc' 68 101 (104060401 * m)
      _ = 68 * (101 * (m * 104060401)) := by rw [Nat.mul_comm 104060401 m]
      _ = 68 * (101 * m * 104060401) := by rw [← mul_assoc' 101 m 104060401]
  have h6 : (101 * 104060401) * (43 * (m + d)) = 451934321543 * (m + d) := by
    have hf : (101 * 104060401) * 43 = 451934321543 := by decide
    calc (101 * 104060401) * (43 * (m + d))
        = ((101 * 104060401) * 43) * (m + d) := (mul_assoc' (101 * 104060401) 43 (m + d)).symm
      _ = 451934321543 * (m + d) := by rw [hf]
  rw [h5, ← hEq, h6] at h4
  -- h4 : 68 * (10201000000 * (m + d)) ≤ 451934321543 * (m + d)
  have h7 : (68 * 10201000000) * (m + d) ≤ 451934321543 * (m + d) := by
    rw [← mul_assoc'] at h4
    exact h4
  have h8 : (m + d) * 693668000000 ≤ (m + d) * 451934321543 := by
    rw [Nat.mul_comm (m + d) 693668000000, Nat.mul_comm (m + d) 451934321543]
    show (68 * 10201000000) * (m + d) ≤ 451934321543 * (m + d)
    exact h7
  exact absurd (Nat.le_of_mul_le_mul_left h8 (Nat.lt_of_lt_of_le hm (Nat.le_add_right m d)))
    (by decide)

/-- **ATTACK** (boundary: degree-exactly-1 reading).  Over degree-exactly-1 polynomials the
variance is exactly 0 (`scaledVar1_eq`), while the conjectured value 101 * (1 - 1/e) is
strictly positive for Euler's number e > 1 (represented by m = n - d > 0): the conjectured
value 101 * m/n cannot vanish. -/
theorem attack_exact1 (m : Nat) (hm : 0 < m) :
    ¬ (totalW2 * 10100 - totalW * totalW) * m = 101 * m * (10100 * 10100) := by
  intro hEq
  rw [scaledVar1_eq, Nat.zero_mul] at hEq
  -- hEq : 0 = 101 * m * (10100 * 10100)
  have hpos : 0 < 101 * m * (10100 * 10100) :=
    Nat.mul_pos (Nat.mul_pos (by decide) hm) (by decide)
  rw [← hEq] at hpos
  exact Nat.not_lt_zero 0 hpos

end TLMC01042
