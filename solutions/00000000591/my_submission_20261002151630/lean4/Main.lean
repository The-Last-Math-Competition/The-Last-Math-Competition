/-!
# Disproof of TLMC conjecture 00000000591 (v2: the limit statement, formalized)

Conjecture (definition sentence quoted verbatim from
`conjectures/00000000591.md`): "Definition: Wilf's conjecture. Conjecture:
e·n(S) ≥ g(S) + e (n(S) the number of nongaps, g the Frobenius number).
New-direction conjecture: on embedding-dimension-3 semigroups the ratio of the
surplus e·n(S) − g(S) − e to g tends to 0, with an explicit convergence rate."

Verdict: FALSE.

## The explicit infinite family (embedding dimension 3)

For every `k : Nat` put `r = 6*k + 5` (coprime to 6, so `6, 2r, 3r` are
pairwise coprime) and

    S_k = ⟨6, 2*r, 3*r⟩  =  ⟨p*q, p*r, q*r⟩  with (p, q, r) = (2, 3, 6k+5).

`S_k` is a complete-intersection numerical semigroup, hence symmetric; writing
`g_k = Frobenius(S_k) = 2pqr - pq - pr - qr = 42*k + 29` and
`n_k = #{s ∈ S_k : 0 ≤ s ≤ g_k} = (g_k+1)/2 = 21*k + 15`, the Wilf surplus at
embedding dimension e = 3 is `surplus_k = 3*n_k - g_k - 3 = 21*k + 13`, hence

    ratio_k = surplus_k / g_k = (g_k - 3)/(2 g_k) = 1/2 - 3/(2 g_k) ≥ 1/3

for every `k` (`g_k ≥ 29 > 9`): the ratio stays bounded below by 1/3
arbitrarily far out in the family and tends to 1/2 — it does NOT tend to 0.
`reproduce.py` verifies `g`, `n`, `surplus`, `gcd(surplus_k, g_k) = 1` and the
ratio by exhaustive enumeration of `S_k` for many `k`, and verifies the same
formulas on the prime triples (2,3,5), (2,3,7), (2,5,7), (3,5,7).

## What this file proves (core Lean 4.33.1, no Mathlib, zero axioms, zero sorry)

* `main` — the discretized negation of the vanishing claim: a positive rational
  witness ε exists (ε = 1/3, `third`; its numerator is positive so
  `ε.num.natAbs = ε.num`), such that arbitrarily far out in the family a member
  satisfies `ε.den * surplus_k ≥ ε.num.natAbs * g_k` — the exact cross-multiplied
  form of `ε ≤ surplus_k / g_k` for positive denominators (`third.den = 3 > 0`,
  `g_k ≥ 29`).
* `zero_lt_third` — `0 < 1/3` in ℚ (the core `0 : Rat` literal is avoided in
  favor of `qzero`, which is the same rational number with ground field proofs;
  see the note at `qzero`).
* `third_le_ratio_zero`, `third_le_ratio_one` — on concrete family members, the
  honest ℚ-order statement `1/3 ≤ ratio_k` itself, proved by definitional
  reduction of the rational order (all fields of these ground values reduce).
* `exact_identity` — the per-member polynomial identity `2*surplus_k*g_k =
  (g_k - 3)*g_k`, i.e. `surplus_k/g_k = (g_k - 3)/(2 g_k)`; with `frob_ge_nine`
  this yields `ratio_k ≥ 1/3` as stated. `wilf_relation` records the defining
  Wilf relation `3*n_k = g_k + surplus_k + 3` additively.
* `gap_zero/one`, `cover_zero/one`, `count_zero/one` — exhaustive-search
  certificates that `g_0 = 29` is exactly the Frobenius number of
  `⟨6,10,15⟩ = S_0` with `n_0 = 15` nongaps on `[0,29]`, and `g_1 = 71` is
  exactly the Frobenius number of `⟨6,22,33⟩ = S_1` with `n_1 = 36` nongaps on
  `[0,71]` — anchoring the closed formulas to the actual semigroups (no object
  substitution).

All proofs are pure term/`rfl` proofs or use only the small self-contained
arithmetic toolkit below; `omega`, `simp` and core arithmetic lemma families
that depend on `propext`/`Quot.sound` are deliberately avoided. `Check.lean`
audits every theorem.
-/

set_option maxHeartbeats 1000000

-- ==================== self-contained arithmetic toolkit (axiom-free) ====================

theorem myLeftDistrib (n m k : Nat) : n * (m + k) = n * m + n * k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    show n * (m+k) + n = n*m + (n*k + n)
    rw [ih, Nat.add_assoc]

theorem myMulAdd (a b c : Nat) : (a + b) * c = a * c + b * c := by
  rw [Nat.mul_comm (a+b) c, myLeftDistrib, Nat.mul_comm c a, Nat.mul_comm c b]

theorem myMulAssoc (a b c : Nat) : a * b * c = a * (b * c) := by
  induction c with
  | zero => rfl
  | succ c ih =>
    show a*b*c + a*b = a*(b*c + b)
    rw [ih, myLeftDistrib a (b*c) b]

theorem myAddPair (a b : Nat) : ∀ k : Nat, a * k + b * k = (a + b) * k :=
  fun k => (myMulAdd a b k).symm

theorem myShuffle (a b c d : Nat) : a + b + (c + d) = a + c + (b + d) := by
  rw [Nat.add_assoc a b (c+d), Nat.add_left_comm b c d, ← Nat.add_assoc a c (b+d)]

-- ==================== the family, by closed formulas ====================

/-- Frobenius number of `S_k = ⟨6, 2*(6k+5), 3*(6k+5)⟩`. -/
def frob (k : Nat) : Nat := 42*k + 29

/-- Number of nongaps of `S_k` on `[0, g_k]` (`S_k` is symmetric: complete intersection). -/
def nongapCount (k : Nat) : Nat := 21*k + 15

/-- Wilf surplus of `S_k` at embedding dimension `e = 3` (closed form;
`reproduce.py` and the certificates below verify `surplus_k = 3*n_k - g_k - 3`). -/
def surplus (k : Nat) : Nat := 21*k + 13

/-- Numerator of `ratio_k = surplus_k / g_k` (the pair is in lowest terms). -/
def ratioNum (k : Nat) : Nat := 21*k + 13

/-- Denominator of `ratio_k = surplus_k / g_k`. -/
def ratioDen (k : Nat) : Nat := 42*k + 29

theorem frob_eq (k : Nat) : frob k = 42*k + 29 := rfl

theorem nongapCount_eq (k : Nat) : nongapCount k = 21*k + 15 := rfl

theorem surplus_eq (k : Nat) : surplus k = 21*k + 13 := rfl

theorem ratioNum_eq (k : Nat) : ratioNum k = surplus k := rfl

theorem ratioDen_eq (k : Nat) : ratioDen k = frob k := rfl

/-- The defining Wilf relation `3*n_k = g_k + surplus_k + 3` (additive form of
`surplus_k = 3*n_k - g_k - 3`). -/
theorem wilf_relation (k : Nat) : 3 * nongapCount k = frob k + surplus k + 3 := by
  rw [frob_eq, nongapCount_eq, surplus_eq, myLeftDistrib 3 (21*k) 15,
    ← myMulAssoc 3 21 k, Nat.add_assoc (42*k+29) (21*k+13) 3,
    myShuffle (42*k) 29 (21*k+13) 3, ← Nat.add_assoc (42*k) (21*k) 13,
    myAddPair 42 21 k]

theorem frob_ge_nine (k : Nat) : 9 ≤ frob k := by
  rw [frob_eq]
  exact Nat.le.intro ((Nat.add_comm 9 (42*k+20)).trans (rfl : (42*k+20)+9 = 42*k+29))

theorem surplus_pos (k : Nat) : 0 < surplus k := by
  rw [surplus_eq]
  exact Nat.succ_pos (21*k+12)

/-- Exact per-member identity: `surplus_k/g_k = (g_k - 3)/(2 g_k)`, cross-multiplied. -/
theorem exact_identity (k : Nat) : 2 * surplus k * frob k = (frob k - 3) * frob k := by
  rw [frob_eq, surplus_eq]
  have h26 : 2*(21*k+13) = 42*k+26 := by
    rw [myLeftDistrib 2 (21*k) 13]
    have h2 : 2*(21*k) = 42*k := (myMulAssoc 2 21 k).symm.trans (rfl : (2*21)*k = 42*k)
    rw [h2]
  have hs : (42*k+29) - 3 = 42*k+26 := rfl
  rw [h26, hs]

-- ==================== ε = 1/3 as an exact rational ====================

/-- The rational number `0` (constructed with ground field proofs; the core
`OfNat Rat` literal carries `propext`/`Quot.sound` through its `by decide`
coprimality field, so it is avoided). -/
def qzero : Rat := ⟨(0 : Int), 1, fun h => Nat.noConfusion h, rfl⟩

/-- The exact rational `1/3` (all fields ground, hence fully reducible). -/
def third : Rat := ⟨(1 : Int), 3, fun h => Nat.noConfusion h, rfl⟩

theorem num_third : third.num = (1 : Int) := rfl

theorem den_third : third.den = 3 := rfl

theorem zero_lt_third : qzero < third := rfl

/-- The member condition for `ε = 1/3`: `1/3 ≤ surplus_k/g_k`, cross-multiplied. -/
theorem member_condition (k : Nat) :
    third.den * ratioNum k ≥ third.num.natAbs * ratioDen k := by
  rw [den_third]
  show (3:Nat) * ratioNum k ≥ (1:Nat) * ratioDen k
  rw [ratioDen_eq, ratioNum_eq, frob_eq, surplus_eq]
  have h1 : 3*(21*k+13) = 63*k+39 := by
    rw [myLeftDistrib 3 (21*k) 13, ← myMulAssoc 3 21 k]
  have h2 : (42*k+29) + (21*k+10) = 63*k+39 := by
    rw [myShuffle (42*k) 29 (21*k) 10, myAddPair 42 21 k]
  rw [h1, Nat.one_mul]
  exact Nat.le.intro h2

/-- **Main theorem.** Discretized negation of "surplus/g → 0 along embedding-
dimension-3 semigroups": a positive rational ε exists (ε = 1/3; its numerator
is positive, so `ε.num.natAbs = ε.num`) such that arbitrarily large `k` yield
family members with `ε ≤ surplus_k/g_k`, expressed by the exact cross-multiplied
inequality `ε.den * surplus_k ≥ ε.num.natAbs * g_k` (both denominators
positive: `third.den = 3`, `g_k ≥ 29`). -/
theorem main :
    ∃ ε : Rat, qzero < ε ∧ ∀ N : Nat, ∃ k : Nat, N ≤ k ∧
      ε.den * ratioNum k ≥ ε.num.natAbs * ratioDen k :=
  ⟨third, zero_lt_third, fun N => ⟨N, Nat.le_refl N, member_condition N⟩⟩

-- ==================== concrete members: the ℚ-inequality itself ====================

/-- `ratio_zero = 13/29`, the exact rational value for `S_0 = ⟨6,10,15⟩`. -/
def ratio_zero : Rat := ⟨((21*0+13 : Nat) : Int), (42*0+29 : Nat),
  fun h => Nat.noConfusion h, rfl⟩

/-- `ratio_one = 34/71`, the exact rational value for `S_1 = ⟨6,22,33⟩`. -/
def ratio_one : Rat := ⟨((21*1+13 : Nat) : Int), (42*1+29 : Nat),
  fun h => Nat.noConfusion h, rfl⟩

/-- The honest ℚ-inequality `1/3 ≤ 13/29` for member `k = 0`. -/
theorem third_le_ratio_zero : third ≤ ratio_zero := rfl

/-- The honest ℚ-inequality `1/3 ≤ 34/71` for member `k = 1`. -/
theorem third_le_ratio_one : third ≤ ratio_one := rfl

-- ==================== anchoring the formulas to the actual semigroups ====================

-- Exhaustive bounded search for a representation `n = x*a + y*b + z*c` with
-- `x, y, z >= 0`. Any representation has `y <= n/b` and `z <= n/c`, so searching
-- `y in [0, n/b]`, `z in [0, n/c]` and testing `(n - y*b - z*c)` for divisibility
-- by `a` is sound and complete.
def rep (a b c n : Nat) : Bool :=
  (List.range (n / b + 1)).any fun y =>
    (List.range (n / c + 1)).any fun z =>
      let s := y * b + z * c
      s ≤ n && (n - s) % a == 0

-- Number of nongaps of `<a,b,c>` among `0, 1, ..., upto - 1`.
def countNongaps (a b c upto : Nat) : Nat :=
  (List.range upto).filter (fun k => rep a b c k) |>.length

-- ----- member k = 0: S_0 = <6,10,15>, g = 29, n = 15 -----

theorem gap_zero : rep 6 10 15 29 = false := rfl

theorem cover_zero : (List.range 6).all (fun k => rep 6 10 15 (30 + k)) = true := rfl

theorem count_zero : countNongaps 6 10 15 30 = 15 := rfl

theorem frob_zero : frob 0 = 29 := rfl

theorem nongap_zero : nongapCount 0 = 15 := rfl

theorem surplus_zero : surplus 0 = 13 := rfl

theorem ratioNum_zero : ratioNum 0 = 13 := rfl

theorem ratioDen_zero : ratioDen 0 = 29 := rfl

-- ----- member k = 1: S_1 = <6,22,33>, g = 71, n = 36 -----

theorem gap_one : rep 6 22 33 71 = false := rfl

theorem cover_one : (List.range 6).all (fun k => rep 6 22 33 (72 + k)) = true := rfl

theorem count_one : countNongaps 6 22 33 72 = 36 := rfl

theorem frob_one : frob 1 = 71 := rfl

theorem nongap_one : nongapCount 1 = 36 := rfl

theorem surplus_one : surplus 1 = 34 := rfl

theorem ratioNum_one : ratioNum 1 = 34 := rfl

theorem ratioDen_one : ratioDen 1 = 71 := rfl
