/-!
Disproof of conjecture 00000000408 at the staircase of order 2.

The staircase of order `n` is the partition `σ_n = (n, n - 1, …, 1)`.
The conjecture says that the Kronecker coefficient `g(σ_n, σ_n, σ_n)` is odd
if and only if `n` is a triangular number.

Here `n = 2`, so `σ_2 = (2, 1)`. The Specht module `S^{(2,1)}` is realised as
the sum-zero plane inside the permutation representation of `S_3`. Its
character is `χ(τ) = fix(τ) - 1`, the representation is irreducible, and
`g(σ_2, σ_2, σ_2) = (1/6) ∑ χ(τ)^3 = 1`, which is odd. The integer `2` is
not triangular, so the claimed equivalence fails.
-/

namespace TLMC408

abbrev Perm := Fin 3 × Fin 3 × Fin 3

def image (σ : Perm) : Fin 3 → Fin 3
  | 0 => σ.1
  | 1 => σ.2.1
  | 2 => σ.2.2

def fixCount (σ : Perm) : Nat :=
  (if image σ 0 = 0 then 1 else 0) +
  (if image σ 1 = 1 then 1 else 0) +
  (if image σ 2 = 2 then 1 else 0)

/-- Character of the standard representation of `S_3`. -/
def chi (σ : Perm) : Int := (fixCount σ : Int) - 1

def group : List Perm :=
  [(0, 1, 2), (0, 2, 1), (1, 0, 2), (1, 2, 0), (2, 0, 1), (2, 1, 0)]

def isBijection (σ : Perm) : Bool :=
  image σ 0 != image σ 1 && image σ 0 != image σ 2 && image σ 1 != image σ 2

theorem group_elements_are_bijections :
    isBijection (0, 1, 2) && isBijection (0, 2, 1) && isBijection (1, 0, 2) &&
      isBijection (1, 2, 0) && isBijection (2, 0, 1) && isBijection (2, 1, 0) = true := by
  decide

theorem group_exhaustive (a b c : Fin 3) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    (a, b, c) ∈ group := by
  match a, b, c with
  | 0, 0, 0 => exact (hab rfl).elim
  | 0, 0, 1 => exact (hab rfl).elim
  | 0, 0, 2 => exact (hab rfl).elim
  | 0, 1, 0 => exact (hac rfl).elim
  | 0, 1, 1 => exact (hbc rfl).elim
  | 0, 1, 2 => decide
  | 0, 2, 0 => exact (hac rfl).elim
  | 0, 2, 1 => decide
  | 0, 2, 2 => exact (hbc rfl).elim
  | 1, 0, 0 => exact (hbc rfl).elim
  | 1, 0, 1 => exact (hac rfl).elim
  | 1, 0, 2 => decide
  | 1, 1, 0 => exact (hab rfl).elim
  | 1, 1, 1 => exact (hab rfl).elim
  | 1, 1, 2 => exact (hab rfl).elim
  | 1, 2, 0 => decide
  | 1, 2, 1 => exact (hac rfl).elim
  | 1, 2, 2 => exact (hbc rfl).elim
  | 2, 0, 0 => exact (hbc rfl).elim
  | 2, 0, 1 => decide
  | 2, 0, 2 => exact (hac rfl).elim
  | 2, 1, 0 => decide
  | 2, 1, 1 => exact (hbc rfl).elim
  | 2, 1, 2 => exact (hac rfl).elim
  | 2, 2, 0 => exact (hab rfl).elim
  | 2, 2, 1 => exact (hab rfl).elim
  | 2, 2, 2 => exact (hab rfl).elim

structure Vec where
  x : Int
  y : Int
  z : Int

def Vec.sum (v : Vec) : Int := v.x + v.y + v.z

def coord (v : Vec) : Fin 3 → Int
  | 0 => v.x
  | 1 => v.y
  | 2 => v.z

/-- `σ⁻¹(j)`, using that `σ` will be a bijection whenever this is evaluated on `group`. -/
def preimage (σ : Perm) (j : Fin 3) : Fin 3 :=
  if image σ 0 = j then 0 else if image σ 1 = j then 1 else 2

def act (σ : Perm) (v : Vec) : Vec where
  x := coord v (preimage σ 0)
  y := coord v (preimage σ 1)
  z := coord v (preimage σ 2)

def b1 : Vec := ⟨1, -1, 0⟩
def b2 : Vec := ⟨1, 0, -1⟩

def combine (α β : Int) : Vec where
  x := α + β
  y := -α
  z := -β

theorem b1_sum : b1.sum = 0 := by decide
theorem b2_sum : b2.sum = 0 := by decide

theorem reconstruct (v : Vec) (h : v.sum = 0) : combine (-v.y) (-v.z) = v := by
  have h' : v.x + (v.y + v.z) = 0 := by
    simpa [Vec.sum, Int.add_assoc] using h
  have hcancel := Int.add_neg_cancel_right v.x (v.y + v.z)
  have hxneg : v.x = -(v.y + v.z) := by
    rw [h'] at hcancel
    simpa [Int.zero_add] using hcancel.symm
  have hyz : v.x = -v.y + -v.z := by
    simpa [Int.neg_add] using hxneg
  cases v with
  | mk x y z =>
    have hyz' : x = -y + -z := by simpa using hyz
    simp [combine, hyz', Int.neg_neg]

/-- Trace on the sum-zero plane in the basis `(b₁, b₂)`. -/
def traceStd (σ : Perm) : Int :=
  -(act σ b1).y + -(act σ b2).z

theorem trace_eq_chi :
    traceStd (0, 1, 2) = chi (0, 1, 2) ∧
    traceStd (0, 2, 1) = chi (0, 2, 1) ∧
    traceStd (1, 0, 2) = chi (1, 0, 2) ∧
    traceStd (1, 2, 0) = chi (1, 2, 0) ∧
    traceStd (2, 0, 1) = chi (2, 0, 1) ∧
    traceStd (2, 1, 0) = chi (2, 1, 0) := by
  decide

def cube (σ : Perm) : Int := chi σ * chi σ * chi σ

def sumCubes : Int :=
  cube (0, 1, 2) + cube (0, 2, 1) + cube (1, 0, 2) +
    cube (1, 2, 0) + cube (2, 0, 1) + cube (2, 1, 0)

def sumSquares : Int :=
  chi (0, 1, 2) * chi (0, 1, 2) + chi (0, 2, 1) * chi (0, 2, 1) +
    chi (1, 0, 2) * chi (1, 0, 2) + chi (1, 2, 0) * chi (1, 2, 0) +
    chi (2, 0, 1) * chi (2, 0, 1) + chi (2, 1, 0) * chi (2, 1, 0)

theorem sumCubes_eq : sumCubes = 6 := by decide

theorem sumSquares_eq : sumSquares = 6 := by decide

def sumChi : Int :=
  chi (0, 1, 2) + chi (0, 2, 1) + chi (1, 0, 2) +
    chi (1, 2, 0) + chi (2, 0, 1) + chi (2, 1, 0)

/-- Trivial-character pairing `∑ χ`. -/
theorem sumChi_eq : sumChi = 0 := by decide

/-- Sign via the parity of the number of inversions in the one-line notation. -/
def sgn (σ : Perm) : Int :=
  let a := (image σ 0).1
  let b := (image σ 1).1
  let c := (image σ 2).1
  let inversions :=
    (if a > b then 1 else 0) + (if a > c then 1 else 0) + (if b > c then 1 else 0)
  if inversions % 2 = 0 then 1 else -1

def sumSignChi : Int :=
  sgn (0, 1, 2) * chi (0, 1, 2) + sgn (0, 2, 1) * chi (0, 2, 1) +
    sgn (1, 0, 2) * chi (1, 0, 2) + sgn (1, 2, 0) * chi (1, 2, 0) +
    sgn (2, 0, 1) * chi (2, 0, 1) + sgn (2, 1, 0) * chi (2, 1, 0)

theorem sumSignChi_eq : sumSignChi = 0 := by decide

/-- Kronecker coefficient `g((2,1),(2,1),(2,1)) = (1/|S₃|) ∑ χ³`. -/
def kronecker : Int := sumCubes / 6

theorem kronecker_eq : kronecker = 1 := by
  unfold kronecker
  rw [sumCubes_eq]
  decide

/-- `⟨χ, χ⟩ = (1/|S₃|) ∑ χ² = 1`. -/
def characterInner : Int := sumSquares / 6

theorem characterInner_eq : characterInner = 1 := by
  unfold characterInner
  rw [sumSquares_eq]
  decide

def IsOdd (n : Int) : Prop := ∃ k : Int, n = 2 * k + 1

theorem kronecker_odd : IsOdd kronecker := by
  refine ⟨0, ?_⟩
  rw [kronecker_eq]
  rfl

def Triangular (n : Nat) : Prop := ∃ k : Nat, k * (k + 1) = 2 * n

theorem not_triangular_two : ¬ Triangular 2 := by
  intro h
  rcases h with ⟨k, hk⟩
  match k with
  | 0 =>
    simp at hk
  | 1 =>
    simp at hk
  | 2 =>
    simp at hk
  | n + 3 =>
    have hk' : (n + 3) * (n + 4) = 4 := hk
    have h3 : n + 3 ≥ 3 := Nat.le_add_left 3 n
    have h4 : n + 4 ≥ 4 := Nat.succ_le_succ h3
    have hmul : (n + 3) * (n + 4) ≥ 3 * 4 := Nat.mul_le_mul h3 h4
    have hge : (n + 3) * (n + 4) ≥ 12 := by
      simp at hmul
      exact hmul
    have hle : 12 ≤ 4 := by
      rw [hk'] at hge
      exact hge
    exact (by decide : ¬ (12 ≤ (4 : Nat))) hle

/-- The order-2 case of the conjectured equivalence is false. -/
theorem staircase_two_breaks_the_equivalence :
    ¬ (IsOdd kronecker ↔ Triangular 2) := by
  intro h
  exact not_triangular_two (h.mp kronecker_odd)

/--
The universal claim fails: it is not true that for every positive integer `n`,
the Kronecker coefficient of the staircase triple is odd if and only if `n`
is triangular. The witness is `n = 2`.
-/
theorem conjecture_00000000408_fails
    (staircaseKronecker : Nat → Int)
    (h2 : staircaseKronecker 2 = kronecker) :
    ¬ ∀ n, IsOdd (staircaseKronecker n) ↔ Triangular n := by
  intro h
  have : IsOdd kronecker ↔ Triangular 2 := by simpa [h2] using h 2
  exact staircase_two_breaks_the_equivalence this

end TLMC408
