import Mathlib.Tactic
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Fintype.EquivFin

namespace SylvesterSpectrum
open scoped BigOperators

def Index : Nat → Type
  | 0 => Unit
  | n+1 => Bool × Index n

instance indexFintype : (n : Nat) → Fintype (Index n)
  | 0 => inferInstanceAs (Fintype Unit)
  | n+1 => by
    letI := indexFintype n
    exact inferInstanceAs (Fintype (Bool × Index n))
instance indexDecidableEq : (n : Nat) → DecidableEq (Index n)
  | 0 => inferInstanceAs (DecidableEq Unit)
  | n+1 => by
    letI := indexDecidableEq n
    exact inferInstanceAs (DecidableEq (Bool × Index n))

def sign (a b : Bool) : Int := if a && b then -1 else 1

def sylvester : (n : Nat) → Matrix (Index n) (Index n) Int
  | 0 => fun _ _ => 1
  | n+1 => fun x y => sign x.1 y.1 * sylvester n x.2 y.2

theorem card_index (n : Nat) : Fintype.card (Index n) = 2^n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change Fintype.card (Bool × Index n) = _
    simp [ih, pow_succ, Nat.mul_comm]

theorem entries_sign (n : Nat) (x y : Index n) :
    sylvester n x y = 1 ∨ sylvester n x y = -1 := by
  induction n with
  | zero => exact Or.inl rfl
  | succ n ih =>
    obtain ⟨a,x⟩ := x
    obtain ⟨b,y⟩ := y
    have h := ih x y
    cases a <;> cases b <;> rcases h with h | h <;> simp [sylvester, sign, h]

theorem row_inner (n : Nat) (x y : Index n) :
    (∑ z : Index n, sylvester n x z * sylvester n y z) =
      if x=y then (2^n : Int) else 0 := by
  induction n with
  | zero =>
    cases x
    cases y
    simp [sylvester, Index]
  | succ n ih =>
    obtain ⟨a,x⟩ := x
    obtain ⟨b,y⟩ := y
    change (∑ z : Bool × Index n,
      (sign a z.1 * sylvester n x z.2) * (sign b z.1 * sylvester n y z.2)) =
      if (a,x) = (b,y) then (2^(n+1) : Int) else 0
    have factor : ∀ d : Bool, ∀ z : Index n,
        (sign a d * sylvester n x z) * (sign b d * sylvester n y z) =
        (sign a d * sign b d) * (sylvester n x z * sylvester n y z) := by
      intros; ring
    rw [Fintype.sum_prod_type]
    simp_rw [factor, ← Finset.mul_sum, ih]
    cases a <;> cases b <;> by_cases h : x=y <;>
      simp [sign, h, pow_succ, Prod.mk.injEq] <;> ring

/-- The usual definition: all entries are signs, distinct rows are orthogonal,
    and every squared row norm is the order. -/
def HadamardOrder (m : Nat) : Prop :=
  ∃ H : Matrix (Fin m) (Fin m) Int,
    (∀ i j, H i j = 1 ∨ H i j = -1) ∧
    (∀ i j, (∑ k : Fin m, H i k * H j k) = if i=j then (m : Int) else 0)

noncomputable def indexEquiv (n : Nat) : Index n ≃ Fin (2^n) :=
  Fintype.equivFinOfCardEq (card_index n)

noncomputable def matrix (n : Nat) : Matrix (Fin (2^n)) (Fin (2^n)) Int :=
  fun i j => sylvester n ((indexEquiv n).symm i) ((indexEquiv n).symm j)

theorem sylvester_is_hadamard (n : Nat) : HadamardOrder (2^n) := by
  refine ⟨matrix n, ?_, ?_⟩
  · intro i j
    exact entries_sign n _ _
  · intro i j
    unfold matrix
    rw [(indexEquiv n).symm.sum_comp (fun z =>
      sylvester n ((indexEquiv n).symm i) z * sylvester n ((indexEquiv n).symm j) z)]
    rw [row_inner]
    simp only [(indexEquiv n).symm.injective.eq_iff, Nat.cast_pow, Nat.cast_ofNat]

/-- The attainable-order construction spectrum for genuine sign matrices. -/
def constructionSpectrum : Set Nat := {m | HadamardOrder m}

theorem arbitrarily_large_constructed_orders (N : Nat) :
    ∃ m ∈ constructionSpectrum, N < m := by
  refine ⟨2^(N+1), sylvester_is_hadamard (N+1), ?_⟩
  have h := Nat.lt_two_pow_self (n := N+1)
  omega

theorem construction_spectrum_infinite : constructionSpectrum.Infinite := by
  intro h
  obtain ⟨m, hm, hlarge⟩ := arbitrarily_large_constructed_orders (h.toFinset.sup id)
  have hle : m ≤ h.toFinset.sup id := Finset.le_sup (f := id) (h.mem_toFinset.mpr hm)
  omega

theorem conjectured_finiteness_false : ¬ constructionSpectrum.Finite :=
  construction_spectrum_infinite

#print axioms entries_sign
#print axioms row_inner
#print axioms sylvester_is_hadamard
#print axioms arbitrarily_large_constructed_orders
#print axioms construction_spectrum_infinite
#print axioms conjectured_finiteness_false
end SylvesterSpectrum
