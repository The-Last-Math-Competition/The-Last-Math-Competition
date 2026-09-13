/-
  Disproof of conjecture `00000000153`: formalisation.

  Conjecture (as filed):
    "Minimal transitivity of prime orbits: in any minimal topological dynamical
    system (X, T), for every x ∈ X the orbit closure {T^{p_n} x : n ≥ 1}
    equals X", where p_n is the n-th prime.

  Refutation.  Take X = Fin 4 = Z/4 with the discrete topology and T x = x + 1.
  Then T is a single 4-cycle, so every full orbit is all of X and (X, T) is
  minimal.  But for every x the prime-index orbit {T^p x : p prime} omits x
  itself: no prime is divisible by 4 (the only even prime is 2, and 4 ∤ 2).
  In the discrete topology the closure of a set is the set itself, so the
  prime-index orbit closure omits x and is therefore not all of X.  In
  particular the conjecture fails at x = 0, where the prime-index orbit is
  {p mod 4 : p prime} = {1, 2, 3}, whose closure {1, 2, 3} ≠ Fin 4.

  Core Lean only (`import Std`).  No Mathlib, no `Finset`, no `ZMod`, no
  `Nat.Prime` (core Lean and `Std` provide none), no `sorry`.
  `Function.iterate` / the `f^[n]` notation are Mathlib-only here, so the
  iteration of T is defined directly as `iter`.
-/

import Std

namespace Tlmc153

/-! ## Primality

Core Lean and `Std` do not provide `Nat.Prime` (it is Mathlib-only), so we
define our own.  The definition is the standard one: a prime is an integer
`≥ 2` whose only divisors are `1` and itself. -/

/-- `IsPrime p` means `p ≥ 2` and the only divisors of `p` are `1` and `p`. -/
def IsPrime (p : Nat) : Prop := 2 ≤ p ∧ ∀ m : Nat, m ∣ p → m = 1 ∨ m = p

/-- No prime is divisible by `4`.  If `4 ∣ p` then `2 ∣ p`; primality then
forces `p = 2`, but `4 ∤ 2`.  This is the arithmetic heart of the refutation:
it is exactly why no prime-indexed iterate can return to its starting point. -/
theorem four_not_dvd_of_isPrime {p : Nat} (hp : IsPrime p) : ¬ 4 ∣ p := by
  intro h
  have h2 : 2 ∣ p := by
    rcases h with ⟨k, rfl⟩
    exact ⟨2 * k, by omega⟩
  have hp2 : p = 2 := by
    rcases hp.2 2 h2 with h1 | h1
    · omega
    · exact h1.symm
  rw [hp2] at h
  omega

/-! ## The dynamical system `X = Fin 4`, `T x = x + 1` -/

/-- The shift `T` on `Z/4`, written on `Fin 4`. -/
def T (x : Fin 4) : Fin 4 := ⟨(x.val + 1) % 4, by omega⟩

/-- The `n`-th iterate of `T`.  (`Function.iterate` and the notation `f^[n]`
are not available in core Lean / `Std`, so the iteration is defined directly.) -/
def iter : Nat → Fin 4 → Fin 4
  | 0, x => x
  | n + 1, x => T (iter n x)

/-- `iter 0 x = x`. -/
theorem iter_zero (x : Fin 4) : iter 0 x = x := rfl

/-- `iter (n+1) x = T (iter n x)`. -/
theorem iter_succ (n : Nat) (x : Fin 4) : iter (n + 1) x = T (iter n x) := rfl

/-- Closed form of the iteration: `(T^n x).val = (x.val + n) % 4`.  This is the
computation that turns the dynamics into arithmetic modulo 4. -/
theorem iter_val (n : Nat) (x : Fin 4) : (iter n x).val = (x.val + n) % 4 := by
  induction n with
  | zero => exact (Nat.mod_eq_of_lt x.isLt).symm
  | succ k ih =>
      simp only [iter, T, ih]
      omega

/-! ## Minimality: every full orbit is all of `X` -/

/-- `FullOrbit x y`: `y` is hit by some iterate of `T` starting at `x`. -/
def FullOrbit (x y : Fin 4) : Prop := ∃ n : Nat, iter n x = y

/-- `(Fin 4, T)` is minimal: for every `x` and every `y` the full orbit of `x`
reaches `y`.  Indeed `T` is a single 4-cycle, so the full orbit of every point
is all of `X`. -/
theorem minimal (x y : Fin 4) : FullOrbit x y := by
  refine ⟨(y.val + 4 - x.val) % 4, ?_⟩
  apply Fin.ext
  rw [iter_val]
  omega

/-- `(Fin 4, T)` is a minimal system, packaged as a proposition. -/
def IsMinimal : Prop := ∀ x y : Fin 4, FullOrbit x y

/-- The system is minimal. -/
theorem isMinimal : IsMinimal := minimal

/-! ## The prime-index orbit

`PrimeOrbitAt x y` says that `y = T^p x` for some prime `p`.  This is the
set `{T^{p_n} x : n ≥ 1}` of the conjecture (indexed by the primes rather than
by their positions in the prime sequence; the two sets are equal because
`p ↦ p_n` is a bijection onto the primes). -/

/-- `PrimeOrbitAt x y`: `y = T^p x` for some prime `p`. -/
def PrimeOrbitAt (x y : Fin 4) : Prop := ∃ p : Nat, IsPrime p ∧ iter p x = y

/-- The prime-index orbit of `x`, as a predicate on `X`. -/
def PrimeOrbit (x y : Fin 4) : Prop := PrimeOrbitAt x y

/-- The prime-index orbit of any `x` omits `x` itself: a prime `p` with
`T^p x = x` would satisfy `(x.val + p) % 4 = x.val`, hence `4 ∣ p`,
contradicting `four_not_dvd_of_isPrime`. -/
theorem primeOrbitAt_not_self (x : Fin 4) : ¬ PrimeOrbitAt x x := by
  rintro ⟨p, hp, hp'⟩
  have hval : (x.val + p) % 4 = x.val := by
    have h := congrArg Fin.val hp'
    rwa [iter_val] at h
  have h4 : 4 ∣ p := by
    have h := Nat.div_add_mod (x.val + p) 4
    rw [hval] at h
    exact ⟨(x.val + p) / 4, by omega⟩
  exact four_not_dvd_of_isPrime hp h4

/-- Consequently the prime-index orbit of every `x` is a proper subset of `X`:
it never equals `X`, and in particular never equals the full orbit. -/
theorem primeOrbitAt_not_univ (x : Fin 4) :
    ¬ (∀ y : Fin 4, PrimeOrbitAt x y) :=
  fun h => primeOrbitAt_not_self x (h x)

/-- For `x = 0`, no prime-indexed iterate returns to `0`; equivalently, no
prime `p` satisfies `p % 4 = 0`. -/
theorem prime_iter_zero_val_ne_zero (p : Nat) (hp : IsPrime p) :
    (iter p 0).val ≠ 0 := by
  intro h
  rw [iter_val] at h
  have hp4 : p % 4 = 0 := by omega
  exact four_not_dvd_of_isPrime hp (Nat.dvd_of_mod_eq_zero hp4)

/-- The prime-index orbit of `0` omits `0`. -/
theorem zero_not_mem_primeOrbit : ¬ PrimeOrbitAt 0 0 :=
  primeOrbitAt_not_self 0

/-! ## Modelling the topological closure

The space `X = Fin 4` is finite; we give it the discrete topology, in which
every subset is open and closed, so the closure of any set is the set itself.
We therefore model the closure of the prime-index orbit of `x` by the
predicate `PrimeOrbitAt x` itself.  No topology library is needed: the
refutation only needs the resulting set inequality `closure ≠ X`, formalised
below as `¬ (∀ y, PrimeOrbitAt x y)`. -/

/-- Model of the closure of the prime-index orbit of `x` in the discrete
topology on `Fin 4`: every point is isolated, so `closure S = S`. -/
def PrimeOrbitClosure (x : Fin 4) : Fin 4 → Prop := PrimeOrbitAt x

/-- For every `x`, the closure of the prime-index orbit of `x` is not all
of `X`.  Hence the conclusion of the conjecture fails for every `x`, and a
fortiori for `x = 0`. -/
theorem primeOrbitClosure_not_univ (x : Fin 4) :
    ¬ (∀ y : Fin 4, PrimeOrbitClosure x y) :=
  primeOrbitAt_not_univ x

/-! ## The refutation -/

/-- The packaged refutation of conjecture `00000000153`: the system
`(Fin 4, T)` is minimal (every full orbit is all of `X`), yet for every `x`
the closure of the prime-index orbit of `x` is not all of `X`.  The
conjecture's conclusion is therefore false in a minimal system, and the
conjecture is false as stated. -/
theorem conjecture_00000000153_false :
    IsMinimal ∧ ∀ x : Fin 4, ¬ (∀ y : Fin 4, PrimeOrbitClosure x y) :=
  ⟨isMinimal, primeOrbitClosure_not_univ⟩

/-- The refutation specialised to the witness point `x = 0` of the
conjecture's universal quantifier. -/
theorem conjecture_00000000153_false_at_zero :
    (∀ y : Fin 4, FullOrbit 0 y) ∧
    ¬ (∀ y : Fin 4, PrimeOrbitClosure 0 y) :=
  ⟨fun y => minimal 0 y, primeOrbitClosure_not_univ 0⟩

end Tlmc153

#print axioms Tlmc153.conjecture_00000000153_false
