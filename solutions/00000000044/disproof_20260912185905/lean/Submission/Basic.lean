import Mathlib

/-!
# A counterexample to conjecture 00000000044

Conjecture 00000000044 asserts two things about Egyptian fractions with prime
denominators:

* (i) every positive rational is a finite sum of reciprocals of *distinct*
  primes;
* (ii) the greedy algorithm restricted to prime denominators always terminates.

Both fail, and for the same reason. If

  `q = ∑ p ∈ S, 1/p`

for a finite set `S` of distinct primes, then `q.den` divides `∏ p ∈ S, p`,
which is squarefree because the primes in `S` are distinct. Hence **the
denominator of such a sum is always squarefree**, and any positive rational
whose reduced denominator is not — `1/4` is the smallest — is not representable.

Part (ii) follows: a terminating run of any procedure that repeatedly subtracts
reciprocals of distinct primes and reaches `0` exhibits such a representation,
so no such procedure terminates on `1/4`, whatever rule it uses to choose the
next prime. This is `no_prime_greedy_terminates`.
-/

namespace Submission00000000044

open Finset

/-- `q` is a finite sum of reciprocals of distinct primes. -/
def IsPrimeReciprocalSum (q : ℚ) : Prop :=
  ∃ S : Finset ℕ, (∀ p ∈ S, p.Prime) ∧ ∑ p ∈ S, (1 : ℚ) / p = q

/-- Conjecture 00000000044(i). -/
def ConjectureHolds : Prop :=
  ∀ q : ℚ, 0 < q → IsPrimeReciprocalSum q

/-! ## The denominator of a prime-reciprocal sum is squarefree -/

/-- The denominator of `∑ 1/p` over a finite set of primes divides their
product. Induction on the set, using `Rat.add_den_dvd` at each step. -/
theorem den_dvd_prod {S : Finset ℕ} (hS : ∀ p ∈ S, p.Prime) :
    (∑ p ∈ S, (1 : ℚ) / p).den ∣ ∏ p ∈ S, p := by
  induction S using Finset.induction_on with
  | empty => simp
  | insert a S ha ih =>
      have hap : a.Prime := hS a (mem_insert_self a S)
      have hS' : ∀ p ∈ S, p.Prime := fun p hp => hS p (mem_insert_of_mem hp)
      rw [Finset.sum_insert ha, Finset.prod_insert ha]
      refine dvd_trans (Rat.add_den_dvd _ _) ?_
      have hden : ((1 : ℚ) / a).den = a := by
        rw [one_div, Rat.inv_natCast_den_of_pos hap.pos]
      rw [hden]
      exact mul_dvd_mul_left a (ih hS')

/-- A product of distinct primes is squarefree. -/
theorem prod_primes_squarefree {S : Finset ℕ} (hS : ∀ p ∈ S, p.Prime) :
    Squarefree (∏ p ∈ S, p) := by
  refine Finset.squarefree_prod_of_pairwise_isCoprime ?_ (fun p hp => (hS p hp).squarefree)
  intro p hp q hq hpq
  exact Nat.coprime_iff_isRelPrime.1 ((Nat.coprime_primes (hS p hp) (hS q hq)).2 hpq)

/-- Only rationals with squarefree denominator can be written as a sum of
reciprocals of distinct primes. -/
theorem squarefree_den_of_isPrimeReciprocalSum {q : ℚ} (h : IsPrimeReciprocalSum q) :
    Squarefree q.den := by
  obtain ⟨S, hS, rfl⟩ := h
  exact Squarefree.squarefree_of_dvd (den_dvd_prod hS) (prod_primes_squarefree hS)

/-! ## Every prime dividing the denominator must occur

A sharper obstruction, which shows the failure is not isolated: since `q.den`
divides `∏ p ∈ S, p` and the members of `S` are prime, every prime dividing
`q.den` *is* a member of `S`. So `q` is at least the sum of the reciprocals of
the prime factors of its own denominator. -/

theorem primeFactors_den_subset {q : ℚ} {S : Finset ℕ} (hS : ∀ p ∈ S, p.Prime)
    (hsum : ∑ p ∈ S, (1 : ℚ) / p = q) : q.den.primeFactors ⊆ S := by
  intro r hr
  rw [Nat.mem_primeFactors] at hr
  obtain ⟨hrp, hrd, -⟩ := hr
  subst hsum
  have hdvd : r ∣ ∏ p ∈ S, p := hrd.trans (den_dvd_prod hS)
  obtain ⟨p, hpS, hrp'⟩ := (Nat.Prime.prime hrp).exists_mem_finset_dvd hdvd
  rwa [((Nat.prime_dvd_prime_iff_eq hrp (hS p hpS)).1 hrp')]

theorem sum_primeFactors_den_le {q : ℚ} (h : IsPrimeReciprocalSum q) :
    ∑ r ∈ q.den.primeFactors, (1 : ℚ) / r ≤ q := by
  obtain ⟨S, hS, hsum⟩ := h
  have hsub := primeFactors_den_subset hS hsum
  calc ∑ r ∈ q.den.primeFactors, (1 : ℚ) / r
      ≤ ∑ p ∈ S, (1 : ℚ) / p := by
        refine Finset.sum_le_sum_of_subset_of_nonneg hsub (fun i _ _ => ?_)
        positivity
    _ = q := hsum

/-! ## The counterexample -/

/-- `1/4` is not a sum of reciprocals of distinct primes: its denominator `4`
is not squarefree. -/
theorem not_isPrimeReciprocalSum_one_div_four :
    ¬ IsPrimeReciprocalSum (1 / 4 : ℚ) := by
  intro h
  have hsq := squarefree_den_of_isPrimeReciprocalSum h
  rw [show ((1 : ℚ) / 4).den = 4 by norm_num] at hsq
  exact absurd (hsq 2 (by norm_num)) (by decide)

/-- `1/n` is representable only if `n` is `1` or prime: for composite `n` the
denominator has a prime factor `r < n`, and already `1/r > 1/n`. -/
theorem not_isPrimeReciprocalSum_one_div_composite {n : ℕ} (hn : 2 ≤ n)
    (hnp : ¬ n.Prime) : ¬ IsPrimeReciprocalSum (1 / n : ℚ) := by
  intro h
  have hle := sum_primeFactors_den_le h
  have hden : ((1 : ℚ) / n).den = n := by
    rw [one_div, Rat.inv_natCast_den_of_pos (by omega)]
  rw [hden] at hle
  set r := n.minFac with hr
  have hrp : r.Prime := Nat.minFac_prime (by omega)
  have hrd : r ∣ n := Nat.minFac_dvd n
  have hrn : r < n := lt_of_le_of_ne (Nat.le_of_dvd (by omega) hrd)
    (fun hEq => hnp (hEq ▸ hrp))
  have hmem : r ∈ n.primeFactors := Nat.mem_primeFactors.2 ⟨hrp, hrd, by omega⟩
  have hsingle : (1 : ℚ) / r ≤ ∑ x ∈ n.primeFactors, (1 : ℚ) / x :=
    Finset.single_le_sum (f := fun x : ℕ => (1 : ℚ) / x)
      (fun i _ => by positivity) hmem
  have hlt : (1 : ℚ) / n < 1 / r := by
    apply one_div_lt_one_div_of_lt
    · exact_mod_cast hrp.pos
    · exact_mod_cast hrn
  linarith

/-- Conjecture 00000000044(i) is false. -/
theorem conjecture_00000000044_false : ¬ ConjectureHolds := fun h =>
  not_isPrimeReciprocalSum_one_div_four (h (1 / 4) (by norm_num))

/-! ## Part (ii)

A run of a greedy procedure over prime denominators is just a list of distinct
primes whose reciprocals are subtracted in turn; terminating at `0` means their
sum is the starting value. So termination on `q` is exactly
`IsPrimeReciprocalSum q`, independently of the rule used to pick the next
prime, and no such procedure terminates on `1/4`. -/
theorem no_prime_greedy_terminates_at_one_div_four
    (run : Finset ℕ) (h_primes : ∀ p ∈ run, p.Prime)
    (h_sum : ∑ p ∈ run, (1 : ℚ) / p = 1 / 4) : False :=
  not_isPrimeReciprocalSum_one_div_four ⟨run, h_primes, h_sum⟩

end Submission00000000044
