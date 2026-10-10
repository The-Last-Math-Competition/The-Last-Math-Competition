import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.RingTheory.Localization.AtPrime
import Mathlib.Tactic

noncomputable section
namespace PIPrimeChains
abbrev R := MvPolynomial ℕ ℚ
open MvPolynomial

def kill (n : ℕ) : R →+* R := eval₂Hom C (fun i => if i < n then 0 else X i)
def P (n : ℕ) : Ideal R := RingHom.ker (kill n)
def zeroEval : R →+* ℚ := eval (fun _ => 0)
def M : Ideal R := RingHom.ker zeroEval

instance M_prime : M.IsPrime := RingHom.ker_isPrime zeroEval

theorem P_prime (n : ℕ) : (P n).IsPrime := RingHom.ker_isPrime (kill n)

theorem kill_comp (m n : ℕ) (h : m ≤ n) : (kill n).comp (kill m) = kill n := by
  apply MvPolynomial.ringHom_ext
  · intro r
    simp [kill]
  · intro i
    simp only [RingHom.comp_apply,kill,eval₂Hom_X']
    by_cases hi : i < m
    · have hn : i < n := lt_of_lt_of_le hi h
      simp [hi,hn]
    · simp [hi,kill]

theorem P_mono (m n : ℕ) (h : m ≤ n) : P m ≤ P n := by
  intro p hp
  change kill m p = 0 at hp
  change kill n p = 0
  have he := congrArg (fun f : R →+* R => f p) (kill_comp m n h)
  simpa [RingHom.comp_apply,hp] using he.symm

theorem X_mem_next (n : ℕ) : X n ∈ P (n+1) := by
  change kill (n+1) (X n) = 0
  simp [kill]

theorem X_not_mem (n : ℕ) : X n ∉ P n := by
  change kill n (X n) ≠ 0
  simp [kill]

theorem chain_strict (n : ℕ) : P n < P (n+1) := by
  refine lt_of_le_of_ne (P_mono n (n+1) (by omega)) ?_
  intro h
  exact X_not_mem n (h ▸ X_mem_next n)

theorem zero_comp (n : ℕ) : zeroEval.comp (kill n) = zeroEval := by
  apply MvPolynomial.ringHom_ext
  · intro r
    simp [zeroEval,kill]
  · intro i
    simp only [RingHom.comp_apply,kill,eval₂Hom_X']
    by_cases h : i < n <;> simp [h,zeroEval]

theorem P_le_M (n : ℕ) : P n ≤ M := by
  intro p hp
  change kill n p = 0 at hp
  change zeroEval p = 0
  have he := congrArg (fun f : R →+* ℚ => f p) (zero_comp n)
  simpa [RingHom.comp_apply,hp] using he.symm

-- Actual localized prime ideals, constructed through the library's order isomorphism.
abbrev LocalR := Localization.AtPrime M

def inside (n : ℕ) : {I : Ideal R // I.IsPrime ∧ I ≤ M} :=
  ⟨P n,P_prime n,P_le_M n⟩

def localizedPrime (n : ℕ) : {I : Ideal LocalR // I.IsPrime} :=
  (IsLocalization.AtPrime.orderIsoOfPrime LocalR M).symm (inside n)

theorem localized_strict (n : ℕ) : (localizedPrime n).val < (localizedPrime (n+1)).val := by
  change localizedPrime n < localizedPrime (n+1)
  apply (IsLocalization.AtPrime.orderIsoOfPrime LocalR M).symm.strictMono
  exact chain_strict n

theorem fixed_PI_identity (x y : R) : x*y - y*x = 0 := by rw [mul_comm x y,sub_self]

theorem counterexample : (∀ x y : R, x*y-y*x=0) ∧
    ∃ Q : ℕ → Ideal LocalR, (∀ n, (Q n).IsPrime) ∧ (∀ n, Q n < Q (n+1)) := by
  refine ⟨fixed_PI_identity,fun n => (localizedPrime n).val,?_,localized_strict⟩
  exact fun n => (localizedPrime n).property

#print axioms P_prime
#print axioms chain_strict
#print axioms P_le_M
#print axioms localized_strict
#print axioms counterexample
end PIPrimeChains
