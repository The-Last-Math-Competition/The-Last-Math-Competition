import Mathlib
import Conjecture8524.Statement

/-! # Conjecture 8524: the differential dimension polynomial (Kolchin)

Disproof of "its degree is the number of variables" (the number of variables being read either as
the number `m` of derivations or as the number `n` of differential indeterminates), by the prime
differential ideal `[y']` in `Q{y}` (ordinary case, one indeterminate). -/

-- (formal statement: see Statement.lean)

namespace C8524

open MvPolynomial

/-- Evaluation killing every derivative variable of positive order (ordinary case, `n = m = 1`). -/
noncomputable def phi : DRing 1 1 →ₐ[ℚ] Polynomial ℚ :=
  aeval (fun v : Var 1 1 => if v.2 0 = 0 then Polynomial.X else 0)

/-- The witness ideal: `[y']`, the kernel of `phi`. -/
noncomputable def W : Ideal (DRing 1 1) := RingHom.ker phi.toRingHom

theorem W_prime : W.IsPrime := RingHom.ker_isPrime _

theorem W_ne_top : W ≠ ⊤ := W_prime.ne_top

theorem phi_delta (p : DRing 1 1) : phi (delta (0 : Fin 1) p) = 0 := by
  induction p using MvPolynomial.induction_on with
  | C a => simp [delta]
  | add p q hp hq => simp [hp, hq]
  | mul_X p v hp =>
    simp only [delta, Derivation.leibniz, map_add, smul_eq_mul, map_mul] at hp ⊢
    simp [mkDerivation_X, phi, hp] at *

theorem W_diff : IsDiffIdeal W := by
  intro k p hp
  obtain rfl : k = 0 := Subsingleton.elim _ _
  simpa [W, RingHom.mem_ker] using phi_delta p

/-- Order-`t` evaluation map. -/
noncomputable def psi (t : ℕ) : MvPolynomial (Low 1 1 t) ℚ →ₐ[ℚ] Polynomial ℚ :=
  aeval (fun v : Low 1 1 t => if v.1.2 0 = 0 then Polynomial.X else 0)

theorem phi_comp (t : ℕ) : phi.comp (rename (Subtype.val : Low 1 1 t → Var 1 1)) = psi t := by
  apply MvPolynomial.algHom_ext
  intro v
  simp [phi, psi]

theorem trunc_eq (t : ℕ) :
    W.comap (rename (Subtype.val : Low 1 1 t → Var 1 1)).toRingHom = RingHom.ker (psi t).toRingHom := by
  ext p
  have := congrArg (fun f => f p) (phi_comp t)
  simp only [AlgHom.comp_apply] at this
  simp [W, RingHom.mem_ker, this]

theorem psi_surj (t : ℕ) : Function.Surjective (psi t) := by
  let o : Low 1 1 t := ⟨(0, fun _ => 0), by simp [ord]⟩
  let s : Polynomial ℚ →ₐ[ℚ] MvPolynomial (Low 1 1 t) ℚ := Polynomial.aeval (X o)
  have : (psi t).comp s = AlgHom.id ℚ _ := by
    apply Polynomial.algHom_ext
    simp [s, psi, o]
  intro q
  exact ⟨s q, by simpa using congrArg (fun f => f q) this⟩

theorem omega_W (t : ℕ) : omega W t = 1 := by
  unfold omega Trunc
  rw [trunc_eq]
  have e := RingHom.quotientKerEquivOfSurjective (psi_surj t)
  rw [ringKrullDim_eq_of_ringEquiv e]
  rw [Polynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field]
  simp

theorem not_conj (N : ℕ → ℕ → ℕ) (hN : N 1 1 ≠ 0) : ¬ Conjecture N := by
  intro h
  obtain ⟨P, ⟨M, hM⟩, hdeg, -⟩ := h 1 1 W W_diff W_ne_top
  have hP : P = 1 := by
    apply Polynomial.eq_of_infinite_eval_eq
    apply Set.infinite_of_forall_exists_gt
    intro a
    obtain ⟨d, hd, hev⟩ := hM (max M (⌈a⌉₊ + 1)) (le_max_left _ _)
    rw [omega_W] at hd
    have : d = 1 := by simpa using hd.symm
    subst this
    refine ⟨((max M (⌈a⌉₊ + 1) : ℕ) : ℚ), ?_, ?_⟩
    · simpa using hev
    · calc a ≤ ⌈a⌉₊ := Nat.le_ceil a
        _ < _ := by exact_mod_cast lt_max_of_lt_right (Nat.lt_succ_self _)
  subst hP
  simp at hdeg
  exact hN hdeg.symm

theorem main : Claim := ⟨not_conj _ (by simp), not_conj _ (by simp)⟩

end C8524
