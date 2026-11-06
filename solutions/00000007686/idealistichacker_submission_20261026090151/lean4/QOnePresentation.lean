import Gaussian

noncomputable section

namespace Gaussian7686

open Polynomial

theorem gaussian_above (n k : ℕ) (h : n < k) : gaussian n k = 0 := by
  induction n generalizing k with
  | zero =>
      cases k with
      | zero => omega
      | succ k => rfl
  | succ n ih =>
      cases k with
      | zero => omega
      | succ k =>
          rw [gaussian_pascal, ih k (by omega), ih (k + 1) (by omega)]
          simp

theorem gaussian_diagonal (n : ℕ) : gaussian n n = 1 := by
  induction n with
  | zero => rfl
  | succ n ih => rw [gaussian_pascal, ih, gaussian_above n (n + 1) (by omega)]; simp

theorem gaussian_characterization_unique (f : ℕ → ℕ → Polynomial ℕ)
    (h00 : f 0 0 = 1) (h0s : ∀ k, f 0 (k + 1) = 0)
    (hs0 : ∀ n, f (n + 1) 0 = 1)
    (hrec : ∀ n k, f (n + 1) (k + 1) = f n k + X ^ (k + 1) * f n (k + 1)) :
    f = gaussian := by
  funext n k
  induction n generalizing k with
  | zero => cases k with | zero => exact h00 | succ k => exact h0s k
  | succ n ih =>
      cases k with
      | zero => exact hs0 n
      | succ k => rw [hrec, gaussian_pascal, ih k, ih (k + 1)]

def generatedAtOne : RingCon (Polynomial ℕ) :=
  ringConGen (fun p q => p = X ∧ q = 1)

theorem generatedAtOne_X : generatedAtOne X 1 :=
  RingConGen.Rel.of _ _ ⟨rfl, rfl⟩

theorem generatedAtOne_poly_constant (p : Polynomial ℕ) :
    generatedAtOne p (C (p.eval 1)) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simpa using generatedAtOne.add hp hq
  | monomial n a =>
      have hx := generatedAtOne.toCon.pow n generatedAtOne_X
      have hc := generatedAtOne.mul (generatedAtOne.refl (C a)) hx
      rw [Polynomial.C_mul_X_pow_eq_monomial] at hc
      simpa only [one_pow, mul_one, Polynomial.eval_monomial] using hc

theorem generatedAtOne_implies_kernel {p q : Polynomial ℕ} (h : generatedAtOne p q) :
    atOne p q := by
  change RingConGen.Rel (fun p q : Polynomial ℕ => p = X ∧ q = 1) p q at h
  induction h with
  | of p q h => rcases h with ⟨rfl, rfl⟩; simp [atOne, RingCon.ker_apply]
  | refl p => exact atOne.refl p
  | symm h ih => exact atOne.symm ih
  | trans h1 h2 ih1 ih2 => exact atOne.trans ih1 ih2
  | add h1 h2 ih1 ih2 => exact atOne.add ih1 ih2
  | mul h1 h2 ih1 ih2 => exact atOne.mul ih1 ih2

theorem generatedAtOne_eq_kernel : generatedAtOne = atOne := by
  apply RingCon.ext
  intro p q
  constructor
  · exact generatedAtOne_implies_kernel
  · intro h
    have he : p.eval 1 = q.eval 1 := h
    have hp := generatedAtOne_poly_constant p
    have hq := generatedAtOne_poly_constant q
    rw [he] at hp
    exact generatedAtOne.trans hp (generatedAtOne.symm hq)

end Gaussian7686
