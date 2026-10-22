import Main
import Square
namespace TLMC523Bridge
open TLMC523 TLMC523Square
/-- Evaluation of sparse finite monomial sums in the actual bounded Laurent space. -/
def eval : List Int → Laurent
| [] => TLMC523.zero
| a::as => add (monomial a) (eval as)

theorem eval_coeff (as : List Int) (k : Int) : (eval as).coeff k = coeff as k := by
  induction as with
  | nil => rfl
  | cons a as ih => simp [eval,add,monomial,coeff,ih,eq_comm]

/-- The formal Frobenius used on the quotient agrees with ordinary Laurent
polynomial squaring (finite convolution), for every sparse polynomial. -/
theorem frobenius_is_square (as : List Int) :
    frobenius (eval as) = eval (mulList as as) := by
  apply Laurent.ext
  intro k
  rw [eval_coeff,coeff_mulList,square_frobenius]
  simp [frobenius,eval_coeff]

theorem class_frobenius_is_square (as : List Int) :
    F (classOf (eval as)) = classOf (eval (mulList as as)) := by
  change classOf (frobenius (eval as)) = _
  rw [frobenius_is_square]

/-- Enumerate coefficients on the finite interval [-offset,n-offset). -/
def enumerate (a : Laurent) (offset : Int) : Nat → List Int
| 0 => []
| n+1 => if a.coeff ((n:Int)-offset) then
    ((n:Int)-offset)::enumerate a offset n else enumerate a offset n

theorem enumerate_coeff (a : Laurent) (offset : Int) (n : Nat) (k : Int) :
    coeff (enumerate a offset n) k =
      (if -offset ≤ k ∧ k < (n:Int)-offset then a.coeff k else false) := by
  induction n with
  | zero => simp [enumerate,coeff]; omega
  | succ n ih =>
    simp only [enumerate]
    by_cases he : k = (n:Int)-offset
    · subst k
      have hold : ¬ (-offset ≤ (n:Int)-offset ∧ (n:Int)-offset < (n:Int)-offset) := by omega
      have hnew : -offset ≤ (n:Int)-offset ∧ (n:Int)-offset < ((n+1:Nat):Int)-offset := by omega
      cases hval : a.coeff ((n:Int)-offset) <;> simp [coeff,ih,hnew] <;> omega
    · have hiff : k < (n:Int)+1-offset ↔ k < (n:Int)-offset := by omega
      cases hval : a.coeff ((n:Int)-offset) <;> simp [coeff,ih,Ne.symm he,hiff]

/-- Every finitely supported coefficient Laurent polynomial has a sparse representation. -/
theorem eval_surjective (a : Laurent) : ∃ as : List Int, eval as = a := by
  obtain ⟨N,hN⟩ := a.bounded
  refine ⟨enumerate a (N:Int) (2*N+1), ?_⟩
  apply Laurent.ext
  intro k
  rw [eval_coeff,enumerate_coeff]
  split <;> rename_i h
  · rfl
  · have hout : (N:Int) < k ∨ k < -(N:Int) := by omega
    exact (hN k hout).symm
end TLMC523Bridge
