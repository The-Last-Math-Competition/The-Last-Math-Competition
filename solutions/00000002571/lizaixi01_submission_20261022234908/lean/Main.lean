import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FinCases

namespace TLMC2571

attribute [local instance] Classical.propDecidable

/-- Binary deterministic communication, with Bob allowed to use his local input
without communication at an output leaf. -/
inductive Protocol where
  | output : (Bool → Bool) → Protocol
  | alice : (Bool → Bool) → Protocol → Protocol → Protocol
  | bob : (Bool → Bool) → Protocol → Protocol → Protocol

def Protocol.run : Protocol → Bool → Bool → Bool
  | .output g, _, b => g b
  | .alice s l r, a, b => if s a then r.run a b else l.run a b
  | .bob s l r, a, b => if s b then r.run a b else l.run a b

def Protocol.cost : Protocol → ℕ
  | .output _ => 0
  | .alice _ l r => 1 + max l.cost r.cost
  | .bob _ l r => 1 + max l.cost r.cost

def Correct (P : Protocol) (f : Bool → Bool → Bool) : Prop :=
  ∀ a b, P.run a b = f a b

def canonical (f : Bool → Bool → Bool) : Protocol :=
  .alice id (.output (f false)) (.output (f true))

theorem canonical_correct (f : Bool → Bool → Bool) : Correct (canonical f) f := by
  intro a b
  cases a <;> rfl

theorem canonical_cost (f : Bool → Bool → Bool) : (canonical f).cost = 1 := rfl

theorem protocol_exists (f : Bool → Bool → Bool) :
    ∃ n : ℕ, ∃ P : Protocol, Correct P f ∧ P.cost = n :=
  ⟨1, canonical f, canonical_correct f, canonical_cost f⟩

noncomputable def D (f : Bool → Bool → Bool) : ℕ := Nat.find (protocol_exists f)

theorem D_spec (f : Bool → Bool → Bool) :
    ∃ P : Protocol, Correct P f ∧ P.cost = D f :=
  Nat.find_spec (protocol_exists f)

theorem D_le_one (f : Bool → Bool → Bool) : D f ≤ 1 :=
  Nat.find_min' (protocol_exists f) ⟨canonical f, canonical_correct f, canonical_cost f⟩

theorem zero_cost_local (P : Protocol) (h : P.cost = 0) :
    ∃ g : Bool → Bool, ∀ a b, P.run a b = g b := by
  cases P with
  | output g => exact ⟨g, fun _ _ => rfl⟩
  | alice s l r => simp [Protocol.cost] at h
  | bob s l r => simp [Protocol.cost] at h

theorem positive_of_alice_dependence (f : Bool → Bool → Bool)
    (h : ∃ b, f false b ≠ f true b) : 0 < D f := by
  by_contra hn
  have hz : D f = 0 := by omega
  obtain ⟨P, hP, hcost⟩ := D_spec f
  obtain ⟨g, hg⟩ := zero_cost_local P (hcost.trans hz)
  obtain ⟨b, hb⟩ := h
  exact hb ((hP false b).symm.trans ((hg false b).trans ((hg true b).symm.trans (hP true b))))

def xorFun (a b : Bool) : Bool := xor a b
def andFun (a b : Bool) : Bool := a && b

theorem xor_not_local :
    (¬ ∃ g : Bool → Bool, ∀ a b, xorFun a b = g a) ∧
    (¬ ∃ g : Bool → Bool, ∀ a b, xorFun a b = g b) := by
  constructor
  · rintro ⟨g, hg⟩
    have := (hg false false).trans (hg false true).symm
    simp [xorFun] at this
  · rintro ⟨g, hg⟩
    have := (hg false false).trans (hg true false).symm
    simp [xorFun] at this

theorem and_not_local :
    (¬ ∃ g : Bool → Bool, ∀ a b, andFun a b = g a) ∧
    (¬ ∃ g : Bool → Bool, ∀ a b, andFun a b = g b) := by
  constructor
  · rintro ⟨g, hg⟩
    have := (hg true false).trans (hg true true).symm
    simp [andFun] at this
  · rintro ⟨g, hg⟩
    have := (hg false true).trans (hg true true).symm
    simp [andFun] at this

theorem D_xor : D xorFun = 1 := by
  have hp := positive_of_alice_dependence xorFun ⟨false, by decide⟩
  have hu := D_le_one xorFun
  omega

theorem D_and : D andFun = 1 := by
  have hp := positive_of_alice_dependence andFun ⟨true, by decide⟩
  have hu := D_le_one andFun
  omega

def signMatrix (f : Bool → Bool → Bool) : Matrix Bool Bool ℝ :=
  fun a b => if f a b then -1 else 1

def bitMatrix (f : Bool → Bool → Bool) : Matrix Bool Bool ℝ :=
  fun a b => if f a b then 1 else 0

theorem sign_xor_outer : signMatrix xorFun =
    Matrix.vecMulVec (fun a : Bool => if a then (-1 : ℝ) else 1)
      (fun b : Bool => if b then (-1 : ℝ) else 1) := by
  ext a b
  cases a <;> cases b <;> norm_num [signMatrix, xorFun, Matrix.vecMulVec]

theorem bit_and_outer : bitMatrix andFun =
    Matrix.vecMulVec (fun a : Bool => if a then (1 : ℝ) else 0)
      (fun b : Bool => if b then (1 : ℝ) else 0) := by
  ext a b
  cases a <;> cases b <;> norm_num [bitMatrix, andFun, Matrix.vecMulVec]

theorem rank_sign_xor : (signMatrix xorFun).rank = 1 := by
  have hu : (signMatrix xorFun).rank ≤ 1 := by
    rw [sign_xor_outer]
    exact Matrix.rank_vecMulVec_le _ _
  have hm : (signMatrix xorFun).submatrix (fun _ : Fin 1 => false)
      (fun _ : Fin 1 => false) = 1 := by
    ext i j
    fin_cases i; fin_cases j
    norm_num [signMatrix, xorFun, Matrix.submatrix]
  have hl := Matrix.rank_submatrix_le (signMatrix xorFun)
    (fun _ : Fin 1 => false) (fun _ : Fin 1 => false)
  rw [hm, Matrix.rank_one] at hl
  simp only [Fintype.card_fin] at hl
  omega

theorem rank_bit_and : (bitMatrix andFun).rank = 1 := by
  have hu : (bitMatrix andFun).rank ≤ 1 := by
    rw [bit_and_outer]
    exact Matrix.rank_vecMulVec_le _ _
  have hm : (bitMatrix andFun).submatrix (fun _ : Fin 1 => true)
      (fun _ : Fin 1 => true) = 1 := by
    ext i j
    fin_cases i; fin_cases j
    norm_num [bitMatrix, andFun, Matrix.submatrix]
  have hl := Matrix.rank_submatrix_le (bitMatrix andFun)
    (fun _ : Fin 1 => true) (fun _ : Fin 1 => true)
  rw [hm, Matrix.rank_one] at hl
  simp only [Fintype.card_fin] at hl
  omega

theorem sign_encoding_counterexample :
    ¬ ((D xorFun : ℝ) ≤ 16 * (Real.logb 2 ((signMatrix xorFun).rank : ℝ)) ^ 2) := by
  rw [D_xor, rank_sign_xor]
  norm_num [Real.logb]

theorem bit_encoding_counterexample :
    ¬ ((D andFun : ℝ) ≤ 16 * (Real.logb 2 ((bitMatrix andFun).rank : ℝ)) ^ 2) := by
  rw [D_and, rank_bit_and]
  norm_num [Real.logb]

end TLMC2571
