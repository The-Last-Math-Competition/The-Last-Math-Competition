import Conjecture00000000505.Ring
import Conjecture00000000505.Poly

namespace Conjecture00000000505

/-- A strictly increasing chain `I ⊆ p_0 ⊂ p_1 ⊂ ... ⊂ p_d` of prime ideals of `R`. -/
def IsPrimeChain (R : Type u) [CAlgRing R] (I : Ideal R) (d : Nat)
    (chain : Fin (d + 1) → Ideal R) : Prop :=
  (∀ x : R, x ∈ I → x ∈ chain ⟨0, Nat.zero_lt_succ d⟩) ∧
  (∀ i : Fin (d + 1), Ideal.IsPrime (chain i)) ∧
  (∀ i : Fin d, Ideal.StrictSubset
    (chain ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩)
    (chain ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩))

/-- Krull dimension `dim(R / I) = d`: maximum length of a chain of prime ideals of `R`
containing `I`. -/
def IsKrullDimQuot (R : Type u) [CAlgRing R] (I : Ideal R) (d : Nat) : Prop :=
  (∃ chain : Fin (d + 1) → Ideal R, IsPrimeChain R I d chain) ∧
  (∀ e : Nat, d < e → ¬ ∃ chain : Fin (e + 1) → Ideal R, IsPrimeChain R I e chain)

/-- `r` is a non-zero-divisor (regular element) on `R / J`. -/
def IsRegOnQuot {R : Type u} [CAlgRing R] (J : Ideal R) (r : R) : Prop :=
  ∀ f : R, r * f ∈ J → f ∈ J

/-- Recursive regular-sequence condition on `R / J`, including `(J + (seq)) ≠ R`. -/
def IsRegSeqAux {R : Type u} [CAlgRing R] (J : Ideal R) : List R → Prop
  | [] => (1 : R) ∉ J
  | r :: rs => IsRegOnQuot J r ∧ IsRegSeqAux (Ideal.sum J (Ideal.span [r])) rs

/-- `seq` is an `𝔪`-regular sequence on `R / I`. -/
def IsRegSeq (R : Type u) [CAlgRing R] (I m : Ideal R) (seq : List R) : Prop :=
  (∀ r ∈ seq, r ∈ m) ∧ IsRegSeqAux I seq

/-- Depth `depth_𝔪(R / I) = d`: maximum length of an `𝔪`-regular sequence on `R / I`. -/
def IsDepthQuot (R : Type u) [CAlgRing R] (I m : Ideal R) (d : Nat) : Prop :=
  (∃ seq : List R, seq.length = d ∧ IsRegSeq R I m seq) ∧
  (∀ e : Nat, d < e → ¬ ∃ seq : List R, seq.length = e ∧ IsRegSeq R I m seq)

/-- Standard graded Cohen–Macaulay condition for `R / I` (`R = K[X_0, ..., X_{n-1}]`):
`R / I` is nonzero (`1 ∉ I`) and its `𝔪`-depth equals its Krull dimension. -/
def IsCohenMacaulayQuot (n : Nat) (K : Type u) [CAlgField K] (I : Ideal (MPoly n K)) : Prop :=
  (1 : MPoly n K) ∉ I ∧
  ∃ d : Nat, IsKrullDimQuot (MPoly n K) I d ∧
    IsDepthQuot (MPoly n K) I (MPoly.maxIdeal n K) d

end Conjecture00000000505
