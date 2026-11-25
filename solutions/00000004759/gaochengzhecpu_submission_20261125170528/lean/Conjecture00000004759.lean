import Conjecture00000004759.Basic
import Conjecture00000004759.FockModel
import Conjecture00000004759.Counterexamples
import Conjecture00000004759.NoUnnestedWeightedCount
import Conjecture00000004759.NestedRecursion

/-
  Conjecture 00000004759 — Master Structural Resolution Theorem
  Core Lean 4.19.0 (zero external dependencies).

  Source Statement:
    Definition: Operator-valued free probability is the free theory with values in a subalgebra.
    Conjecture: The convolution recursion is always given by the weighted count of nested
    noncrossing partitions, and polynomials of depth at most three are computable.
    (nested recursion of operator-valued convolution)

  Verdict: DISPROVED (False as stated; Clause 1 fails across every weighted-count formalization,
  while Speicher's nested operator-valued recursion holds and makes depth/degree ≤ 3 polynomials
  constructively computable from the full `B`-multilinear moment maps, though NOT from
  un-inserted moments alone).
-/

namespace Conjecture00000004759

/-- Master Resolution of Conjecture 00000004759:
    1. **Concrete All-Order `B`-Free Realization:** `mat2FockSpace` is a genuine operator-valued
       probability space over `B = M₂(ℤ)` with proved all-order `B`-freeness (`mat2Fock_isBFree`).
    2. **Disproof of Moment/Cumulant Weighted-Count Convolutions:** `opX` and `opXtilde` have
       identical power moments `E(X^k) = E(X̃^k)` for all `k ∈ ℕ`, yet disagree under `B`-free
       additive convolution already at `n = 3` (`diag(4,0) ≠ diag(3,1)`, minimal nested order)
       with `Y_det = ι(E₁₁)`, at `n = 2` multiplicatively (`E₁₁ ≠ 0`), and at `n = 4` (`diag(8,2) ≠ diag(7,3)`)
       and `n = 6` (`diag(40,5) ≠ diag(30,12)`) for strictly centered `B`-free semicirculars!
    3. **Disproof of Un-Nested Block-Evaluation Weightings:** Even given full `B`-insertions
       `(B₁, B₂, B₃)` and covariance `η_swap(B) = diag(b₂₂, b₁₁)`, NO `ℤ`-linear combination of
       ALL 78 un-nested trilinear operators equals either `η_swap(B₁ η_swap(B₂) B₃)` or `μ₄^{X_swap}`.
    4. **Exact Central-Commutative Boundary:** Over any commutative `B`, central cumulant maps
       `κ(r, args) = (∏ args) * c(r + 1)` DO collapse `evalNC` to `(∏ b_i) * blockWeightProd π c`.
    5. **Computability of Depth/Degree ≤ 3 Polynomials:** Given the genuine `B`-multilinear moment
       oracles, `computePolyDeg3` constructively computes `E(P(X, Y))` for every degree-`≤ 3`
       polynomial `P ∈ B⟨X, Y⟩` over EVERY abstract `OpValProbSpace`, and `sumOverNC` computes
       depth-3 nested convolutions at `n = 6`. -/
theorem conjecture_00000004759_resolution :
    IsBFree mat2FockSpace (InMat2Color false) (InMat2Color true) ∧
    (∀ k : Nat, mat2FockSpace.exp (ringPow opX k) = mat2FockSpace.exp (ringPow opXtilde k)) ∧
    mat2FockSpace.exp (ringPow (opX + opYdet) 3) ≠
      mat2FockSpace.exp (ringPow (opXtilde + opYdet) 3) ∧
    mat2FockSpace.exp (ringPow (opX + opYsemi) 4) ≠
      mat2FockSpace.exp (ringPow (opXtilde + opYsemi) 4) ∧
    mat2FockSpace.exp (ringPow (opX + opYsemi) 6) ≠
      mat2FockSpace.exp (ringPow (opXtilde + opYsemi) 6) ∧
    (∀ cs : UnnestedComb,
      evalUnnestedComb cs etaSwap ≠ nestedRainbowSwap ∧
      evalUnnestedComb cs etaSwap ≠ mu4Xswap) ∧
    (∀ (B : Type) [CommAssocRing B] (c : Nat → B) (π : NCDecomp) (bs : List B),
      π.size ≥ 1 → bs.length = π.size - 1 →
      evalNC (fun r args => listProd args * c (r + 1)) π bs =
        listProd bs * blockWeightProd c π) ∧
    (∀ (A B : Type) [AssocRing A] [AssocRing B] (S : OpValProbSpace A B)
      (P₀ P₁ : A → Prop) (_ : IsBFree S P₀ P₁) (X Y : A),
      P₀ X → P₁ Y → ∀ P : PolyDeg3 B,
        S.exp (evalPolyInA S X Y P) =
          computePolyDeg3 (oracleOfVar S X) (oracleOfVar S Y) P) := by
  refine ⟨mat2Fock_isBFree,
          all_power_moments_eq,
          conv_det_n3_ne,
          conv_semi_n4_ne,
          conv_semi_n6_ne,
          no_unnested_weighted_count_all78,
          fun _ _ c π bs hsz hlen => central_commutative_weighted_count c π bs hsz hlen,
          fun _ _ _ _ S _ _ hF _ _ hX hY P => poly_deg_le_3_universal_soundness S hF hX hY P⟩

end Conjecture00000004759
