/-
  Conjecture 00000004766 — Two-Dimensional Noncrossing and Narayana Polynomials
  MainTheorems.lean:
  - Positive Small-Order Mirage Theorems (explaining why n ≤ 3 and boundary grids satisfy
    symmetric Narayana formulas and why bi-free BNC(χ) is word-invariant).
  - Complete Formal Refutations of Readings I, II, III, and IV.
  - Master Disproof Theorem `conjecture_00000004766_false`.
-/
import TwoDimNarayana.Basic
import TwoDimNarayana.Partitions
import TwoDimNarayana.Grid2D

namespace TwoDimNarayana

/-! ### Reading II: Bi-Ordered / 2D Poset Joint Noncrossing `NC(id) ∩ NC(σ)` -/

/-- Block-enumerator polynomial of partitions of `{0, ..., n-1}` noncrossing in both
    the standard order `0 < 1 < ... < n-1` and the second linear order `sigma`. -/
def poset2DPoly (n : Nat) (sigma : List Nat) : Poly1 :=
  blockPoly1 n ((allRGS n).filter (fun p => isNCOrder p (List.range n) && isNCOrder p sigma))

/-- **Positive Mirage (Reading II, n ≤ 3):** For n ∈ {1, 2, 3}, joint noncrossing wrt
    any permutation matches the palindromic 1D Narayana polynomial. -/
theorem poset2D_mirage_le3 :
    poset2DPoly 1 [0] = narayanaPoly1 1 ∧
    poset2DPoly 2 [1, 0] = narayanaPoly1 2 ∧
    poset2DPoly 3 [0, 2, 1] = narayanaPoly1 3 ∧
    poset2DPoly 3 [1, 2, 0] = narayanaPoly1 3 := by
  decide

/-- **Disproof of Reading II (n = 4):**
    1. Order-dependence: `σ₁ = [0, 1, 2, 3]` gives `t + 6 t^2 + 6 t^3 + t^4` (total 14),
       whereas `σ₂ = [0, 1, 3, 2]` gives `t + 5 t^2 + 6 t^3 + t^4` (total 13), so no closed
       polynomial in `(n, t)` alone exists.
    2. Failure of Narayana palindromicity: `poset2DPoly 4 [0, 1, 3, 2]` has `c_2 = 5 ≠ 6 = c_3`. -/
theorem reading2_poset2D_disproof :
    poset2DPoly 4 [0, 1, 2, 3] = [0, 1, 6, 6, 1] ∧
    poset2DPoly 4 [0, 1, 3, 2] = [0, 1, 5, 6, 1] ∧
    poset2DPoly 4 [0, 1, 2, 3] ≠ poset2DPoly 4 [0, 1, 3, 2] ∧
    isPalindromic1 4 (poset2DPoly 4 [0, 1, 3, 2]) = false := by
  decide

/-! ### Reading III: Voiculescu's Bi-Free `BNC(χ)` & Untwisted Two-Channel `NC_2(χ)` -/

inductive Channel where
  | L : Channel
  | R : Channel
  deriving DecidableEq, Repr

/-- Charlesworth–Nelson–Skoufranis bi-free reading order `s_χ`:
    Left indices in increasing order followed by Right indices in decreasing order. -/
def biFreeOrder (chi : List Channel) : List Nat :=
  let idx := List.range chi.length
  let lefts := idx.filter (fun i => chi.getD i Channel.L == Channel.L)
  let rights := idx.filter (fun i => chi.getD i Channel.L == Channel.R)
  lefts ++ rights.reverse

/-- Number of blocks of `part` intersecting channel `c`. -/
def channelBlockCount (chi : List Channel) (c : Channel) (part : List Nat) : Nat :=
  let k := numBlocks part
  let n := chi.length
  ((List.range k).filter (fun b =>
    (List.range n).any (fun i => part.getD i 0 == b && chi.getD i Channel.L == c))).length

/-- Bivariate Left/Right block-generating polynomial `∑_{π ∈ BNC(χ)} u^{b_L(π)} v^{b_R(π)}`. -/
def biFreePoly2 (chi : List Channel) : Poly2 :=
  let n := chi.length
  let parts := (allRGS n).filter (fun p => isNCOrder p (biFreeOrder chi))
  makePoly2 n parts (channelBlockCount chi Channel.L) (channelBlockCount chi Channel.R)

/-- Untwisted two-channel noncrossing polynomial `∑_{π ∈ NC(n)} u^{b_L(π)} v^{b_R(π)}`. -/
def untwisted2ChannelPoly2 (chi : List Channel) : Poly2 :=
  let n := chi.length
  let parts := ncPartitions n
  makePoly2 n parts (channelBlockCount chi Channel.L) (channelBlockCount chi Channel.R)

/-- **Positive CNS Word-Invariance Theorem at (m, n) = (2, 2):**
    In Voiculescu's bi-free `BNC(χ)`, `LLRR`, `LRLR`, and `LRRL` yield the identical polynomial
    `2 u v + 3 u v^2 + 3 u^2 v + 6 u^2 v^2`. -/
theorem bnc_word_invariance_2_2 :
    biFreePoly2 [.L, .L, .R, .R] = biFreePoly2 [.L, .R, .L, .R] ∧
    biFreePoly2 [.L, .L, .R, .R] = biFreePoly2 [.L, .R, .R, .L] ∧
    coeff2 (biFreePoly2 [.L, .L, .R, .R]) 1 1 = 2 ∧
    coeff2 (biFreePoly2 [.L, .L, .R, .R]) 1 2 = 3 ∧
    coeff2 (biFreePoly2 [.L, .L, .R, .R]) 2 1 = 3 ∧
    coeff2 (biFreePoly2 [.L, .L, .R, .R]) 2 2 = 6 := by
  decide

/-- **Disproof of Reading III (Bi-Free & Two-Channel Noncrossing):**
    1. Asymmetric `(u, v)` polynomial when `m ≠ n`: for `χ = LLR` (`m = 2, n = 1`),
       `P_{LLR}(u, v) = 2 u v + 3 u^2 v` (`[u^2 v] = 3 ≠ 0 = [u v^2]`, `isSymmetric2 = false`).
    2. Failure of Narayana biduality even when `m = n = 2`: `BNC(LLRR)` has `[u v] = 2 ≠ 6 = [u^2 v^2]`.
    3. Word-dependence for untwisted 2-channel `NC_2(χ)` at `m = n = 2`:
       `LLRR` has `[u v] = 2, [u^2 v^2] = 6`, whereas `LRLR` has `[u v] = 1, [u^2 v^2] = 7`. -/
theorem reading3_bifree_twochannel_disproof :
    coeff2 (biFreePoly2 [.L, .L, .R]) 2 1 = 3 ∧
    coeff2 (biFreePoly2 [.L, .L, .R]) 1 2 = 0 ∧
    isSymmetric2 3 (biFreePoly2 [.L, .L, .R]) = false ∧
    isBidual2 2 (biFreePoly2 [.L, .L, .R, .R]) = false ∧
    coeff2 (untwisted2ChannelPoly2 [.L, .L, .R, .R]) 1 1 = 2 ∧
    coeff2 (untwisted2ChannelPoly2 [.L, .R, .L, .R]) 1 1 = 1 ∧
    untwisted2ChannelPoly2 [.L, .L, .R, .R] ≠ untwisted2ChannelPoly2 [.L, .R, .L, .R] := by
  decide

/-! ### Reading IV: Coupled Pairs `(π₁, π₂) ∈ NC(n) × NC(n)` -/

/-- Cartesian product of `NC(n) × NC(n)`. -/
def ncPairs (n : Nat) : List (List Nat × List Nat) :=
  let nc := ncPartitions n
  nc.flatMap (fun p1 => nc.map (fun p2 => (p1, p2)))

/-- Reading IV-a: Join-compatible noncrossing pairs `{(π₁, π₂) ∈ NC(n)² : π₁ ∨_{Π(n)} π₂ ∈ NC(n)}`. -/
def joinNCPoly2 (n : Nat) : Poly2 :=
  let pairs := (ncPairs n).filter (fun (p1, p2) => isNCOrder (joinPartition n p1 p2) (List.range n))
  makePoly2 n pairs (fun x => numBlocks x.1) (fun x => numBlocks x.2)

/-- Reading IV-b: Mutually block-noncrossing pairs on `{0, ..., n-1}`. -/
def mutualNCPoly2 (n : Nat) : Poly2 :=
  let pairs := (ncPairs n).filter (fun (p1, p2) => mutuallyBlockNC n p1 p2)
  makePoly2 n pairs (fun x => numBlocks x.1) (fun x => numBlocks x.2)

/-- Reading IV-c: Refinement 2-chains `π₁ ≤ π₂` in `NC(n)`. -/
def chain2NCPoly2 (n : Nat) : Poly2 :=
  let pairs := (ncPairs n).filter (fun (p1, p2) => refines n p1 p2)
  makePoly2 n pairs (fun x => numBlocks x.1) (fun x => numBlocks x.2)

/-- Reading IV-d: Bicolored interleaved circle `π ⊔ σ ∈ NC(χ)` for signature `χ`. -/
def bicoloredDisjointPoly2 (chi : List Channel) : Poly2 :=
  let idx := List.range chi.length
  let leftPos := idx.filter (fun i => chi.getD i Channel.L == Channel.L)
  let rightPos := idx.filter (fun i => chi.getD i Channel.L == Channel.R)
  let m := leftPos.length
  let n := rightPos.length
  let ncL := ncPartitions m
  let ncR := ncPartitions n
  let allPairs := ncL.flatMap (fun pL => ncR.map (fun pR => (pL, pR)))
  let validPairs := allPairs.filter (fun (pL, pR) =>
    -- Embed pL on leftPos (labels 0..m-1) and pR on rightPos (labels m..m+n-1)
    let combined := idx.map (fun pos =>
      if chi.getD pos Channel.L == Channel.L then
        let k := (leftPos.idxOf pos)
        pL.getD k 0
      else
        let k := (rightPos.idxOf pos)
        m + pR.getD k 0)
    isNCOrder combined idx)
  makePoly2 (Nat.max m n) validPairs (fun x => numBlocks x.1) (fun x => numBlocks x.2)

/-- **Positive Mirage (Reading IV, n ≤ 3):** For ALL `n ∈ {1, 2, 3}`, both join-compatible
    and mutually block-noncrossing pairs have bivariate polynomial equal to the symmetric
    closed product `N_n(u) * N_n(v)`! -/
theorem coupled_pairs_mirage_le3 :
    joinNCPoly2 1 = outerProdPoly (narayanaPoly1 1) (narayanaPoly1 1) ∧
    joinNCPoly2 2 = outerProdPoly (narayanaPoly1 2) (narayanaPoly1 2) ∧
    joinNCPoly2 3 = outerProdPoly (narayanaPoly1 3) (narayanaPoly1 3) ∧
    mutualNCPoly2 1 = outerProdPoly (narayanaPoly1 1) (narayanaPoly1 1) ∧
    mutualNCPoly2 2 = outerProdPoly (narayanaPoly1 2) (narayanaPoly1 2) ∧
    mutualNCPoly2 3 = outerProdPoly (narayanaPoly1 3) (narayanaPoly1 3) := by
  decide

/-- **Disproof of Reading IV (Coupled Pairs in `NC(n)²`):**
    1. Join-compatible pairs break at `n = 4`: total count drops from `14² = 196` to `194`,
       and `[u^3 v^3] = 34 ≠ 36 = [u^2 v^2]` (`isBidual2 4 = false`).
    2. Mutually block-noncrossing pairs break at `n = 4`: total count drops to `165`,
       with `[u^1 v^1] = 0 ≠ 1 = [u^4 v^4]` (`isBidual2 4 = false`).
    3. Refinement 2-chains `π₁ ≤ π₂` fail `(u, v)`-symmetry at `n = 2`:
       `[u^2 v^1] = 1 ≠ 0 = [u^1 v^2]` (`isSymmetric2 2 = false`).
    4. Bicolored circle `π ⊔ σ ∈ NC(χ)` fails `(u, v)`-symmetry at `(2, 1)` (`χ = LLR`),
       fails word-independence at `(2, 2)` (`LLRR` total `4 ≠ 3` `LRLR`), and fails Narayana
       biduality even on alternating `LRLR` (`[u^1 v^1] = 0 ≠ 1 = [u^2 v^2]`). -/
theorem reading4_coupled_pairs_disproof :
    totalCount2 (joinNCPoly2 4) = 194 ∧
    coeff2 (joinNCPoly2 4) 2 2 = 36 ∧
    coeff2 (joinNCPoly2 4) 3 3 = 34 ∧
    isBidual2 4 (joinNCPoly2 4) = false ∧
    totalCount2 (mutualNCPoly2 4) = 165 ∧
    coeff2 (mutualNCPoly2 4) 1 1 = 0 ∧
    coeff2 (mutualNCPoly2 4) 4 4 = 1 ∧
    isBidual2 4 (mutualNCPoly2 4) = false ∧
    isSymmetric2 2 (chain2NCPoly2 2) = false ∧
    isSymmetric2 2 (bicoloredDisjointPoly2 [.L, .L, .R]) = false ∧
    totalCount2 (bicoloredDisjointPoly2 [.L, .L, .R, .R]) = 4 ∧
    totalCount2 (bicoloredDisjointPoly2 [.L, .R, .L, .R]) = 3 ∧
    isBidual2 2 (bicoloredDisjointPoly2 [.L, .R, .L, .R]) = false := by
  decide

/-! ### Consolidated Reading I Bundle & Master Disproof Theorem -/

theorem reading1_grid2D_disproof :
    isPalindromic1 4 (gridBiNCPoly 2 2) = false ∧
    isPalindromic1 4 (gridSliceNCPoly 2 2) = false ∧
    (∀ m n : Nat, 2 ≤ m → 2 ≤ n → c2Grid m n = m * n + 1) ∧
    c2Grid 2 1 = 1 ∧
    (¬ ∃ (D : Nat) (P : Poly2), 0 < D ∧
      ∀ m n : Nat, 1 ≤ m → 1 ≤ n →
        evalPoly2 P (m : Int) (n : Int) = ((D * c2Grid m n) : Int)) := by
  refine ⟨gridBiNCPoly_2_2_disproof.2.2, gridSliceNCPoly_2_2_disproof.2,
    c2Grid_eq_mul_add_one, c2Grid_small_values.1, grid2D_twoBlock_not_polynomial⟩

/-- **Master Theorem (`conjecture_00000004766_false`):**
    Conjecture 00000004766 is FALSE across all four canonical mathematical readings of
    two-dimensional noncrossing (Cartesian grid bi-noncrossing, 2D poset bi-ordered noncrossing,
    Voiculescu's bi-free / two-channel noncrossing, and coupled pairs of noncrossing partitions). -/
theorem conjecture_00000004766_false :
    -- Reading I (Grid [m] × [n]): non-palindromic at (2,2) and non-polynomial in (m,n) at k = 2
    (isPalindromic1 4 (gridBiNCPoly 2 2) = false ∧
     (∀ m n : Nat, 2 ≤ m → 2 ≤ n → c2Grid m n = m * n + 1) ∧
     ¬ ∃ (D : Nat) (P : Poly2), 0 < D ∧
       ∀ m n : Nat, 1 ≤ m → 1 ≤ n →
         evalPoly2 P (m : Int) (n : Int) = ((D * c2Grid m n) : Int)) ∧
    -- Reading II (2D Poset NC(id) ∩ NC(σ)): order-dependent and non-palindromic at n = 4
    (poset2DPoly 4 [0, 1, 2, 3] ≠ poset2DPoly 4 [0, 1, 3, 2] ∧
     isPalindromic1 4 (poset2DPoly 4 [0, 1, 3, 2]) = false) ∧
    -- Reading III (Bi-free BNC(χ) & two-channel NC_2(χ)): asymmetric for m ≠ n, word-dependent untwisted
    (isSymmetric2 3 (biFreePoly2 [.L, .L, .R]) = false ∧
     isBidual2 2 (biFreePoly2 [.L, .L, .R, .R]) = false ∧
     untwisted2ChannelPoly2 [.L, .L, .R, .R] ≠ untwisted2ChannelPoly2 [.L, .R, .L, .R]) ∧
    -- Reading IV (Coupled pairs in NC(n)²): breaks Narayana product & biduality at n = 4, asymmetric 2-chains at n = 2
    (totalCount2 (joinNCPoly2 4) = 194 ∧
     isBidual2 4 (joinNCPoly2 4) = false ∧
     isBidual2 4 (mutualNCPoly2 4) = false ∧
     isSymmetric2 2 (chain2NCPoly2 2) = false) := by
  refine ⟨⟨reading1_grid2D_disproof.1, reading1_grid2D_disproof.2.2.1, reading1_grid2D_disproof.2.2.2.2⟩,
    ⟨reading2_poset2D_disproof.2.2.1, reading2_poset2D_disproof.2.2.2⟩,
    ⟨reading3_bifree_twochannel_disproof.2.2.1, reading3_bifree_twochannel_disproof.2.2.2.1,
     reading3_bifree_twochannel_disproof.2.2.2.2.2.2⟩,
    ⟨reading4_coupled_pairs_disproof.1, reading4_coupled_pairs_disproof.2.2.2.1,
     reading4_coupled_pairs_disproof.2.2.2.2.2.2.2.1, reading4_coupled_pairs_disproof.2.2.2.2.2.2.2.2.1⟩⟩

end TwoDimNarayana
