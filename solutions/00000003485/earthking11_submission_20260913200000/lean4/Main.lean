/-
  Disproof of conjecture `00000003485`: kernels of bounded-out-degree digraphs
  of girth at least five.

  Conjecture (as filed): every digraph with bounded out-degree and (directed)
  girth at least five has a kernel; its "critical configuration" was said to be
  the directed odd cycle with a one-point source, and the bound was described as
  a tightening of Richardson's theorem.

  We refute the statement with the smallest possible witness, the directed
  `5`-cycle `C₅` on the vertices `0, 1, 2, 3, 4` with arcs `i → i + 1 (mod 5)`:

    * its out-degree is `1` at every vertex (so "bounded" holds in the sharpest
      possible sense);
    * its directed girth is `5` (no directed closed walk of length `1, 2, 3, 4`;
      the cycle `0 → 1 → 2 → 3 → 4 → 0` has length `5`); the underlying
      undirected graph is a `5`-cycle, so its undirected girth is `5` as well;
    * it has no kernel: no subset `S ⊆ {0,1,2,3,4}` is simultaneously
      independent and out-stable.

  A kernel here is a set `S` that is
    (i)  *independent*: no arc in either direction joins two members of `S`;
    (ii) *out-stable* (absorbing): every vertex outside `S` has an arc into `S`.
  A subset of `Fin 5` is the same thing as a function `Fin 5 → Bool` (its
  indicator). The main theorem `no_kernel5` quantifies over an *arbitrary* such
  function and proves, by case analysis on its five values (the `2^5 = 32`
  subsets), that the kernel predicate is always `false`. The list computation
  `kernelMasks5_nil` records the same fact as an explicit brute force over the
  `32` bitmasks.

  The same computation is repeated for `C₃` and `C₇`, exhibiting the general
  odd-cycle obstruction at three sizes. The general theorem ("a directed cycle
  has a kernel iff it is even") is proved by the alternating-set argument in
  `main.tex`; it is not formalised here beyond the concrete witnesses.

  This file uses CORE LEAN ONLY (`import Std`); it does not use Mathlib,
  `Finset`, `ZMod`, `SimpleGraph`, `List.permutations`, or `sorry`. Function
  equality is never needed: subsets are compared value by value, and the
  enumerations filter with a `Bool`-valued predicate.
-/

import Std

set_option maxRecDepth 1000000

namespace Tlmc3485

/-! ## The witness `C₅`: vertices, arcs, out-degree, girth -/

/-- The five vertices of `C₅`. -/
def V5 : List (Fin 5) := [(0 : Fin 5), 1, 2, 3, 4]

/-- The arc relation of the directed `5`-cycle: `arc5 i j` is `true` exactly
when `j = i + 1 (mod 5)`. Addition in `Fin 5` is modular, so this is the cyclic
successor. -/
def arc5 (i j : Fin 5) : Bool := decide (j = i + 1)

/-- The out-degree of a vertex of `C₅`, by counting its out-neighbours. -/
def outDeg5 (i : Fin 5) : Nat := (V5.filter (fun j => arc5 i j)).length

/-- `walk5 k i j` is `true` exactly when there is a directed walk of length
exactly `k` from `i` to `j` in `C₅`. -/
def walk5 : Nat → Fin 5 → Fin 5 → Bool
  | 0, i, j => decide (i = j)
  | k + 1, i, j => V5.any (fun m => walk5 k i m && arc5 m j)

/-- The out-degree is bounded by `1` at every vertex of `C₅` (indeed it equals
`1`). -/
theorem outdeg5_le_one : (V5.map outDeg5).all (fun d => d ≤ 1) = true := by decide

/-- Every vertex of `C₅` has out-degree exactly `1`. -/
theorem outdeg5_eq_one : (V5.map outDeg5).all (fun d => d = 1) = true := by decide

/-- There is no directed closed walk of length `1`, `2`, `3`, or `4` in `C₅`,
i.e. the directed girth of `C₅` is at least `5`. -/
theorem girth5_ge_five :
    (V5.all (fun i =>
      !(walk5 1 i i) && !(walk5 2 i i) && !(walk5 3 i i) && !(walk5 4 i i))) = true := by
  decide

/-- The directed cycle `0 → 1 → 2 → 3 → 4 → 0` is a directed closed walk of
length `5`, so the directed girth of `C₅` is *exactly* `5`. -/
theorem girth5_le_five : walk5 5 0 0 = true := by decide

/-! ## Subsets of `Fin 5` and the kernel conditions -/

/-- Independence: no arc in either direction joins two members of `S`. The only
unordered pairs joined by an arc of `C₅` are `{0,1}, {1,2}, {2,3}, {3,4},
{4,0}`; each such pair must not be fully contained in `S`. -/
def independent5 (S : Fin 5 → Bool) : Bool :=
  !(S 0 && S 1) && !(S 1 && S 2) && !(S 2 && S 3) && !(S 3 && S 4) && !(S 4 && S 0)

/-- Out-stability (the absorbing property): every vertex outside `S` has an arc
into `S`. Since every vertex of `C₅` has the single out-neighbour `i + 1`, this
says: for every vertex `i`, either `i ∈ S` or `i + 1 ∈ S`. -/
def outStable5 (S : Fin 5 → Bool) : Bool :=
  (S 0 || S 1) && (S 1 || S 2) && (S 2 || S 3) && (S 3 || S 4) && (S 4 || S 0)

/-- `S` is a kernel of `C₅` iff it is independent and out-stable. -/
def kernel5 (S : Fin 5 → Bool) : Bool := independent5 S && outStable5 S

/-- **The directed `5`-cycle has no kernel.** For an arbitrary subset
`S : Fin 5 → Bool`, case analysis on its five values (the `2^5 = 32` subsets)
shows that `kernel5 S` is always `false`. -/
theorem no_kernel5 (S : Fin 5 → Bool) : kernel5 S = false := by
  unfold kernel5 independent5 outStable5
  cases h0 : S 0 <;> cases h1 : S 1 <;> cases h2 : S 2 <;> cases h3 : S 3 <;>
    cases h4 : S 4
  all_goals decide

/-- `C₅` has a kernel. -/
def HasKernel5 : Prop := ∃ S : Fin 5 → Bool, kernel5 S = true

/-- **No kernel exists.** Negation form of `no_kernel5`. -/
theorem no_kernel5_exists : ¬ HasKernel5 := by
  rintro ⟨S, hS⟩
  have h := no_kernel5 S
  rw [h] at hS
  exact Bool.noConfusion hS

/-! ## The same brute force as an explicit enumeration of the `32` bitmasks -/

/-- Bit `i` of the mask `S`. -/
def bit (S i : Nat) : Bool := decide (S / 2 ^ i % 2 = 1)

/-- Independence, read off a `5`-bit mask. -/
def independentMask5 (S : Nat) : Bool :=
  !(bit S 0 && bit S 1) && !(bit S 1 && bit S 2) && !(bit S 2 && bit S 3) &&
    !(bit S 3 && bit S 4) && !(bit S 4 && bit S 0)

/-- Out-stability, read off a `5`-bit mask. -/
def outStableMask5 (S : Nat) : Bool :=
  (bit S 0 || bit S 1) && (bit S 1 || bit S 2) && (bit S 2 || bit S 3) &&
    (bit S 3 || bit S 4) && (bit S 4 || bit S 0)

/-- The kernel predicate on `5`-bit masks. -/
def kernelMask5 (S : Nat) : Bool := independentMask5 S && outStableMask5 S

/-- The kernels of `C₅` among all `2^5 = 32` subsets. -/
def kernelMasks5 : List Nat := (List.range 32).filter kernelMask5

/-- **Brute force over all `32` subsets: none is a kernel.** -/
theorem kernelMasks5_nil : kernelMasks5 = [] := by decide

/-- The number of kernels of `C₅` is `0`. -/
theorem kernelMasks5_count : kernelMasks5.length = 0 := by decide

/-- Evaluation form of the `32`-subset brute force (prints `[]`). -/
example : kernelMasks5 = [] := kernelMasks5_nil

/-! ## Odd cycles `C₃` and `C₇` -/

/-- Independence for the directed `3`-cycle: no arc either way joins two
members. -/
def independent3 (S : Fin 3 → Bool) : Bool :=
  !(S 0 && S 1) && !(S 1 && S 2) && !(S 2 && S 0)

/-- Out-stability for the directed `3`-cycle. -/
def outStable3 (S : Fin 3 → Bool) : Bool :=
  (S 0 || S 1) && (S 1 || S 2) && (S 2 || S 0)

/-- The kernel predicate of `C₃`. -/
def kernel3 (S : Fin 3 → Bool) : Bool := independent3 S && outStable3 S

/-- **`C₃` has no kernel** (case analysis over the `2^3 = 8` subsets). -/
theorem no_kernel3 (S : Fin 3 → Bool) : kernel3 S = false := by
  unfold kernel3 independent3 outStable3
  cases h0 : S 0 <;> cases h1 : S 1 <;> cases h2 : S 2
  all_goals decide

/-- Independence for the directed `7`-cycle. -/
def independent7 (S : Fin 7 → Bool) : Bool :=
  !(S 0 && S 1) && !(S 1 && S 2) && !(S 2 && S 3) && !(S 3 && S 4) &&
    !(S 4 && S 5) && !(S 5 && S 6) && !(S 6 && S 0)

/-- Out-stability for the directed `7`-cycle. -/
def outStable7 (S : Fin 7 → Bool) : Bool :=
  (S 0 || S 1) && (S 1 || S 2) && (S 2 || S 3) && (S 3 || S 4) &&
    (S 4 || S 5) && (S 5 || S 6) && (S 6 || S 0)

/-- The kernel predicate of `C₇`. -/
def kernel7 (S : Fin 7 → Bool) : Bool := independent7 S && outStable7 S

/-- **`C₇` has no kernel** (case analysis over the `2^7 = 128` subsets). -/
theorem no_kernel7 (S : Fin 7 → Bool) : kernel7 S = false := by
  unfold kernel7 independent7 outStable7
  cases h0 : S 0 <;> cases h1 : S 1 <;> cases h2 : S 2 <;> cases h3 : S 3 <;>
    cases h4 : S 4 <;> cases h5 : S 5 <;> cases h6 : S 6
  all_goals decide

/-! ## The refutation of conjecture `00000003485` -/

/-- The hypotheses of the conjecture hold for `C₅`: out-degree at most `1`
(bounded) and directed girth at least `5`. -/
theorem C5_in_class :
    (V5.map outDeg5).all (fun d => d ≤ 1) = true ∧
      (V5.all (fun i =>
        !(walk5 1 i i) && !(walk5 2 i i) && !(walk5 3 i i) && !(walk5 4 i i))) = true :=
  ⟨outdeg5_le_one, girth5_ge_five⟩

/-- **Conjecture `00000003485` is false.** The directed `5`-cycle satisfies the
conjectured hypotheses (bounded out-degree, girth at least five) but has no
kernel, so the asserted implication fails. -/
theorem conjecture_00000003485_false :
    (V5.map outDeg5).all (fun d => d ≤ 1) = true ∧
      (V5.all (fun i =>
        !(walk5 1 i i) && !(walk5 2 i i) && !(walk5 3 i i) && !(walk5 4 i i))) = true ∧
        ¬ HasKernel5 :=
  ⟨outdeg5_le_one, girth5_ge_five, no_kernel5_exists⟩

/-- The collected refutation, including the three concrete odd-cycle witnesses
and the explicit `32`-subset enumeration. -/
theorem conjecture_00000003485_refuted :
    (V5.map outDeg5).all (fun d => d ≤ 1) = true ∧
      (V5.all (fun i =>
        !(walk5 1 i i) && !(walk5 2 i i) && !(walk5 3 i i) && !(walk5 4 i i))) = true ∧
      walk5 5 0 0 = true ∧ (∀ S : Fin 5 → Bool, kernel5 S = false) ∧
      kernelMasks5 = [] ∧ (∀ S : Fin 3 → Bool, kernel3 S = false) ∧
      (∀ S : Fin 7 → Bool, kernel7 S = false) :=
  ⟨outdeg5_le_one, girth5_ge_five, girth5_le_five, no_kernel5, kernelMasks5_nil,
    no_kernel3, no_kernel7⟩

end Tlmc3485
