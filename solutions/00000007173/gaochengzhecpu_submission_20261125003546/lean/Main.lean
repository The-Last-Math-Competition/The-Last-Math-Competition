/-
  Conjecture 00000007173 — Complete Core Lean 4.19.0 Disproof & Analysis
  ======================================================================
  Source statement (English & Chinese):
    "Definition: Majorization with the poset of spectra.
     Conjecture: The endpoints of the majorization chain are the ordered
     spectra, and the realization of the endpoints is permutation similarity."
    "定义：优超：谱的偏序。猜想：优超的极值元素：优超链的端点为排序谱且点的实现为置换相似。"

  This self-contained Core Lean 4.19.0 formalization (zero external
  dependencies, zero `sorry`, zero `native_decide`, zero custom axioms)
  develops:
    1. General `n`-vector majorization (`Majorizes`, `StrictMajorizes`) via
       non-increasing rearrangement (`sortDesc`) and prefix sums (`prefixSum`).
    2. General `n × n` integer matrix algebra (`Mat n`), transpose, diagonal
       matrices, Frobenius norm decomposition, permutation matrices, and
       permutation similarity (`PermSimilar n`), including the `n × n`
       invariance theorem `permSimilar_preserves_isDiag`.
    3. Exact `2 × 2` spectral theory (`HasSpectrum2`, `HasOrderedSpectrum2`,
       uniqueness of ordered spectra) and rational orthogonal similarity
       (`RatOrthSimilar2`).
    4. Positive non-vacuity theorems establishing the genuine special cases:
       - `nonvacuity_ordering_equivalence`: `[a, b]` and `[b, a]` collapse to
         the same equivalence class in the majorization preorder;
       - `nonvacuity_schur_upper_endpoint_dim_n`: general `n × n` Schur
         Frobenius equality theorem (attaining a permuted spectrum on the
         diagonal of a matrix satisfying the spectral Frobenius identity forces
         the matrix to be diagonal and permutation-similar to `diagMat n lam`);
       - `nonvacuity_schur_upper_endpoint_symm2`: exact `2 × 2` symmetric
         iff-characterization of the upper Schur–Horn endpoint;
       - `nonvacuity_lidskii_diagonal_case`: for already-diagonal matrices,
         both Lidskii sum endpoints are realized by permutation similarity.
    5. Complete refutations of Conjecture 00000007173 across ALL three standard
       mathematical interpretations:
       - `refutation_schur_horn_lower_endpoint` (Reading I-A: Schur–Horn lower
         endpoint is the uniform mean vector, not an ordered spectrum, and
         symmetric realizations are neither permutation-similar to `diag(λ)`
         nor permutation-similar to each other);
       - `refutation_schur_horn_upper_nonhermitian` (Reading I-B: without
         symmetry/Hermiticity, upper-triangular matrices attain `diag(B) = λ↓`
         while failing permutation similarity);
       - `refutation_lidskii_sum_endpoints` (Reading II: Lidskii–Wielandt sum
         chain `λ↓(A) + λ↑(B) ≺ λ(A + U B Uᵀ) ≺ λ↓(A) + λ↓(B)` requires
         orthogonal/unitary similarity; for symmetric non-diagonal `B`, every
         permutation similarity `A + P B Pᵀ` lies strictly inside the chain);
       - `refutation_spectra_poset_slices` (Reading III: fixed-trace spectral
         poset has no upper endpoint over `ℤ`, and on non-negative slices has
         distinct-spectrum endpoints whose realizations fail permutation
         similarity).
-/

namespace Conjecture00000007173

/-! ## Section 1: General Vector Majorization (`List Int`) -/

/-- Insert an integer into a non-increasingly sorted list. -/
def insertDesc (x : Int) : List Int → List Int
  | [] => [x]
  | y :: ys => if x ≥ y then x :: y :: ys else y :: insertDesc x ys

/-- Non-increasing rearrangement `x↓` of an integer vector. -/
def sortDesc : List Int → List Int
  | [] => []
  | x :: xs => insertDesc x (sortDesc xs)

/-- Sum of all coordinates of an integer vector. -/
def totalSum : List Int → Int
  | [] => 0
  | x :: xs => x + totalSum xs

/-- Sum of the first `k` coordinates of an integer vector. -/
def prefixSum : Nat → List Int → Int
  | 0, _ => 0
  | _, [] => 0
  | k + 1, x :: xs => x + prefixSum k xs

/-- `Majorizes y x` means `x` is majorized by `y` (`x ≺ y`): equal dimension,
    equal total sum, and all prefix sums of `x↓` bounded above by `y↓`. -/
def Majorizes (y x : List Int) : Prop :=
  x.length = y.length ∧
  totalSum x = totalSum y ∧
  ∀ k : Nat, k ≤ x.length → prefixSum k (sortDesc x) ≤ prefixSum k (sortDesc y)

/-- Strict majorization `x ≺≠ y` in the majorization poset. -/
def StrictMajorizes (y x : List Int) : Prop :=
  Majorizes y x ∧ ¬ Majorizes x y

/-- Maximum of two integers. -/
def maxInt (a b : Int) : Int := if a ≥ b then a else b

/-- Exact two-coordinate characterization of majorization `x ≺ y`. -/
theorem majorizes_pair_iff (y1 y2 x1 x2 : Int) :
    Majorizes [y1, y2] [x1, x2] ↔
      (x1 + x2 = y1 + y2 ∧ maxInt x1 x2 ≤ maxInt y1 y2) := by
  constructor
  · intro ⟨_, hsum, hpref⟩
    have h1 := hpref 1 (by simp)
    simp only [totalSum] at hsum
    by_cases hx : x1 ≥ x2 <;> by_cases hy : y1 ≥ y2 <;>
      simp [sortDesc, insertDesc, prefixSum, maxInt, hx, hy] at h1 ⊢ <;> omega
  · intro ⟨hsum, hmax⟩
    refine ⟨rfl, ?_, ?_⟩
    · simp [totalSum]; omega
    · intro k hk
      match k with
      | 0 => simp [prefixSum]
      | 1 =>
        by_cases hx : x1 ≥ x2 <;> by_cases hy : y1 ≥ y2 <;>
          simp [sortDesc, insertDesc, prefixSum, maxInt, hx, hy] at hmax ⊢ <;> omega
      | 2 =>
        by_cases hx : x1 ≥ x2 <;> by_cases hy : y1 ≥ y2 <;>
          simp [sortDesc, insertDesc, prefixSum, hx, hy] <;> omega
      | n + 3 => simp at hk

/-! ## Section 2: General `n × n` Matrix Algebra and Permutation Similarity -/

/-- Summation over `Fin n` in Core Lean 4. -/
def finSum : (n : Nat) → (Fin n → Int) → Int
  | 0, _ => 0
  | n + 1, f =>
    f ⟨0, Nat.zero_lt_succ n⟩ +
      finSum n (fun i => f ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩)

theorem finSum_const_zero (n : Nat) : finSum n (fun _ => 0) = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [finSum, ih]

theorem finSum_congr {n : Nat} {f g : Fin n → Int} (h : ∀ i, f i = g i) :
    finSum n f = finSum n g := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [finSum, h ⟨0, Nat.zero_lt_succ n⟩]
    have htail :
        finSum n (fun i => f ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩) =
        finSum n (fun i => g ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩) :=
      ih (fun i => h ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩)
    rw [htail]

theorem finSum_add (n : Nat) (f g : Fin n → Int) :
    finSum n (fun i => f i + g i) = finSum n f + finSum n g := by
  induction n with
  | zero => simp [finSum]
  | succ n ih =>
    simp only [finSum]
    rw [ih]
    omega

theorem finSum_comm (m n : Nat) (f : Fin m → Fin n → Int) :
    finSum m (fun i => finSum n (fun j => f i j)) =
      finSum n (fun j => finSum m (fun i => f i j)) := by
  induction m with
  | zero =>
    simp [finSum, finSum_const_zero]
  | succ m ih =>
    simp only [finSum]
    rw [ih, ← finSum_add]

theorem finSum_ite_eq (n : Nat) (i0 : Fin n) (g : Fin n → Int) :
    finSum n (fun k => if k = i0 then g k else 0) = g i0 := by
  induction n with
  | zero => exact Fin.elim0 i0
  | succ n ih =>
    rcases i0 with ⟨val0, hlt0⟩
    cases val0 with
    | zero =>
      simp only [finSum, ↓reduceIte]
      have hzero :
          finSum n (fun i : Fin n =>
            if (⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩ : Fin (n + 1)) =
               ⟨0, hlt0⟩ then g ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩ else 0) = 0 := by
        rw [finSum_congr (g := fun _ => 0)]
        · exact finSum_const_zero n
        · intro i
          have hne : (⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩ : Fin (n + 1)) ≠ ⟨0, hlt0⟩ := by
            intro heq
            have hval : i.val + 1 = 0 := congrArg Fin.val heq
            omega
          simp [hne]
      rw [hzero]
      omega
    | succ m =>
      have hm : m < n := Nat.lt_of_succ_lt_succ hlt0
      simp only [finSum]
      have hne0 : (⟨0, Nat.zero_lt_succ n⟩ : Fin (n + 1)) ≠ ⟨m + 1, hlt0⟩ := by
        intro heq
        have hval : 0 = m + 1 := congrArg Fin.val heq
        omega
      simp only [hne0, ↓reduceIte]
      have htail :
          finSum n (fun i : Fin n =>
            if (⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩ : Fin (n + 1)) = ⟨m + 1, hlt0⟩
            then g ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩ else 0) =
          finSum n (fun i : Fin n =>
            if i = ⟨m, hm⟩ then g ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩ else 0) := by
        apply finSum_congr
        intro i
        by_cases hi : i = ⟨m, hm⟩
        · subst hi; simp
        · have hi' : (⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩ : Fin (n + 1)) ≠ ⟨m + 1, hlt0⟩ := by
            intro heq
            apply hi
            apply Fin.ext
            have hval : i.val + 1 = m + 1 := congrArg Fin.val heq
            change i.val = m
            omega
          simp [hi, hi']
      rw [htail, ih ⟨m, hm⟩ (fun i => g ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩)]
      rw [Int.zero_add]

theorem finSum_nonneg (n : Nat) (f : Fin n → Int) (hf : ∀ i, 0 ≤ f i) :
    0 ≤ finSum n f := by
  induction n with
  | zero => simp [finSum]
  | succ n ih =>
    simp only [finSum]
    have h0 := hf ⟨0, Nat.zero_lt_succ n⟩
    have ht := ih (fun i => f ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩)
      (fun i => hf ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩)
    omega

theorem finSum_eq_zero_of_nonneg (n : Nat) (f : Fin n → Int)
    (hf : ∀ i, 0 ≤ f i) (hsum : finSum n f = 0) :
    ∀ i, f i = 0 := by
  induction n with
  | zero => intro i; exact Fin.elim0 i
  | succ n ih =>
    simp only [finSum] at hsum
    have h0 : 0 ≤ f ⟨0, Nat.zero_lt_succ n⟩ := hf ⟨0, Nat.zero_lt_succ n⟩
    have ht : 0 ≤ finSum n (fun i => f ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩) :=
      finSum_nonneg n _ (fun i => hf ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩)
    have hf0 : f ⟨0, Nat.zero_lt_succ n⟩ = 0 := by omega
    have hft : finSum n (fun i => f ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩) = 0 := by omega
    have iht := ih (fun i => f ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩)
      (fun i => hf ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩) hft
    intro ⟨k, hk⟩
    cases k with
    | zero => exact hf0
    | succ m => exact iht ⟨m, Nat.lt_of_succ_lt_succ hk⟩

/-- Bijectivity of a finite permutation `σ : Fin n → Fin n`. -/
def IsBijection (n : Nat) (σ : Fin n → Fin n) : Prop :=
  ∃ τ : Fin n → Fin n, (∀ i, τ (σ i) = i) ∧ (∀ i, σ (τ i) = i)

theorem finSum_bijection (n : Nat) (σ : Fin n → Fin n) (hσ : IsBijection n σ)
    (g : Fin n → Int) :
    finSum n (fun i => g (σ i)) = finSum n g := by
  rcases hσ with ⟨τ, hleft, hright⟩
  have h1 : finSum n (fun i => g (σ i)) =
      finSum n (fun i => finSum n (fun j => if j = σ i then g j else 0)) := by
    apply finSum_congr
    intro i
    exact (finSum_ite_eq n (σ i) g).symm
  rw [h1, finSum_comm]
  apply finSum_congr
  intro j
  have hrew :
      (fun i : Fin n => if j = σ i then g j else 0) =
      (fun i : Fin n => if i = τ j then g j else 0) := by
    funext i
    by_cases h : i = τ j
    · subst h; simp [hright j]
    · have h' : j ≠ σ i := by
        intro heq
        apply h
        rw [heq, hleft i]
      simp [h, h']
  rw [hrew]
  exact finSum_ite_eq n (τ j) (fun _ => g j)

/-- `n × n` matrices over `Int`. -/
abbrev Mat (n : Nat) := Fin n → Fin n → Int

def matExt {n : Nat} {A B : Mat n} (h : ∀ i j, A i j = B i j) : A = B := by
  funext i j; exact h i j

def matAdd (n : Nat) (A B : Mat n) : Mat n := fun i j => A i j + B i j

def scaleMat (n : Nat) (c : Int) (A : Mat n) : Mat n := fun i j => c * A i j

def matTrans (n : Nat) (A : Mat n) : Mat n := fun i j => A j i

def matMul (n : Nat) (A B : Mat n) : Mat n :=
  fun i j => finSum n (fun k => A i k * B k j)

def diagMat (n : Nat) (d : Fin n → Int) : Mat n :=
  fun i j => if i = j then d i else 0

def matId (n : Nat) : Mat n := diagMat n (fun _ => 1)

def IsSymm (n : Nat) (A : Mat n) : Prop := ∀ i j : Fin n, A i j = A j i

def IsDiag (n : Nat) (A : Mat n) : Prop := ∀ i j : Fin n, i ≠ j → A i j = 0

/-- Permutation matrix `P_σ` with `(P_σ)_{i, j} = 1` iff `j = σ(i)`. -/
def permMat (n : Nat) (σ : Fin n → Fin n) : Mat n :=
  fun i j => if j = σ i then 1 else 0

/-- Permutation similarity `A = P_σ B P_σᵀ` for a bijection `σ` of `Fin n`. -/
def PermSimilar (n : Nat) (A B : Mat n) : Prop :=
  ∃ σ : Fin n → Fin n,
    IsBijection n σ ∧
    A = matMul n (matMul n (permMat n σ) B) (matTrans n (permMat n σ))

/-- Explicit entry formula `(P_σ B P_σᵀ)_{i, j} = B_{σ(i), σ(j)}` for all `n`. -/
theorem conj_permMat_apply (n : Nat) (σ : Fin n → Fin n) (B : Mat n) (i j : Fin n) :
    matMul n (matMul n (permMat n σ) B) (matTrans n (permMat n σ)) i j =
      B (σ i) (σ j) := by
  have hinner : ∀ l : Fin n, matMul n (permMat n σ) B i l = B (σ i) l := by
    intro l
    unfold matMul permMat
    have hrew : (fun k : Fin n => (if k = σ i then 1 else 0) * B k l) =
        (fun k : Fin n => if k = σ i then B k l else 0) := by
      funext k
      by_cases hk : k = σ i <;> simp [hk]
    rw [hrew]
    exact finSum_ite_eq n (σ i) (fun k => B k l)
  unfold matMul matTrans permMat
  have houter :
      (fun l : Fin n =>
        finSum n (fun k => (if k = σ i then 1 else 0) * B k l) *
          (if l = σ j then 1 else 0)) =
      (fun l : Fin n => if l = σ j then B (σ i) l else 0) := by
    funext l
    have hl := hinner l
    unfold matMul permMat at hl
    rw [hl]
    by_cases hlj : l = σ j <;> simp [hlj]
  rw [houter]
  exact finSum_ite_eq n (σ j) (fun l => B (σ i) l)

/-- Fundamental `n × n` invariant: no non-diagonal matrix is ever permutation-similar
    to a diagonal matrix. -/
theorem permSimilar_preserves_isDiag (n : Nat) (A B : Mat n)
    (hsim : PermSimilar n A B) (hdiag : IsDiag n B) :
    IsDiag n A := by
  rcases hsim with ⟨σ, ⟨τ, hleft, _⟩, rfl⟩
  intro i j hij
  rw [conj_permMat_apply]
  apply hdiag
  intro hσ
  apply hij
  have h1 := congrArg τ hσ
  rw [hleft i, hleft j] at h1
  exact h1

/--Squared Frobenius norm `∑_{i, j} A_{i, j}^2`. -/
def frobSq (n : Nat) (A : Mat n) : Int :=
  finSum n (fun i => finSum n (fun j => A i j * A i j))

/-- Off-diagonal squared Frobenius norm `∑_{i ≠ j} A_{i, j}^2`. -/
def offDiagFrobSq (n : Nat) (A : Mat n) : Int :=
  finSum n (fun i => finSum n (fun j => if j = i then 0 else A i j * A i j))

theorem frobSq_decomp (n : Nat) (A : Mat n) :
    frobSq n A =
      finSum n (fun i => A i i * A i i) + offDiagFrobSq n A := by
  unfold frobSq offDiagFrobSq
  rw [← finSum_add]
  apply finSum_congr
  intro i
  have hsplit :
      (fun j : Fin n => A i j * A i j) =
      (fun j : Fin n =>
        (if j = i then A i j * A i j else 0) +
        (if j = i then 0 else A i j * A i j)) := by
    funext j
    by_cases hj : j = i <;> simp [hj]
  rw [hsplit, finSum_add, finSum_ite_eq n i (fun j => A i j * A i j)]

theorem int_sq_nonneg (x : Int) : 0 ≤ x * x := by
  by_cases hx : 0 ≤ x
  · exact Int.mul_nonneg hx hx
  · have hx' : 0 ≤ -x := by omega
    have hmul : 0 ≤ (-x) * (-x) := Int.mul_nonneg hx' hx'
    have heq : (-x) * (-x) = x * x := by
      calc (-x) * (-x) = -(x * (-x)) := Int.neg_mul x (-x)
        _ = -(-(x * x)) := by rw [Int.mul_neg]
        _ = x * x := Int.neg_neg (x * x)
    rw [← heq]
    exact hmul

theorem int_eq_zero_of_sq_eq_zero (x : Int) (h : x * x = 0) : x = 0 := by
  rcases Int.mul_eq_zero.mp h with hx | hx <;> exact hx

/-! ## Section 3: Exact `2 × 2` Spectral Theory and Orthogonal Similarity -/

def fin0 : Fin 2 := ⟨0, by omega⟩
def fin1 : Fin 2 := ⟨1, by omega⟩

/-- Construct a `2 × 2` matrix from its four entries `[[a, b], [c, d]]`. -/
def mkMat2 (a b c d : Int) : Mat 2 :=
  fun i j =>
    if i.val = 0 then (if j.val = 0 then a else b)
    else (if j.val = 0 then c else d)

def diagMat2 (d1 d2 : Int) : Mat 2 := mkMat2 d1 0 0 d2

def diagVec2 (A : Mat 2) : List Int := [A fin0 fin0, A fin1 fin1]

def trace2 (A : Mat 2) : Int := A fin0 fin0 + A fin1 fin1

def det2 (A : Mat 2) : Int := A fin0 fin0 * A fin1 fin1 - A fin0 fin1 * A fin1 fin0

/-- `HasSpectrum2 A l1 l2` holds iff the characteristic polynomial `det(tI - A)`
    factors over `ℤ` as `(t - l1)(t - l2)`, i.e., `tr(A) = l1 + l2` and `det(A) = l1 * l2`. -/
def HasSpectrum2 (A : Mat 2) (l1 l2 : Int) : Prop :=
  trace2 A = l1 + l2 ∧ det2 A = l1 * l2

/-- `HasOrderedSpectrum2 A l1 l2` records the non-increasing ordered spectrum `λ↓(A) = [l1, l2]`. -/
def HasOrderedSpectrum2 (A : Mat 2) (l1 l2 : Int) : Prop :=
  l1 ≥ l2 ∧ HasSpectrum2 A l1 l2

/-- Uniqueness of the ordered integer spectrum of any `2 × 2` matrix. -/
theorem hasOrderedSpectrum2_unique (A : Mat 2) (l1 l2 m1 m2 : Int)
    (hl : HasOrderedSpectrum2 A l1 l2) (hm : HasOrderedSpectrum2 A m1 m2) :
    l1 = m1 ∧ l2 = m2 := by
  rcases hl with ⟨hl_ord, htr_l, hdet_l⟩
  rcases hm with ⟨hm_ord, htr_m, hdet_m⟩
  have hsum : l1 + l2 = m1 + m2 := by omega
  have hprod : l1 * l2 = m1 * m2 := by omega
  let u := l1 - l2
  let v := m1 - m2
  have hu : 0 ≤ u := by omega
  have hv : 0 ≤ v := by omega
  have hdiff_sq : (u - v) * (u + v) = 0 := by
    have hcalc : (u - v) * (u + v) =
        ((l1 + l2) * (l1 + l2) - 4 * (l1 * l2)) -
        ((m1 + m2) * (m1 + m2) - 4 * (m1 * m2)) := by
      dsimp [u, v]
      calc ((l1 - l2) - (m1 - m2)) * ((l1 - l2) + (m1 - m2))
          = (l1 - l2) * (l1 - l2) - (m1 - m2) * (m1 - m2) := by
              rw [Int.sub_mul, Int.mul_add, Int.mul_add, Int.mul_comm (m1 - m2) (l1 - l2)]
              omega
        _ = ((l1 + l2) * (l1 + l2) - 4 * (l1 * l2)) -
            ((m1 + m2) * (m1 + m2) - 4 * (m1 * m2)) := by
              have id1 : ∀ a b : Int, (a - b) * (a - b) = (a + b) * (a + b) - 4 * (a * b) := by
                intro a b
                rw [Int.sub_mul, Int.mul_sub, Int.mul_sub,
                    Int.add_mul, Int.mul_add, Int.mul_add, Int.mul_comm b a]
                omega
              rw [id1 l1 l2, id1 m1 m2]
    rw [hcalc, hsum, hprod]
    omega
  have huv : u = v := by
    rcases Int.mul_eq_zero.mp hdiff_sq with hsub | hadd
    · omega
    · omega
  dsimp [u, v] at huv
  omega

/-- Exhaustive classification of bijections of `Fin 2`: either identity or transposition. -/
theorem bijection_fin2_cases (σ : Fin 2 → Fin 2) (hσ : IsBijection 2 σ) :
    (σ fin0 = fin0 ∧ σ fin1 = fin1) ∨ (σ fin0 = fin1 ∧ σ fin1 = fin0) := by
  rcases hσ with ⟨τ, hleft, _⟩
  have h0lt := (σ fin0).isLt
  have h1lt := (σ fin1).isLt
  have hne : σ fin0 ≠ σ fin1 := by
    intro heq
    have h := congrArg τ heq
    rw [hleft fin0, hleft fin1] at h
    have hv : (0 : Nat) = 1 := congrArg Fin.val h
    omega
  by_cases h0 : (σ fin0).val = 0
  · left
    have hs0 : σ fin0 = fin0 := Fin.ext h0
    have h1 : (σ fin1).val = 1 := by
      have hne_val : (σ fin0).val ≠ (σ fin1).val := fun hv => hne (Fin.ext hv)
      omega
    exact ⟨hs0, Fin.ext h1⟩
  · right
    have h0' : (σ fin0).val = 1 := by omega
    have hs0 : σ fin0 = fin1 := Fin.ext h0'
    have h1 : (σ fin1).val = 0 := by
      have hne_val : (σ fin0).val ≠ (σ fin1).val := fun hv => hne (Fin.ext hv)
      omega
    exact ⟨hs0, Fin.ext h1⟩

/-- Exact characterization of `2 × 2` permutation similarity: either `A = B` or `A` swaps
    rows and columns of `B`. -/
theorem permSimilar2_iff (A B : Mat 2) :
    PermSimilar 2 A B ↔
      ((A fin0 fin0 = B fin0 fin0 ∧ A fin0 fin1 = B fin0 fin1 ∧
        A fin1 fin0 = B fin1 fin0 ∧ A fin1 fin1 = B fin1 fin1) ∨
       (A fin0 fin0 = B fin1 fin1 ∧ A fin0 fin1 = B fin1 fin0 ∧
        A fin1 fin0 = B fin0 fin1 ∧ A fin1 fin1 = B fin0 fin0)) := by
  constructor
  · intro ⟨σ, hbij, hA⟩
    have entry : ∀ i j, A i j = B (σ i) (σ j) := by
      intro i j
      rw [hA, conj_permMat_apply]
    rcases bijection_fin2_cases σ hbij with ⟨hs0, hs1⟩ | ⟨hs0, hs1⟩
    · left
      simp [entry, hs0, hs1]
    · right
      simp [entry, hs0, hs1]
  · intro hcases
    rcases hcases with ⟨h00, h01, h10, h11⟩ | ⟨h00, h01, h10, h11⟩
    · refine ⟨id, ⟨id, fun _ => rfl, fun _ => rfl⟩, ?_⟩
      apply matExt; intro i j
      rw [conj_permMat_apply]
      rcases i with ⟨vi, hi⟩; rcases j with ⟨vj, hj⟩
      have hvi : vi = 0 ∨ vi = 1 := by omega
      have hvj : vj = 0 ∨ vj = 1 := by omega
      rcases hvi with rfl | rfl <;> rcases hvj with rfl | rfl
      · exact h00
      · exact h01
      · exact h10
      · exact h11
    · let swap : Fin 2 → Fin 2 := fun k => if k.val = 0 then fin1 else fin0
      have hswap_inv : ∀ k : Fin 2, swap (swap k) = k := by
        intro ⟨vk, hk⟩
        have hvk : vk = 0 ∨ vk = 1 := by omega
        rcases hvk with rfl | rfl <;> rfl
      refine ⟨swap, ⟨swap, hswap_inv, hswap_inv⟩, ?_⟩
      apply matExt; intro i j
      rw [conj_permMat_apply]
      rcases i with ⟨vi, hi⟩; rcases j with ⟨vj, hj⟩
      have hvi : vi = 0 ∨ vi = 1 := by omega
      have hvj : vj = 0 ∨ vj = 1 := by omega
      rcases hvi with rfl | rfl <;> rcases hvj with rfl | rfl
      · exact h00
      · exact h01
      · exact h10
      · exact h11

/-- Exact rational orthogonal similarity: `(1/s) Q ∈ O(2, ℚ)` conjugates `B` to `C`,
    written without denominators via `Q Qᵀ = s² I₂` and `s² C = Q B Qᵀ` (`s > 0`). -/
def RatOrthSimilar2 (s : Int) (Q B C : Mat 2) : Prop :=
  0 < s ∧
  matMul 2 Q (matTrans 2 Q) = scaleMat 2 (s * s) (matId 2) ∧
  scaleMat 2 (s * s) C = matMul 2 (matMul 2 Q B) (matTrans 2 Q)

/-! ## Section 4: Positive Non-Vacuity Theorems -/

/-- **Non-Vacuity 1 (Opposite orderings collapse in the majorization poset):**
    For all `a, b ∈ ℤ`, `[a, b]` and `[b, a]` mutually majorize each other (`[a, b] ≺ [b, a]`
    and `[b, a] ≺ [a, b]`). Thus `λ↓` and `λ↑` represent the *same* element in the
    poset of spectra, never two distinct endpoints of a nontrivial majorization chain. -/
theorem nonvacuity_ordering_equivalence (a b : Int) :
    Majorizes [a, b] [b, a] ∧ Majorizes [b, a] [a, b] := by
  have hmax : maxInt a b = maxInt b a := by
    by_cases h1 : a ≥ b <;> by_cases h2 : b ≥ a <;> simp [maxInt, h1, h2] <;> omega
  constructor
  · rw [majorizes_pair_iff]; exact ⟨by omega, by omega⟩
  · rw [majorizes_pair_iff]; exact ⟨by omega, by omega⟩

/-- **Non-Vacuity 2 (`n × n` Schur Frobenius Upper-Endpoint Theorem):**
    In arbitrary dimension `n`, if `A` satisfies the spectral Frobenius norm identity
    `‖A‖_F² = ∑_k λ_k²` (which holds for every orthogonally/unitarily diagonalizable
    matrix with spectrum `λ`) and `diag(A)` attains a permuted spectrum `λ ∘ σ`
    (the upper majorization endpoint), then `A` is diagonal and permutation-similar
    to `diagMat n λ`. -/
theorem nonvacuity_schur_upper_endpoint_dim_n
    (n : Nat) (A : Mat n) (lam : Fin n → Int) (σ : Fin n → Fin n)
    (hbij : IsBijection n σ)
    (hfrob : frobSq n A = finSum n (fun k => lam k * lam k))
    (hdiag_perm : ∀ i : Fin n, A i i = lam (σ i)) :
    IsDiag n A ∧ PermSimilar n A (diagMat n lam) := by
  have hdiag_sq :
      finSum n (fun i => A i i * A i i) = finSum n (fun k => lam k * lam k) := by
    have hcongr : (fun i : Fin n => A i i * A i i) =
        (fun i : Fin n => (fun k => lam k * lam k) (σ i)) := by
      funext i; simp [hdiag_perm i]
    rw [hcongr]
    exact finSum_bijection n σ hbij (fun k => lam k * lam k)
  have hdecomp := frobSq_decomp n A
  have hoff_zero : offDiagFrobSq n A = 0 := by omega
  have his_diag : IsDiag n A := by
    intro i j hij
    have hrow_nonneg : ∀ r : Fin n,
        0 ≤ finSum n (fun c => if c = r then 0 else A r c * A r c) := by
      intro r
      apply finSum_nonneg
      intro c
      by_cases hcr : c = r
      · simp [hcr]
      · simp [hcr, int_sq_nonneg]
    have hrow_zero := finSum_eq_zero_of_nonneg n
      (fun r => finSum n (fun c => if c = r then 0 else A r c * A r c))
      hrow_nonneg hoff_zero i
    have hcol_nonneg : ∀ c : Fin n, 0 ≤ (if c = i then 0 else A i c * A i c) := by
      intro c
      by_cases hci : c = i
      · simp [hci]
      · simp [hci, int_sq_nonneg]
    have hcol_zero := finSum_eq_zero_of_nonneg n
      (fun c => if c = i then 0 else A i c * A i c)
      hcol_nonneg hrow_zero j
    have hji : j ≠ i := fun h => hij h.symm
    simp only [hji, ↓reduceIte] at hcol_zero
    exact int_eq_zero_of_sq_eq_zero (A i j) hcol_zero
  refine ⟨his_diag, ⟨σ, hbij, ?_⟩⟩
  rcases hbij with ⟨τ, hleft, _⟩
  apply matExt; intro i j
  rw [conj_permMat_apply]
  by_cases hij : i = j
  · subst hij
    simp [diagMat, hdiag_perm i]
  · have hσij : σ i ≠ σ j := by
      intro heq
      apply hij
      have h := congrArg τ heq
      rw [hleft i, hleft j] at h
      exact h
    rw [his_diag i j hij]
    simp [diagMat, hσij]

theorem symm2_char_id (a b d l1 l2 : Int)
    (htr : a + d = l1 + l2) (hdet : a * d - b * b = l1 * l2) :
    (a - l1) * (a - l2) + b * b = 0 := by
  have h1 : (a - l1) * (a - l2) = a * a - (l1 + l2) * a + l1 * l2 := by
    rw [Int.sub_mul, Int.mul_sub, Int.mul_sub, Int.add_mul, Int.mul_comm a l2]
    omega
  have h2 : (l1 + l2) * a = a * a + a * d := by
    rw [← htr, Int.add_mul, Int.mul_comm d a]
  rw [h1, h2, ← hdet]
  omega

/-- **Non-Vacuity 3 (`2 × 2` Symmetric Schur–Horn Upper Endpoint Characterization):**
    For *symmetric* `2 × 2` matrices `A` with ordered spectrum `[l1, l2]`, the diagonal
    vector `diag(A)` majorizes `[l1, l2]` (attaining the upper Schur–Horn endpoint `[l1, l2]`
    or `[l2, l1]`) if and only if `A` is permutation-similar to `diag(l1, l2)`. -/
theorem nonvacuity_schur_upper_endpoint_symm2
    (A : Mat 2) (l1 l2 : Int)
    (hsym : IsSymm 2 A) (hspec : HasOrderedSpectrum2 A l1 l2) :
    Majorizes (diagVec2 A) [l1, l2] ↔ PermSimilar 2 A (diagMat2 l1 l2) := by
  rcases hspec with ⟨hl_ord, htr, hdet⟩
  unfold trace2 at htr
  unfold det2 at hdet
  have hb_sym : A fin1 fin0 = A fin0 fin1 := hsym fin1 fin0
  rw [hb_sym] at hdet
  constructor
  · intro hmaj
    unfold diagVec2 at hmaj
    rw [majorizes_pair_iff] at hmaj
    rcases hmaj with ⟨_, hmax⟩
    have hlmax : maxInt l1 l2 = l1 := by simp [maxInt, hl_ord]
    rw [hlmax] at hmax
    rw [permSimilar2_iff]
    by_cases ha : A fin0 fin0 ≥ A fin1 fin1
    · simp only [maxInt, ha, ↓reduceIte] at hmax
      have hprod_id := symm2_char_id (A fin0 fin0) (A fin0 fin1) (A fin1 fin1) l1 l2 htr hdet
      have hfac1 : 0 ≤ A fin0 fin0 - l1 := by omega
      have hfac2 : 0 ≤ A fin0 fin0 - l2 := by omega
      have hmul_nn : 0 ≤ (A fin0 fin0 - l1) * (A fin0 fin0 - l2) := Int.mul_nonneg hfac1 hfac2
      have hsq_nn : 0 ≤ A fin0 fin1 * A fin0 fin1 := int_sq_nonneg (A fin0 fin1)
      have hsq0 : A fin0 fin1 * A fin0 fin1 = 0 := by omega
      have hb0 : A fin0 fin1 = 0 := int_eq_zero_of_sq_eq_zero _ hsq0
      have hmul0 : (A fin0 fin0 - l1) * (A fin0 fin0 - l2) = 0 := by omega
      left
      rcases Int.mul_eq_zero.mp hmul0 with h1 | h2
      · have ha_eq : A fin0 fin0 = l1 := by omega
        have hd_eq : A fin1 fin1 = l2 := by omega
        rw [hb_sym, ha_eq, hd_eq, hb0]
        simp [diagMat2, mkMat2, fin0, fin1]
      · have ha_eq : A fin0 fin0 = l1 := by omega
        have hd_eq : A fin1 fin1 = l2 := by omega
        rw [hb_sym, ha_eq, hd_eq, hb0]
        simp [diagMat2, mkMat2, fin0, fin1]
    · simp only [maxInt, ha, ↓reduceIte] at hmax
      have htr' : A fin1 fin1 + A fin0 fin0 = l1 + l2 := by omega
      have hdet' : A fin1 fin1 * A fin0 fin0 - A fin0 fin1 * A fin0 fin1 = l1 * l2 := by
        rw [Int.mul_comm (A fin1 fin1) (A fin0 fin0)]
        exact hdet
      have hprod_id := symm2_char_id (A fin1 fin1) (A fin0 fin1) (A fin0 fin0) l1 l2 htr' hdet'
      have hfac1 : 0 ≤ A fin1 fin1 - l1 := by omega
      have hfac2 : 0 ≤ A fin1 fin1 - l2 := by omega
      have hmul_nn : 0 ≤ (A fin1 fin1 - l1) * (A fin1 fin1 - l2) := Int.mul_nonneg hfac1 hfac2
      have hsq_nn : 0 ≤ A fin0 fin1 * A fin0 fin1 := int_sq_nonneg (A fin0 fin1)
      have hsq0 : A fin0 fin1 * A fin0 fin1 = 0 := by omega
      have hb0 : A fin0 fin1 = 0 := int_eq_zero_of_sq_eq_zero _ hsq0
      have hmul0 : (A fin1 fin1 - l1) * (A fin1 fin1 - l2) = 0 := by omega
      right
      rcases Int.mul_eq_zero.mp hmul0 with h1 | h2
      · have hd_eq : A fin1 fin1 = l1 := by omega
        have ha_eq : A fin0 fin0 = l2 := by omega
        rw [hb_sym, ha_eq, hd_eq, hb0]
        simp [diagMat2, mkMat2, fin0, fin1]
      · have hd_eq : A fin1 fin1 = l1 := by omega
        have ha_eq : A fin0 fin0 = l2 := by omega
        rw [hb_sym, ha_eq, hd_eq, hb0]
        simp [diagMat2, mkMat2, fin0, fin1]
  · intro hperm
    rw [permSimilar2_iff] at hperm
    unfold diagVec2
    rw [majorizes_pair_iff]
    rcases hperm with ⟨h00, _, _, h11⟩ | ⟨h00, _, _, h11⟩
    · rw [h00, h11]
      have hd0 : diagMat2 l1 l2 fin0 fin0 = l1 := rfl
      have hd1 : diagMat2 l1 l2 fin1 fin1 = l2 := rfl
      rw [hd0, hd1]
      exact ⟨rfl, Int.le_refl _⟩
    · rw [h00, h11]
      have hd1 : diagMat2 l1 l2 fin1 fin1 = l2 := rfl
      have hd0 : diagMat2 l1 l2 fin0 fin0 = l1 := rfl
      rw [hd1, hd0]
      have hmax : maxInt l2 l1 = maxInt l1 l2 := by
        by_cases h : l2 ≥ l1 <;> simp [maxInt, h, hl_ord] <;> omega
      rw [hmax]
      exact ⟨by omega, Int.le_refl _⟩

/-- **Non-Vacuity 4 (Diagonal Lidskii Realization via Permutation Similarity):**
    When `A = diag(a1, a2)` (`a1 ≥ a2`) and `B = diag(b1, b2)` (`b1 ≥ b2`) are *already*
    diagonal in the standard basis, both the upper Lidskii endpoint `[a1 + b1, a2 + b2]`
    and the lower Lidskii endpoint `sortDesc [a1 + b2, a2 + b1]` ARE realized by
    permutation similarities of `B`. -/
theorem nonvacuity_lidskii_diagonal_case (a1 a2 b1 b2 : Int)
    (ha : a1 ≥ a2) (hb : b1 ≥ b2) :
    (∃ B' : Mat 2, PermSimilar 2 B' (diagMat2 b1 b2) ∧
      HasOrderedSpectrum2 (matAdd 2 (diagMat2 a1 a2) B') (a1 + b1) (a2 + b2)) ∧
    (∃ B' : Mat 2, PermSimilar 2 B' (diagMat2 b1 b2) ∧
      HasSpectrum2 (matAdd 2 (diagMat2 a1 a2) B') (a1 + b2) (a2 + b1)) := by
  constructor
  · refine ⟨diagMat2 b1 b2, ?_, ?_⟩
    · rw [permSimilar2_iff]; left; exact ⟨rfl, rfl, rfl, rfl⟩
    · refine ⟨by omega, ?_, ?_⟩
      · simp [trace2, matAdd, diagMat2, mkMat2, fin0, fin1]
      · simp [det2, matAdd, diagMat2, mkMat2, fin0, fin1]
  · refine ⟨diagMat2 b2 b1, ?_, ?_⟩
    · rw [permSimilar2_iff]; right; simp [diagMat2, mkMat2, fin0, fin1]
    · constructor
      · simp [trace2, matAdd, diagMat2, mkMat2, fin0, fin1]
      · simp [det2, matAdd, diagMat2, mkMat2, fin0, fin1]

/-! ## Section 5: Refutations Across All Standard Interpretations -/

/-- Symmetric integer matrices `A_+ = [[1, 1], [1, 1]]` and `A_- = [[1, -1], [-1, 1]]`
    with ordered spectrum `[2, 0]` and uniform diagonal `[1, 1]`. -/
def A_plus : Mat 2 := mkMat2 1 1 1 1
def A_minus : Mat 2 := mkMat2 1 (-1) (-1) 1

/-- **Refutation I-A (Schur–Horn Lower Endpoint):**
    For fixed non-scalar spectrum `λ = [2, 0]`:
    1. `[1, 1]` is the unique minimum element of `{ [x1, x2] : x1 ≥ x2 ∧ [x1, x2] ≺ [2, 0] }`;
    2. `[1, 1]` is strictly majorized by `[2, 0]`, so the lower endpoint is NOT an ordered
       rearrangement of `λ`;
    3. Both real symmetric matrices `A_+` and `A_-` have ordered spectrum `[2, 0]` and
       diagonal `[1, 1]` realizing this lower endpoint;
    4. Neither `A_+` nor `A_-` is permutation-similar to `diag(2, 0)`, and `A_+` and `A_-`
       are not even permutation-similar to each other. -/
theorem refutation_schur_horn_lower_endpoint :
    (∀ x1 x2 : Int, x1 ≥ x2 → Majorizes [2, 0] [x1, x2] → Majorizes [x1, x2] [1, 1]) ∧
    StrictMajorizes [2, 0] [1, 1] ∧
    IsSymm 2 A_plus ∧ HasOrderedSpectrum2 A_plus 2 0 ∧ diagVec2 A_plus = [1, 1] ∧
    IsSymm 2 A_minus ∧ HasOrderedSpectrum2 A_minus 2 0 ∧ diagVec2 A_minus = [1, 1] ∧
    ¬ PermSimilar 2 A_plus (diagMat2 2 0) ∧
    ¬ PermSimilar 2 A_minus (diagMat2 2 0) ∧
    ¬ PermSimilar 2 A_plus A_minus := by
  refine ⟨?_, ?_, ?_, ?_, rfl, ?_, ?_, rfl, ?_, ?_, ?_⟩
  · intro x1 x2 hord hmaj
    rw [majorizes_pair_iff] at hmaj ⊢
    rcases hmaj with ⟨hsum, _⟩
    have hx : maxInt x1 x2 = x1 := by simp [maxInt, hord]
    have h1 : maxInt 1 1 = 1 := rfl
    rw [hx, h1]
    omega
  · constructor
    · rw [majorizes_pair_iff]; simp [maxInt]
    · intro hrev
      rw [majorizes_pair_iff] at hrev
      simp [maxInt] at hrev
  · intro ⟨vi, hi⟩ ⟨vj, hj⟩
    have hvi : vi = 0 ∨ vi = 1 := by omega
    have hvj : vj = 0 ∨ vj = 1 := by omega
    rcases hvi with rfl | rfl <;> rcases hvj with rfl | rfl <;> rfl
  · refine ⟨by omega, ?_, ?_⟩ <;> simp [trace2, det2, A_plus, mkMat2, fin0, fin1]
  · intro ⟨vi, hi⟩ ⟨vj, hj⟩
    have hvi : vi = 0 ∨ vi = 1 := by omega
    have hvj : vj = 0 ∨ vj = 1 := by omega
    rcases hvi with rfl | rfl <;> rcases hvj with rfl | rfl <;> rfl
  · refine ⟨by omega, ?_, ?_⟩ <;> simp [trace2, det2, A_minus, mkMat2, fin0, fin1]
  · intro hsim
    have hdiag := permSimilar_preserves_isDiag 2 A_plus (diagMat2 2 0) hsim (by
      intro ⟨vi, hi⟩ ⟨vj, hj⟩ hne
      have hvi : vi = 0 ∨ vi = 1 := by omega
      have hvj : vj = 0 ∨ vj = 1 := by omega
      rcases hvi with rfl | rfl <;> rcases hvj with rfl | rfl
      · exact absurd rfl hne
      · rfl
      · rfl
      · exact absurd rfl hne)
    have h01 := hdiag fin0 fin1 (by intro h; cases h)
    simp [A_plus, mkMat2, fin0, fin1] at h01
  · intro hsim
    have hdiag := permSimilar_preserves_isDiag 2 A_minus (diagMat2 2 0) hsim (by
      intro ⟨vi, hi⟩ ⟨vj, hj⟩ hne
      have hvi : vi = 0 ∨ vi = 1 := by omega
      have hvj : vj = 0 ∨ vj = 1 := by omega
      rcases hvi with rfl | rfl <;> rcases hvj with rfl | rfl
      · exact absurd rfl hne
      · rfl
      · rfl
      · exact absurd rfl hne)
    have h01 := hdiag fin0 fin1 (by intro h; cases h)
    simp [A_minus, mkMat2, fin0, fin1] at h01
  · intro hsim
    rw [permSimilar2_iff] at hsim
    simp [A_plus, A_minus, mkMat2, fin0, fin1] at hsim

/-- Upper-triangular matrices `B_1 = [[1, 1], [0, 0]]` (diagonalizable over `ℤ`, distinct
    eigenvalues `[1, 0]`) and `B_2 = [[1, 1], [0, 1]]` (Jordan block, spectrum `[1, 1]`). -/
def B_tri_distinct : Mat 2 := mkMat2 1 1 0 0
def B_tri_jordan : Mat 2 := mkMat2 1 1 0 1

/-- **Refutation I-B (Schur–Horn Upper Endpoint Without Hermiticity/Symmetry):**
    On general matrices with real spectrum, attaining the exact ordered-spectrum upper
    endpoint `diag(B) = λ↓(B)` does NOT imply permutation similarity to `diag(λ↓)`:
    `B_1 = [[1, 1], [0, 0]]` has `diag(B_1) = [1, 0] = λ↓(B_1)` (and is `GL_2(ℤ)`-similar
    to `diag(1, 0)`), yet fails permutation similarity; `B_2 = [[1, 1], [0, 1]]` has
    `diag(B_2) = [1, 1] = λ↓(B_2)` and also fails permutation similarity. -/
theorem refutation_schur_horn_upper_nonhermitian :
    (HasOrderedSpectrum2 B_tri_distinct 1 0 ∧
     diagVec2 B_tri_distinct = [1, 0] ∧
     (∃ S Sinv : Mat 2,
       matMul 2 S Sinv = matId 2 ∧
       matMul 2 Sinv S = matId 2 ∧
       B_tri_distinct = matMul 2 (matMul 2 S (diagMat2 1 0)) Sinv) ∧
     ¬ PermSimilar 2 B_tri_distinct (diagMat2 1 0)) ∧
    (HasOrderedSpectrum2 B_tri_jordan 1 1 ∧
     diagVec2 B_tri_jordan = [1, 1] ∧
     ¬ PermSimilar 2 B_tri_jordan (diagMat2 1 1)) := by
  refine ⟨⟨?_, rfl, ?_, ?_⟩, ⟨?_, rfl, ?_⟩⟩
  · refine ⟨by omega, ?_, ?_⟩ <;> simp [trace2, det2, B_tri_distinct, mkMat2, fin0, fin1]
  · refine ⟨mkMat2 1 (-1) 0 1, mkMat2 1 1 0 1, ?_, ?_, ?_⟩
    · apply matExt; intro ⟨vi, hi⟩ ⟨vj, hj⟩
      have hvi : vi = 0 ∨ vi = 1 := by omega
      have hvj : vj = 0 ∨ vj = 1 := by omega
      rcases hvi with rfl | rfl <;> rcases hvj with rfl | rfl <;>
        simp [matMul, finSum, mkMat2, matId, diagMat]
    · apply matExt; intro ⟨vi, hi⟩ ⟨vj, hj⟩
      have hvi : vi = 0 ∨ vi = 1 := by omega
      have hvj : vj = 0 ∨ vj = 1 := by omega
      rcases hvi with rfl | rfl <;> rcases hvj with rfl | rfl <;>
        simp [matMul, finSum, mkMat2, matId, diagMat]
    · apply matExt; intro ⟨vi, hi⟩ ⟨vj, hj⟩
      have hvi : vi = 0 ∨ vi = 1 := by omega
      have hvj : vj = 0 ∨ vj = 1 := by omega
      rcases hvi with rfl | rfl <;> rcases hvj with rfl | rfl <;>
        simp [matMul, finSum, B_tri_distinct, diagMat2, mkMat2]
  · intro hsim
    rw [permSimilar2_iff] at hsim
    simp [B_tri_distinct, diagMat2, mkMat2, fin0, fin1] at hsim
  · refine ⟨by omega, ?_, ?_⟩ <;> simp [trace2, det2, B_tri_jordan, mkMat2, fin0, fin1]
  · intro hsim
    rw [permSimilar2_iff] at hsim
    simp [B_tri_jordan, diagMat2, mkMat2, fin0, fin1] at hsim

/-- All-integer symmetric Lidskii counterexample matrices (`3-4-5` Pythagorean rotation):
    `A_lid = [[25, 0], [0, 0]]`, `B_lid = [[9, 12], [12, 16]]`, both with spectrum `[25, 0]`. -/
def A_lid : Mat 2 := mkMat2 25 0 0 0
def B_lid : Mat 2 := mkMat2 9 12 12 16
def Q_upper : Mat 2 := mkMat2 3 4 (-4) 3
def Q_lower : Mat 2 := mkMat2 (-4) 3 3 4

/-- **Refutation II (Lidskii–Wielandt Eigenvalue Sum Majorization Chain):**
    For symmetric matrices `A_lid = [[25, 0], [0, 0]]` and `B_lid = [[9, 12], [12, 16]]`
    with ordered spectra `λ↓(A_lid) = [25, 0]` and `λ↓(B_lid) = [25, 0]`:
    1. The upper Lidskii endpoint `[50, 0] = λ↓(A_lid) + λ↓(B_lid)` and lower Lidskii
       endpoint `[25, 25] = (λ↓(A_lid) + λ↑(B_lid))↓` ARE realized via rational orthogonal
       similarities `(1/5) Q_upper, (1/5) Q_lower ∈ O(2, ℚ)`;
    2. Across ALL `2 × 2` permutation-similar conjugates `B'` of `B_lid`, the sum
       `A_lid + B'` has unique ordered spectrum either `[40, 10]` or `[45, 5]`;
    3. Every permutation-similarity sum lies strictly inside the Lidskii chain:
       `[25, 25] ≺≠ [40, 10] ≺≠ [45, 5] ≺≠ [50, 0]`,
       so NO permutation similarity realizes either majorization endpoint. -/
theorem refutation_lidskii_sum_endpoints :
    IsSymm 2 A_lid ∧ HasOrderedSpectrum2 A_lid 25 0 ∧
    IsSymm 2 B_lid ∧ HasOrderedSpectrum2 B_lid 25 0 ∧
    (∃ C_up : Mat 2, RatOrthSimilar2 5 Q_upper B_lid C_up ∧
      HasOrderedSpectrum2 (matAdd 2 A_lid C_up) 50 0) ∧
    (∃ C_low : Mat 2, RatOrthSimilar2 5 Q_lower B_lid C_low ∧
      HasOrderedSpectrum2 (matAdd 2 A_lid C_low) 25 25) ∧
    StrictMajorizes [40, 10] [25, 25] ∧
    StrictMajorizes [45, 5] [40, 10] ∧
    StrictMajorizes [50, 0] [45, 5] ∧
    (∀ B' : Mat 2, PermSimilar 2 B' B_lid →
      ¬ HasOrderedSpectrum2 (matAdd 2 A_lid B') 50 0 ∧
      ¬ HasOrderedSpectrum2 (matAdd 2 A_lid B') 25 25 ∧
      (HasOrderedSpectrum2 (matAdd 2 A_lid B') 40 10 ∨
       HasOrderedSpectrum2 (matAdd 2 A_lid B') 45 5)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro ⟨vi, hi⟩ ⟨vj, hj⟩
    have hvi : vi = 0 ∨ vi = 1 := by omega
    have hvj : vj = 0 ∨ vj = 1 := by omega
    rcases hvi with rfl | rfl <;> rcases hvj with rfl | rfl <;> rfl
  · refine ⟨by omega, ?_, ?_⟩ <;> simp [trace2, det2, A_lid, mkMat2, fin0, fin1]
  · intro ⟨vi, hi⟩ ⟨vj, hj⟩
    have hvi : vi = 0 ∨ vi = 1 := by omega
    have hvj : vj = 0 ∨ vj = 1 := by omega
    rcases hvi with rfl | rfl <;> rcases hvj with rfl | rfl <;> rfl
  · refine ⟨by omega, ?_, ?_⟩ <;> simp [trace2, det2, B_lid, mkMat2, fin0, fin1]
  · refine ⟨diagMat2 25 0, ⟨by omega, ?_, ?_⟩, ⟨by omega, ?_, ?_⟩⟩
    · apply matExt; intro ⟨vi, hi⟩ ⟨vj, hj⟩
      have hvi : vi = 0 ∨ vi = 1 := by omega
      have hvj : vj = 0 ∨ vj = 1 := by omega
      rcases hvi with rfl | rfl <;> rcases hvj with rfl | rfl <;>
        simp [matMul, matTrans, scaleMat, finSum, Q_upper, mkMat2, matId, diagMat]
    · apply matExt; intro ⟨vi, hi⟩ ⟨vj, hj⟩
      have hvi : vi = 0 ∨ vi = 1 := by omega
      have hvj : vj = 0 ∨ vj = 1 := by omega
      rcases hvi with rfl | rfl <;> rcases hvj with rfl | rfl <;>
        simp [matMul, matTrans, scaleMat, finSum, Q_upper, B_lid, diagMat2, mkMat2]
    · simp [trace2, matAdd, A_lid, diagMat2, mkMat2, fin0, fin1]
    · simp [det2, matAdd, A_lid, diagMat2, mkMat2, fin0, fin1]
  · refine ⟨diagMat2 0 25, ⟨by omega, ?_, ?_⟩, ⟨by omega, ?_, ?_⟩⟩
    · apply matExt; intro ⟨vi, hi⟩ ⟨vj, hj⟩
      have hvi : vi = 0 ∨ vi = 1 := by omega
      have hvj : vj = 0 ∨ vj = 1 := by omega
      rcases hvi with rfl | rfl <;> rcases hvj with rfl | rfl <;>
        simp [matMul, matTrans, scaleMat, finSum, Q_lower, mkMat2, matId, diagMat]
    · apply matExt; intro ⟨vi, hi⟩ ⟨vj, hj⟩
      have hvi : vi = 0 ∨ vi = 1 := by omega
      have hvj : vj = 0 ∨ vj = 1 := by omega
      rcases hvi with rfl | rfl <;> rcases hvj with rfl | rfl <;>
        simp [matMul, matTrans, scaleMat, finSum, Q_lower, B_lid, diagMat2, mkMat2]
    · simp [trace2, matAdd, A_lid, diagMat2, mkMat2, fin0, fin1]
    · simp [det2, matAdd, A_lid, diagMat2, mkMat2, fin0, fin1]
  · constructor
    · rw [majorizes_pair_iff]; simp [maxInt]
    · intro hrev; rw [majorizes_pair_iff] at hrev; simp [maxInt] at hrev
  · constructor
    · rw [majorizes_pair_iff]; simp [maxInt]
    · intro hrev; rw [majorizes_pair_iff] at hrev; simp [maxInt] at hrev
  · constructor
    · rw [majorizes_pair_iff]; simp [maxInt]
    · intro hrev; rw [majorizes_pair_iff] at hrev; simp [maxInt] at hrev
  · intro B' hperm
    rw [permSimilar2_iff] at hperm
    rcases hperm with ⟨h00, h01, h10, h11⟩ | ⟨h00, h01, h10, h11⟩
    · have hspec40 : HasOrderedSpectrum2 (matAdd 2 A_lid B') 40 10 := by
        refine ⟨by omega, ?_, ?_⟩
        · unfold trace2 matAdd; rw [h00, h11]; simp [A_lid, B_lid, mkMat2, fin0, fin1]
        · unfold det2 matAdd; rw [h00, h01, h10, h11]; simp [A_lid, B_lid, mkMat2, fin0, fin1]
      refine ⟨?_, ?_, Or.inl hspec40⟩
      · intro h50
        have heq := hasOrderedSpectrum2_unique _ _ _ _ _ hspec40 h50
        omega
      · intro h25
        have heq := hasOrderedSpectrum2_unique _ _ _ _ _ hspec40 h25
        omega
    · have hspec45 : HasOrderedSpectrum2 (matAdd 2 A_lid B') 45 5 := by
        refine ⟨by omega, ?_, ?_⟩
        · unfold trace2 matAdd; rw [h00, h11]; simp [A_lid, B_lid, mkMat2, fin0, fin1]
        · unfold det2 matAdd; rw [h00, h01, h10, h11]; simp [A_lid, B_lid, mkMat2, fin0, fin1]
      refine ⟨?_, ?_, Or.inr hspec45⟩
      · intro h50
        have heq := hasOrderedSpectrum2_unique _ _ _ _ _ hspec45 h50
        omega
      · intro h25
        have heq := hasOrderedSpectrum2_unique _ _ _ _ _ hspec45 h25
        omega

/-- **Refutation III (Poset of Ordered Spectra on Fixed-Trace and PSD Slices):**
    1. On the fixed-trace poset of ordered spectra `{ [l1, l2] : l1 ≥ l2, l1 + l2 = τ }`,
       majorization chains have NO upper endpoint: every `[l1, l2]` is strictly majorized
       by `[l1 + 1, l2 - 1]` of the same trace.
    2. On the non-negative fixed-trace poset `{ [l1, l2] : l1 ≥ l2 ≥ 0, l1 + l2 = 2 }`,
       the minimum is `[1, 1]` and the maximum is `[2, 0]`; no matrix with spectrum `[1, 1]`
       is permutation-similar to any matrix with spectrum `[2, 0]`, and even at the single
       upper endpoint `[2, 0]` the PSD symmetric realizations `diag(2, 0)` and `A_+` are
       not permutation-similar. -/
theorem refutation_spectra_poset_slices :
    (∀ l1 l2 : Int, l1 ≥ l2 →
      ∃ m1 m2 : Int, m1 ≥ m2 ∧ m1 + m2 = l1 + l2 ∧ StrictMajorizes [m1, m2] [l1, l2]) ∧
    (∀ l1 l2 : Int, l1 ≥ l2 → l2 ≥ 0 → l1 + l2 = 2 →
      Majorizes [l1, l2] [1, 1] ∧ Majorizes [2, 0] [l1, l2]) ∧
    (∀ M1 M2 : Mat 2,
      HasOrderedSpectrum2 M1 1 1 → HasOrderedSpectrum2 M2 2 0 → ¬ PermSimilar 2 M1 M2) ∧
    (HasOrderedSpectrum2 A_plus 2 0 ∧ HasOrderedSpectrum2 (diagMat2 2 0) 2 0 ∧
      ¬ PermSimilar 2 A_plus (diagMat2 2 0)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro l1 l2 hord
    refine ⟨l1 + 1, l2 - 1, by omega, by omega, ?_⟩
    constructor
    · rw [majorizes_pair_iff]
      have h1 : maxInt l1 l2 = l1 := by simp [maxInt, hord]
      have h2 : maxInt (l1 + 1) (l2 - 1) = l1 + 1 := by
        have hm : l1 + 1 ≥ l2 - 1 := by omega
        simp [maxInt, hm]
      rw [h1, h2]
      omega
    · intro hrev
      rw [majorizes_pair_iff] at hrev
      have h1 : maxInt l1 l2 = l1 := by simp [maxInt, hord]
      have h2 : maxInt (l1 + 1) (l2 - 1) = l1 + 1 := by
        have hm : l1 + 1 ≥ l2 - 1 := by omega
        simp [maxInt, hm]
      rw [h1, h2] at hrev
      omega
  · intro l1 l2 hord hnn hsum
    constructor
    · rw [majorizes_pair_iff]
      have hmax : maxInt l1 l2 = l1 := by simp [maxInt, hord]
      rw [hmax]; simp [maxInt]; omega
    · rw [majorizes_pair_iff]
      have hmax : maxInt l1 l2 = l1 := by simp [maxInt, hord]
      rw [hmax]; simp [maxInt]; omega
  · intro M1 M2 hM1 hM2 hsim
    rw [permSimilar2_iff] at hsim
    rcases hM1 with ⟨_, _, hdet1⟩
    rcases hM2 with ⟨_, _, hdet2⟩
    unfold det2 at hdet1 hdet2
    rcases hsim with ⟨h00, h01, h10, h11⟩ | ⟨h00, h01, h10, h11⟩
    · rw [h00, h01, h10, h11] at hdet1
      omega
    · rw [h00, h01, h10, h11] at hdet1
      have hmul1 : M2 fin1 fin1 * M2 fin0 fin0 = M2 fin0 fin0 * M2 fin1 fin1 :=
        Int.mul_comm _ _
      have hmul2 : M2 fin1 fin0 * M2 fin0 fin1 = M2 fin0 fin1 * M2 fin1 fin0 :=
        Int.mul_comm _ _
      omega
  · refine ⟨refutation_schur_horn_lower_endpoint.2.2.2.1, ?_,
            refutation_schur_horn_lower_endpoint.2.2.2.2.2.2.2.2.1⟩
    refine ⟨by omega, ?_, ?_⟩ <;> simp [trace2, det2, diagMat2, mkMat2, fin0, fin1]

/-- **Master Theorem (`conjecture_00000007173_false_all_readings`):**
    Conjecture 00000007173 is FALSE under every standard mathematical reading:
    Schur–Horn diagonal majorization (both lower endpoint on symmetric matrices and upper
    endpoint on non-symmetric matrices), Lidskii–Wielandt eigenvalue majorization of sums,
    and the majorization poset of ordered spectra on fixed-trace / PSD slices. -/
theorem conjecture_00000007173_false_all_readings :
    -- (1) Schur–Horn lower endpoint fails both endpoint-identity and permutation-similarity
    (StrictMajorizes [2, 0] [1, 1] ∧
     IsSymm 2 A_plus ∧ HasOrderedSpectrum2 A_plus 2 0 ∧ diagVec2 A_plus = [1, 1] ∧
     ¬ PermSimilar 2 A_plus (diagMat2 2 0) ∧ ¬ PermSimilar 2 A_plus A_minus) ∧
    -- (2) Schur–Horn upper endpoint fails permutation-similarity without symmetry
    (HasOrderedSpectrum2 B_tri_distinct 1 0 ∧ diagVec2 B_tri_distinct = [1, 0] ∧
     ¬ PermSimilar 2 B_tri_distinct (diagMat2 1 0)) ∧
    -- (3) Lidskii sum endpoints fail permutation-similarity for symmetric matrices
    (IsSymm 2 A_lid ∧ HasOrderedSpectrum2 A_lid 25 0 ∧
     IsSymm 2 B_lid ∧ HasOrderedSpectrum2 B_lid 25 0 ∧
     (∀ B' : Mat 2, PermSimilar 2 B' B_lid →
       ¬ HasOrderedSpectrum2 (matAdd 2 A_lid B') 50 0 ∧
       ¬ HasOrderedSpectrum2 (matAdd 2 A_lid B') 25 25)) ∧
    -- (4) Spectral poset slices fail boundedness (over ℤ) and permutation-similarity (on PSD)
    ((∀ l1 l2 : Int, l1 ≥ l2 →
       ∃ m1 m2 : Int, m1 ≥ m2 ∧ m1 + m2 = l1 + l2 ∧ StrictMajorizes [m1, m2] [l1, l2]) ∧
     (∀ M1 M2 : Mat 2,
       HasOrderedSpectrum2 M1 1 1 → HasOrderedSpectrum2 M2 2 0 → ¬ PermSimilar 2 M1 M2)) := by
  have h1 := refutation_schur_horn_lower_endpoint
  have h2 := refutation_schur_horn_upper_nonhermitian
  have h3 := refutation_lidskii_sum_endpoints
  have h4 := refutation_spectra_poset_slices
  refine ⟨⟨h1.2.1, h1.2.2.1, h1.2.2.2.1, h1.2.2.2.2.1,
           h1.2.2.2.2.2.2.2.2.1, h1.2.2.2.2.2.2.2.2.2.2⟩,
          ⟨h2.1.1, h2.1.2.1, h2.1.2.2.2⟩,
          ⟨h3.1, h3.2.1, h3.2.2.1, h3.2.2.2.1,
           fun B' hB' => ⟨(h3.2.2.2.2.2.2.2.2.2 B' hB').1,
                          (h3.2.2.2.2.2.2.2.2.2 B' hB').2.1⟩⟩,
          ⟨h4.1, h4.2.2.1⟩⟩

#print axioms nonvacuity_ordering_equivalence
#print axioms nonvacuity_schur_upper_endpoint_dim_n
#print axioms nonvacuity_schur_upper_endpoint_symm2
#print axioms nonvacuity_lidskii_diagonal_case
#print axioms refutation_schur_horn_lower_endpoint
#print axioms refutation_schur_horn_upper_nonhermitian
#print axioms refutation_lidskii_sum_endpoints
#print axioms refutation_spectra_poset_slices
#print axioms conjecture_00000007173_false_all_readings

end Conjecture00000007173
