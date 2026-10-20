import Std

/-!
# Counterexample to TLMC 00000005207

All matrices and matrix spaces are over the rational field. Matrix rank is given
by its standard nonsingular-minor characterization. Commutative matrix-space
rank is the maximum rank of its scalar evaluations. Noncommutative rank uses
the standard maximum normalized tensor-blowup characterization, with both an
attainment witness and a bound for every positive blowup size.

No rank value below is postulated. Each is derived from a symbolic determinant
identity, a nonzero minor, or a nonsingular explicit blowup.
-/
namespace TLMC5207

abbrev Matrix := Nat → Nat → Rat
abbrev Pencil := Nat → Matrix

/-- Sum the first `n` values. -/
def sum (n : Nat) (f : Nat → Rat) : Rat :=
  ((List.range n).map f).sum

/-- The determinant, by ordinary Laplace expansion along the first row. -/
def det : Nat → Matrix → Rat
  | 0, _ => 1
  | n+1, A => sum (n+1) (fun j =>
      (if j % 2 = 0 then (1 : Rat) else -1) * A 0 j *
      det n (fun r c => A (r+1) (if c < j then c else c+1)))

/-- Strictly increasing selection of `k` indices from `[0,n)`. -/
def IndexSelection (n k : Nat) (f : Nat → Nat) : Prop :=
  (∀ i, i < k → f i < n) ∧
  (∀ i j, i < j → j < k → f i < f j)

def minor (A : Matrix) (f g : Nat → Nat) : Matrix :=
  fun i j => A (f i) (g j)

/-- Every minor larger than `r` vanishes. -/
def RankLE (n : Nat) (A : Matrix) (r : Nat) : Prop :=
  ∀ k, r < k → k ≤ n → ∀ f g,
    IndexSelection n k f → IndexSelection n k g →
    det k (minor A f g) = 0

/-- A nonzero `r` by `r` minor exists. -/
def RankGE (n : Nat) (A : Matrix) (r : Nat) : Prop :=
  r ≤ n ∧ ∃ f g, IndexSelection n r f ∧ IndexSelection n r g ∧
    det r (minor A f g) ≠ 0

/-- Scalar evaluation of the linear matrix with coefficient matrices `A`. -/
def evaluate (m : Nat) (A : Pencil) (x : Nat → Rat) : Matrix :=
  fun i j => sum m (fun v => A v i j * x v)

/-- Kronecker block substitution, with independent `d` by `d` matrices. -/
def blowup (m d : Nat) (A : Pencil) (T : Nat → Matrix) : Matrix :=
  fun i j => sum m (fun v => A v (i / d) (j / d) * T v (i % d) (j % d))

/-- Exact commutative matrix-space rank: universal upper bound and attainment. -/
def CommutativeRank (m n : Nat) (A : Pencil) (r : Nat) : Prop :=
  (∀ x, RankLE n (evaluate m A x) r) ∧
  ∃ x, RankGE n (evaluate m A x) r

/-- Exact noncommutative rank in the tensor-blowup definition.
The upper bound ranges over all positive integers `d`, not just small tests. -/
def NoncommutativeRank (m n : Nat) (A : Pencil) (r : Nat) : Prop :=
  (∀ d, 0 < d → ∀ T, RankLE (n*d) (blowup m d A T) (r*d)) ∧
  ∃ d, 0 < d ∧ ∃ T, RankGE (n*d) (blowup m d A T) (r*d)

/-- Tensor product of coefficient tensors, using lexicographic indices. -/
def tensor (m₂ n₂ : Nat) (A B : Pencil) : Pencil :=
  fun v i j => A (v / m₂) (i / n₂) (j / n₂) *
    B (v % m₂) (i % n₂) (j % n₂)

/-- The three standard skew-symmetric coefficient matrices. -/
def skew : Pencil := fun v i j =>
  if v = 0 then
    if i = 0 ∧ j = 1 then 1 else if i = 1 ∧ j = 0 then -1 else 0
  else if v = 1 then
    if i = 0 ∧ j = 2 then 1 else if i = 2 ∧ j = 0 then -1 else 0
  else if v = 2 then
    if i = 1 ∧ j = 2 then 1 else if i = 2 ∧ j = 1 then -1 else 0
  else 0

/-- The one-dimensional scalar matrix space. -/
def unit : Pencil := fun _ _ _ => 1

/-- A scalar specialization giving a nonzero principal two-by-two minor. -/
def rankTwoPoint : Nat → Rat := fun v => if v = 0 then 1 else 0

/-- The explicit two-by-two matrices substituted for the three variables. -/
def blocks : Nat → Matrix := fun v i j =>
  if v = 0 then
    if i = 0 ∧ j = 0 then 1 else 0
  else if v = 1 then
    if (i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 0) then 1 else 0
  else if v = 2 then
    if i = 1 ∧ j = 1 then 1 else 0
  else 0

theorem selection_id (n : Nat) : IndexSelection n n id := by
  constructor <;> intro i
  · exact fun h => h
  · intro j hij _
    exact hij

theorem selection_initial {r n : Nat} (h : r ≤ n) : IndexSelection n r id := by
  constructor
  · intro i hi
    exact Nat.lt_of_lt_of_le hi h
  · intro i j hij _
    exact hij

theorem rank_le_size (n : Nat) (A : Matrix) : RankLE n A n := by
  intro k hk hn
  omega

theorem selection_three {f : Nat → Nat} (h : IndexSelection 3 3 f) :
    f 0 = 0 ∧ f 1 = 1 ∧ f 2 = 2 := by
  have h0 := h.1 0 (by decide)
  have h1 := h.1 1 (by decide)
  have h2 := h.1 2 (by decide)
  have h01 := h.2 0 1 (by decide) (by decide)
  have h12 := h.2 1 2 (by decide) (by decide)
  omega

/-- The symbolic 3 by 3 determinant vanishes for all rational scalars. -/
theorem skew_determinant_zero (x : Nat → Rat) : det 3 (evaluate 3 skew x) = 0 := by
  simp [det, sum, evaluate, skew, List.range_succ]
  grind

/-- The scalar specialization has the advertised nonzero minor. -/
theorem skew_minor_two : det 2 (minor (evaluate 3 skew rankTwoPoint) id id) = 1 := by
  simp [det, sum, minor, evaluate, skew, rankTwoPoint, List.range_succ]
  grind

/-- The block substitution is nonsingular; this is a 6 by 6 determinant. -/
theorem skew_blowup_determinant : det 6 (blowup 3 2 skew blocks) = 1 := by
  simp [det, sum, blowup, skew, blocks, List.range_succ]
  grind

/-- Every commutative evaluation has rank at most two. -/
theorem skew_commutative_upper (x : Nat → Rat) : RankLE 3 (evaluate 3 skew x) 2 := by
  intro k hk hn f g hf hg
  have hk3 : k = 3 := by omega
  subst k
  obtain ⟨hf0, hf1, hf2⟩ := selection_three hf
  obtain ⟨hg0, hg1, hg2⟩ := selection_three hg
  simp [det, sum, minor, evaluate, skew, List.range_succ,
    hf0, hf1, hf2, hg0, hg1, hg2]
  grind

theorem skew_commutative_rank : CommutativeRank 3 3 skew 2 := by
  constructor
  · exact skew_commutative_upper
  · refine ⟨rankTwoPoint, by decide, id, id,
      selection_initial (by decide), selection_initial (by decide), ?_⟩
    rw [skew_minor_two]
    decide

theorem skew_noncommutative_rank : NoncommutativeRank 3 3 skew 3 := by
  constructor
  · intro d _ T
    exact rank_le_size (3*d) _
  · refine ⟨2, by decide, blocks, by decide, id, id, selection_id 6, selection_id 6, ?_⟩
    change det 6 (blowup 3 2 skew blocks) ≠ 0
    rw [skew_blowup_determinant]
    decide

theorem unit_commutative_rank : CommutativeRank 1 1 unit 1 := by
  constructor
  · intro x
    exact rank_le_size 1 _
  · refine ⟨(fun _ => 1), by decide, id, id, selection_id 1, selection_id 1, ?_⟩
    simp [det, sum, minor, evaluate, unit, List.range_succ]
    grind

theorem unit_noncommutative_rank : NoncommutativeRank 1 1 unit 1 := by
  constructor
  · intro d _ T
    exact rank_le_size (1*d) _
  · refine ⟨1, by decide, (fun _ _ _ => 1), by decide, id, id,
      selection_id 1, selection_id 1, ?_⟩
    simp [det, sum, minor, blowup, unit, List.range_succ]
    grind

/-- The actual coefficient tensor product is the original skew pencil. -/
theorem tensor_unit : tensor 1 1 skew unit = skew := by
  funext v i j
  simp [tensor, unit]

theorem tensor_commutative_rank : CommutativeRank (3*1) (3*1) (tensor 1 1 skew unit) 2 := by
  rw [tensor_unit]
  exact skew_commutative_rank

theorem tensor_noncommutative_rank :
    NoncommutativeRank (3*1) (3*1) (tensor 1 1 skew unit) 3 := by
  rw [tensor_unit]
  exact skew_noncommutative_rank

/-- Explicit disproof: the tensor-product gap is one, whereas the product of
factor gaps is zero. All three matrices have size at most three. -/
theorem counterexample :
    CommutativeRank 3 3 skew 2 ∧ NoncommutativeRank 3 3 skew 3 ∧
    CommutativeRank 1 1 unit 1 ∧ NoncommutativeRank 1 1 unit 1 ∧
    CommutativeRank 3 3 (tensor 1 1 skew unit) 2 ∧
    NoncommutativeRank 3 3 (tensor 1 1 skew unit) 3 ∧
    (3 - 2 : Nat) ≠ (3 - 2) * (1 - 1) := by
  exact ⟨skew_commutative_rank, skew_noncommutative_rank,
    unit_commutative_rank, unit_noncommutative_rank,
    tensor_commutative_rank, tensor_noncommutative_rank, by decide⟩

/-- The conjectured multiplicativity law, even restricted so that both factors
and the tensor product have matrix size at most three. The rank arguments are
not assigned values: their actual rank predicates are required as hypotheses. -/
def MultiplicativeGap : Prop :=
  ∀ (m₁ n₁ m₂ n₂ : Nat) (A B : Pencil)
    (cA rA cB rB cP rP : Nat),
    0 < m₁ → 0 < n₁ → 0 < m₂ → 0 < n₂ →
    n₁ ≤ 3 → n₂ ≤ 3 → n₁*n₂ ≤ 3 →
    CommutativeRank m₁ n₁ A cA → NoncommutativeRank m₁ n₁ A rA →
    CommutativeRank m₂ n₂ B cB → NoncommutativeRank m₂ n₂ B rB →
    CommutativeRank (m₁*m₂) (n₁*n₂) (tensor m₂ n₂ A B) cP →
    NoncommutativeRank (m₁*m₂) (n₁*n₂) (tensor m₂ n₂ A B) rP →
    rP-cP = (rA-cA)*(rB-cB)

/-- Conjecture 00000005207 is false: its multiplicativity clause already fails
for nonzero rational matrix spaces of sizes 3 and 1. -/
theorem conjecture_00000005207_false : ¬ MultiplicativeGap := by
  intro h
  have bad := h 3 3 1 1 skew unit 2 3 1 1 2 3
    (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)
    skew_commutative_rank skew_noncommutative_rank
    unit_commutative_rank unit_noncommutative_rank
    tensor_commutative_rank tensor_noncommutative_rank
  contradiction

#print axioms counterexample
#print axioms conjecture_00000005207_false
end TLMC5207
