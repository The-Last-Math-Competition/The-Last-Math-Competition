/-
  Conjecture 00000007159 — Simplex Lattice & Multiplicative Trace-Product Systems
  Core Lean 4.19.0 (zero external dependencies)
-/
import Conjecture00000007159.MatrixTrace

namespace Conjecture00000007159

/-- Exponent tuple `α = (α_0, ..., α_{m-1}) ∈ ℕ^m`. -/
abbrev ExpVec (m : Nat) := Fin m → Nat

/-- Total degree `∑_i α_i` of an exponent tuple. -/
def expSum : {m : Nat} → ExpVec m → Nat
  | 0, _ => 0
  | m + 1, α => expSum (fun i : Fin m => α ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩) + α ⟨m, Nat.lt_succ_self m⟩

/-- Membership in the `m`-variable degree-`k` simplex lattice `Δ_k^(m)`. -/
def InSimplexLattice (m k : Nat) (α : ExpVec m) : Prop := expSum α = k

/-- Midpoint relation `2 β = α + γ` on the simplex lattice `Δ_k^(m)`. -/
def IsLatticeMidpoint {m : Nat} (α β γ : ExpVec m) : Prop :=
  ∀ i : Fin m, 2 * β i = α i + γ i

/-- Pointwise addition of exponent vectors in the simplex-lattice semigroup `⊔_k Δ_k^(m)`. -/
def expAdd {m : Nat} (α β : ExpVec m) : ExpVec m := fun i => α i + β i

/-- Elementary Robin-Hood / `T`-transfer covering step on the simplex lattice:
    moves `1` unit of exponent from `p` to `q` when `α_p ≥ α_q + 2`. -/
def IsElementaryTransfer {m : Nat} (α β : ExpVec m) (p q : Fin m) : Prop :=
  p ≠ q ∧ α p ≥ α q + 2 ∧ β p = α p - 1 ∧ β q = α q + 1 ∧
    ∀ i : Fin m, i ≠ p → i ≠ q → β i = α i

theorem midpoint_preserves_simplex {m k : Nat} {α β γ : ExpVec m}
    (hα : InSimplexLattice m k α) (hγ : InSimplexLattice m k γ)
    (hmid : IsLatticeMidpoint α β γ) : InSimplexLattice m k β := by
  have h2 : ∀ {r : Nat} (α' β' γ' : ExpVec r),
      IsLatticeMidpoint α' β' γ' → 2 * expSum β' = expSum α' + expSum γ' := by
    intro r
    induction r with
    | zero => intros; rfl
    | succ m' ih =>
      intro α' β' γ' hm
      simp only [expSum]
      have hrec := ih
        (fun i : Fin m' => α' ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩)
        (fun i : Fin m' => β' ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩)
        (fun i : Fin m' => γ' ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩)
        (fun i => hm _)
      have hlast := hm ⟨m', Nat.lt_succ_self m'⟩
      omega
  have hsum := h2 α β γ hmid
  dsimp [InSimplexLattice] at hα hγ ⊢
  omega

/-- Ordered product `A_0^{α_0} ⋯ A_{m-1}^{α_{m-1}}` of `m` matrices. -/
def orderedProd {n : Nat} : {m : Nat} → (Fin m → Mat n) → ExpVec m → Mat n
  | 0, _, _ => Mat.one n
  | m + 1, mats, α =>
    Mat.mul
      (orderedProd (fun i : Fin m => mats ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩)
                   (fun i : Fin m => α ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩))
      (Mat.pow (mats ⟨m, Nat.lt_succ_self m⟩) (α ⟨m, Nat.lt_succ_self m⟩))

/-- Ordered product trace `F(α) = tr(A_0^{α_0} ⋯ A_{m-1}^{α_{m-1}})`. -/
def orderedProdTrace {n m : Nat} (mats : Fin m → Mat n) (α : ExpVec m) : Int :=
  Mat.tr (orderedProd mats α)

/-- Squared Frobenius norm `G(α) = ‖A_0^{α_0} ⋯ A_{m-1}^{α_{m-1}}‖_F^2` (manifestly `≥ 0`). -/
def orderedProdFrobSq {n m : Nat} (mats : Fin m → Mat n) (α : ExpVec m) : Int :=
  Mat.frobNormSq (orderedProd mats α)

/-- Product of matrices along a noncommutative word `w : List (Fin m)`. -/
def wordProd {n m : Nat} (mats : Fin m → Mat n) : List (Fin m) → Mat n
  | [] => Mat.one n
  | idx :: rest => Mat.mul (mats idx) (wordProd mats rest)

/-- Trace of a noncommutative matrix word `tr(W(A_0, ..., A_{m-1}))`. -/
def wordTrace {n m : Nat} (mats : Fin m → Mat n) (w : List (Fin m)) : Int :=
  Mat.tr (wordProd mats w)

/-- Multi-degree (abelianization weight) `α(w) ∈ Δ_{|w|}^(m)` of a word `w`. -/
def wordWeight {m : Nat} : List (Fin m) → ExpVec m
  | [] => fun _ => 0
  | idx :: rest => fun i => (if i = idx then 1 else 0) + wordWeight rest i

theorem wordWeight_in_simplex {m : Nat} (w : List (Fin m)) :
    InSimplexLattice m w.length (wordWeight w) := by
  induction w with
  | nil =>
    dsimp [InSimplexLattice, wordWeight]
    induction m with
    | zero => rfl
    | succ m' ih => simp [expSum, ih]
  | cons idx rest ih =>
    dsimp [InSimplexLattice] at ih ⊢
    have hstep : ∀ {r : Nat} (idx' : Fin r) (f : ExpVec r),
        expSum (fun i : Fin r => (if i = idx' then 1 else 0) + f i) = 1 + expSum f := by
      intro r
      induction r with
      | zero => intro idx'; exact Fin.elim0 idx'
      | succ r' ihr =>
        intro idx' f
        simp only [expSum]
        by_cases hlast : idx'.val = r'
        · have heq : idx' = ⟨r', Nat.lt_succ_self r'⟩ := Fin.ext hlast
          subst heq
          have hzero : expSum (fun i : Fin r' =>
              (if (⟨i.val, Nat.lt_succ_of_lt i.isLt⟩ : Fin (r' + 1)) = ⟨r', Nat.lt_succ_self r'⟩
               then 1 else 0) + f ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩) =
              expSum (fun i : Fin r' => f ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩) := by
            congr 1
            funext i
            have hne : (⟨i.val, Nat.lt_succ_of_lt i.isLt⟩ : Fin (r' + 1)) ≠ ⟨r', Nat.lt_succ_self r'⟩ := by
              intro h; exact Nat.ne_of_lt i.isLt (congrArg Fin.val h)
            simp [hne]
          rw [hzero]
          simp
          omega
        · have hlt : idx'.val < r' := Nat.lt_of_le_of_ne (Nat.le_of_lt_succ idx'.isLt) hlast
          let idx'' : Fin r' := ⟨idx'.val, hlt⟩
          have hne_last : (⟨r', Nat.lt_succ_self r'⟩ : Fin (r' + 1)) ≠ idx' := by
            intro h; exact hlast (congrArg Fin.val h).symm
          have hcong : expSum (fun i : Fin r' =>
              (if (⟨i.val, Nat.lt_succ_of_lt i.isLt⟩ : Fin (r' + 1)) = idx' then 1 else 0) +
                f ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩) =
              expSum (fun i : Fin r' =>
                (if i = idx'' then 1 else 0) + f ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩) := by
            congr 1
            funext i
            by_cases hi : i = idx''
            · have heq : (⟨i.val, Nat.lt_succ_of_lt i.isLt⟩ : Fin (r' + 1)) = idx' :=
                Fin.ext (show i.val = idx'.val from congrArg Fin.val hi)
              rw [if_pos heq, if_pos hi]
            · have hne : (⟨i.val, Nat.lt_succ_of_lt i.isLt⟩ : Fin (r' + 1)) ≠ idx' := by
                intro heq
                exact hi (Fin.ext (show i.val = idx'.val from congrArg Fin.val heq))
              rw [if_neg hne, if_neg hi]
          rw [hcong, ihr idx'']
          simp [hne_last]
          omega
    simp only [wordWeight, List.length_cons]
    rw [hstep idx (wordWeight rest), ih]
    omega

/-- Helper constructors for `2` and `3` matrices / exponents. -/
def vec2 {α : Type} (x y : α) : Fin 2 → α :=
  fun i => if i.val = 0 then x else y

def vec3 {α : Type} (x y z : α) : Fin 3 → α :=
  fun i =>
    match i.val with
    | 0 => x
    | 1 => y
    | _ => z

/-- `S_3`-symmetrized Ordered Matrix Muirhead functional
    `M^ord_{(a,b,c)}(A, B, C) = ∑_{σ ∈ S_3} tr(A_{σ(1)}^a A_{σ(2)}^b A_{σ(3)}^c)`. -/
def orderedMuirhead3 {n : Nat} (A B C : Mat n) (a b c : Nat) : Int :=
  Mat.tr (Mat.mul (Mat.mul (Mat.pow A a) (Mat.pow B b)) (Mat.pow C c)) +
  Mat.tr (Mat.mul (Mat.mul (Mat.pow A a) (Mat.pow C b)) (Mat.pow B c)) +
  Mat.tr (Mat.mul (Mat.mul (Mat.pow B a) (Mat.pow A b)) (Mat.pow C c)) +
  Mat.tr (Mat.mul (Mat.mul (Mat.pow B a) (Mat.pow C b)) (Mat.pow A c)) +
  Mat.tr (Mat.mul (Mat.mul (Mat.pow C a) (Mat.pow A b)) (Mat.pow B c)) +
  Mat.tr (Mat.mul (Mat.mul (Mat.pow C a) (Mat.pow B b)) (Mat.pow A c))

/-- Structural-fuel helper for summing noncommutative words of weight `(a, b, c)`
    on the simplex lattice `Δ_k^(3)` (`fuel = a + b + c`), ensuring pure structural kernel reduction. -/
def hurwitzMatAux {n : Nat} (X Y Z : Mat n) : Nat → Nat → Nat → Nat → Mat n
  | 0, _, _, _ => Mat.one n
  | k + 1, a, b, c =>
    let tA := match a with | 0 => Mat.zero n | a' + 1 => Mat.mul (hurwitzMatAux X Y Z k a' b c) X
    let tB := match b with | 0 => Mat.zero n | b' + 1 => Mat.mul (hurwitzMatAux X Y Z k a b' c) Y
    let tC := match c with | 0 => Mat.zero n | c' + 1 => Mat.mul (hurwitzMatAux X Y Z k a b c') Z
    Mat.add (Mat.add tA tB) tC

/-- Sum of matrices over all noncommutative words of weight `(a, b, c)` for `(X, Y, Z)`. -/
def hurwitzCoeffMat {n : Nat} (X Y Z : Mat n) (a b c : Nat) : Mat n :=
  hurwitzMatAux X Y Z (a + b + c) a b c

/-- Structural-fuel helper for multinomial word count `k! / (a! b! c!)`. -/
def multinom3Aux : Nat → Nat → Nat → Nat → Nat
  | 0, _, _, _ => 1
  | k + 1, a, b, c =>
    (match a with | 0 => 0 | a' + 1 => multinom3Aux k a' b c) +
    (match b with | 0 => 0 | b' + 1 => multinom3Aux k a b' c) +
    (match c with | 0 => 0 | c' + 1 => multinom3Aux k a b c')

/-- Multinomial word count `(a + b + c)! / (a! b! c!)` matching `hurwitzCoeffMat`. -/
def multinom3 (a b c : Nat) : Nat :=
  multinom3Aux (a + b + c) a b c

/-- `S_3`-symmetrized sum of traces over all words of weight `(a, b, c)` (before dividing by `multinom3`). -/
def hurwitzSymWordSum3 {n : Nat} (A B C : Mat n) (a b c : Nat) : Int :=
  Mat.tr (hurwitzCoeffMat A B C a b c) +
  Mat.tr (hurwitzCoeffMat A C B a b c) +
  Mat.tr (hurwitzCoeffMat B A C a b c) +
  Mat.tr (hurwitzCoeffMat B C A a b c) +
  Mat.tr (hurwitzCoeffMat C A B a b c) +
  Mat.tr (hurwitzCoeffMat C B A a b c)

/-! ### Formal Candidate Interpretations of the Simplex-Lattice Trace-Product System -/

/-- Candidate System 1: Simplex-Lattice Ordered-Product Positivity (`tr(A_1^{α_1} ⋯ A_m^{α_m}) ≥ 0`). -/
def SimplexPositivitySystem (n m k : Nat) : Prop :=
  ∀ (mats : Fin m → Mat n), (∀ i, Mat.IsGramPSD (mats i)) →
    ∀ α : ExpVec m, InSimplexLattice m k α → 0 ≤ orderedProdTrace mats α

/-- Candidate System 2: Simplex-Lattice Log-Convexity (`F(β)^2 ≤ F(α) F(γ)` whenever `2 β = α + γ` in `Δ_k^(m)`). -/
def SimplexLogConvexSystem (n m k : Nat) : Prop :=
  ∀ (mats : Fin m → Mat n), (∀ i, Mat.IsGramPSD (mats i)) →
    ∀ α β γ : ExpVec m,
      InSimplexLattice m k α → InSimplexLattice m k γ → IsLatticeMidpoint α β γ →
      orderedProdTrace mats β * orderedProdTrace mats β ≤
        orderedProdTrace mats α * orderedProdTrace mats γ

/-- Candidate System 3: Simplex-Lattice Frobenius-Norm / Sandwich Log-Convexity (`G(β)^2 ≤ G(α) G(γ)`). -/
def SimplexFrobeniusLogConvexSystem (n m k : Nat) : Prop :=
  ∀ (mats : Fin m → Mat n), (∀ i, Mat.IsGramPSD (mats i)) →
    ∀ α β γ : ExpVec m,
      InSimplexLattice m k α → InSimplexLattice m k γ → IsLatticeMidpoint α β γ →
      orderedProdFrobSq mats β * orderedProdFrobSq mats β ≤
        orderedProdFrobSq mats α * orderedProdFrobSq mats γ

/-- Candidate System 4: Lattice-Semigroup Trace-Product Submultiplicativity (`F(α + β) ≤ F(α) F(β)` for non-zero `α, β`). -/
def SimplexSubmultiplicativeSystem (n m : Nat) : Prop :=
  ∀ (mats : Fin m → Mat n), (∀ i, Mat.IsGramPSD (mats i)) →
    ∀ (k₁ k₂ : Nat) (α β : ExpVec m),
      1 ≤ k₁ → 1 ≤ k₂ →
      InSimplexLattice m k₁ α → InSimplexLattice m k₂ β →
      orderedProdTrace mats (expAdd α β) ≤ orderedProdTrace mats α * orderedProdTrace mats β

/-- Candidate System 5: Simplex-Lattice Word-Grouping Extrema (`tr(W) ≤ F(α(W))`). -/
def SimplexWordExtremaSystem (n m k : Nat) : Prop :=
  ∀ (mats : Fin m → Mat n), (∀ i, Mat.IsGramPSD (mats i)) →
    ∀ w : List (Fin m), w.length = k →
      wordTrace mats w ≤ orderedProdTrace mats (wordWeight w)

/-- Candidate System 6a: Simplex-Lattice Ordered Matrix Muirhead System on `Δ_k^(3)`. -/
def SimplexOrderedMuirhead3System (n k : Nat) : Prop :=
  ∀ (A B C : Mat n), Mat.IsGramPSD A → Mat.IsGramPSD B → Mat.IsGramPSD C →
    ∀ (a₁ b₁ c₁ a₂ b₂ c₂ : Nat) (p q : Fin 3),
      InSimplexLattice 3 k (vec3 a₁ b₁ c₁) →
      IsElementaryTransfer (vec3 a₁ b₁ c₁) (vec3 a₂ b₂ c₂) p q →
      orderedMuirhead3 A B C a₂ b₂ c₂ ≤ orderedMuirhead3 A B C a₁ b₁ c₁

/-- Candidate System 6b: Simplex-Lattice Word-Averaged (Hurwitz/BMV) Muirhead System on `Δ_k^(3)`
    (cross-multiplied by the positive word counts `multinom3`). -/
def SimplexHurwitzMuirhead3System (n k : Nat) : Prop :=
  ∀ (A B C : Mat n), Mat.IsGramPSD A → Mat.IsGramPSD B → Mat.IsGramPSD C →
    ∀ (a₁ b₁ c₁ a₂ b₂ c₂ : Nat) (p q : Fin 3),
      InSimplexLattice 3 k (vec3 a₁ b₁ c₁) →
      IsElementaryTransfer (vec3 a₁ b₁ c₁) (vec3 a₂ b₂ c₂) p q →
      (multinom3 a₁ b₁ c₁ : Int) * hurwitzSymWordSum3 A B C a₂ b₂ c₂ ≤
        (multinom3 a₂ b₂ c₂ : Int) * hurwitzSymWordSum3 A B C a₁ b₁ c₁

end Conjecture00000007159
