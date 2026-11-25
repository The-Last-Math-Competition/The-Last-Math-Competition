/-
  OrbitSperner/BooleanSperner.lean
  Core Lean 4.19.0 formalization of the Boolean lattice B_n, binomial coefficients,
  De Bruijn-Tengbergen-Kruyswijk symmetric chain decomposition, Sperner's Theorem
  for all n : Nat, and exponential growth bounds for the Sperner number.
-/
import OrbitSperner.Foundations

namespace OrbitSperner

/-- Subsets of `[n]` represented as Boolean indicator vectors `Fin n → Bool`. -/
abbrev BVec (n : Nat) : Type := Fin n → Bool

/-- Empty indicator vector on `Fin 0`. -/
def emptyBVec : BVec 0 := fun i => Fin.elim0 i

/-- All-false (empty set) indicator vector on `Fin n`. -/
def falseBVec (n : Nat) : BVec n := fun _ => false

/-- Restriction of `x : BVec (n + 1)` to `Fin n`. -/
def bvecInit {n : Nat} (x : BVec (n + 1)) : BVec n :=
  fun i => x i.castSucc

/-- Top bit of `x : BVec (n + 1)` at `Fin.last n`. -/
def bvecLast {n : Nat} (x : BVec (n + 1)) : Bool :=
  x (Fin.last n)

/-- Extend `x : BVec n` by appending `b : Bool` at `Fin.last n`. -/
def extendBVec {n : Nat} (b : Bool) (x : BVec n) : BVec (n + 1) :=
  fun i => if h : i.val < n then x ⟨i.val, h⟩ else b

theorem extendBVec_castSucc {n : Nat} (b : Bool) (x : BVec n) (i : Fin n) :
    extendBVec b x i.castSucc = x i := by
  unfold extendBVec
  have hi : (i.castSucc).val < n := i.isLt
  simp [hi]

theorem extendBVec_last {n : Nat} (b : Bool) (x : BVec n) :
    extendBVec b x (Fin.last n) = b := by
  unfold extendBVec
  have h : ¬ ((Fin.last n).val < n) := by
    have hv : (Fin.last n).val = n := rfl
    omega
  simp [h]

theorem bvecInit_extend {n : Nat} (b : Bool) (x : BVec n) :
    bvecInit (extendBVec b x) = x := by
  funext i
  exact extendBVec_castSucc b x i

theorem bvecLast_extend {n : Nat} (b : Bool) (x : BVec n) :
    bvecLast (extendBVec b x) = b :=
  extendBVec_last b x

theorem extendBVec_eta {n : Nat} (x : BVec (n + 1)) :
    extendBVec (bvecLast x) (bvecInit x) = x := by
  funext i
  unfold extendBVec bvecInit bvecLast
  by_cases hi : i.val < n
  · simp [hi]
  · simp [hi]
    have hieq : Fin.last n = i := Fin.ext (by
      have hilt : i.val < n + 1 := i.isLt
      have hlv : (Fin.last n).val = n := rfl
      omega)
    rw [hieq]

theorem extendBVec_injective {n : Nat} (b : Bool) :
    ∀ ⦃x y : BVec n⦄, extendBVec b x = extendBVec b y → x = y := by
  intro x y h
  have h' := congrArg bvecInit h
  rw [bvecInit_extend, bvecInit_extend] at h'
  exact h'

theorem extendBVec_false_ne_true {n : Nat} (x y : BVec n) :
    extendBVec false x ≠ extendBVec true y := by
  intro h
  have h' := congrArg bvecLast h
  rw [bvecLast_extend, bvecLast_extend] at h'
  cases h'

/-- Decidable equality on `BVec n`. -/
def decEqBVec : (n : Nat) → DecidableEq (BVec n)
  | 0, _, _ => isTrue (funext (fun i => Fin.elim0 i))
  | n + 1, x, y =>
    match decEq (bvecLast x) (bvecLast y), decEqBVec n (bvecInit x) (bvecInit y) with
    | isTrue hl, isTrue hi =>
      isTrue (by rw [← extendBVec_eta x, ← extendBVec_eta y, hl, hi])
    | isFalse hl, _ =>
      isFalse (fun h => hl (congrArg bvecLast h))
    | _, isFalse hi =>
      isFalse (fun h => hi (congrArg bvecInit h))

instance instDecidableEqBVec (n : Nat) : DecidableEq (BVec n) := decEqBVec n

/-- Sum `f i` over `i : Fin n`. -/
def finSum : (n : Nat) → (Fin n → Nat) → Nat
  | 0, _ => 0
  | n + 1, f => finSum n (fun i => f i.castSucc) + f (Fin.last n)

theorem finSum_le_finSum : ∀ {n : Nat} {f g : Fin n → Nat},
    (∀ i, f i ≤ g i) → finSum n f ≤ finSum n g
  | 0, _, _, _ => Nat.le_refl 0
  | n + 1, f, g, h => by
    unfold finSum
    have ih := finSum_le_finSum (n := n) (f := fun i => f i.castSucc)
      (g := fun i => g i.castSucc) (fun i => h i.castSucc)
    have hl := h (Fin.last n)
    omega

theorem finSum_eq_iff_of_le : ∀ {n : Nat} {f g : Fin n → Nat},
    (∀ i, f i ≤ g i) → (finSum n f = finSum n g ↔ ∀ i, f i = g i)
  | 0, _, _, _ => ⟨fun _ i => Fin.elim0 i, fun _ => rfl⟩
  | n + 1, f, g, h => by
    constructor
    · intro hsum
      unfold finSum at hsum
      have hle_init : finSum n (fun i => f i.castSucc) ≤ finSum n (fun i => g i.castSucc) :=
        finSum_le_finSum (fun i => h i.castSucc)
      have hle_last : f (Fin.last n) ≤ g (Fin.last n) := h (Fin.last n)
      have heq_init : finSum n (fun i => f i.castSucc) = finSum n (fun i => g i.castSucc) := by
        omega
      have heq_last : f (Fin.last n) = g (Fin.last n) := by omega
      have hall_init := (finSum_eq_iff_of_le (fun i => h i.castSucc)).mp heq_init
      intro i
      if hi : i.val < n then
        let i' : Fin n := ⟨i.val, hi⟩
        have hc : i'.castSucc = i := Fin.ext rfl
        rw [← hc]
        exact hall_init i'
      else
        have hl : i = Fin.last n := Fin.ext (by
          have hilt : i.val < n + 1 := i.isLt
          have hlv : (Fin.last n).val = n := rfl
          omega)
        rw [hl]
        exact heq_last
    · intro hall
      have hf : f = g := funext hall
      rw [hf]

/-- Cardinality / Hamming weight `|x|` of a subset `x : BVec n`. -/
def weight {n : Nat} (x : BVec n) : Nat :=
  finSum n (fun i => if x i then 1 else 0)

theorem weight_empty (x : BVec 0) : weight x = 0 := rfl

theorem weight_extend_false {n : Nat} (x : BVec n) :
    weight (extendBVec false x) = weight x := by
  change finSum n (fun i => if extendBVec false x i.castSucc then 1 else 0) +
      (if extendBVec false x (Fin.last n) then 1 else 0) = weight x
  have h1 : (fun i : Fin n => if extendBVec false x i.castSucc then 1 else 0) =
      (fun i : Fin n => if x i then 1 else 0) := by
    funext i
    rw [extendBVec_castSucc]
  rw [h1, extendBVec_last]
  simp [weight]

theorem weight_extend_true {n : Nat} (x : BVec n) :
    weight (extendBVec true x) = weight x + 1 := by
  change finSum n (fun i => if extendBVec true x i.castSucc then 1 else 0) +
      (if extendBVec true x (Fin.last n) then 1 else 0) = weight x + 1
  have h1 : (fun i : Fin n => if extendBVec true x i.castSucc then 1 else 0) =
      (fun i : Fin n => if x i then 1 else 0) := by
    funext i
    rw [extendBVec_castSucc]
  rw [h1, extendBVec_last]
  simp [weight]

/-- Subset inclusion order `x ⊆ y` on `BVec n`. -/
def subsetLe {n : Nat} (x y : BVec n) : Prop :=
  ∀ i : Fin n, x i = true → y i = true

/-- The Boolean lattice `B_n = (P([n]), ⊆)` as a `Poset`. -/
def booleanPoset (n : Nat) : Poset (BVec n) where
  le := subsetLe
  le_refl := fun _ _ h => h
  le_antisymm := by
    intro x y hxy hyx
    funext i
    cases hx : x i <;> cases hy : y i
    · rfl
    · have := hyx i hy; rw [hx] at this; cases this
    · have := hxy i hx; rw [hy] at this; cases this
    · rfl
  le_trans := fun hxy hyz i hx => hyz i (hxy i hx)

theorem subsetLe_extend {n : Nat} {b₁ b₂ : Bool} {x y : BVec n}
    (hb : b₁ = true → b₂ = true) (hxy : subsetLe x y) :
    subsetLe (extendBVec b₁ x) (extendBVec b₂ y) := by
  intro i hi
  by_cases hlt : i.val < n
  · let i' : Fin n := ⟨i.val, hlt⟩
    have hc : i'.castSucc = i := Fin.ext rfl
    rw [← hc, extendBVec_castSucc] at hi ⊢
    exact hxy i' hi
  · have hl : i = Fin.last n := Fin.ext (by
      have hilt : i.val < n + 1 := i.isLt
      have hlv : (Fin.last n).val = n := rfl
      omega)
    rw [hl, extendBVec_last] at hi ⊢
    exact hb hi

theorem weight_le_of_subsetLe {n : Nat} {x y : BVec n} (h : subsetLe x y) :
    weight x ≤ weight y := by
  apply finSum_le_finSum
  intro i
  cases hx : x i <;> cases hy : y i
  · simp
  · simp
  · have := h i hx; rw [hy] at this; cases this
  · simp

theorem eq_of_subsetLe_of_weight_eq {n : Nat} {x y : BVec n}
    (h : subsetLe x y) (hw : weight x = weight y) : x = y := by
  have hpt : ∀ i : Fin n, (if x i then 1 else 0) ≤ (if y i then 1 else 0) := by
    intro i
    cases hx : x i <;> cases hy : y i
    · simp
    · simp
    · have := h i hx; rw [hy] at this; cases this
    · simp
  have hall := (finSum_eq_iff_of_le hpt).mp hw
  funext i
  have hi := hall i
  cases hx : x i <;> cases hy : y i <;> simp [hx, hy] at hi <;> rfl

/-- Every rank level `{x ∈ B_n | weight x = k}` is an antichain in `B_n`. -/
theorem layer_isAntichain (n k : Nat) :
    (booleanPoset n).IsAntichainPred (fun x => weight x = k) := by
  intro x y hx hy hle
  exact eq_of_subsetLe_of_weight_eq hle (by omega)

/-! ### Complete Enumeration of `B_n` and Binomial Coefficients -/

/-- Duplicate-free enumeration of all `2^n` elements of `BVec n`. -/
def allBVec : (n : Nat) → List (BVec n)
  | 0 => [emptyBVec]
  | n + 1 => (allBVec n).map (extendBVec false) ++ (allBVec n).map (extendBVec true)

theorem allBVec_length : ∀ n : Nat, (allBVec n).length = 2 ^ n
  | 0 => rfl
  | n + 1 => by
    simp [allBVec, List.length_append, List.length_map, allBVec_length n, Nat.pow_succ]
    omega

theorem mem_allBVec : ∀ {n : Nat} (x : BVec n), x ∈ allBVec n
  | 0, x => by
    have hx : x = emptyBVec := funext (fun i => Fin.elim0 i)
    rw [hx]
    simp [allBVec]
  | n + 1, x => by
    rw [← extendBVec_eta x]
    simp only [allBVec, List.mem_append, List.mem_map]
    cases bvecLast x with
    | false => exact Or.inl ⟨bvecInit x, mem_allBVec (bvecInit x), rfl⟩
    | true => exact Or.inr ⟨bvecInit x, mem_allBVec (bvecInit x), rfl⟩

theorem nodup_map_of_injective {α β : Type} {f : α → β}
    (hinj : ∀ ⦃u v⦄, f u = f v → u = v) :
    ∀ {l : List α}, l.Nodup → (l.map f).Nodup
  | [], _ => List.Pairwise.nil
  | _ :: _, h => by
    cases h with
    | cons hnot htail =>
      apply List.Pairwise.cons
      · intro b hb heq
        rcases List.mem_map.mp hb with ⟨a', ha', rfl⟩
        exact hnot a' ha' (hinj heq)
      · exact nodup_map_of_injective hinj htail

theorem nodup_append_of_disjoint {α : Type} {l₁ l₂ : List α}
    (h₁ : l₁.Nodup) (h₂ : l₂.Nodup) (hdisj : ∀ x, x ∈ l₁ → x ∈ l₂ → False) :
    (l₁ ++ l₂).Nodup := by
  induction l₁ with
  | nil => exact h₂
  | cons a as ih =>
    cases h₁ with
    | cons ha has =>
      apply List.Pairwise.cons
      · intro b hb heq
        subst heq
        rcases List.mem_append.mp hb with hba | hbl₂
        · exact ha a hba rfl
        · exact hdisj a (List.Mem.head as) hbl₂
      · exact ih has (fun x hx => hdisj x (List.Mem.tail a hx))

theorem nodup_allBVec : ∀ n : Nat, (allBVec n).Nodup
  | 0 => List.Pairwise.cons (fun _ h => nomatch h) List.Pairwise.nil
  | n + 1 => by
    unfold allBVec
    apply nodup_append_of_disjoint
    · exact nodup_map_of_injective (extendBVec_injective false) (nodup_allBVec n)
    · exact nodup_map_of_injective (extendBVec_injective true) (nodup_allBVec n)
    · intro z hz₁ hz₂
      rcases List.mem_map.mp hz₁ with ⟨x, _, hx⟩
      rcases List.mem_map.mp hz₂ with ⟨y, _, hy⟩
      rw [← hx] at hy
      exact extendBVec_false_ne_true x y hy.symm

/-- Cardinality of a decidable subset `S : BVec n → Bool`. -/
def setCard {n : Nat} (S : BVec n → Bool) : Nat :=
  ((allBVec n).filter S).length

/-- Binomial coefficient `binom n k = C(n, k)` via Pascal recursion. -/
def binom : Nat → Nat → Nat
  | _, 0 => 1
  | 0, _ + 1 => 0
  | n + 1, k + 1 => binom n k + binom n (k + 1)

/-- The classical Sperner number `C(n, ⌊n/2⌋)`. -/
def spernerNum (n : Nat) : Nat := binom n (n / 2)

theorem filter_map_length {α β : Type} (f : α → β) (P : β → Bool) :
    ∀ l : List α, ((l.map f).filter P).length = (l.filter (fun x => P (f x))).length
  | [] => rfl
  | a :: as => by
    simp only [List.map, List.filter]
    cases P (f a) <;> simp [filter_map_length f P as]

theorem filter_all_false_length {α : Type} {P : α → Bool} :
    ∀ {l : List α}, (∀ y ∈ l, P y = false) → (l.filter P).length = 0
  | [], _ => rfl
  | a :: as, hall => by
    have ha := hall a (List.Mem.head as)
    simp only [List.filter, ha]
    exact filter_all_false_length (fun y hy => hall y (List.Mem.tail a hy))

/-- Exact size of rank level `k` in `B_n` is `binom n k`. -/
theorem layerCard_eq_binom : ∀ (n k : Nat),
    setCard (n := n) (fun x => weight x == k) = binom n k
  | 0, 0 => rfl
  | 0, _ + 1 => rfl
  | n + 1, 0 => by
    change (((allBVec n).map (extendBVec false) ++ (allBVec n).map (extendBVec true)).filter
      (fun x => weight x == 0)).length = 1
    rw [List.filter_append, List.length_append, filter_map_length, filter_map_length]
    have hf : (fun x : BVec n => weight (extendBVec false x) == 0) = (fun x => weight x == 0) := by
      funext x; rw [weight_extend_false]
    have ht : ((allBVec n).filter (fun x : BVec n => weight (extendBVec true x) == 0)).length = 0 := by
      apply filter_all_false_length
      intro x _
      rw [weight_extend_true]
      simp
    rw [hf, ht]
    have ih := layerCard_eq_binom n 0
    unfold setCard at ih
    have hb0 : binom n 0 = 1 := by cases n <;> rfl
    omega
  | n + 1, k + 1 => by
    change (((allBVec n).map (extendBVec false) ++ (allBVec n).map (extendBVec true)).filter
      (fun x => weight x == k + 1)).length = binom n k + binom n (k + 1)
    rw [List.filter_append, List.length_append, filter_map_length, filter_map_length]
    have hf : (fun x : BVec n => weight (extendBVec false x) == k + 1) =
        (fun x => weight x == k + 1) := by
      funext x; rw [weight_extend_false]
    have ht : (fun x : BVec n => weight (extendBVec true x) == k + 1) =
        (fun x => weight x == k) := by
      funext x
      rw [weight_extend_true]
      by_cases h : weight x = k <;> simp [h]
    rw [hf, ht]
    have ih0 := layerCard_eq_binom n k
    have ih1 := layerCard_eq_binom n (k + 1)
    unfold setCard at ih0 ih1
    omega

/-! ### Symmetric Chain Decomposition and Sperner's Theorem -/

/-- Upper child chain obtained from a non-empty chain `x₀ :: xs` in `B_n`. -/
def topChain {n : Nat} (x₀ : BVec n) : List (BVec n) → List (BVec (n + 1))
  | [] => [extendBVec false x₀, extendBVec true x₀]
  | x₁ :: xs => extendBVec false x₀ :: topChain x₁ xs

/-- Lower child chain obtained from `x₀ :: xs` in `B_n` (non-empty when `xs ≠ []`). -/
def botChain {n : Nat} (x₀ : BVec n) : List (BVec n) → List (BVec (n + 1))
  | [] => []
  | x₁ :: xs => extendBVec true x₀ :: botChain x₁ xs

/-- Split one chain in `B_n` into 1 or 2 symmetric chains in `B_{n+1}`. -/
def splitChain {n : Nat} : List (BVec n) → List (List (BVec (n + 1)))
  | [] => []
  | [x₀] => [topChain x₀ []]
  | x₀ :: x₁ :: xs => [topChain x₀ (x₁ :: xs), botChain x₀ (x₁ :: xs)]

/-- De Bruijn-Tengbergen-Kruyswijk Symmetric Chain Decomposition of `B_n`. -/
def scd : (n : Nat) → List (List (BVec n))
  | 0 => [[emptyBVec]]
  | n + 1 => ((scd n).map splitChain).flatten

/-- Sum of a `List Nat`. -/
def sumNatList : List Nat → Nat
  | [] => 0
  | a :: as => a + sumNatList as

theorem sumNatList_append : ∀ l₁ l₂ : List Nat,
    sumNatList (l₁ ++ l₂) = sumNatList l₁ + sumNatList l₂
  | [], _ => by simp [sumNatList]
  | a :: as, l₂ => by
    simp only [List.cons_append, sumNatList, sumNatList_append as l₂]
    omega

theorem filter_cons_len {α : Type} (P : α → Bool) (a : α) (as : List α) :
    ((a :: as).filter P).length = (if P a then 1 else 0) + (as.filter P).length := by
  simp only [List.filter]
  cases P a <;> simp [Nat.add_comm]

theorem top_bot_filter_count {n : Nat} (P : BVec (n + 1) → Bool) (x₀ : BVec n) :
    ∀ xs : List (BVec n),
      ((topChain x₀ xs).filter P).length + ((botChain x₀ xs).filter P).length =
        ((x₀ :: xs).filter (fun x => P (extendBVec false x))).length +
          ((x₀ :: xs).filter (fun x => P (extendBVec true x))).length
  | [] => by
    simp only [topChain, botChain]
    rw [filter_cons_len, filter_cons_len, filter_cons_len, filter_cons_len]
    simp only [List.filter, List.length]
    omega
  | x₁ :: rest => by
    have ih := top_bot_filter_count P x₁ rest
    simp only [topChain, botChain]
    rw [filter_cons_len P (extendBVec false x₀),
        filter_cons_len P (extendBVec true x₀),
        filter_cons_len (fun x => P (extendBVec false x)) x₀,
        filter_cons_len (fun x => P (extendBVec true x)) x₀]
    omega

theorem splitChain_filter_count {n : Nat} (P : BVec (n + 1) → Bool) :
    ∀ c : List (BVec n),
      sumNatList ((splitChain c).map (fun ch => (ch.filter P).length)) =
        (c.filter (fun x => P (extendBVec false x))).length +
          (c.filter (fun x => P (extendBVec true x))).length
  | [] => rfl
  | [x₀] => by
    have h := top_bot_filter_count P x₀ []
    have hb : ((botChain x₀ []).filter P).length = 0 := rfl
    rw [hb] at h
    simp only [splitChain, List.map, sumNatList]
    omega
  | x₀ :: x₁ :: rest => by
    have h := top_bot_filter_count P x₀ (x₁ :: rest)
    simp only [splitChain, List.map, sumNatList]
    omega

theorem sum_flatten_splitChain {n : Nat} (P : BVec (n + 1) → Bool) :
    ∀ cs : List (List (BVec n)),
      sumNatList (((cs.map splitChain).flatten).map (fun ch => (ch.filter P).length)) =
        sumNatList (cs.map (fun c => (c.filter (fun x => P (extendBVec false x))).length)) +
          sumNatList (cs.map (fun c => (c.filter (fun x => P (extendBVec true x))).length))
  | [] => rfl
  | c :: cs => by
    simp only [List.map, List.flatten_cons, List.map_append, sumNatList_append, sumNatList]
    rw [splitChain_filter_count P c, sum_flatten_splitChain P cs]
    omega

/-- **Partition Identity for `scd n`**: Summing `(c.filter P).length` across all chains
    `c ∈ scd n` equals `setCard P`. -/
theorem sum_filter_scd : ∀ (n : Nat) (P : BVec n → Bool),
    sumNatList ((scd n).map (fun c => (c.filter P).length)) = setCard P
  | 0, P => by
    unfold scd setCard allBVec sumNatList
    simp only [List.map, sumNatList]
    omega
  | n + 1, P => by
    change sumNatList ((((scd n).map splitChain).flatten).map (fun c => (c.filter P).length)) =
      (((allBVec n).map (extendBVec false) ++ (allBVec n).map (extendBVec true)).filter P).length
    rw [sum_flatten_splitChain P (scd n)]
    rw [sum_filter_scd n (fun x => P (extendBVec false x)),
        sum_filter_scd n (fun x => P (extendBVec true x))]
    unfold setCard
    rw [List.filter_append, List.length_append, filter_map_length, filter_map_length]

/-- Stepwise saturation invariant for chains `[x₀, x₁, ..., x_last]`. -/
def IsChainStep {n : Nat} : BVec n → List (BVec n) → BVec n → Prop
  | x, [], last => x = last
  | x, y :: ys, last => subsetLe x y ∧ weight y = weight x + 1 ∧ IsChainStep y ys last

/-- A list `c` is a symmetric chain in `B_n`. -/
def IsSymChain (n : Nat) (c : List (BVec n)) : Prop :=
  ∃ x₀ xs xlast, c = x₀ :: xs ∧ IsChainStep x₀ xs xlast ∧ weight x₀ + weight xlast = n

theorem topChain_step {n : Nat} {x₀ xlast : BVec n} :
    ∀ {xs : List (BVec n)}, IsChainStep x₀ xs xlast →
      ∃ ts, topChain x₀ xs = extendBVec false x₀ :: ts ∧
        IsChainStep (extendBVec false x₀) ts (extendBVec true xlast)
  | [], h => by
    subst h
    refine ⟨[extendBVec true x₀], rfl, ?_, ?_, rfl⟩
    · exact subsetLe_extend (fun h => nomatch h) (fun _ h => h)
    · rw [weight_extend_true, weight_extend_false]
  | x₁ :: rest, ⟨hle, hw, hrest⟩ => by
    rcases topChain_step hrest with ⟨ts, htop, hts⟩
    refine ⟨extendBVec false x₁ :: ts, ?_, ?_, ?_, hts⟩
    · change extendBVec false x₀ :: topChain x₁ rest = extendBVec false x₀ :: extendBVec false x₁ :: ts
      rw [htop]
    · exact subsetLe_extend (fun h => h) hle
    · rw [weight_extend_false, weight_extend_false, hw]

theorem botChain_step {n : Nat} {x₀ x₁ xlast : BVec n} :
    ∀ {rest : List (BVec n)}, IsChainStep x₀ (x₁ :: rest) xlast →
      ∃ bs blast, botChain x₀ (x₁ :: rest) = extendBVec true x₀ :: bs ∧
        IsChainStep (extendBVec true x₀) bs blast ∧
        weight blast = weight xlast
  | [], ⟨_, hw, hlast⟩ => by
    subst hlast
    refine ⟨[], extendBVec true x₀, rfl, rfl, ?_⟩
    rw [weight_extend_true, hw]
  | x₂ :: rest', ⟨hle, hw, hrest⟩ => by
    rcases botChain_step hrest with ⟨bs, blast, hbot, hbs, hwlast⟩
    refine ⟨extendBVec true x₁ :: bs, blast, ?_, ⟨?_, ?_, hbs⟩, hwlast⟩
    · change extendBVec true x₀ :: botChain x₁ (x₂ :: rest') = extendBVec true x₀ :: extendBVec true x₁ :: bs
      rw [hbot]
    · exact subsetLe_extend (fun h => h) hle
    · rw [weight_extend_true, weight_extend_true, hw]

theorem splitChain_symChain {n : Nat} {c : List (BVec n)} (hc : IsSymChain n c) :
    ∀ ch ∈ splitChain c, IsSymChain (n + 1) ch := by
  rcases hc with ⟨x₀, xs, xlast, rfl, hstep, hsum⟩
  cases xs with
  | nil =>
    have hxl : x₀ = xlast := hstep
    subst hxl
    intro ch hch
    simp only [splitChain, List.mem_singleton] at hch
    subst hch
    rcases topChain_step (x₀ := x₀) (xlast := x₀) (xs := []) rfl with ⟨ts, htop, hts⟩
    refine ⟨extendBVec false x₀, ts, extendBVec true x₀, htop, hts, ?_⟩
    rw [weight_extend_false, weight_extend_true]
    omega
  | cons x₁ rest =>
    intro ch hch
    simp only [splitChain, List.mem_cons, List.not_mem_nil, or_false] at hch
    rcases hch with rfl | rfl
    · rcases topChain_step hstep with ⟨ts, htop, hts⟩
      refine ⟨extendBVec false x₀, ts, extendBVec true xlast, htop, hts, ?_⟩
      rw [weight_extend_false, weight_extend_true]
      omega
    · rcases botChain_step hstep with ⟨bs, blast, hbot, hbs, hwlast⟩
      refine ⟨extendBVec true x₀, bs, blast, hbot, hbs, ?_⟩
      rw [weight_extend_true, hwlast]
      omega

theorem scd_all_symChain : ∀ (n : Nat) (c : List (BVec n)), c ∈ scd n → IsSymChain n c
  | 0, c, hc => by
    simp only [scd, List.mem_singleton] at hc
    subst hc
    exact ⟨emptyBVec, [], emptyBVec, rfl, rfl, rfl⟩
  | n + 1, c, hc => by
    unfold scd at hc
    rcases List.mem_flatten.mp hc with ⟨l, hl, hcl⟩
    rcases List.mem_map.mp hl with ⟨c₀, hc₀, rfl⟩
    exact splitChain_symChain (scd_all_symChain n c₀ hc₀) c hcl

/-- Along `IsChainStep x₀ xs xlast`, `x₀` is strictly below every element of `xs` in `weight`
    and `subsetLe x₀ y` holds for all `y ∈ xs`. -/
theorem chainStep_head_lt {n : Nat} {x₀ xlast : BVec n} :
    ∀ {xs : List (BVec n)}, IsChainStep x₀ xs xlast →
      ∀ y ∈ xs, subsetLe x₀ y ∧ weight x₀ < weight y
  | [], _, _, hy => nomatch hy
  | x₁ :: rest, ⟨hle, hw, hrest⟩, y, hy => by
    rcases List.mem_cons.mp hy with rfl | hmem
    · exact ⟨hle, by omega⟩
    · rcases chainStep_head_lt hrest y hmem with ⟨hle', hw'⟩
      exact ⟨(booleanPoset n).le_trans hle hle', by omega⟩

theorem chainStep_weight_le_last {n : Nat} {x₀ xlast : BVec n} :
    ∀ {xs : List (BVec n)}, IsChainStep x₀ xs xlast → weight x₀ ≤ weight xlast
  | [], h => by subst h; omega
  | _ :: _, ⟨_, hw, hrest⟩ => by
    have ih := chainStep_weight_le_last hrest
    omega

/-- In a saturated chain `IsChainStep x₀ xs xlast` with `weight x₀ ≤ k ≤ weight xlast`,
    filtering by `weight · == k` yields length `1`. -/
theorem chainStep_filter_weight_eq_one {n : Nat} (k : Nat) :
    ∀ {x₀ xlast : BVec n} {xs : List (BVec n)},
      IsChainStep x₀ xs xlast → weight x₀ ≤ k → k ≤ weight xlast →
      (((x₀ :: xs).filter (fun x => weight x == k)).length) = 1
  | x₀, _, [], hstep, hlo, hhi => by
    subst hstep
    have hk : weight x₀ = k := by omega
    simp [hk]
  | x₀, xlast, x₁ :: rest, ⟨_, hw, hrest⟩, hlo, hhi => by
    rw [filter_cons_len]
    by_cases hk : weight x₀ = k
    · have hnone : ∀ y ∈ x₁ :: rest, (weight y == k) = false := by
        intro y hy
        rcases List.mem_cons.mp hy with rfl | hmem
        · simp; omega
        · rcases chainStep_head_lt hrest y hmem with ⟨_, hwy⟩
          simp; omega
      have hzero := filter_all_false_length hnone
      rw [hzero]
      simp [hk]
    · have hk_ne : (weight x₀ == k) = false := by simp; omega
      rw [hk_ne]
      simp only [Bool.false_eq_true, ↓reduceIte, Nat.zero_add]
      exact chainStep_filter_weight_eq_one k hrest (by omega) hhi

/-- Every symmetric chain in `B_n` contains a unique element of middle weight `n / 2`. -/
theorem symChain_mid_count_eq_one {n : Nat} {c : List (BVec n)} (hc : IsSymChain n c) :
    (c.filter (fun x => weight x == n / 2)).length = 1 := by
  rcases hc with ⟨x₀, xs, xlast, rfl, hstep, hsum⟩
  have hle := chainStep_weight_le_last hstep
  exact chainStep_filter_weight_eq_one (n / 2) hstep (by omega) (by omega)

/-- Every antichain `S : BVec n → Bool` intersects a saturated chain in at most `1` element. -/
theorem chainStep_antichain_le_one {n : Nat} {S : BVec n → Bool}
    (hant : (booleanPoset n).IsAntichainPred (fun x => S x = true)) :
    ∀ {x₀ xlast : BVec n} {xs : List (BVec n)},
      IsChainStep x₀ xs xlast → ((x₀ :: xs).filter S).length ≤ 1
  | x₀, _, [], _ => by
    simp only [List.filter]
    cases S x₀ <;> simp
  | x₀, _, x₁ :: rest, hstep => by
    rw [filter_cons_len]
    cases hs : S x₀ with
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte, Nat.zero_add]
      exact chainStep_antichain_le_one hant hstep.2.2
    | true =>
      have hnone : ∀ y ∈ x₁ :: rest, S y = false := by
        intro y hy
        rcases chainStep_head_lt hstep y hy with ⟨hle, hwlt⟩
        cases hsy : S y with
        | false => rfl
        | true =>
          have heq := hant hs hsy hle
          subst heq
          omega
      rw [filter_all_false_length hnone]
      simp

theorem sumNatList_eq_length_of_all_one : ∀ {α : Type} {l : List α} {f : α → Nat},
    (∀ a ∈ l, f a = 1) → sumNatList (l.map f) = l.length
  | _, [], _, _ => rfl
  | _, a :: as, f, hall => by
    simp only [List.map, sumNatList, List.length, hall a (List.Mem.head as)]
    have ih := sumNatList_eq_length_of_all_one (l := as) (f := f)
      (fun b hb => hall b (List.Mem.tail a hb))
    omega

theorem sumNatList_le_length_of_all_le_one : ∀ {α : Type} {l : List α} {f : α → Nat},
    (∀ a ∈ l, f a ≤ 1) → sumNatList (l.map f) ≤ l.length
  | _, [], _, _ => Nat.le_refl 0
  | _, a :: as, f, hall => by
    simp only [List.map, sumNatList, List.length]
    have ha := hall a (List.Mem.head as)
    have ih := sumNatList_le_length_of_all_le_one (l := as) (f := f)
      (fun b hb => hall b (List.Mem.tail a hb))
    omega

/-- The number of symmetric chains in `scd n` equals the classical Sperner number `C(n, ⌊n/2⌋)`. -/
theorem scd_length_eq_spernerNum (n : Nat) : (scd n).length = spernerNum n := by
  have h1 : sumNatList ((scd n).map (fun c => (c.filter (fun x => weight x == n / 2)).length)) =
      (scd n).length := by
    apply sumNatList_eq_length_of_all_one
    intro c hc
    exact symChain_mid_count_eq_one (scd_all_symChain n c hc)
  rw [← h1, sum_filter_scd n (fun x => weight x == n / 2)]
  exact layerCard_eq_binom n (n / 2)

/-- **Sperner's Theorem (Set Form)**: Every antichain `S : BVec n → Bool` in `B_n`
    has cardinality at most `spernerNum n = C(n, ⌊n/2⌋)`. -/
theorem sperner_theorem {n : Nat} {S : BVec n → Bool}
    (hant : (booleanPoset n).IsAntichainPred (fun x => S x = true)) :
    setCard S ≤ spernerNum n := by
  rw [← sum_filter_scd n S, ← scd_length_eq_spernerNum n]
  apply sumNatList_le_length_of_all_le_one
  intro c hc
  rcases scd_all_symChain n c hc with ⟨x₀, xs, _, rfl, hstep, _⟩
  exact chainStep_antichain_le_one hant hstep

/-- Middle layer `L_{⌊n/2⌋}` achieves the Sperner bound `spernerNum n`. -/
def midLayer (n : Nat) (x : BVec n) : Bool := weight x == n / 2

theorem midLayer_isAntichain (n : Nat) :
    (booleanPoset n).IsAntichainPred (fun x => midLayer n x = true) := by
  intro x y hx hy hle
  unfold midLayer at hx hy
  simp at hx hy
  exact layer_isAntichain n (n / 2) hx hy hle

theorem midLayer_card_eq_spernerNum (n : Nat) :
    setCard (midLayer n) = spernerNum n :=
  layerCard_eq_binom n (n / 2)

theorem filter_ne_length_lt {α : Type} [DecidableEq α] (a : α) :
    ∀ {U : List α}, a ∈ U → (U.filter (fun u => decide (u ≠ a))).length + 1 ≤ U.length
  | [], hm => nomatch hm
  | u :: us, hm => by
    rw [filter_cons_len]
    by_cases hua : u = a
    · subst hua
      have hf : decide (u ≠ u) = false := by simp
      rw [hf]
      have hle : (us.filter (fun x => decide (x ≠ u))).length ≤ us.length :=
        List.length_filter_le _ _
      simp only [Bool.false_eq_true, ↓reduceIte, Nat.zero_add, List.length]
      omega
    · have ht : decide (u ≠ a) = true := decide_eq_true hua
      rw [ht]
      rcases List.mem_cons.mp hm with rfl | hm'
      · exact False.elim (hua rfl)
      · have ih := filter_ne_length_lt a hm'
        simp only [↓reduceIte, List.length]
        omega

/-- Every duplicate-free list `L` contained in `U` has `L.length ≤ U.length`. -/
theorem length_le_filter_of_sublist_nodup {α : Type} [DecidableEq α] :
    ∀ {L U : List α}, L.Nodup → (∀ x ∈ L, x ∈ U) → L.length ≤ U.length
  | [], _, _, _ => Nat.zero_le _
  | a :: as, U, List.Pairwise.cons ha has, hsub => by
    let U' := U.filter (fun u => decide (u ≠ a))
    have hmema : a ∈ U := hsub a (List.Mem.head as)
    have hlenU : U'.length + 1 ≤ U.length := filter_ne_length_lt a hmema
    have hsub' : ∀ x ∈ as, x ∈ U' := by
      intro x hx
      have hxU : x ∈ U := hsub x (List.Mem.tail a hx)
      have hne : x ≠ a := fun heq => ha a (heq ▸ hx) rfl
      exact List.mem_filter.mpr ⟨hxU, decide_eq_true hne⟩
    have ih := length_le_filter_of_sublist_nodup has hsub'
    simp only [List.length]
    omega

theorem nodup_of_pairwise_incomp {α : Type} (P : Poset α) :
    ∀ {L : List α}, List.Pairwise (fun x y => P.Incomp x y) L → L.Nodup
  | [], _ => List.Pairwise.nil
  | a :: _, List.Pairwise.cons ha has =>
    List.Pairwise.cons
      (fun _ hb heq => by subst heq; exact (ha a hb).1 (P.le_refl a))
      (nodup_of_pairwise_incomp P has)

/-- **Sperner's Theorem (List Form)**: Any list `L : List (BVec n)` of pairwise incomparable
    subsets has `L.length ≤ spernerNum n`. -/
theorem sperner_theorem_list {n : Nat} {L : List (BVec n)}
    (hpw : List.Pairwise (fun x y => (booleanPoset n).Incomp x y) L) :
    L.length ≤ spernerNum n := by
  have hnodup : L.Nodup := nodup_of_pairwise_incomp (booleanPoset n) hpw
  let S : BVec n → Bool := fun x => decide (x ∈ L)
  have hant : (booleanPoset n).IsAntichainPred (fun x => S x = true) := by
    intro x y hx hy hle
    have hmx : x ∈ L := of_decide_eq_true hx
    have hmy : y ∈ L := of_decide_eq_true hy
    clear hx hy S hnodup
    induction L with
    | nil => nomatch hmx
    | cons a as ih =>
      cases hpw with
      | cons ha has =>
        rcases List.mem_cons.mp hmx with rfl | hmx' <;>
          rcases List.mem_cons.mp hmy with rfl | hmy'
        · rfl
        · exact False.elim ((ha y hmy').1 hle)
        · exact False.elim ((ha x hmx').2 hle)
        · exact ih has hmx' hmy'
  have hsub : ∀ x ∈ L, x ∈ (allBVec n).filter S := by
    intro x hx
    exact List.mem_filter.mpr ⟨mem_allBVec x, decide_eq_true hx⟩
  have hle1 : L.length ≤ setCard S := length_le_filter_of_sublist_nodup hnodup hsub
  have hle2 : setCard S ≤ spernerNum n := sperner_theorem hant
  omega

/-! ### Exponential Lower Bound on `spernerNum n` -/

/-- Every binomial coefficient `binom n k` is bounded by `spernerNum n`. -/
theorem binom_le_spernerNum (n k : Nat) : binom n k ≤ spernerNum n := by
  rw [← layerCard_eq_binom n k]
  apply sperner_theorem
  intro x y hx hy hle
  simp at hx hy
  exact layer_isAntichain n k hx hy hle

/-- Sum of `binom n k` for `0 ≤ k ≤ n` equals `2^n`. -/
def sumBinom (n : Nat) : Nat → Nat
  | 0 => binom n 0
  | k + 1 => sumBinom n k + binom n (k + 1)

theorem binom_gt_zero : ∀ {n k : Nat}, n < k → binom n k = 0
  | 0, _ + 1, _ => rfl
  | n + 1, k + 1, h => by
    unfold binom
    rw [binom_gt_zero (by omega), binom_gt_zero (by omega)]

theorem sumBinom_succ_step (n : Nat) :
    ∀ m : Nat, sumBinom (n + 1) (m + 1) = sumBinom n (m + 1) + sumBinom n m
  | 0 => by
    change binom (n + 1) 0 + binom (n + 1) 1 = (binom n 0 + binom n 1) + binom n 0
    have h4 : binom (n + 1) 0 = 1 := rfl
    have h5 : binom n 0 = 1 := by cases n <;> rfl
    have h6 : binom (n + 1) 1 = binom n 0 + binom n 1 := rfl
    omega
  | m + 1 => by
    have ih := sumBinom_succ_step n m
    have lhs : sumBinom (n + 1) (m + 1 + 1) = sumBinom (n + 1) (m + 1) + binom (n + 1) (m + 1 + 1) := rfl
    have rhs1 : sumBinom n (m + 1 + 1) = sumBinom n (m + 1) + binom n (m + 1 + 1) := rfl
    have rhs2 : sumBinom n (m + 1) = sumBinom n m + binom n (m + 1) := rfl
    have pasc : binom (n + 1) (m + 1 + 1) = binom n (m + 1) + binom n (m + 1 + 1) := rfl
    omega

theorem sumBinom_eq_pow : ∀ n : Nat, sumBinom n n = 2 ^ n
  | 0 => rfl
  | n + 1 => by
    rw [sumBinom_succ_step n n]
    have htop : sumBinom n (n + 1) = sumBinom n n + binom n (n + 1) := rfl
    rw [htop, binom_gt_zero (by omega), sumBinom_eq_pow n, Nat.pow_succ]
    omega

theorem sumBinom_le_mul_sperner (n : Nat) :
    ∀ k : Nat, sumBinom n k ≤ (k + 1) * spernerNum n
  | 0 => by
    simp only [sumBinom, Nat.zero_add, Nat.one_mul]
    exact binom_le_spernerNum n 0
  | k + 1 => by
    simp only [sumBinom]
    have ih := sumBinom_le_mul_sperner n k
    have hk := binom_le_spernerNum n (k + 1)
    have hmul : (k + 1 + 1) * spernerNum n = (k + 1) * spernerNum n + spernerNum n :=
      Nat.succ_mul (k + 1) (spernerNum n)
    omega

/-- **Exponential Lower Bound**: `(n + 1) * C(n, ⌊n/2⌋) ≥ 2^n` for all `n`. -/
theorem spernerNum_exp_lower (n : Nat) : 2 ^ n ≤ (n + 1) * spernerNum n := by
  rw [← sumBinom_eq_pow n]
  exact sumBinom_le_mul_sperner n n

end OrbitSperner
