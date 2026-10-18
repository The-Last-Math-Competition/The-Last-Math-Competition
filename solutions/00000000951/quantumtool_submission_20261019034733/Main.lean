import Std

/-- All Boolean words of the requested length, with no omissions or repeats. -/
def allBitWords : Nat → List (List Bool)
  | 0 => [[]]
  | n + 1 =>
      (allBitWords n).map (fun w => true :: w) ++
      (allBitWords n).map (fun w => false :: w)

/-- The complete Boolean-word enumeration has `2^m` entries. -/
theorem allBitWords_length (m : Nat) : (allBitWords m).length = 2 ^ m := by
  induction m with
  | zero => simp [allBitWords]
  | succ m ih =>
      calc
        (allBitWords (m + 1)).length =
            (allBitWords m).length + (allBitWords m).length := by
              simp [allBitWords]
        _ = 2 ^ m + 2 ^ m := by rw [ih]
        _ = 2 ^ (m + 1) := by rw [Nat.pow_succ]; omega

/-- Filtering a finite enumeration cannot increase its length. -/
theorem filter_length_le (p : α → Bool) : ∀ xs : List α, (xs.filter p).length ≤ xs.length
  | [] => by simp
  | x :: xs => by
      cases h : p x with
      | false =>
          have ih := filter_length_le p xs
          simp [h]
          omega
      | true =>
          have ih := filter_length_le p xs
          simp [h]
          omega

/-- Every generated word has the requested length. -/
theorem allBitWords_sound (m : Nat) : ∀ w, w ∈ allBitWords m → w.length = m := by
  induction m with
  | zero =>
      intro w hw
      simp [allBitWords] at hw
      simp [hw]
  | succ m ih =>
      intro w hw
      simp only [allBitWords, List.mem_append] at hw
      rcases hw with hw | hw
      · simp only [List.mem_map] at hw
        rcases hw with ⟨v, hv, rfl⟩
        simp [ih v hv]
      · simp only [List.mem_map] at hw
        rcases hw with ⟨v, hv, rfl⟩
        simp [ih v hv]

/-- Every Boolean word of length `m` occurs in the enumeration. -/
theorem allBitWords_complete (m : Nat) : ∀ w, w.length = m → w ∈ allBitWords m := by
  induction m with
  | zero =>
      intro w hw
      cases w with
      | nil => simp [allBitWords]
      | cons b tail => simp at hw
  | succ m ih =>
      intro w hw
      cases w with
      | nil => simp at hw
      | cons b tail =>
          have ht : tail.length = m := by simpa using hw
          cases b <;> simp [allBitWords, ih tail ht]

/-- Injective maps preserve the no-duplicates property of lists. -/
theorem nodup_map_injective {α β : Type} (f : α → β) (hf : Function.Injective f) :
    ∀ xs : List α, xs.Nodup → (xs.map f).Nodup
  | [], _ => by simp
  | x :: xs, h => by
      have hx := (List.nodup_cons.mp h)
      apply List.nodup_cons.mpr
      constructor
      · intro hmem
        rcases List.mem_map.mp hmem with ⟨y, hy, hEq⟩
        have hyx : y = x := hf hEq
        subst y
        exact hx.1 hy
      · exact nodup_map_injective f hf xs hx.2

/-- No word is repeated in the complete enumeration. -/
theorem allBitWords_nodup : ∀ m, (allBitWords m).Nodup
  | 0 => by simp [allBitWords]
  | m + 1 => by
      have ih := allBitWords_nodup m
      apply List.nodup_append.mpr
      constructor
      · exact nodup_map_injective (fun w => true :: w) (by intro a b h; cases h; rfl) _ ih
      constructor
      · exact nodup_map_injective (fun w => false :: w) (by intro a b h; cases h; rfl) _ ih
      · intro a ha b hb hab
        rcases List.mem_map.mp ha with ⟨v, hv, rfl⟩
        rcases List.mem_map.mp hb with ⟨w, hw, rfl⟩
        cases hab

/-- Filtering a duplicate-free enumeration preserves distinctness. -/
theorem nodup_filter {α : Type} (p : α → Bool) :
    ∀ xs : List α, xs.Nodup → (xs.filter p).Nodup
  | [], _ => by simp
  | x :: xs, h => by
      have hx := (List.nodup_cons.mp h)
      cases hp : p x with
      | false =>
          simp only [List.filter, hp]
          exact nodup_filter p xs hx.2
      | true =>
          simp only [List.filter, hp]
          apply List.nodup_cons.mpr
          constructor
          · intro hmem
            rcases List.mem_filter.mp hmem with ⟨hy, _⟩
            exact hx.1 hy
          · exact nodup_filter p xs hx.2

/-- The qualifying canonical unordered splits form a duplicate-free list of
at most `2^(n-1)` codes. The first index is fixed to one side; the Boolean
word records the side of every other index. -/
theorem qualifying_splits_bound (n : Nat) (qualifies : List Bool → Bool) :
    ((allBitWords (Nat.pred n)).filter qualifies).Nodup ∧
      ((allBitWords (Nat.pred n)).filter qualifies).length ≤ 2 ^ Nat.pred n := by
  constructor
  · exact nodup_filter qualifies _ (allBitWords_nodup _)
  · calc
      ((allBitWords (Nat.pred n)).filter qualifies).length ≤
          (allBitWords (Nat.pred n)).length := filter_length_le qualifies _
      _ = 2 ^ Nat.pred n := allBitWords_length _

/-- The conjecture's bound under the standard finite-frame interpretation:
`n` counts indexed vectors, and a split is an unordered pair of complementary
subfamilies. The Riesz requirement is represented by an arbitrary predicate,
so the proof applies to any choice of which splits qualify as Riesz splits. -/
theorem riesz_split_bound (n : Nat) (isRieszSplit : List Bool → Bool) :
    ((allBitWords (Nat.pred n)).filter isRieszSplit).Nodup ∧
      ((allBitWords (Nat.pred n)).filter isRieszSplit).length ≤ 2 ^ Nat.pred n :=
  qualifying_splits_bound n isRieszSplit
