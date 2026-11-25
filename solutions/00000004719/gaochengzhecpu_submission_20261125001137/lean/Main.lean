/-
  Conjecture 00000004719 — Complete Core Lean 4.19.0 Disproof
  Zero external dependencies; compiled with `-DwarningAsError=true`.
-/

namespace Conjecture4719

/-! ## Section 1: Duplicate-Free Lists, Exact Finite Cardinality, Words, and Factors -/

/-- Duplicate-free predicate on lists. -/
inductive ListNodup {α : Type u} : List α → Prop where
  | nil : ListNodup []
  | cons {x : α} {xs : List α} : (∀ y ∈ xs, x ≠ y) → ListNodup xs → ListNodup (x :: xs)

/-- Exact finite cardinality `|α| = n`: witnessed by a duplicate-free exhaustive list of length `n`. -/
def HasCardinality (α : Type u) (n : Nat) : Prop :=
  ∃ elems : List α, ListNodup elems ∧ (∀ x : α, x ∈ elems) ∧ elems.length = n

/-- Finite-type predicate `|α| < ∞`. -/
def IsFiniteType (α : Type u) : Prop :=
  ∃ n : Nat, HasCardinality α n

theorem nodup_filter {α : Type u} (p : α → Bool) :
    ∀ {xs : List α}, ListNodup xs → ListNodup (xs.filter p)
  | [], _ => .nil
  | x :: xs, .cons hnot hnd => by
    simp only [List.filter]
    cases hp : p x with
    | false => exact nodup_filter p hnd
    | true =>
      refine .cons ?_ (nodup_filter p hnd)
      intro y hy
      have hy_mem : y ∈ xs := (List.mem_filter.mp hy).1
      exact hnot y hy_mem

theorem nodup_map_of_inj {α : Type u} {β : Type v} (f : α → β)
    (hinj : ∀ x y : α, f x = f y → x = y) :
    ∀ {xs : List α}, ListNodup xs → ListNodup (xs.map f)
  | [], _ => .nil
  | x :: xs, .cons hnot hnd => by
    refine .cons ?_ (nodup_map_of_inj f hinj hnd)
    intro b hb hfb
    rcases List.mem_map.mp hb with ⟨y, hy, rfl⟩
    exact hnot y hy (hinj x y hfb)

theorem nodup_append {α : Type u} :
    ∀ {xs ys : List α}, ListNodup xs → ListNodup ys →
      (∀ x ∈ xs, ∀ y ∈ ys, x ≠ y) → ListNodup (xs ++ ys)
  | [], _, _, hys, _ => hys
  | x :: xs, ys, .cons hnot hnd, hys, hdisj => by
    refine .cons ?_ (nodup_append hnd hys (fun a ha b hb => hdisj a (List.mem_cons_of_mem x ha) b hb))
    intro z hz hxz
    rcases List.mem_append.mp hz with hzx | hzy
    · exact hnot z hzx hxz
    · exact hdisj x List.mem_cons_self z hzy hxz

private def eraseFirst {α : Type u} [DecidableEq α] (a : α) : List α → List α
  | [] => []
  | x :: xs => if a = x then xs else x :: eraseFirst a xs

private theorem length_eraseFirst_of_mem {α : Type u} [DecidableEq α] (a : α) :
    ∀ {ys : List α}, a ∈ ys → ys.length = (eraseFirst a ys).length + 1
  | [], h => nomatch h
  | x :: xs, h => by
    simp only [eraseFirst]
    by_cases hax : a = x
    · simp [hax]
    · cases h with
      | head _ => exact absurd rfl hax
      | tail _ hmem =>
        have ih := length_eraseFirst_of_mem a hmem
        simp [hax, ih, Nat.add_assoc]

private theorem mem_eraseFirst_of_ne {α : Type u} [DecidableEq α] {a z : α} (hne : z ≠ a) :
    ∀ {ys : List α}, z ∈ ys → z ∈ eraseFirst a ys
  | [], h => nomatch h
  | x :: xs, h => by
    simp only [eraseFirst]
    by_cases hax : a = x
    · subst hax
      simp only [ite_true]
      cases h with
      | head _ => exact absurd rfl hne
      | tail _ hmem => exact hmem
    · simp [hax]
      cases h with
      | head _ => exact Or.inl rfl
      | tail _ hmem => exact Or.inr (mem_eraseFirst_of_ne hne hmem)

theorem nodup_length_le_of_subset {α : Type u} :
    ∀ {xs ys : List α}, ListNodup xs → (∀ x ∈ xs, x ∈ ys) → xs.length ≤ ys.length
  | [], _, _, _ => Nat.zero_le _
  | x :: xs, ys, .cons hnot hnd, hsub => by
    letI : DecidableEq α := Classical.typeDecidableEq α
    have hx : x ∈ ys := hsub x List.mem_cons_self
    have hlen : ys.length = (eraseFirst x ys).length + 1 := length_eraseFirst_of_mem x hx
    have hsub' : ∀ z ∈ xs, z ∈ eraseFirst x ys := by
      intro z hz
      have hne : z ≠ x := fun hzx => hnot z hz hzx.symm
      exact mem_eraseFirst_of_ne hne (hsub z (List.mem_cons_of_mem x hz))
    have ih : xs.length ≤ (eraseFirst x ys).length := nodup_length_le_of_subset hnd hsub'
    simp only [List.length_cons]
    omega

theorem hasCardinality_unique {α : Type u} {m n : Nat}
    (hm : HasCardinality α m) (hn : HasCardinality α n) : m = n := by
  rcases hm with ⟨xs, hnd_x, hall_x, hlen_x⟩
  rcases hn with ⟨ys, hnd_y, hall_y, hlen_y⟩
  have h1 : xs.length ≤ ys.length := nodup_length_le_of_subset hnd_x (fun x _ => hall_y x)
  have h2 : ys.length ≤ xs.length := nodup_length_le_of_subset hnd_y (fun y _ => hall_x y)
  omega

/-- Finite alphabet of size `k` and finite words over `Fin k`. -/
abbrev Alphabet (k : Nat) : Type := Fin k
abbrev Word (k : Nat) : Type := List (Fin k)

/-- `u` is a contiguous factor (substring) of `w`. -/
def IsFactor {k : Nat} (u w : Word k) : Prop :=
  ∃ p s : Word k, p ++ u ++ s = w

theorem isFactor_refl {k : Nat} (w : Word k) : IsFactor w w :=
  ⟨[], [], by simp⟩

theorem isFactor_trans {k : Nat} {u v w : Word k}
    (huv : IsFactor u v) (hvw : IsFactor v w) : IsFactor u w := by
  rcases huv with ⟨p1, s1, rfl⟩
  rcases hvw with ⟨p2, s2, rfl⟩
  refine ⟨p2 ++ p1, s1 ++ s2, ?_⟩
  simp [List.append_assoc]

theorem isFactor_length_le {k : Nat} {u w : Word k} (h : IsFactor u w) :
    u.length ≤ w.length := by
  rcases h with ⟨p, s, rfl⟩
  simp [List.length_append]
  omega

theorem isFactor_take_drop {k : Nat} (w : Word k) (i len : Nat) :
    IsFactor ((w.drop i).take len) w := by
  refine ⟨w.take i, (w.drop i).drop len, ?_⟩
  have h1 : (w.drop i).take len ++ (w.drop i).drop len = w.drop i := List.take_append_drop len (w.drop i)
  rw [List.append_assoc, h1, List.take_append_drop]

theorem isFactor_iff_slice {k : Nat} (u w : Word k) :
    IsFactor u w ↔ ∃ i : Nat, i + u.length ≤ w.length ∧ (w.drop i).take u.length = u := by
  constructor
  · rintro ⟨p, s, rfl⟩
    refine ⟨p.length, ?_, ?_⟩
    · simp [List.length_append]
    · have hd : (p ++ u ++ s).drop p.length = u ++ s := by
        rw [List.append_assoc, List.drop_append_of_le_length (Nat.le_refl _)]
        simp
      rw [hd, List.take_append_of_le_length (Nat.le_refl _)]
      simp
  · rintro ⟨_, _, htake⟩
    rw [← htake]
    exact isFactor_take_drop w _ _

/-- Number of occurrences of letter `a` in word `w`. -/
def letterCount {k : Nat} (a : Fin k) : Word k → Nat
  | [] => 0
  | x :: xs => (if x = a then 1 else 0) + letterCount a xs

theorem letterCount_nil {k : Nat} (a : Fin k) : letterCount a [] = 0 := rfl

theorem letterCount_cons {k : Nat} (a x : Fin k) (xs : Word k) :
    letterCount a (x :: xs) = (if x = a then 1 else 0) + letterCount a xs := rfl

theorem letterCount_append {k : Nat} (a : Fin k) :
    ∀ u v : Word k, letterCount a (u ++ v) = letterCount a u + letterCount a v
  | [], v => by simp [letterCount]
  | x :: xs, v => by
    simp only [List.cons_append, letterCount_cons, letterCount_append a xs v]
    omega

theorem letterCount_le_length {k : Nat} (a : Fin k) :
    ∀ w : Word k, letterCount a w ≤ w.length
  | [] => Nat.le_refl 0
  | x :: xs => by
    have ih := letterCount_le_length a xs
    simp only [letterCount_cons, List.length_cons]
    split <;> omega

theorem letterCount_pos_iff_mem {k : Nat} (a : Fin k) :
    ∀ w : Word k, 0 < letterCount a w ↔ a ∈ w
  | [] => by simp [letterCount]
  | x :: xs => by
    simp only [letterCount_cons, List.mem_cons]
    have ih := letterCount_pos_iff_mem a xs
    by_cases hxa : x = a
    · subst hxa
      simp
      omega
    · have hax : a ≠ x := fun h => hxa h.symm
      simp [hxa, hax, ← ih]

/-- Absolute difference `|x - y|` on `Nat`. -/
def natDist (x y : Nat) : Nat :=
  if x ≤ y then y - x else x - y

theorem natDist_le_one_iff (x y : Nat) :
    natDist x y ≤ 1 ↔ x ≤ y + 1 ∧ y ≤ x + 1 := by
  unfold natDist
  split <;> omega

theorem natDist_eq_int_natAbs (x y : Nat) :
    natDist x y = Int.natAbs ((x : Int) - (y : Int)) := by
  unfold natDist
  split <;> omega

/--
  **Official Definition (`SOURCE.md`):**
  A *balanced word* is a word where letter counts of same-length contiguous factors
  differ by at most one.
-/
def IsBalanced {k : Nat} (w : Word k) : Prop :=
  ∀ u v : Word k, IsFactor u w → IsFactor v w → u.length = v.length →
    ∀ a : Fin k, natDist (letterCount a u) (letterCount a v) ≤ 1

theorem isBalanced_of_isFactor {k : Nat} {u w : Word k}
    (hb : IsBalanced w) (hf : IsFactor u w) : IsBalanced u := by
  intro x y hx hy hlen a
  exact hb x y (isFactor_trans hx hf) (isFactor_trans hy hf) hlen a

/-- Surjective (strictly `k`-letter) word: every letter of `Fin k` occurs at least once. -/
def UsesAllLetters (k : Nat) (w : Word k) : Prop :=
  ∀ a : Fin k, a ∈ w

/-- Word containing at least `r` distinct letters. -/
def HasAtLeastLetters {k : Nat} (r : Nat) (w : Word k) : Prop :=
  ∃ L : List (Fin k), ListNodup L ∧ L.length = r ∧ ∀ a ∈ L, a ∈ w

/-! ## Section 1B: Decidable Reflection and Exact Per-Length Counting Functions -/

def finList : (k : Nat) → List (Fin k)
  | 0 => []
  | k + 1 => ⟨0, Nat.zero_lt_succ k⟩ :: (finList k).map Fin.succ

theorem mem_finList {k : Nat} : ∀ a : Fin k, a ∈ finList k := by
  induction k with
  | zero => intro a; exact Fin.elim0 a
  | succ k ih =>
    intro ⟨v, hv⟩
    cases v with
    | zero => exact List.mem_cons_self
    | succ v' =>
      have hv' : v' < k := Nat.lt_of_succ_lt_succ hv
      have hm := ih ⟨v', hv'⟩
      exact List.mem_cons_of_mem _ (List.mem_map_of_mem hm)

theorem nodup_finList : ∀ k : Nat, ListNodup (finList k)
  | 0 => .nil
  | k + 1 => by
    refine .cons ?_ (nodup_map_of_inj Fin.succ (fun x y h => Fin.ext (by
      have := congrArg Fin.val h
      simpa using this)) (nodup_finList k))
    intro y hy h0
    rcases List.mem_map.mp hy with ⟨z, _, rfl⟩
    have := congrArg Fin.val h0
    simp at this

theorem length_finList : ∀ k : Nat, (finList k).length = k
  | 0 => rfl
  | k + 1 => by simp [finList, length_finList k]

def rangeList : Nat → List Nat
  | 0 => []
  | n + 1 => rangeList n ++ [n]

theorem mem_rangeList {m n : Nat} : m ∈ rangeList n ↔ m < n := by
  induction n with
  | zero => simp [rangeList]
  | succ n ih =>
    simp only [rangeList, List.mem_append, List.mem_singleton, ih]
    omega

/-- Computable boolean test for `IsBalanced w`. -/
def isBalancedBool {k : Nat} (w : Word k) : Bool :=
  (rangeList (w.length + 1)).all fun len =>
    (rangeList (w.length + 1 - len)).all fun i =>
      (rangeList (w.length + 1 - len)).all fun j =>
        (finList k).all fun a =>
          decide (natDist (letterCount a ((w.drop i).take len))
                          (letterCount a ((w.drop j).take len)) ≤ 1)

theorem isBalancedBool_eq_true_iff {k : Nat} (w : Word k) :
    isBalancedBool w = true ↔ IsBalanced w := by
  unfold isBalancedBool IsBalanced
  simp only [List.all_eq_true, mem_rangeList, decide_eq_true_eq]
  constructor
  · intro h u v hu hv hlen a
    rcases (isFactor_iff_slice u w).mp hu with ⟨i, hi, hu_eq⟩
    rcases (isFactor_iff_slice v w).mp hv with ⟨j, hj, hv_eq⟩
    rw [← hu_eq, ← hv_eq, ← hlen]
    apply h u.length (by omega) i (by omega) j (by omega) a (mem_finList a)
  · intro h len hlen i hi j hj a _
    have hu := isFactor_take_drop w i len
    have hv := isFactor_take_drop w j len
    have hlu : ((w.drop i).take len).length = len := by
      rw [List.length_take, List.length_drop]; omega
    have hlv : ((w.drop j).take len).length = len := by
      rw [List.length_take, List.length_drop]; omega
    exact h _ _ hu hv (hlu.trans hlv.symm) a

def usesAllLettersBool (k : Nat) (w : Word k) : Bool :=
  (finList k).all fun a => decide (a ∈ w)

theorem usesAllLettersBool_eq_true_iff (k : Nat) (w : Word k) :
    usesAllLettersBool k w = true ↔ UsesAllLetters k w := by
  unfold usesAllLettersBool UsesAllLetters
  simp only [List.all_eq_true, decide_eq_true_eq]
  exact ⟨fun h a => h a (mem_finList a), fun h a _ => h a⟩

def distinctLettersBool {k : Nat} (w : Word k) : Nat :=
  ((finList k).filter fun a => decide (a ∈ w)).length

def hasAtLeastLettersBool {k : Nat} (r : Nat) (w : Word k) : Bool :=
  decide (r ≤ distinctLettersBool w)

private theorem take_nodup {α : Type u} :
    ∀ (n : Nat) {xs : List α}, ListNodup xs → ListNodup (xs.take n)
  | 0, _, _ => .nil
  | _ + 1, [], _ => .nil
  | n + 1, _ :: _, .cons hnot hnd =>
    .cons (fun y hy => hnot y (List.mem_of_mem_take hy)) (take_nodup n hnd)

theorem hasAtLeastLettersBool_eq_true_iff {k : Nat} (r : Nat) (w : Word k) :
    hasAtLeastLettersBool r w = true ↔ HasAtLeastLetters r w := by
  unfold hasAtLeastLettersBool distinctLettersBool HasAtLeastLetters
  simp only [decide_eq_true_eq]
  let present := (finList k).filter fun a => decide (a ∈ w)
  have hnd_p : ListNodup present := nodup_filter _ (nodup_finList k)
  constructor
  · intro hr
    refine ⟨present.take r, take_nodup r hnd_p, ?_, ?_⟩
    · rw [List.length_take]
      exact Nat.min_eq_left hr
    · intro a ha
      have hm : a ∈ present := List.mem_of_mem_take ha
      exact of_decide_eq_true (List.mem_filter.mp hm).2
  · rintro ⟨L, hndL, hlenL, hsubL⟩
    have hsub : ∀ a ∈ L, a ∈ present := by
      intro a ha
      exact List.mem_filter.mpr ⟨mem_finList a, decide_eq_true (hsubL a ha)⟩
    have hle : L.length ≤ present.length := nodup_length_le_of_subset hndL hsub
    change r ≤ present.length
    omega

/-- Exhaustive duplicate-free list of all words of length `n` over `Fin k`. -/
def allWords (k : Nat) : Nat → List (Word k)
  | 0 => [[]]
  | n + 1 =>
    (finList k).flatMap fun a => (allWords k n).map fun w => a :: w

private theorem nodup_flatMap_cons {k : Nat} {as : List (Fin k)} {ws : List (Word k)}
    (has : ListNodup as) (hws : ListNodup ws) :
    ListNodup (as.flatMap fun a => ws.map fun w => a :: w) := by
  induction as with
  | nil => exact .nil
  | cons a as ih =>
    cases has with
    | cons hnot hnd_as =>
      simp only [List.flatMap_cons]
      refine nodup_append
        (nodup_map_of_inj (fun w => a :: w) (fun _ _ h => by injection h) hws)
        (ih hnd_as) ?_
      intro u hu v hv huv
      rcases List.mem_map.mp hu with ⟨w1, _, rfl⟩
      rcases List.mem_flatMap.mp hv with ⟨b, hb, hvb⟩
      rcases List.mem_map.mp hvb with ⟨w2, _, rfl⟩
      injection huv with hab _
      exact hnot b hb hab

theorem nodup_allWords (k : Nat) : ∀ n : Nat, ListNodup (allWords k n)
  | 0 => .cons (fun _ h => nomatch h) .nil
  | n + 1 => nodup_flatMap_cons (nodup_finList k) (nodup_allWords k n)

theorem mem_allWords_iff (k : Nat) :
    ∀ (n : Nat) (w : Word k), w ∈ allWords k n ↔ w.length = n
  | 0, w => by
    simp only [allWords, List.mem_singleton, List.length_eq_zero_iff]
  | n + 1, [] => by
    simp only [allWords, List.mem_flatMap, List.mem_map]
    constructor
    · rintro ⟨_, _, _, _, h⟩; cases h
    · intro h; cases h
  | n + 1, x :: xs => by
    simp only [allWords, List.mem_flatMap, List.mem_map, List.length_cons]
    constructor
    · rintro ⟨_, _, u, hu, h⟩
      injection h with _ huxs
      subst huxs
      have := (mem_allWords_iff k n u).mp hu
      omega
    · intro hlen
      have hxs : xs.length = n := by omega
      exact ⟨x, mem_finList x, xs, (mem_allWords_iff k n xs).mpr hxs, rfl⟩

/-- Exact count `b_k(n)` of balanced words of length `n` over `Fin k`. -/
def balancedWordsList (k n : Nat) : List (Word k) :=
  (allWords k n).filter isBalancedBool

def balancedCount (k n : Nat) : Nat :=
  (balancedWordsList k n).length

/-- Exact count `surj_k(n)` of surjective (`k`-letter) balanced words of length `n` over `Fin k`. -/
def surjBalancedWordsList (k n : Nat) : List (Word k) :=
  (balancedWordsList k n).filter (usesAllLettersBool k)

def surjBalancedCount (k n : Nat) : Nat :=
  (surjBalancedWordsList k n).length

/-- Exact count `m_{k,>=r}(n)` of balanced words of length `n` over `Fin k` with `>= r` distinct letters. -/
def atLeastBalancedWordsList (k r n : Nat) : List (Word k) :=
  (balancedWordsList k n).filter (hasAtLeastLettersBool r)

def atLeastBalancedCount (k r n : Nat) : Nat :=
  (atLeastBalancedWordsList k r n).length

private def attachSubtype {α : Type u} {P : α → Prop} :
    (xs : List α) → (∀ x ∈ xs, P x) → List { x : α // P x }
  | [], _ => []
  | x :: xs, h =>
    ⟨x, h x List.mem_cons_self⟩ ::
      attachSubtype xs (fun y hy => h y (List.mem_cons_of_mem x hy))

private theorem length_attachSubtype {α : Type u} {P : α → Prop} :
    ∀ (xs : List α) (h : ∀ x ∈ xs, P x), (attachSubtype xs h).length = xs.length
  | [], _ => rfl
  | _ :: xs, _ => by simp [attachSubtype, length_attachSubtype xs]

private theorem mem_attachSubtype {α : Type u} {P : α → Prop} :
    ∀ (xs : List α) (h : ∀ x ∈ xs, P x) (s : { x : α // P x }),
      s.1 ∈ xs → s ∈ attachSubtype xs h
  | [], _, _, hm => nomatch hm
  | x :: xs, _, ⟨val, hval⟩, hm => by
    cases hm with
    | head _ => exact List.mem_cons_self
    | tail _ hrest => exact List.mem_cons_of_mem _ (mem_attachSubtype xs _ ⟨val, hval⟩ hrest)

private theorem mem_of_mem_attachSubtype {α : Type u} {P : α → Prop} :
    ∀ {xs : List α} {h : ∀ x ∈ xs, P x} {s : { x : α // P x }},
      s ∈ attachSubtype xs h → s.1 ∈ xs
  | [], _, _, hm => nomatch hm
  | _ :: _, _, _, hm => by
    cases hm with
    | head _ => exact List.mem_cons_self
    | tail _ hrest => exact List.mem_cons_of_mem _ (mem_of_mem_attachSubtype hrest)

private theorem nodup_attachSubtype {α : Type u} {P : α → Prop} :
    ∀ (xs : List α) (h : ∀ x ∈ xs, P x), ListNodup xs → ListNodup (attachSubtype xs h)
  | [], _, _ => .nil
  | x :: xs, _, .cons hnot hnd => by
    refine .cons ?_ (nodup_attachSubtype xs _ hnd)
    intro ⟨y, hy⟩ hmem heq
    have hxy : x = y := congrArg Subtype.val heq
    exact hnot y (mem_of_mem_attachSubtype hmem) hxy

theorem balancedCount_spec (k n : Nat) :
    HasCardinality { w : Word k // w.length = n ∧ IsBalanced w } (balancedCount k n) := by
  have hp : ∀ w ∈ balancedWordsList k n, w.length = n ∧ IsBalanced w := by
    intro w hw
    rcases List.mem_filter.mp hw with ⟨hw_all, hw_bal⟩
    exact ⟨(mem_allWords_iff k n w).mp hw_all, (isBalancedBool_eq_true_iff w).mp hw_bal⟩
  refine ⟨attachSubtype (balancedWordsList k n) hp,
          nodup_attachSubtype _ hp (nodup_filter _ (nodup_allWords k n)),
          ?_, length_attachSubtype _ hp⟩
  rintro ⟨w, hlen, hbal⟩
  apply mem_attachSubtype
  exact List.mem_filter.mpr ⟨(mem_allWords_iff k n w).mpr hlen, (isBalancedBool_eq_true_iff w).mpr hbal⟩

theorem surjBalancedCount_spec (k n : Nat) :
    HasCardinality { w : Word k // w.length = n ∧ IsBalanced w ∧ UsesAllLetters k w }
      (surjBalancedCount k n) := by
  have hp : ∀ w ∈ surjBalancedWordsList k n, w.length = n ∧ IsBalanced w ∧ UsesAllLetters k w := by
    intro w hw
    rcases List.mem_filter.mp hw with ⟨hw_b, hw_s⟩
    rcases List.mem_filter.mp hw_b with ⟨hw_all, hw_bal⟩
    exact ⟨(mem_allWords_iff k n w).mp hw_all,
           (isBalancedBool_eq_true_iff w).mp hw_bal,
           (usesAllLettersBool_eq_true_iff k w).mp hw_s⟩
  refine ⟨attachSubtype (surjBalancedWordsList k n) hp,
          nodup_attachSubtype _ hp (nodup_filter _ (nodup_filter _ (nodup_allWords k n))),
          ?_, length_attachSubtype _ hp⟩
  rintro ⟨w, hlen, hbal, hsurj⟩
  apply mem_attachSubtype
  exact List.mem_filter.mpr ⟨List.mem_filter.mpr
    ⟨(mem_allWords_iff k n w).mpr hlen, (isBalancedBool_eq_true_iff w).mpr hbal⟩,
    (usesAllLettersBool_eq_true_iff k w).mpr hsurj⟩

theorem atLeastBalancedCount_spec (k r n : Nat) :
    HasCardinality { w : Word k // w.length = n ∧ IsBalanced w ∧ HasAtLeastLetters r w }
      (atLeastBalancedCount k r n) := by
  have hp : ∀ w ∈ atLeastBalancedWordsList k r n,
      w.length = n ∧ IsBalanced w ∧ HasAtLeastLetters r w := by
    intro w hw
    rcases List.mem_filter.mp hw with ⟨hw_b, hw_r⟩
    rcases List.mem_filter.mp hw_b with ⟨hw_all, hw_bal⟩
    exact ⟨(mem_allWords_iff k n w).mp hw_all,
           (isBalancedBool_eq_true_iff w).mp hw_bal,
           (hasAtLeastLettersBool_eq_true_iff r w).mp hw_r⟩
  refine ⟨attachSubtype (atLeastBalancedWordsList k r n) hp,
          nodup_attachSubtype _ hp (nodup_filter _ (nodup_filter _ (nodup_allWords k n))),
          ?_, length_attachSubtype _ hp⟩
  rintro ⟨w, hlen, hbal, hr⟩
  apply mem_attachSubtype
  exact List.mem_filter.mpr ⟨List.mem_filter.mpr
    ⟨(mem_allWords_iff k n w).mpr hlen, (isBalancedBool_eq_true_iff w).mpr hbal⟩,
    (hasAtLeastLettersBool_eq_true_iff r w).mpr hr⟩

/-! ## Section 2: Periodic Balanced Words & Disproof of Total-Count Finiteness (Reading 1) -/

/-- Periodic word over `Fin k` starting at offset `s` of length `len`: `j ↦ (s + j) % k`. -/
def periodicSlice (k : Nat) (hk : 0 < k) (s : Nat) : Nat → Word k
  | 0 => []
  | len + 1 => ⟨s % k, Nat.mod_lt s hk⟩ :: periodicSlice k hk (s + 1) len

def periodicWord (k : Nat) (hk : 0 < k) (n : Nat) : Word k :=
  periodicSlice k hk 0 n

theorem length_periodicSlice (k : Nat) (hk : 0 < k) :
    ∀ s len : Nat, (periodicSlice k hk s len).length = len
  | _, 0 => rfl
  | s, len + 1 => by simp [periodicSlice, length_periodicSlice k hk (s + 1) len]

theorem periodicSlice_append (k : Nat) (hk : 0 < k) :
    ∀ s l1 l2 : Nat,
      periodicSlice k hk s (l1 + l2) =
        periodicSlice k hk s l1 ++ periodicSlice k hk (s + l1) l2
  | s, 0, l2 => by simp [periodicSlice]
  | s, l1 + 1, l2 => by
    have hadd : s + (l1 + 1) = (s + 1) + l1 := by omega
    rw [Nat.add_right_comm l1 1 l2]
    simp only [periodicSlice, List.cons_append, hadd]
    rw [periodicSlice_append k hk (s + 1) l1 l2]

theorem drop_periodicSlice (k : Nat) (hk : 0 < k) :
    ∀ s i len : Nat, i ≤ len →
      (periodicSlice k hk s len).drop i = periodicSlice k hk (s + i) (len - i)
  | s, 0, len, _ => by simp
  | _, _ + 1, 0, hi => by omega
  | s, i + 1, len + 1, hi => by
    simp only [periodicSlice, List.drop_succ_cons]
    have h1 := drop_periodicSlice k hk (s + 1) i len (by omega)
    have h2 : (s + 1) + i = s + (i + 1) := by omega
    have h3 : len + 1 - (i + 1) = len - i := by omega
    rw [h1, h2, h3]

theorem take_periodicSlice (k : Nat) (hk : 0 < k) :
    ∀ s m len : Nat, m ≤ len →
      (periodicSlice k hk s len).take m = periodicSlice k hk s m
  | _, 0, _, _ => by simp [periodicSlice]
  | _, _ + 1, 0, hm => by omega
  | s, m + 1, len + 1, hm => by
    simp only [periodicSlice, List.take_succ_cons]
    rw [take_periodicSlice k hk (s + 1) m len (by omega)]

/-- On a short periodic slice of length `r ≤ k`, each letter `a : Fin k` occurs at most once. -/
theorem letterCount_periodicSlice_le_one (k : Nat) (hk : 0 < k) (a : Fin k) :
    ∀ (r s : Nat), r ≤ k → letterCount a (periodicSlice k hk s r) ≤ 1
  | 0, _, _ => by simp [periodicSlice, letterCount]
  | r + 1, s, hr => by
    simp only [periodicSlice, letterCount_cons]
    by_cases hsa : (⟨s % k, Nat.mod_lt s hk⟩ : Fin k) = a
    · have hzero : ∀ (m t : Nat), m + t ≤ r + 1 → t ≥ 1 →
          letterCount a (periodicSlice k hk (s + t) m) = 0 := by
        intro m
        induction m with
        | zero => intro _ _ _; rfl
        | succ m ih =>
          intro t hmt ht
          simp only [periodicSlice, letterCount_cons]
          have hne : (⟨(s + t) % k, Nat.mod_lt _ hk⟩ : Fin k) ≠ a := by
            intro heq
            have hval1 : s % k = a.val := congrArg Fin.val hsa
            have hval2 : (s + t) % k = a.val := congrArg Fin.val heq
            have hmod : (s + t) % k = s % k := hval2.trans hval1.symm
            have hlt : t < k := by omega
            have hsm : s % k < k := Nat.mod_lt s hk
            have hst : (s + t) % k = (s % k + t) % k := by
              rw [Nat.add_mod s t k, Nat.mod_eq_of_lt hlt]
            rw [hst] at hmod
            by_cases hsum : s % k + t < k
            · rw [Nat.mod_eq_of_lt hsum] at hmod
              omega
            · have hsum2 : s % k + t - k < k := by omega
              have hsub : (s % k + t) % k = s % k + t - k := by
                conv => lhs; rw [show s % k + t = k + (s % k + t - k) by omega]
                rw [Nat.add_mod_left, Nat.mod_eq_of_lt hsum2]
              rw [hsub] at hmod
              omega
          have ih' := ih (t + 1) (by omega) (by omega)
          have hadd : s + t + 1 = s + (t + 1) := by omega
          simp [hne, hadd, ih']
      have hz := hzero r 1 (by omega) (by omega)
      simp [hsa, hz]
    · have ih := letterCount_periodicSlice_le_one k hk a r (s + 1) (by omega)
      simp [hsa, ih]

/-- On a full period of length `k`, each letter `a : Fin k` occurs exactly once. -/
theorem letterCount_periodicSlice_full_eq_one (k : Nat) (hk : 0 < k) (a : Fin k) (s : Nat) :
    letterCount a (periodicSlice k hk s k) = 1 := by
  have hle : letterCount a (periodicSlice k hk s k) ≤ 1 :=
    letterCount_periodicSlice_le_one k hk a k s (Nat.le_refl k)
  let j := (k + a.val - s % k) % k
  have hj_lt : j < k := Nat.mod_lt _ hk
  have hj_mod : (s + j) % k = a.val := by
    have hsm : s % k < k := Nat.mod_lt s hk
    have ha : a.val < k := a.isLt
    have hst : (s + j) % k = (s % k + j) % k := by
      rw [Nat.add_mod s j k, Nat.mod_eq_of_lt hj_lt]
    rw [hst]
    by_cases hle_sa : s % k ≤ a.val
    · have hj_eq : j = a.val - s % k := by
        dsimp [j]
        rw [show k + a.val - s % k = k + (a.val - s % k) by omega,
            Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)]
      rw [hj_eq, show s % k + (a.val - s % k) = a.val by omega, Nat.mod_eq_of_lt ha]
    · have hj_eq : j = k + a.val - s % k := by
        dsimp [j]
        exact Nat.mod_eq_of_lt (by omega)
      rw [hj_eq, show s % k + (k + a.val - s % k) = k + a.val by omega,
          Nat.add_mod_left, Nat.mod_eq_of_lt ha]
  have hsplit : k = j + (1 + (k - 1 - j)) := by omega
  have happ := periodicSlice_append k hk s j (1 + (k - 1 - j))
  rw [← hsplit] at happ
  have happ2 := periodicSlice_append k hk (s + j) 1 (k - 1 - j)
  have h1 : letterCount a (periodicSlice k hk (s + j) 1) = 1 := by
    simp only [periodicSlice, letterCount_cons, letterCount_nil]
    have hfin : (⟨(s + j) % k, Nat.mod_lt _ hk⟩ : Fin k) = a := Fin.ext hj_mod
    simp [hfin]
  have hge : 1 ≤ letterCount a (periodicSlice k hk s k) := by
    rw [happ, happ2, letterCount_append, letterCount_append, h1]
    omega
  omega

/-- Every periodic slice of length `len` has count of `a` in `[len / k, len / k + 1]`. -/
theorem letterCount_periodicSlice_bounds (k : Nat) (hk : 0 < k) (a : Fin k) (s len : Nat) :
    len / k ≤ letterCount a (periodicSlice k hk s len) ∧
    letterCount a (periodicSlice k hk s len) ≤ len / k + 1 := by
  have hdiv : len = k * (len / k) + len % k := (Nat.div_add_mod len k).symm
  have hrem_lt : len % k < k := Nat.mod_lt len hk
  have hblocks : ∀ (q t : Nat),
      letterCount a (periodicSlice k hk t (k * q)) = q := by
    intro q
    induction q with
    | zero => intro t; simp [periodicSlice, letterCount]
    | succ q ih =>
      intro t
      have hmul : k * (q + 1) = k + k * q := by
        rw [Nat.mul_add, Nat.mul_one, Nat.add_comm]
      rw [hmul, periodicSlice_append, letterCount_append,
          letterCount_periodicSlice_full_eq_one k hk a t, ih (t + k)]
      omega
  have heq_cnt : letterCount a (periodicSlice k hk s len) =
      len / k + letterCount a (periodicSlice k hk (s + k * (len / k)) (len % k)) := by
    conv => lhs; rw [hdiv]
    rw [periodicSlice_append, letterCount_append, hblocks (len / k) s]
  have hrem := letterCount_periodicSlice_le_one k hk a (len % k) (s + k * (len / k)) (by omega)
  omega

theorem periodicWord_isBalanced (k : Nat) (hk : 0 < k) (n : Nat) :
    IsBalanced (periodicWord k hk n) := by
  intro u v hu hv hlen a
  rcases (isFactor_iff_slice u (periodicWord k hk n)).mp hu with ⟨i, hi, hu_eq⟩
  rcases (isFactor_iff_slice v (periodicWord k hk n)).mp hv with ⟨j, hj, hv_eq⟩
  have hlen_w : (periodicWord k hk n).length = n := length_periodicSlice k hk 0 n
  have hlu : ((periodicWord k hk n).drop i).take u.length = periodicSlice k hk i u.length := by
    unfold periodicWord
    rw [drop_periodicSlice k hk 0 i n (by omega), Nat.zero_add,
        take_periodicSlice k hk i u.length (n - i) (by omega)]
  have hlv : ((periodicWord k hk n).drop j).take v.length = periodicSlice k hk j v.length := by
    unfold periodicWord
    rw [drop_periodicSlice k hk 0 j n (by omega), Nat.zero_add,
        take_periodicSlice k hk j v.length (n - j) (by omega)]
  rw [← hu_eq, ← hv_eq, hlu, hlv, ← hlen]
  have hb1 := letterCount_periodicSlice_bounds k hk a i u.length
  have hb2 := letterCount_periodicSlice_bounds k hk a j u.length
  rw [natDist_le_one_iff]
  omega

theorem periodicWord_usesAllLetters (k : Nat) (hk : 0 < k) {n : Nat} (hn : k ≤ n) :
    UsesAllLetters k (periodicWord k hk n) := by
  intro a
  rw [← letterCount_pos_iff_mem]
  have hb := (letterCount_periodicSlice_bounds k hk a 0 n).1
  have hdiv : 1 ≤ n / k := (Nat.le_div_iff_mul_le hk).mpr (by omega)
  unfold periodicWord
  omega

theorem periodicWord_hasAtLeastLetters (k r : Nat) (hk : 0 < k) (hr : r ≤ k)
    {n : Nat} (hn : k ≤ n) :
    HasAtLeastLetters r (periodicWord k hk n) := by
  refine ⟨(finList k).take r, take_nodup r (nodup_finList k), ?_, ?_⟩
  · rw [List.length_take, length_finList]; omega
  · intro a _
    exact periodicWord_usesAllLetters k hk hn a

/--
  **Main Theorem 1 (Disproof of Total-Count Finiteness):**
  For every alphabet size `k ≥ 1` (and specifically every multiletter alphabet `k ≥ 2` and `k ≥ 3`),
  the set of surjective `k`-letter balanced words over `Fin k` is **infinite**.
-/
theorem not_finite_surjBalancedWords (k : Nat) (hk : 1 ≤ k) :
    ¬ IsFiniteType { w : Word k // IsBalanced w ∧ UsesAllLetters k w } := by
  rintro ⟨_, elems, _, hall, _⟩
  let maxLen : List { w : Word k // IsBalanced w ∧ UsesAllLetters k w } → Nat :=
    fun xs => xs.foldr (fun s acc => Nat.max s.1.length acc) 0
  have hle_max : ∀ (xs : List { w : Word k // IsBalanced w ∧ UsesAllLetters k w })
      (s : { w : Word k // IsBalanced w ∧ UsesAllLetters k w }),
      s ∈ xs → s.1.length ≤ maxLen xs := by
    intro xs
    induction xs with
    | nil => intro _ hm; nomatch hm
    | cons _ xs ih =>
      intro s hm
      simp only [maxLen, List.foldr_cons]
      cases hm with
      | head _ => exact Nat.le_max_left _ _
      | tail _ hr => exact Nat.le_trans (ih s hr) (Nat.le_max_right _ _)
  let N := Nat.max k (maxLen elems + 1)
  have hN_ge_k : k ≤ N := Nat.le_max_left _ _
  have hN_gt : maxLen elems < N := by
    have : maxLen elems + 1 ≤ N := Nat.le_max_right _ _
    omega
  let wN : { w : Word k // IsBalanced w ∧ UsesAllLetters k w } :=
    ⟨periodicWord k hk N, periodicWord_isBalanced k hk N, periodicWord_usesAllLetters k hk hN_ge_k⟩
  have hbound := hle_max elems wN (hall wN)
  have hlenN : wN.1.length = N := length_periodicSlice k hk 0 N
  omega

theorem not_finite_balancedWords (k : Nat) (hk : 1 ≤ k) :
    ¬ IsFiniteType { w : Word k // IsBalanced w } := by
  rintro ⟨_, elems, _, hall, _⟩
  have hle_max : ∀ (xs : List { w : Word k // IsBalanced w })
      (s : { w : Word k // IsBalanced w }),
      s ∈ xs → s.1.length ≤ xs.foldr (fun s acc => Nat.max s.1.length acc) 0 := by
    intro xs
    induction xs with
    | nil => intro _ hm; nomatch hm
    | cons _ xs ih =>
      intro s hm
      simp only [List.foldr_cons]
      cases hm with
      | head _ => exact Nat.le_max_left _ _
      | tail _ hr => exact Nat.le_trans (ih s hr) (Nat.le_max_right _ _)
  let maxLen := elems.foldr (fun s acc => Nat.max s.1.length acc) 0
  let N := maxLen + 1
  let wN : { w : Word k // IsBalanced w } := ⟨periodicWord k hk N, periodicWord_isBalanced k hk N⟩
  have hbound := hle_max elems wN (hall wN)
  have hlenN : wN.1.length = N := length_periodicSlice k hk 0 N
  omega

theorem not_finite_atLeastBalancedWords (k r : Nat) (hk : 1 ≤ k) (hr : r ≤ k) :
    ¬ IsFiniteType { w : Word k // IsBalanced w ∧ HasAtLeastLetters r w } := by
  rintro ⟨_, elems, _, hall, _⟩
  have hle_max : ∀ (xs : List { w : Word k // IsBalanced w ∧ HasAtLeastLetters r w })
      (s : { w : Word k // IsBalanced w ∧ HasAtLeastLetters r w }),
      s ∈ xs → s.1.length ≤ xs.foldr (fun s acc => Nat.max s.1.length acc) 0 := by
    intro xs
    induction xs with
    | nil => intro _ hm; nomatch hm
    | cons _ xs ih =>
      intro s hm
      simp only [List.foldr_cons]
      cases hm with
      | head _ => exact Nat.le_max_left _ _
      | tail _ hr => exact Nat.le_trans (ih s hr) (Nat.le_max_right _ _)
  let maxLen := elems.foldr (fun s acc => Nat.max s.1.length acc) 0
  let N := Nat.max k (maxLen + 1)
  let wN : { w : Word k // IsBalanced w ∧ HasAtLeastLetters r w } :=
    ⟨periodicWord k hk N,
     periodicWord_isBalanced k hk N,
     periodicWord_hasAtLeastLetters k r hk hr (Nat.le_max_left _ _)⟩
  have hbound := hle_max elems wN (hall wN)
  have hlenN : wN.1.length = N := length_periodicSlice k hk 0 N
  have hgt : maxLen < N := by
    have : maxLen + 1 ≤ N := Nat.le_max_right _ _
    omega
  omega


/-! ## Section 2B: Hubert's Cyclic-Splitting Embedding (`Word 2 → Word k`) -/

def bit0 : Fin 2 := ⟨0, by decide⟩
def bit1 : Fin 2 := ⟨1, by decide⟩

theorem letterCount_periodicSlice_mul (k : Nat) (hk : 0 < k) (a : Fin k) :
    ∀ (q s : Nat), letterCount a (periodicSlice k hk s (k * q)) = q
  | 0, _ => by simp [periodicSlice, letterCount]
  | q + 1, s => by
    have hmul : k * (q + 1) = k + k * q := by
      rw [Nat.mul_add, Nat.mul_one, Nat.add_comm]
    rw [hmul, periodicSlice_append, letterCount_append,
        letterCount_periodicSlice_full_eq_one k hk a s,
        letterCount_periodicSlice_mul k hk a q (s + k)]
    omega

/-- Replace `0 ↦ 0` and the `j`-th `1` (starting from offset `idx`) by `1 + (idx + j) % (k - 1)`. -/
def hubertSplitAux (k : Nat) (hk : 2 ≤ k) : Nat → Word 2 → Word k
  | _, [] => []
  | idx, x :: xs =>
    if x = bit0 then
      ⟨0, by omega⟩ :: hubertSplitAux k hk idx xs
    else
      ⟨1 + idx % (k - 1), by
        have hlt : idx % (k - 1) < k - 1 := Nat.mod_lt idx (by omega)
        omega⟩ :: hubertSplitAux k hk (idx + 1) xs

def hubertSplit (k : Nat) (hk : 2 ≤ k) (u : Word 2) : Word k :=
  hubertSplitAux k hk 0 u

private theorem fin2_dichotomy (x : Fin 2) : x = bit0 ∨ x = bit1 := by
  rcases x with ⟨v, hv⟩
  cases v with
  | zero => exact Or.inl rfl
  | succ v' =>
    cases v' with
    | zero => exact Or.inr rfl
    | succ _ => omega

private theorem bit0_ne_bit1 : bit0 ≠ bit1 := by decide

theorem length_hubertSplitAux (k : Nat) (hk : 2 ≤ k) :
    ∀ (idx : Nat) (u : Word 2), (hubertSplitAux k hk idx u).length = u.length
  | _, [] => rfl
  | idx, x :: xs => by
    simp only [hubertSplitAux]
    split <;> simp [length_hubertSplitAux k hk _ xs]

theorem hubertSplitAux_append (k : Nat) (hk : 2 ≤ k) :
    ∀ (idx : Nat) (u v : Word 2),
      hubertSplitAux k hk idx (u ++ v) =
        hubertSplitAux k hk idx u ++ hubertSplitAux k hk (idx + letterCount bit1 u) v
  | idx, [], v => by simp [hubertSplitAux, letterCount]
  | idx, x :: xs, v => by
    rcases fin2_dichotomy x with rfl | rfl
    · simp only [List.cons_append, hubertSplitAux, ite_true, letterCount_cons, bit0_ne_bit1,
                 ite_false, Nat.zero_add]
      rw [hubertSplitAux_append k hk idx xs v]
    · have hne : bit1 ≠ bit0 := fun h => bit0_ne_bit1 h.symm
      simp only [List.cons_append, hubertSplitAux, hne, ite_false, letterCount_cons, ite_true]
      rw [hubertSplitAux_append k hk (idx + 1) xs v]
      have hadd : idx + 1 + letterCount bit1 xs = idx + (1 + letterCount bit1 xs) := by omega
      rw [hadd]

theorem letterCount_zero_hubertSplitAux (k : Nat) (hk : 2 ≤ k) :
    ∀ (idx : Nat) (u : Word 2),
      letterCount ⟨0, by omega⟩ (hubertSplitAux k hk idx u) = letterCount bit0 u
  | _, [] => rfl
  | idx, x :: xs => by
    rcases fin2_dichotomy x with rfl | rfl
    · simp only [hubertSplitAux, ite_true, letterCount_cons]
      rw [letterCount_zero_hubertSplitAux k hk idx xs]
    · have hne : bit1 ≠ bit0 := fun h => bit0_ne_bit1 h.symm
      have hlt_mod : idx % (k - 1) < k - 1 := Nat.mod_lt idx (by omega)
      have hne0 : (⟨1 + idx % (k - 1), by omega⟩ : Fin k) ≠ ⟨0, by omega⟩ := by
        intro h; have := congrArg Fin.val h; simp at this
      simp only [hubertSplitAux, hne, ite_false, letterCount_cons, hne0, Nat.zero_add]
      exact letterCount_zero_hubertSplitAux k hk (idx + 1) xs

theorem letterCount_pos_hubertSplitAux (k : Nat) (hk : 2 ≤ k) (a : Fin k) (ha : 0 < a.val) :
    ∀ (idx : Nat) (u : Word 2),
      letterCount a (hubertSplitAux k hk idx u) =
        letterCount ⟨a.val - 1, by
          have := a.isLt; omega⟩
          (periodicSlice (k - 1) (by omega) idx (letterCount bit1 u))
  | _, [] => by simp [hubertSplitAux, letterCount, periodicSlice]
  | idx, x :: xs => by
    have ha_lt : a.val < k := a.isLt
    rcases fin2_dichotomy x with rfl | rfl
    · have h0a : (⟨0, by omega⟩ : Fin k) ≠ a := by
        intro h; have := congrArg Fin.val h; simp at this; omega
      simp only [hubertSplitAux, ite_true, letterCount_cons, bit0_ne_bit1, ite_false,
                 h0a, Nat.zero_add]
      exact letterCount_pos_hubertSplitAux k hk a ha idx xs
    · have hne : bit1 ≠ bit0 := fun h => bit0_ne_bit1 h.symm
      have hlt_mod : idx % (k - 1) < k - 1 := Nat.mod_lt idx (by omega)
      have h1_add : 1 + letterCount bit1 xs = letterCount bit1 xs + 1 := by omega
      simp only [hubertSplitAux, hne, ite_false, letterCount_cons, ite_true, h1_add, periodicSlice]
      by_cases hval : 1 + idx % (k - 1) = a.val
      · have hc1 : (⟨1 + idx % (k - 1), by omega⟩ : Fin k) = a := Fin.ext hval
        have hc2 : (⟨idx % (k - 1), hlt_mod⟩ : Fin (k - 1)) = ⟨a.val - 1, by omega⟩ :=
          Fin.ext (by simp; omega)
        simp only [hc1, hc2, ite_true]
        rw [letterCount_pos_hubertSplitAux k hk a ha (idx + 1) xs]
      · have hc1 : (⟨1 + idx % (k - 1), by omega⟩ : Fin k) ≠ a :=
          fun h => hval (congrArg Fin.val h)
        have hc2 : (⟨idx % (k - 1), hlt_mod⟩ : Fin (k - 1)) ≠ ⟨a.val - 1, by omega⟩ := by
          intro h; have hv := congrArg Fin.val h; simp at hv; omega
        simp only [hc1, hc2, ite_false, Nat.zero_add]
        exact letterCount_pos_hubertSplitAux k hk a ha (idx + 1) xs

private theorem div_succ_of_dvd {m c : Nat} (hm : 0 < m) (hrem : (c + 1) % m = 0) :
    c / m + 1 = (c + 1) / m := by
  have hmul : c + 1 = m * ((c + 1) / m) := by
    have hdm := Nat.div_add_mod (c + 1) m
    omega
  have hq_pos : 1 ≤ (c + 1) / m := by
    cases hq0 : (c + 1) / m with
    | zero => rw [hq0, Nat.mul_zero] at hmul; omega
    | succ _ => omega
  have h1 : m * ((c + 1) / m) = m * ((c + 1) / m - 1) + m := by
    conv => lhs; rw [show (c + 1) / m = ((c + 1) / m - 1) + 1 by omega]
    rw [Nat.mul_add, Nat.mul_one]
  have hc_eq : c = m * ((c + 1) / m - 1) + (m - 1) := by omega
  have hm1_div : (m - 1) / m = 0 := Nat.div_eq_of_lt (by omega)
  have hdiv_c : c / m = (c + 1) / m - 1 := by
    calc c / m
      _ = (m * ((c + 1) / m - 1) + (m - 1)) / m := by conv => lhs; rw [hc_eq]
      _ = ((c + 1) / m - 1) + (m - 1) / m := Nat.mul_add_div hm _ _
      _ = ((c + 1) / m - 1) + 0 := by rw [hm1_div]
      _ = (c + 1) / m - 1 := Nat.add_zero _
  omega

private theorem div_succ_of_not_dvd {m c : Nat} (hm : 0 < m) (hrem : (c + 1) % m ≠ 0) :
    (c + 1) / m = c / m := by
  have hdm := Nat.div_add_mod c m
  have hlt_r : c % m < m := Nat.mod_lt c hm
  have hne_r : c % m + 1 ≠ m := by
    intro hr_eq
    have h1 : c + 1 = m * (c / m + 1) := by
      rw [Nat.mul_add, Nat.mul_one]
      omega
    rw [h1, Nat.mul_mod_right] at hrem
    exact hrem rfl
  have hlt_r2 : c % m + 1 < m := by omega
  have h1 : c + 1 = m * (c / m) + (c % m + 1) := by omega
  calc (c + 1) / m
    _ = (m * (c / m) + (c % m + 1)) / m := by rw [h1]
    _ = c / m + (c % m + 1) / m := Nat.mul_add_div hm (c / m) (c % m + 1)
    _ = c / m + 0 := by rw [Nat.div_eq_of_lt hlt_r2]
    _ = c / m := Nat.add_zero _

private theorem periodicSlice_close_counts (m : Nat) (hm : 0 < m) (b : Fin m)
    {s1 s2 c1 c2 : Nat} (hdist : natDist c1 c2 ≤ 1) :
    natDist (letterCount b (periodicSlice m hm s1 c1))
            (letterCount b (periodicSlice m hm s2 c2)) ≤ 1 := by
  rw [natDist_le_one_iff] at hdist ⊢
  have hb1 := letterCount_periodicSlice_bounds m hm b s1 c1
  have hb2 := letterCount_periodicSlice_bounds m hm b s2 c2
  by_cases heq : c1 = c2
  · subst heq; omega
  · by_cases hlt : c1 < c2
    · have hc2 : c2 = c1 + 1 := by omega
      subst hc2
      by_cases hrem : (c1 + 1) % m = 0
      · have hmul : c1 + 1 = m * ((c1 + 1) / m) := by
          have := Nat.div_add_mod (c1 + 1) m; omega
        have hexact : letterCount b (periodicSlice m hm s2 (c1 + 1)) = (c1 + 1) / m := by
          conv => lhs; rw [hmul]
          exact letterCount_periodicSlice_mul m hm b ((c1 + 1) / m) s2
        have hdiv := div_succ_of_dvd hm hrem
        omega
      · have hdiv := div_succ_of_not_dvd hm hrem
        omega
    · have hc1 : c1 = c2 + 1 := by omega
      subst hc1
      by_cases hrem : (c2 + 1) % m = 0
      · have hmul : c2 + 1 = m * ((c2 + 1) / m) := by
          have := Nat.div_add_mod (c2 + 1) m; omega
        have hexact : letterCount b (periodicSlice m hm s1 (c2 + 1)) = (c2 + 1) / m := by
          conv => lhs; rw [hmul]
          exact letterCount_periodicSlice_mul m hm b ((c2 + 1) / m) s1
        have hdiv := div_succ_of_dvd hm hrem
        omega
      · have hdiv := div_succ_of_not_dvd hm hrem
        omega

private theorem isFactor_hubertSplitAux_inv (k : Nat) (hk : 2 ≤ k) {v : Word k} {u : Word 2}
    (hf : IsFactor v (hubertSplit k hk u)) :
    ∃ (u' : Word 2) (idx : Nat),
      IsFactor u' u ∧ u'.length = v.length ∧ v = hubertSplitAux k hk idx u' := by
  rcases (isFactor_iff_slice v (hubertSplit k hk u)).mp hf with ⟨i, hi, hv_eq⟩
  have hlen_hs : (hubertSplit k hk u).length = u.length := length_hubertSplitAux k hk 0 u
  let p := u.take i
  let rest := u.drop i
  let u' := rest.take v.length
  let s := rest.drop v.length
  have hu_decomp : u = p ++ u' ++ s := by
    have h1 : u' ++ s = rest := List.take_append_drop v.length rest
    rw [List.append_assoc, h1, List.take_append_drop]
  have hp_len : p.length = i := by
    dsimp [p]; rw [List.length_take]; omega
  have hu'_len : u'.length = v.length := by
    dsimp [u', rest]; rw [List.length_take, List.length_drop]; omega
  let hs_p := hubertSplitAux k hk 0 p
  let hs_u' := hubertSplitAux k hk (letterCount bit1 p) u'
  let hs_s := hubertSplitAux k hk (letterCount bit1 p + letterCount bit1 u') s
  have hsplit_eq : hubertSplit k hk u = hs_p ++ (hs_u' ++ hs_s) := by
    unfold hubertSplit
    conv => lhs; rw [hu_decomp]
    rw [hubertSplitAux_append, hubertSplitAux_append, List.append_assoc]
    simp [hs_p, hs_u', hs_s, letterCount_append, Nat.zero_add]
  refine ⟨u', letterCount bit1 p, ⟨p, s, hu_decomp.symm⟩, hu'_len, ?_⟩
  rw [← hv_eq, hsplit_eq]
  have hp_hs_len : hs_p.length = i := by
    dsimp [hs_p]; rw [length_hubertSplitAux, hp_len]
  have hu'_hs_len : hs_u'.length = v.length := by
    dsimp [hs_u']; rw [length_hubertSplitAux, hu'_len]
  have hdrop : (hs_p ++ (hs_u' ++ hs_s)).drop i = hs_u' ++ hs_s := by
    rw [← hp_hs_len]
    simp
  rw [hdrop, ← hu'_hs_len]
  simp [hs_u']

/-- **Hubert's Cyclic-Splitting Theorem:** Cyclic splitting of `1`s preserves balancedness for all `k ≥ 2`. -/
theorem hubertSplit_isBalanced (k : Nat) (hk : 2 ≤ k) {u : Word 2} (hu : IsBalanced u) :
    IsBalanced (hubertSplit k hk u) := by
  intro v1 v2 hv1 hv2 hlen a
  rcases isFactor_hubertSplitAux_inv k hk hv1 with ⟨u1, idx1, hfu1, hlu1, rfl⟩
  rcases isFactor_hubertSplitAux_inv k hk hv2 with ⟨u2, idx2, hfu2, hlu2, rfl⟩
  have hlen_u : u1.length = u2.length := by omega
  by_cases ha0 : a.val = 0
  · have hfin : a = ⟨0, by omega⟩ := Fin.ext ha0
    rw [hfin, letterCount_zero_hubertSplitAux, letterCount_zero_hubertSplitAux]
    exact hu u1 u2 hfu1 hfu2 hlen_u bit0
  · have ha_pos : 0 < a.val := by omega
    have ha_lt : a.val < k := a.isLt
    rw [letterCount_pos_hubertSplitAux k hk a ha_pos,
        letterCount_pos_hubertSplitAux k hk a ha_pos]
    exact periodicSlice_close_counts (k - 1) (by omega) ⟨a.val - 1, by omega⟩
      (hu u1 u2 hfu1 hfu2 hlen_u bit1)

theorem hubertSplit_usesAllLetters (k : Nat) (hk : 2 ≤ k) {u : Word 2}
    (h0 : 0 < letterCount bit0 u)
    (h1 : k - 1 ≤ letterCount bit1 u) :
    UsesAllLetters k (hubertSplit k hk u) := by
  intro a
  rw [← letterCount_pos_iff_mem]
  unfold hubertSplit
  by_cases ha0 : a.val = 0
  · have hfin : a = ⟨0, by omega⟩ := Fin.ext ha0
    rw [hfin, letterCount_zero_hubertSplitAux]
    exact h0
  · have ha_pos : 0 < a.val := by omega
    have ha_lt : a.val < k := a.isLt
    rw [letterCount_pos_hubertSplitAux k hk a ha_pos]
    have hb := (letterCount_periodicSlice_bounds (k - 1) (by omega)
      ⟨a.val - 1, by omega⟩ 0 (letterCount bit1 u)).1
    have hdiv : 1 ≤ letterCount bit1 u / (k - 1) :=
      (Nat.le_div_iff_mul_le (by omega)).mpr (by omega)
    omega

/-! ## Section 3: Exact Rationals (`RatQ`), Formal Power Series, Rationality, and Positive Witnesses -/

def listGetD {α : Type u} (d : α) : List α → Nat → α
  | [], _ => d
  | x :: _, 0 => x
  | _ :: xs, n + 1 => listGetD d xs n

theorem listGetD_eq_default {α : Type u} (d : α) :
    ∀ (xs : List α) (n : Nat), xs.length ≤ n → listGetD d xs n = d
  | [], _, _ => rfl
  | _ :: _, 0, h => by simp at h
  | _ :: xs, n + 1, h => listGetD_eq_default d xs n (by simp at h; omega)

theorem listGetD_map {α : Type u} {β : Type v} (f : α → β) (d : α) :
    ∀ (xs : List α) (n : Nat), listGetD (f d) (xs.map f) n = f (listGetD d xs n)
  | [], _ => rfl
  | _ :: _, 0 => rfl
  | _ :: xs, n + 1 => listGetD_map f d xs n

private theorem int_eq_zero_of_mul_nat_pos {a : Int} {d : Nat} (hd : 0 < d)
    (h : a * (d : Int) = 0) : a = 0 := by
  by_cases ha : a = 0
  · exact ha
  · by_cases hpos : 0 < a
    · have h1 : (1 : Int) * (d : Int) ≤ a * (d : Int) :=
        Int.mul_le_mul_of_nonneg_right (by omega) (by omega)
      omega
    · have hneg : 0 < -a := by omega
      have h1 : (1 : Int) * (d : Int) ≤ (-a) * (d : Int) :=
        Int.mul_le_mul_of_nonneg_right (by omega) (by omega)
      have h2 : (-a) * (d : Int) = -(a * (d : Int)) := Int.neg_mul a (d : Int)
      omega

structure RawRat where
  num : Int
  den : Nat
  den_pos : 0 < den

def RawRatEq (x y : RawRat) : Prop :=
  x.num * (y.den : Int) = y.num * (x.den : Int)

theorem rawRatEq_refl (x : RawRat) : RawRatEq x x := rfl

theorem rawRatEq_symm {x y : RawRat} (h : RawRatEq x y) : RawRatEq y x := h.symm

theorem rawRatEq_trans {x y z : RawRat} (hxy : RawRatEq x y) (hyz : RawRatEq y z) :
    RawRatEq x z := by
  unfold RawRatEq at *
  have hcalc : (x.num * (z.den : Int) - z.num * (x.den : Int)) * (y.den : Int) = 0 := by
    rw [Int.sub_mul, Int.mul_right_comm x.num (z.den : Int) (y.den : Int), hxy,
        Int.mul_right_comm y.num (x.den : Int) (z.den : Int), hyz,
        Int.mul_right_comm z.num (y.den : Int) (x.den : Int), Int.sub_self]
  have hzero := int_eq_zero_of_mul_nat_pos y.den_pos hcalc
  omega

/-- Exact rational numbers `ℚ` constructed as quotient of integer fractions. -/
def RatQ : Type := Quot RawRatEq

def ratMk (n : Int) (d : Nat) (hd : 0 < d) : RatQ :=
  Quot.mk RawRatEq ⟨n, d, hd⟩

def ratOfInt (n : Int) : RatQ := ratMk n 1 (by decide)
def ratOfNat (n : Nat) : RatQ := ratOfInt (n : Int)
def ratZero : RatQ := ratOfInt 0
def ratOne : RatQ := ratOfInt 1

theorem ratMk_eq_iff {x y : RawRat} :
    Quot.mk RawRatEq x = Quot.mk RawRatEq y ↔ RawRatEq x y := by
  constructor
  · intro heq
    let propFn : RatQ → Prop :=
      Quot.lift (fun z => RawRatEq x z) (fun a b hab => propext
        ⟨fun hxa => rawRatEq_trans hxa hab,
         fun hxb => rawRatEq_trans hxb (rawRatEq_symm hab)⟩)
    have hx : propFn (Quot.mk RawRatEq x) := rawRatEq_refl x
    rw [heq] at hx
    exact hx
  · exact Quot.sound

def rawAdd (x y : RawRat) : RawRat :=
  ⟨x.num * (y.den : Int) + y.num * (x.den : Int), x.den * y.den, Nat.mul_pos x.den_pos y.den_pos⟩

def rawMul (x y : RawRat) : RawRat :=
  ⟨x.num * y.num, x.den * y.den, Nat.mul_pos x.den_pos y.den_pos⟩

private theorem rawAdd_congr_right (x y1 y2 : RawRat) (hy : RawRatEq y1 y2) :
    RawRatEq (rawAdd x y1) (rawAdd x y2) := by
  unfold RawRatEq rawAdd at *
  simp only [Int.ofNat_mul]
  rw [Int.add_mul, Int.add_mul]
  have h1 : x.num * (y1.den : Int) * ((x.den : Int) * (y2.den : Int)) =
            x.num * (y2.den : Int) * ((x.den : Int) * (y1.den : Int)) := by
    simp [Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
  have h2 : y1.num * (x.den : Int) * ((x.den : Int) * (y2.den : Int)) =
            y2.num * (x.den : Int) * ((x.den : Int) * (y1.den : Int)) := by
    calc y1.num * (x.den : Int) * ((x.den : Int) * (y2.den : Int))
      _ = (y1.num * (y2.den : Int)) * ((x.den : Int) * (x.den : Int)) := by
          simp [Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
      _ = (y2.num * (y1.den : Int)) * ((x.den : Int) * (x.den : Int)) := by rw [hy]
      _ = y2.num * (x.den : Int) * ((x.den : Int) * (y1.den : Int)) := by
          simp [Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
  rw [h1, h2]

private theorem rawAdd_congr_left (x1 x2 y : RawRat) (hx : RawRatEq x1 x2) :
    RawRatEq (rawAdd x1 y) (rawAdd x2 y) := by
  unfold RawRatEq rawAdd at *
  simp only [Int.ofNat_mul]
  rw [Int.add_mul, Int.add_mul]
  have h1 : x1.num * (y.den : Int) * ((x2.den : Int) * (y.den : Int)) =
            x2.num * (y.den : Int) * ((x1.den : Int) * (y.den : Int)) := by
    calc x1.num * (y.den : Int) * ((x2.den : Int) * (y.den : Int))
      _ = (x1.num * (x2.den : Int)) * ((y.den : Int) * (y.den : Int)) := by
          simp [Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
      _ = (x2.num * (x1.den : Int)) * ((y.den : Int) * (y.den : Int)) := by rw [hx]
      _ = x2.num * (y.den : Int) * ((x1.den : Int) * (y.den : Int)) := by
          simp [Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
  have h2 : y.num * (x1.den : Int) * ((x2.den : Int) * (y.den : Int)) =
            y.num * (x2.den : Int) * ((x1.den : Int) * (y.den : Int)) := by
    simp [Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
  rw [h1, h2]

def ratAdd (q1 q2 : RatQ) : RatQ :=
  Quot.lift
    (fun x => Quot.lift (fun y => Quot.mk RawRatEq (rawAdd x y))
      (fun y1 y2 hy => Quot.sound (rawAdd_congr_right x y1 y2 hy)) q2)
    (fun x1 x2 hx => by
      induction q2 using Quot.ind with
      | mk y => exact Quot.sound (rawAdd_congr_left x1 x2 y hx))
    q1

private theorem rawMul_congr_right (x y1 y2 : RawRat) (hy : RawRatEq y1 y2) :
    RawRatEq (rawMul x y1) (rawMul x y2) := by
  unfold RawRatEq rawMul at *
  simp only [Int.ofNat_mul]
  calc x.num * y1.num * ((x.den : Int) * (y2.den : Int))
    _ = (y1.num * (y2.den : Int)) * (x.num * (x.den : Int)) := by
        simp [Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
    _ = (y2.num * (y1.den : Int)) * (x.num * (x.den : Int)) := by rw [hy]
    _ = x.num * y2.num * ((x.den : Int) * (y1.den : Int)) := by
        simp [Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]

private theorem rawMul_congr_left (x1 x2 y : RawRat) (hx : RawRatEq x1 x2) :
    RawRatEq (rawMul x1 y) (rawMul x2 y) := by
  unfold RawRatEq rawMul at *
  simp only [Int.ofNat_mul]
  calc x1.num * y.num * ((x2.den : Int) * (y.den : Int))
    _ = (x1.num * (x2.den : Int)) * (y.num * (y.den : Int)) := by
        simp [Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
    _ = (x2.num * (x1.den : Int)) * (y.num * (y.den : Int)) := by rw [hx]
    _ = x2.num * y.num * ((x1.den : Int) * (y.den : Int)) := by
        simp [Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]

def ratMul (q1 q2 : RatQ) : RatQ :=
  Quot.lift
    (fun x => Quot.lift (fun y => Quot.mk RawRatEq (rawMul x y))
      (fun y1 y2 hy => Quot.sound (rawMul_congr_right x y1 y2 hy)) q2)
    (fun x1 x2 hx => by
      induction q2 using Quot.ind with
      | mk y => exact Quot.sound (rawMul_congr_left x1 x2 y hx))
    q1

theorem ratMk_same_den_add (a b : Int) (d : Nat) (hd : 0 < d) :
    ratAdd (ratMk a d hd) (ratMk b d hd) = ratMk (a + b) d hd := by
  unfold ratAdd ratMk
  apply Quot.sound
  unfold RawRatEq rawAdd
  simp only [Int.ofNat_mul, Int.add_mul]
  simp [Int.mul_assoc]

theorem ratOfInt_add (a b : Int) :
    ratAdd (ratOfInt a) (ratOfInt b) = ratOfInt (a + b) :=
  ratMk_same_den_add a b 1 (by decide)

theorem ratOfInt_mul (a b : Int) :
    ratMul (ratOfInt a) (ratOfInt b) = ratOfInt (a * b) := by
  unfold ratMul ratOfInt ratMk
  apply Quot.sound
  unfold RawRatEq rawMul
  simp

theorem ratOfInt_inj {a b : Int} (h : ratOfInt a = ratOfInt b) : a = b := by
  have heq := ratMk_eq_iff.mp h
  unfold RawRatEq at heq
  simp at heq
  exact heq

/-- Polynomials over `ℚ` (coefficient lists `c_0 + c_1 x + ... + c_d x^d`) and formal power series. -/
abbrev PolyQ : Type := List RatQ
abbrev SeriesQ : Type := Nat → RatQ

def polyCoeffQ (P : PolyQ) (n : Nat) : RatQ :=
  listGetD ratZero P n

def IsZeroPolyQ (Q : PolyQ) : Prop :=
  ∀ n : Nat, polyCoeffQ Q n = ratZero

/-- Cauchy product coefficient `[x^n](Q(x) * F(x))` of a polynomial `Q` and formal power series `F`. -/
def cauchySumQ (Q : PolyQ) (F : SeriesQ) (n : Nat) : Nat → RatQ
  | 0 => ratZero
  | m + 1 =>
    let term := if m ≤ n then ratMul (polyCoeffQ Q m) (F (n - m)) else ratZero
    ratAdd (cauchySumQ Q F n m) term

def mulPolySeriesQ (Q : PolyQ) (F : SeriesQ) : SeriesQ :=
  fun n => cauchySumQ Q F n Q.length

def polyToSeriesQ (P : PolyQ) : SeriesQ :=
  fun n => polyCoeffQ P n

def ofNatSeriesQ (a : Nat → Nat) : SeriesQ :=
  fun n => ratOfNat (a n)

/--
  **Univariate Rational Generating Function Predicate (`ℚ[[x]]`):**
  The ordinary generating function `∑_{n ≥ 0} a(n) x^n` is rational over `ℚ` iff there exist
  polynomials `P, Q ∈ ℚ[x]` with `Q ≠ 0` such that `Q(x) · (∑_{n ≥ 0} a(n) x^n) = P(x)` in `ℚ[[x]]`.
-/
def IsRationalGF (a : Nat → Nat) : Prop :=
  ∃ P Q : PolyQ, ¬ IsZeroPolyQ Q ∧ mulPolySeriesQ Q (ofNatSeriesQ a) = polyToSeriesQ P

/-- Integer-coefficient polynomial and Cauchy product representation. -/
abbrev PolyZ : Type := List Int

def polyCoeffZ (P : PolyZ) (n : Nat) : Int :=
  listGetD 0 P n

def IsZeroPolyZ (Q : PolyZ) : Prop :=
  ∀ n : Nat, polyCoeffZ Q n = 0

def cauchySumZ (Q : PolyZ) (a : Nat → Int) (n : Nat) : Nat → Int
  | 0 => 0
  | m + 1 =>
    let term := if m ≤ n then polyCoeffZ Q m * a (n - m) else 0
    cauchySumZ Q a n m + term

def mulPolySeriesZ (Q : PolyZ) (a : Nat → Int) (n : Nat) : Int :=
  cauchySumZ Q a n Q.length

def IsRationalGF_Z (a : Nat → Int) : Prop :=
  ∃ P Q : PolyZ, ¬ IsZeroPolyZ Q ∧ ∀ n : Nat, mulPolySeriesZ Q a n = polyCoeffZ P n

/-! ### Clearing Denominators: `IsRationalGF a ↔ IsRationalGF_Z (fun n => (a n : Int))` -/

private noncomputable def chooseRaw (q : RatQ) : RawRat :=
  Classical.choose (Quot.exists_rep q)

private theorem chooseRaw_spec (q : RatQ) : Quot.mk RawRatEq (chooseRaw q) = q :=
  Classical.choose_spec (Quot.exists_rep q)

private theorem polyOfZ_coeff (P : PolyZ) (n : Nat) :
    polyCoeffQ (P.map ratOfInt) n = ratOfInt (polyCoeffZ P n) := by
  unfold polyCoeffQ polyCoeffZ ratZero
  exact listGetD_map ratOfInt 0 P n

private theorem cauchySumQ_of_Z (Q : PolyZ) (a : Nat → Nat) (n : Nat) :
    ∀ m : Nat, cauchySumQ (Q.map ratOfInt) (ofNatSeriesQ a) n m =
      ratOfInt (cauchySumZ Q (fun t => (a t : Int)) n m)
  | 0 => rfl
  | m + 1 => by
    simp only [cauchySumQ, cauchySumZ, cauchySumQ_of_Z Q a n m]
    by_cases hle : m ≤ n
    · simp only [hle, ite_true, polyOfZ_coeff, ofNatSeriesQ, ratOfNat, ratOfInt_mul, ratOfInt_add]
    · simp only [hle, ite_false, ratZero, ratOfInt_add, Int.add_zero]

theorem isRationalGF_of_Z {a : Nat → Nat}
    (h : IsRationalGF_Z (fun n => (a n : Int))) : IsRationalGF a := by
  rcases h with ⟨P, Q, hQnz, heq⟩
  refine ⟨P.map ratOfInt, Q.map ratOfInt, ?_, ?_⟩
  · intro hzero
    apply hQnz
    intro n
    have hz := hzero n
    rw [polyOfZ_coeff] at hz
    exact ratOfInt_inj hz
  · funext n
    unfold mulPolySeriesQ polyToSeriesQ
    rw [List.length_map, cauchySumQ_of_Z]
    have hn : cauchySumZ Q (fun t => (a t : Int)) n Q.length = polyCoeffZ P n := heq n
    rw [hn, polyOfZ_coeff]

private def rawZero : RawRat := ⟨0, 1, by decide⟩

private def prodDenRaw : List RawRat → Nat
  | [] => 1
  | r :: rs => r.den * prodDenRaw rs

private theorem prodDenRaw_pos : ∀ rs : List RawRat, 0 < prodDenRaw rs
  | [] => by decide
  | r :: rs => Nat.mul_pos r.den_pos (prodDenRaw_pos rs)

private def rawCoeff (rs : List RawRat) (i : Nat) : RawRat :=
  listGetD rawZero rs i

private theorem rawCoeff_den_dvd :
    ∀ (rs : List RawRat) (i : Nat), (rawCoeff rs i).den ∣ prodDenRaw rs
  | [], _ => by simp [rawCoeff, rawZero, listGetD]
  | r :: rs, 0 => by simp only [rawCoeff, listGetD, prodDenRaw]; exact Nat.dvd_mul_right _ _
  | r :: rs, i + 1 => by
    simp only [rawCoeff, listGetD, prodDenRaw]
    exact Nat.dvd_trans (rawCoeff_den_dvd rs i) (Nat.dvd_mul_left _ _)

private theorem rawCoeff_map_chooseRaw (L : PolyQ) (i : Nat) :
    Quot.mk RawRatEq (rawCoeff (L.map chooseRaw) i) = polyCoeffQ L i := by
  induction L generalizing i with
  | nil => rfl
  | cons q qs ih =>
    cases i with
    | zero => exact chooseRaw_spec q
    | succ i => exact ih i

private def scaleRawPoly (D : Nat) (rs : List RawRat) : PolyZ :=
  rs.map fun r => r.num * ((D / r.den : Nat) : Int)

private theorem scaleRawPoly_coeff (D : Nat) (rs : List RawRat) (i : Nat) :
    polyCoeffZ (scaleRawPoly D rs) i =
      (rawCoeff rs i).num * ((D / (rawCoeff rs i).den : Nat) : Int) := by
  induction rs generalizing i with
  | nil => simp [scaleRawPoly, polyCoeffZ, rawCoeff, rawZero, listGetD]
  | cons r rs ih =>
    cases i with
    | zero => rfl
    | succ i => exact ih i

private theorem ratMk_scale_eq {r : RawRat} {D : Nat} (hD : 0 < D) (hdvd : r.den ∣ D) :
    Quot.mk RawRatEq r = ratMk (r.num * ((D / r.den : Nat) : Int)) D hD := by
  apply Quot.sound
  unfold RawRatEq
  have hmul : (D / r.den) * r.den = D := Nat.div_mul_cancel hdvd
  calc r.num * (D : Int)
    _ = r.num * (((D / r.den) * r.den : Nat) : Int) := by rw [hmul]
    _ = r.num * (((D / r.den : Nat) : Int) * (r.den : Int)) := by rw [Int.ofNat_mul]
    _ = r.num * ((D / r.den : Nat) : Int) * (r.den : Int) := by rw [Int.mul_assoc]

private theorem cauchySumQ_scale_eq (Q : PolyQ) (a : Nat → Nat) (D : Nat) (hD : 0 < D)
    (hdvdQ : ∀ i : Nat, (rawCoeff (Q.map chooseRaw) i).den ∣ D) (n : Nat) :
    ∀ m : Nat,
      cauchySumQ Q (ofNatSeriesQ a) n m =
        ratMk (cauchySumZ (scaleRawPoly D (Q.map chooseRaw)) (fun t => (a t : Int)) n m) D hD
  | 0 => by
    unfold cauchySumQ cauchySumZ ratZero ratOfInt ratMk
    apply Quot.sound
    unfold RawRatEq
    simp
  | m + 1 => by
    simp only [cauchySumQ, cauchySumZ, cauchySumQ_scale_eq Q a D hD hdvdQ n m]
    by_cases hle : m ≤ n
    · simp only [hle, ite_true]
      have hcoeff : polyCoeffQ Q m =
          ratMk ((rawCoeff (Q.map chooseRaw) m).num *
            ((D / (rawCoeff (Q.map chooseRaw) m).den : Nat) : Int)) D hD := by
        rw [← rawCoeff_map_chooseRaw Q m]
        exact ratMk_scale_eq hD (hdvdQ m)
      have hterm : ratMul (polyCoeffQ Q m) (ofNatSeriesQ a (n - m)) =
          ratMk (polyCoeffZ (scaleRawPoly D (Q.map chooseRaw)) m * (a (n - m) : Int)) D hD := by
        rw [hcoeff, scaleRawPoly_coeff]
        unfold ratMul ofNatSeriesQ ratOfNat ratOfInt ratMk
        apply Quot.sound
        unfold RawRatEq rawMul
        simp
      rw [hterm, ratMk_same_den_add]
    · simp only [hle, ite_false]
      have hz : ratZero = ratMk 0 D hD := by
        unfold ratZero ratOfInt ratMk
        apply Quot.sound
        unfold RawRatEq
        simp
      rw [hz, ratMk_same_den_add, Int.add_zero]

theorem isRationalGF_to_Z {a : Nat → Nat} (h : IsRationalGF a) :
    IsRationalGF_Z (fun n => (a n : Int)) := by
  rcases h with ⟨P, Q, hQnz, heq⟩
  let rP := P.map chooseRaw
  let rQ := Q.map chooseRaw
  let D := prodDenRaw rP * prodDenRaw rQ
  have hD : 0 < D := Nat.mul_pos (prodDenRaw_pos rP) (prodDenRaw_pos rQ)
  have hdvdP : ∀ i : Nat, (rawCoeff rP i).den ∣ D := fun i =>
    Nat.dvd_trans (rawCoeff_den_dvd rP i) (Nat.dvd_mul_right _ _)
  have hdvdQ : ∀ i : Nat, (rawCoeff rQ i).den ∣ D := fun i =>
    Nat.dvd_trans (rawCoeff_den_dvd rQ i) (Nat.dvd_mul_left _ _)
  refine ⟨scaleRawPoly D rP, scaleRawPoly D rQ, ?_, ?_⟩
  · intro hzeroZ
    apply hQnz
    intro i
    have hz := hzeroZ i
    rw [scaleRawPoly_coeff] at hz
    have hcoeff : polyCoeffQ Q i =
        ratMk ((rawCoeff rQ i).num * ((D / (rawCoeff rQ i).den : Nat) : Int)) D hD := by
      rw [← rawCoeff_map_chooseRaw Q i]
      exact ratMk_scale_eq hD (hdvdQ i)
    rw [hcoeff, hz]
    unfold ratZero ratOfInt ratMk
    apply Quot.sound
    unfold RawRatEq
    simp
  · intro n
    have hn_eq : mulPolySeriesQ Q (ofNatSeriesQ a) n = polyToSeriesQ P n :=
      congrFun heq n
    unfold mulPolySeriesQ polyToSeriesQ at hn_eq
    rw [cauchySumQ_scale_eq Q a D hD hdvdQ n Q.length] at hn_eq
    have hp_eq : polyCoeffQ P n = ratMk (polyCoeffZ (scaleRawPoly D rP) n) D hD := by
      rw [← rawCoeff_map_chooseRaw P n, scaleRawPoly_coeff]
      exact ratMk_scale_eq hD (hdvdP n)
    rw [hp_eq] at hn_eq
    have hraw := ratMk_eq_iff.mp hn_eq
    unfold RawRatEq at hraw
    have hlen_scale : (scaleRawPoly D rQ).length = Q.length := by
      simp [scaleRawPoly, rQ]
    unfold mulPolySeriesZ
    rw [hlen_scale]
    have hsub : (cauchySumZ (scaleRawPoly D rQ) (fun t => (a t : Int)) n Q.length -
        polyCoeffZ (scaleRawPoly D rP) n) * (D : Int) = 0 := by
      rw [Int.sub_mul, hraw, Int.sub_self]
    have hz := int_eq_zero_of_mul_nat_pos hD hsub
    omega

theorem isRationalGF_iff_Z (a : Nat → Nat) :
    IsRationalGF a ↔ IsRationalGF_Z (fun n => (a n : Int)) :=
  ⟨isRationalGF_to_Z, isRationalGF_of_Z⟩

/-! ### Positive Non-Vacuity Witnesses -/

theorem unary_allWords_eq_replicate :
    ∀ n : Nat, allWords 1 n = [List.replicate n ⟨0, by decide⟩]
  | 0 => rfl
  | n + 1 => by
    simp [allWords, finList, unary_allWords_eq_replicate n, List.replicate_succ]

theorem unary_balancedCount_eq_one (n : Nat) : balancedCount 1 n = 1 := by
  unfold balancedCount balancedWordsList
  rw [unary_allWords_eq_replicate n]
  let u0 : Fin 1 := ⟨0, by decide⟩
  have hrep : List.replicate n u0 = periodicWord 1 (by decide) n := by
    unfold periodicWord
    have haux : ∀ m s : Nat, periodicSlice 1 (by decide) s m = List.replicate m u0 := by
      intro m
      induction m with
      | zero => intro _; rfl
      | succ m ih =>
        intro s
        have hfin : (⟨s % 1, Nat.mod_lt s (by decide)⟩ : Fin 1) = u0 :=
          Fin.ext (Nat.mod_one s)
        simp only [periodicSlice, hfin, List.replicate_succ]
        rw [ih (s + 1)]
    exact (haux n 0).symm
  have hbal : isBalancedBool (List.replicate n u0) = true := by
    rw [isBalancedBool_eq_true_iff, hrep]
    exact periodicWord_isBalanced 1 (by decide) n
  change ([List.replicate n u0].filter isBalancedBool).length = 1
  simp [hbal]

/-- Witness 2: `∑_{n ≥ 0} b_1(n) x^n = 1 / (1 - x)` satisfies `IsRationalGF`. -/
theorem unary_balanced_isRationalGF : IsRationalGF (balancedCount 1) := by
  apply isRationalGF_of_Z
  refine ⟨[1], [1, -1], ?_, ?_⟩
  · intro hz
    have h0 := hz 0
    simp [polyCoeffZ, listGetD] at h0
  · intro n
    simp only [unary_balancedCount_eq_one]
    cases n with
    | zero => rfl
    | succ n => simp [mulPolySeriesZ, cauchySumZ, polyCoeffZ, listGetD]

/-- Witness 3: `∑_{n ≥ 0} (n + 1) x^n = 1 / (1 - x)^2` satisfies `IsRationalGF`. -/
theorem arith_seq_isRationalGF : IsRationalGF (fun n => n + 1) := by
  apply isRationalGF_of_Z
  refine ⟨[1], [1, -2, 1], ?_, ?_⟩
  · intro hz
    have h0 := hz 0
    simp [polyCoeffZ, listGetD] at h0
  · intro n
    cases n with
    | zero => rfl
    | succ n =>
      cases n with
      | zero => rfl
      | succ m =>
        simp only [mulPolySeriesZ, List.length_cons, List.length_nil,
                   cauchySumZ, polyCoeffZ, listGetD, Nat.zero_le, ite_true]
        have h1 : 1 ≤ m + 1 + 1 := by omega
        have h2 : 2 ≤ m + 1 + 1 := by omega
        simp only [h1, h2, ite_true]
        omega

/-- Witness 4: Concrete ternary Fraenkel word `0102010` is balanced and surjective, while `0011` is not balanced. -/
theorem fraenkel7_balanced_surj_witness :
    let w : Word 3 := [⟨0, by decide⟩, ⟨1, by decide⟩, ⟨0, by decide⟩,
                       ⟨2, by decide⟩, ⟨0, by decide⟩, ⟨1, by decide⟩, ⟨0, by decide⟩]
    IsBalanced w ∧ UsesAllLetters 3 w := by
  intro w
  exact ⟨(isBalancedBool_eq_true_iff w).mp (by decide),
         (usesAllLettersBool_eq_true_iff 3 w).mp (by decide)⟩

theorem word_0011_not_balanced_witness :
    let w : Word 2 := [bit0, bit0, bit1, bit1]
    ¬ IsBalanced w := by
  intro w hbal
  have hb : isBalancedBool w = true := (isBalancedBool_eq_true_iff w).mpr hbal
  revert hb
  decide

/-! ## Section 4: Universal Modular Eventual Periodicity of Rational Generating Functions -/

/-- Elementary primality predicate on `Nat`. -/
def IsPrime (p : Nat) : Prop :=
  2 ≤ p ∧ ∀ d : Nat, d ∣ p → d = 1 ∨ d = p

/-- Bézout's identity for `Nat.gcd` proved by strong induction on `a + b`. -/
theorem bezout_nat (a b : Nat) :
    ∃ u v : Int, u * (a : Int) + v * (b : Int) = (Nat.gcd a b : Int) := by
  have haux : ∀ (sum a b : Nat), a + b ≤ sum →
      ∃ u v : Int, u * (a : Int) + v * (b : Int) = (Nat.gcd a b : Int) := by
    intro sum
    induction sum with
    | zero =>
      intro a b hle
      have ha : a = 0 := by omega
      have hb : b = 0 := by omega
      subst ha; subst hb
      exact ⟨0, 0, by simp⟩
    | succ s ih =>
      intro a b hle
      by_cases ha0 : a = 0
      · subst ha0; exact ⟨0, 1, by simp [Nat.gcd_zero_left]⟩
      · by_cases hb0 : b = 0
        · subst hb0; exact ⟨1, 0, by simp [Nat.gcd_zero_right]⟩
        · by_cases hab : a ≤ b
          · by_cases heq : a = b
            · subst heq; exact ⟨1, 0, by simp [Nat.gcd_self]⟩
            · have hgcd : Nat.gcd a b = Nat.gcd a (b - a) := by
                conv => lhs; rw [show b = (b - a) + a by omega]
                rw [Nat.gcd_add_self_right]
              rcases ih a (b - a) (by omega) with ⟨u, v, huv⟩
              refine ⟨u - v, v, ?_⟩
              rw [hgcd, ← huv]
              have hba : ((b - a : Nat) : Int) = (b : Int) - (a : Int) := by omega
              rw [hba, Int.sub_mul, Int.mul_sub]
              omega
          · have hgcd : Nat.gcd a b = Nat.gcd (a - b) b := by
              conv => lhs; rw [show a = (a - b) + b by omega, Nat.gcd_comm]
              rw [Nat.gcd_add_self_right, Nat.gcd_comm]
            rcases ih (a - b) b (by omega) with ⟨u, v, huv⟩
            refine ⟨u, v - u, ?_⟩
            rw [hgcd, ← huv]
            have hab' : ((a - b : Nat) : Int) = (a : Int) - (b : Int) := by omega
            rw [hab', Int.sub_mul, Int.mul_sub]
            omega
  exact haux (a + b) a b (Nat.le_refl _)

theorem coprime_dvd_of_dvd_mul {p a b : Nat} (hcop : Nat.gcd p a = 1) (hdvd : p ∣ a * b) :
    p ∣ b := by
  rcases bezout_nat p a with ⟨u, v, huv⟩
  rw [hcop] at huv
  rcases hdvd with ⟨k, hk⟩
  have h1 : u * (p : Int) + v * (a : Int) = 1 := by omega
  have hmul : (u * (b : Int) + v * (k : Int)) * (p : Int) = (b : Int) := by
    calc (u * (b : Int) + v * (k : Int)) * (p : Int)
      _ = u * (p : Int) * (b : Int) + v * ((p : Int) * (k : Int)) := by
          rw [Int.add_mul]
          simp [Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
      _ = u * (p : Int) * (b : Int) + v * (((p * k : Nat) : Int)) := by rw [Int.ofNat_mul]
      _ = u * (p : Int) * (b : Int) + v * (((a * b : Nat) : Int)) := by rw [← hk]
      _ = (u * (p : Int) + v * (a : Int)) * (b : Int) := by
          rw [Int.ofNat_mul, ← Int.mul_assoc v (a : Int) (b : Int), ← Int.add_mul]
      _ = (b : Int) := by rw [h1, Int.one_mul]
  have hdvd_int : (p : Int) ∣ (b : Int) := ⟨u * (b : Int) + v * (k : Int), by
    rw [Int.mul_comm]; exact hmul.symm⟩
  exact Int.ofNat_dvd.mp hdvd_int

/-- Sequence `a : Nat → Int` is eventually periodic modulo `p`. -/
def EventuallyPeriodicMod (p : Nat) (a : Nat → Int) : Prop :=
  ∃ N0 T : Nat, 0 < T ∧ ∀ n : Nat, N0 ≤ n → a (n + T) % (p : Int) = a n % (p : Int)

theorem eventuallyPeriodicMod_add {p : Nat} {a b : Nat → Int}
    (ha : EventuallyPeriodicMod p a) (hb : EventuallyPeriodicMod p b) :
    EventuallyPeriodicMod p (fun n => a n + b n) := by
  rcases ha with ⟨Na, Ta, hTa, hpa⟩
  rcases hb with ⟨Nb, Tb, hTb, hpb⟩
  refine ⟨Nat.max Na Nb, Ta * Tb, Nat.mul_pos hTa hTb, ?_⟩
  intro n hn
  have hna : Na ≤ n := Nat.le_trans (Nat.le_max_left _ _) hn
  have hnb : Nb ≤ n := Nat.le_trans (Nat.le_max_right _ _) hn
  have iter_a : ∀ k : Nat, a (n + Ta * k) % (p : Int) = a n % (p : Int) := by
    intro k; induction k with
    | zero => simp
    | succ k ih =>
      have h1 : n + Ta * (k + 1) = (n + Ta * k) + Ta := by rw [Nat.mul_add, Nat.mul_one]; omega
      rw [h1, hpa (n + Ta * k) (by omega), ih]
  have iter_b : ∀ k : Nat, b (n + Tb * k) % (p : Int) = b n % (p : Int) := by
    intro k; induction k with
    | zero => simp
    | succ k ih =>
      have h1 : n + Tb * (k + 1) = (n + Tb * k) + Tb := by rw [Nat.mul_add, Nat.mul_one]; omega
      rw [h1, hpb (n + Tb * k) (by omega), ih]
  have hb_step : b (n + Ta * Tb) % (p : Int) = b n % (p : Int) := by
    rw [Nat.mul_comm Ta Tb]; exact iter_b Ta
  rw [Int.add_emod, iter_a Tb, hb_step, ← Int.add_emod]

theorem eventuallyPeriodicMod_neg {p : Nat} {a : Nat → Int}
    (ha : EventuallyPeriodicMod p a) :
    EventuallyPeriodicMod p (fun n => -a n) := by
  rcases ha with ⟨N0, T, hT, hp⟩
  refine ⟨N0, T, hT, fun n hn => ?_⟩
  have h1 : (-a (n + T)) % (p : Int) = (0 - a (n + T)) % (p : Int) := by simp
  have h2 : (-a n) % (p : Int) = (0 - a n) % (p : Int) := by simp
  rw [h1, h2, Int.sub_emod, hp n hn, ← Int.sub_emod]

theorem eventuallyPeriodicMod_shift {p : Nat} {a : Nat → Int} (k : Nat)
    (ha : EventuallyPeriodicMod p a) :
    EventuallyPeriodicMod p (fun n => a (n + k)) := by
  rcases ha with ⟨N0, T, hT, hp⟩
  refine ⟨N0, T, hT, fun n hn => ?_⟩
  dsimp only
  rw [show n + T + k = (n + k) + T by omega]
  exact hp (n + k) (by omega)

theorem eventuallyPeriodicMod_delta2 {p : Nat} {a : Nat → Int}
    (ha : EventuallyPeriodicMod p a) :
    EventuallyPeriodicMod p (fun n => a (n + 2) - 2 * a (n + 1) + a n) := by
  have h2 : EventuallyPeriodicMod p (fun n => a (n + 2)) := eventuallyPeriodicMod_shift 2 ha
  have h1 : EventuallyPeriodicMod p (fun n => a (n + 1)) := eventuallyPeriodicMod_shift 1 ha
  have h_mid : EventuallyPeriodicMod p (fun n => -(a (n + 1) + a (n + 1))) :=
    eventuallyPeriodicMod_neg (eventuallyPeriodicMod_add h1 h1)
  have hsum := eventuallyPeriodicMod_add (eventuallyPeriodicMod_add h2 h_mid) ha
  rcases hsum with ⟨N0, T, hT, hp⟩
  refine ⟨N0, T, hT, fun n hn => ?_⟩
  dsimp only
  have heq1 : a (n + T + 2) - 2 * a (n + T + 1) + a (n + T) =
      a (n + T + 2) + -(a (n + T + 1) + a (n + T + 1)) + a (n + T) := by omega
  have heq2 : a (n + 2) - 2 * a (n + 1) + a n =
      a (n + 2) + -(a (n + 1) + a (n + 1)) + a n := by omega
  rw [heq1, heq2]
  exact hp n hn

theorem eventuallyPeriodicMod_subseq {p : Nat} {a : Nat → Int} (c d : Nat) (hc : 0 < c)
    (ha : EventuallyPeriodicMod p a) :
    EventuallyPeriodicMod p (fun m => a (c * m + d)) := by
  rcases ha with ⟨N0, T, hT, hp⟩
  refine ⟨N0, T, hT, fun m hm => ?_⟩
  dsimp only
  have hge : N0 ≤ c * m + d := by
    have h1 : 1 * m ≤ c * m := Nat.mul_le_mul_right m hc
    omega
  have iter : ∀ k : Nat, a ((c * m + d) + T * k) % (p : Int) = a (c * m + d) % (p : Int) := by
    intro k; induction k with
    | zero => simp
    | succ k ih =>
      have hstep : (c * m + d) + T * (k + 1) = ((c * m + d) + T * k) + T := by
        rw [Nat.mul_add, Nat.mul_one]; omega
      rw [hstep, hp _ (by omega), ih]
  have hrew : c * (m + T) + d = (c * m + d) + T * c := by
    rw [Nat.mul_add, Nat.mul_comm c T]; omega
  rw [hrew]
  exact iter c

private theorem find_mod_inv {p : Nat} (hp : IsPrime p) {x : Int}
    (hnotdvd : ¬ ((p : Int) ∣ x)) :
    ∃ inv : Int, (inv * x) % (p : Int) = 1 % (p : Int) := by
  have hp_pos : 0 < p := by have := hp.1; omega
  let r : Nat := (x % (p : Int)).toNat
  have hx_nonneg : 0 ≤ x % (p : Int) := Int.emod_nonneg x (by omega)
  have hx_lt : x % (p : Int) < (p : Int) := Int.emod_lt_of_pos x (by omega)
  have hr_eq : (r : Int) = x % (p : Int) := Int.toNat_of_nonneg hx_nonneg
  have hr_pos : 0 < r := by
    by_cases hr0 : r = 0
    · exfalso; apply hnotdvd
      have h0 : x % (p : Int) = 0 := by omega
      exact Int.dvd_of_emod_eq_zero h0
    · omega
  have hr_lt : r < p := by omega
  have hcop : Nat.gcd r p = 1 := by
    have hdvd_p : Nat.gcd r p ∣ p := Nat.gcd_dvd_right r p
    have hdvd_r : Nat.gcd r p ∣ r := Nat.gcd_dvd_left r p
    rcases hp.2 (Nat.gcd r p) hdvd_p with hg1 | hgp
    · exact hg1
    · have hle : p ≤ r := Nat.le_of_dvd hr_pos (hgp ▸ hdvd_r)
      omega
  rcases bezout_nat r p with ⟨u, v, huv⟩
  rw [hcop] at huv
  refine ⟨u, ?_⟩
  have h1 : (1 : Int) = u * (r : Int) + (p : Int) * v := by
    rw [Int.mul_comm (p : Int) v]
    omega
  have hmod_r : (u * (r : Int)) % (p : Int) = 1 % (p : Int) := by
    conv => rhs; rw [h1]
    rw [Int.add_mul_emod_self_left]
  have hr_mod : (r : Int) % (p : Int) = (r : Int) :=
    Int.emod_eq_of_lt (by omega) (by omega)
  rw [Int.mul_emod u x, ← hr_eq, ← hr_mod, ← Int.mul_emod, hmod_r]

private theorem cauchySumZ_div_prime (p : Nat) (hp : 2 ≤ p) (Q : PolyZ) (a : Nat → Int)
    (hdvd : ∀ i : Nat, (p : Int) ∣ polyCoeffZ Q i) (n : Nat) :
    ∀ m : Nat,
      cauchySumZ Q a n m = (p : Int) * cauchySumZ (Q.map fun c => c / (p : Int)) a n m
  | 0 => by simp [cauchySumZ]
  | m + 1 => by
    have hcoeff_map : ∀ j : Nat,
        polyCoeffZ (Q.map fun c => c / (p : Int)) j = polyCoeffZ Q j / (p : Int) := by
      intro j
      unfold polyCoeffZ
      have h0 : (0 : Int) / (p : Int) = 0 := Int.zero_ediv _
      rw [← h0, listGetD_map (fun c => c / (p : Int)) 0 Q j, h0]
    simp only [cauchySumZ, cauchySumZ_div_prime p hp Q a hdvd n m]
    by_cases hle : m ≤ n
    · simp only [hle, ite_true, hcoeff_map]
      rcases hdvd m with ⟨q, hq⟩
      have hdiv : polyCoeffZ Q m / (p : Int) = q := by
        rw [hq, Int.mul_comm (p : Int) q, Int.mul_ediv_cancel _ (by omega)]
      rw [hdiv, hq, Int.mul_add, Int.mul_assoc]
    · simp only [hle, ite_false, Int.add_zero]

private theorem exists_reduced_poly_rec (p : Nat) (hp : 2 ≤ p) {a : Nat → Int}
    (h : IsRationalGF_Z a) :
    ∃ (Q : PolyZ) (N1 : Nat),
      (∃ s : Nat, s < Q.length ∧ ¬ ((p : Int) ∣ polyCoeffZ Q s)) ∧
      (∀ N : Nat, N1 ≤ N → mulPolySeriesZ Q a N = 0) := by
  rcases h with ⟨P, Q0, hQ0nz, heq0⟩
  have hex_i0 : ∃ i0 : Nat, i0 < Q0.length ∧ polyCoeffZ Q0 i0 ≠ 0 := by
    by_cases hall : ∀ i : Nat, i < Q0.length → polyCoeffZ Q0 i = 0
    · exfalso; apply hQ0nz; intro n
      by_cases hlt : n < Q0.length
      · exact hall n hlt
      · exact listGetD_eq_default 0 Q0 n (by omega)
    · let bad := (rangeList Q0.length).filter fun i => decide (polyCoeffZ Q0 i ≠ 0)
      cases hbad : bad with
      | nil =>
        exfalso; apply hall; intro i hi
        by_cases hnz : polyCoeffZ Q0 i = 0
        · exact hnz
        · have hm : i ∈ bad := List.mem_filter.mpr ⟨mem_rangeList.mpr hi, decide_eq_true hnz⟩
          rw [hbad] at hm; nomatch hm
      | cons idx _ =>
        have hm : idx ∈ bad := by rw [hbad]; exact List.mem_cons_self
        rcases List.mem_filter.mp hm with ⟨hr, hnz⟩
        exact ⟨idx, mem_rangeList.mp hr, of_decide_eq_true hnz⟩
  rcases hex_i0 with ⟨i0, hi0_lt, hi0_nz⟩
  have htail0 : ∀ N : Nat, P.length ≤ N → mulPolySeriesZ Q0 a N = 0 := by
    intro N hN
    rw [heq0 N]
    exact listGetD_eq_default 0 P N hN
  have hrec : ∀ (bound : Nat) (Q : PolyZ),
      i0 < Q.length → polyCoeffZ Q i0 ≠ 0 → (polyCoeffZ Q i0).natAbs ≤ bound →
      (∀ N : Nat, P.length ≤ N → mulPolySeriesZ Q a N = 0) →
      ∃ Q' : PolyZ,
        (∃ s : Nat, s < Q'.length ∧ ¬ ((p : Int) ∣ polyCoeffZ Q' s)) ∧
        (∀ N : Nat, P.length ≤ N → mulPolySeriesZ Q' a N = 0) := by
    intro bound
    induction bound with
    | zero =>
      intro Q _ hnz hle _
      have : (polyCoeffZ Q i0).natAbs = 0 := by omega
      exact absurd (Int.natAbs_eq_zero.mp this) hnz
    | succ b ih =>
      intro Q hlen hnz hle htail
      by_cases hall_dvd : ∀ s : Nat, s < Q.length → (p : Int) ∣ polyCoeffZ Q s
      · have hdvd_all : ∀ s : Nat, (p : Int) ∣ polyCoeffZ Q s := by
          intro s
          by_cases hs : s < Q.length
          · exact hall_dvd s hs
          · rw [show polyCoeffZ Q s = 0 from listGetD_eq_default 0 Q s (by omega)]
            exact Int.dvd_zero _
        let Q1 := Q.map fun c => c / (p : Int)
        have hcoeff1 : ∀ j : Nat, polyCoeffZ Q1 j = polyCoeffZ Q j / (p : Int) := by
          intro j
          dsimp [Q1]; unfold polyCoeffZ
          have h0 : (0 : Int) / (p : Int) = 0 := Int.zero_ediv _
          rw [← h0, listGetD_map (fun c => c / (p : Int)) 0 Q j, h0]
        rcases hdvd_all i0 with ⟨q0, hq0⟩
        have hq0_eq : polyCoeffZ Q1 i0 = q0 := by
          rw [hcoeff1 i0, hq0, Int.mul_comm (p : Int) q0, Int.mul_ediv_cancel _ (by omega)]
        have hq0_nz : q0 ≠ 0 := by
          intro hz; rw [hz, Int.mul_zero] at hq0; exact hnz hq0
        have habs_lt : q0.natAbs ≤ b := by
          have habs_eq : (polyCoeffZ Q i0).natAbs = p * q0.natAbs := by
            rw [hq0, Int.natAbs_mul, Int.natAbs_ofNat]
          have hpos_q : 0 < q0.natAbs := Int.natAbs_pos.mpr hq0_nz
          have hmul_ge : 2 * q0.natAbs ≤ p * q0.natAbs := Nat.mul_le_mul_right _ hp
          omega
        have htail1 : ∀ N : Nat, P.length ≤ N → mulPolySeriesZ Q1 a N = 0 := by
          intro N hN
          have hz := htail N hN
          unfold mulPolySeriesZ at hz ⊢
          have hlen1 : Q1.length = Q.length := List.length_map _
          rw [hlen1]
          rw [cauchySumZ_div_prime p hp Q a hdvd_all N Q.length, Int.mul_comm] at hz
          exact int_eq_zero_of_mul_nat_pos (by omega) hz
        exact ih Q1 (by simp [Q1, hlen]) (hq0_eq ▸ hq0_nz) (hq0_eq ▸ habs_lt) htail1
      · let nonDvd := (rangeList Q.length).filter fun s => decide (¬ ((p : Int) ∣ polyCoeffZ Q s))
        cases hnd : nonDvd with
        | nil =>
          exfalso; apply hall_dvd; intro s hs
          by_cases hd : (p : Int) ∣ polyCoeffZ Q s
          · exact hd
          · have hm : s ∈ nonDvd := List.mem_filter.mpr ⟨mem_rangeList.mpr hs, decide_eq_true hd⟩
            rw [hnd] at hm; nomatch hm
        | cons s _ =>
          have hm : s ∈ nonDvd := by rw [hnd]; exact List.mem_cons_self
          rcases List.mem_filter.mp hm with ⟨hr, hnot⟩
          exact ⟨Q, ⟨s, mem_rangeList.mp hr, of_decide_eq_true hnot⟩, htail⟩
  rcases hrec (polyCoeffZ Q0 i0).natAbs Q0 hi0_lt hi0_nz (Nat.le_refl _) htail0 with ⟨Q', hs, ht⟩
  exact ⟨Q', P.length, hs, ht⟩

private theorem length_rangeList : ∀ k : Nat, (rangeList k).length = k
  | 0 => rfl
  | k + 1 => by simp [rangeList, length_rangeList k]

private theorem listGetD_append_left {α : Type u} (d : α) :
    ∀ (xs ys : List α) (idx : Nat), idx < xs.length → listGetD d (xs ++ ys) idx = listGetD d xs idx
  | [], _, _, h => by simp at h
  | _ :: _, _, 0, _ => rfl
  | _ :: cs, ys, idx + 1, h => listGetD_append_left d cs ys idx (by simp at h; omega)

private theorem listGetD_snoc {α : Type u} (d : α) :
    ∀ (xs : List α) (y : α), listGetD d (xs ++ [y]) xs.length = y
  | [], _ => rfl
  | _ :: cs, y => listGetD_snoc d cs y

private theorem listGetD_map_rangeList {α : Type u} (d : α) :
    ∀ (m u : Nat) (f : Nat → α), u < m → listGetD d ((rangeList m).map f) u = f u
  | 0, _, _, hu => by omega
  | m + 1, u, f, hu => by
    simp only [rangeList, List.map_append, List.map]
    have hlen : ((rangeList m).map f).length = m := by
      rw [List.length_map, length_rangeList]
    by_cases hum : u < m
    · rw [listGetD_append_left d _ _ u (by omega), listGetD_map_rangeList d m u f hum]
    · have hueq : u = m := by omega
      subst hueq
      have hsnoc := listGetD_snoc d ((rangeList u).map f) (f u)
      rw [hlen] at hsnoc
      exact hsnoc

/-- Finite pigeonhole lemma: among `M + 1` elements of a type covered by a list of length `M`, two collide. -/
private theorem pigeonhole_seq {α : Type} [DecidableEq α] {univ : List α}
    (hall : ∀ x : α, x ∈ univ) (f : Nat → α) :
    ∃ i j : Nat, i < j ∧ j ≤ univ.length ∧ f i = f j := by
  let pairs := (rangeList (univ.length + 1)).flatMap fun i =>
    (rangeList (univ.length + 1)).filter fun j => decide (i < j ∧ f i = f j)
  by_cases hne : pairs = []
  · have hnd_range : ∀ k : Nat, k ≤ univ.length + 1 → ListNodup ((rangeList k).map f) := by
      intro k
      induction k with
      | zero => intro _; exact .nil
      | succ k ih =>
        intro hk
        simp only [rangeList, List.map_append, List.map]
        refine nodup_append (ih (by omega)) (.cons (fun _ hm => nomatch hm) .nil) ?_
        intro x hx y hy hxy
        simp only [List.mem_singleton] at hy
        subst hy
        rcases List.mem_map.mp hx with ⟨i, hi_mem, rfl⟩
        have hi_lt : i < k := mem_rangeList.mp hi_mem
        have hmem_pairs : k ∈ pairs := by
          refine List.mem_flatMap.mpr ⟨i, mem_rangeList.mpr (by omega), ?_⟩
          exact List.mem_filter.mpr ⟨mem_rangeList.mpr (by omega), decide_eq_true ⟨hi_lt, hxy⟩⟩
        rw [hne] at hmem_pairs
        nomatch hmem_pairs
    have hnd_full := hnd_range (univ.length + 1) (Nat.le_refl _)
    have hle := nodup_length_le_of_subset hnd_full (fun x _ => hall x)
    rw [List.length_map, length_rangeList] at hle
    omega
  · rcases List.exists_mem_of_ne_nil pairs hne with ⟨j, hj⟩
    rcases List.mem_flatMap.mp hj with ⟨i, hi_mem, hj_filt⟩
    rcases List.mem_filter.mp hj_filt with ⟨hj_mem, hdec⟩
    rcases of_decide_eq_true hdec with ⟨hij, hfij⟩
    exact ⟨i, j, hij, by have := mem_rangeList.mp hj_mem; omega, hfij⟩

private theorem cauchySumZ_split_at {p : Nat} (Q : PolyZ) (a : Nat → Int) (N s : Nat)
    (hs : s < Q.length) (hN : Q.length ≤ N)
    (hdvd_low : ∀ i : Nat, i < s → (p : Int) ∣ polyCoeffZ Q i) :
    (cauchySumZ Q a N s) % (p : Int) = 0 := by
  induction s with
  | zero => simp [cauchySumZ]
  | succ s ih =>
    simp only [cauchySumZ]
    have hs_le_N : s ≤ N := by omega
    simp only [hs_le_N, ite_true]
    rcases hdvd_low s (by omega) with ⟨q, hq⟩
    have ih' := ih (by omega) (fun i hi => hdvd_low i (by omega))
    rw [hq, Int.add_emod, ih', Int.mul_assoc, Int.mul_emod_right]
    simp

private def listMinDefault (defVal : Nat) : List Nat → Nat
  | [] => defVal
  | [y] => y
  | y :: z :: zs =>
    let m := listMinDefault defVal (z :: zs)
    if y ≤ m then y else m

private theorem listMinDefault_mem_and_le (defVal : Nat) :
    ∀ (xs : List Nat), xs ≠ [] →
      listMinDefault defVal xs ∈ xs ∧ ∀ x ∈ xs, listMinDefault defVal xs ≤ x
  | [], h => absurd rfl h
  | [y], _ => ⟨List.mem_cons_self, fun x hx => by
      cases hx with
      | head _ => exact Nat.le_refl y
      | tail _ h => nomatch h⟩
  | y :: z :: zs, _ => by
    rcases listMinDefault_mem_and_le defVal (z :: zs) (fun h => by cases h) with ⟨hm_in, hm_le⟩
    simp only [listMinDefault]
    by_cases hyle : y ≤ listMinDefault defVal (z :: zs)
    · simp only [hyle, ite_true]
      refine ⟨List.mem_cons_self, fun x hx => ?_⟩
      cases hx with
      | head _ => exact Nat.le_refl y
      | tail _ hr => exact Nat.le_trans hyle (hm_le x hr)
    · simp only [hyle, ite_false]
      refine ⟨List.mem_cons_of_mem y hm_in, fun x hx => ?_⟩
      cases hx with
      | head _ => omega
      | tail _ hr => exact hm_le x hr

/--
  **Universal Modular Eventual Periodicity Theorem:**
  Every sequence `a : Nat → Nat` whose generating function `∑ a(n) x^n` is rational over `ℚ`
  is eventually periodic modulo **every** prime `p ≥ 2`.
-/
theorem isRationalGF_implies_eventuallyPeriodicMod {p : Nat} (hp : IsPrime p)
    {a : Nat → Nat} (hrat : IsRationalGF a) :
    EventuallyPeriodicMod p (fun n => (a n : Int)) := by
  have hZ := isRationalGF_to_Z hrat
  rcases exists_reduced_poly_rec p hp.1 hZ with ⟨Q, N1, ⟨s_wit, hs_wit_lt, hs_wit_nd⟩, htail⟩
  let cand := (rangeList Q.length).filter fun i => decide (¬ ((p : Int) ∣ polyCoeffZ Q i))
  have hcand_ne : cand ≠ [] := by
    intro he
    have hm : s_wit ∈ cand :=
      List.mem_filter.mpr ⟨mem_rangeList.mpr hs_wit_lt, decide_eq_true hs_wit_nd⟩
    rw [he] at hm; nomatch hm
  let s := listMinDefault Q.length cand
  have hs_props : s ∈ cand ∧ ∀ x ∈ cand, s ≤ x :=
    listMinDefault_mem_and_le Q.length cand hcand_ne
  rcases List.mem_filter.mp hs_props.1 with ⟨hs_range, hs_nd_dec⟩
  have hs_lt : s < Q.length := mem_rangeList.mp hs_range
  have hs_nd : ¬ ((p : Int) ∣ polyCoeffZ Q s) := of_decide_eq_true hs_nd_dec
  have hdvd_low : ∀ i : Nat, i < s → (p : Int) ∣ polyCoeffZ Q i := by
    intro i hi
    by_cases hd : (p : Int) ∣ polyCoeffZ Q i
    · exact hd
    · have hm : i ∈ cand := List.mem_filter.mpr ⟨mem_rangeList.mpr (by omega), decide_eq_true hd⟩
      have hle := hs_props.2 i hm
      omega
  rcases find_mod_inv hp hs_nd with ⟨inv, hinv⟩
  let r := Q.length - 1 - s
  let N2 := N1 + Q.length
  have hp_pos : 0 < p := by have := hp.1; omega
  let aInt : Nat → Int := fun n => (a n : Int)
  have hstep_det : ∀ n1 n2 : Nat, N2 ≤ n1 → N2 ≤ n2 →
      (∀ j : Nat, j < r → aInt (n1 + j) % (p : Int) = aInt (n2 + j) % (p : Int)) →
      aInt (n1 + r) % (p : Int) = aInt (n2 + r) % (p : Int) := by
    intro n1 n2 hn1 hn2 hwin
    let M1 := n1 + r + s
    let M2 := n2 + r + s
    have hM1_ge_Q : Q.length ≤ M1 := by omega
    have hM2_ge_Q : Q.length ≤ M2 := by omega
    have hz1 : cauchySumZ Q aInt M1 Q.length = 0 := htail M1 (by omega)
    have hz2 : cauchySumZ Q aInt M2 Q.length = 0 := htail M2 (by omega)
    have htail_cong : ∀ k : Nat, s + 1 + k ≤ Q.length →
        (cauchySumZ Q aInt M1 (s + 1 + k) - cauchySumZ Q aInt M1 (s + 1)) % (p : Int) =
        (cauchySumZ Q aInt M2 (s + 1 + k) - cauchySumZ Q aInt M2 (s + 1)) % (p : Int) := by
      intro k
      induction k with
      | zero => intro _; simp
      | succ k ih =>
        intro hk
        have ih' := ih (by omega)
        have hle1 : s + 1 + k ≤ M1 := by omega
        have hle2 : s + 1 + k ≤ M2 := by omega
        let j := Q.length - 1 - (s + 1 + k)
        have hj_lt : j < r := by omega
        have hidx1 : M1 - (s + 1 + k) = n1 + j := by omega
        have hidx2 : M2 - (s + 1 + k) = n2 + j := by omega
        have h1 : cauchySumZ Q aInt M1 (s + 1 + (k + 1)) - cauchySumZ Q aInt M1 (s + 1) =
            (cauchySumZ Q aInt M1 (s + 1 + k) - cauchySumZ Q aInt M1 (s + 1)) +
            polyCoeffZ Q (s + 1 + k) * aInt (n1 + j) := by
          rw [show s + 1 + (k + 1) = (s + 1 + k) + 1 by omega]
          simp only [cauchySumZ, hle1, ite_true, hidx1]
          omega
        have h2 : cauchySumZ Q aInt M2 (s + 1 + (k + 1)) - cauchySumZ Q aInt M2 (s + 1) =
            (cauchySumZ Q aInt M2 (s + 1 + k) - cauchySumZ Q aInt M2 (s + 1)) +
            polyCoeffZ Q (s + 1 + k) * aInt (n2 + j) := by
          rw [show s + 1 + (k + 1) = (s + 1 + k) + 1 by omega]
          simp only [cauchySumZ, hle2, ite_true, hidx2]
          omega
        rw [h1, h2, Int.add_emod, ih',
            Int.mul_emod (polyCoeffZ Q (s + 1 + k)) (aInt (n1 + j)),
            hwin j hj_lt,
            ← Int.mul_emod, ← Int.add_emod]
    have hrest_eq := htail_cong r (by omega)
    rw [show s + 1 + r = Q.length by omega, hz1, hz2] at hrest_eq
    have hlow1 := cauchySumZ_split_at (p := p) Q aInt M1 s hs_lt hM1_ge_Q hdvd_low
    have hlow2 := cauchySumZ_split_at (p := p) Q aInt M2 s hs_lt hM2_ge_Q hdvd_low
    have hs1 : cauchySumZ Q aInt M1 (s + 1) = cauchySumZ Q aInt M1 s + polyCoeffZ Q s * aInt (n1 + r) := by
      simp only [cauchySumZ, show s ≤ M1 by omega, ite_true, show M1 - s = n1 + r by omega]
    have hs2 : cauchySumZ Q aInt M2 (s + 1) = cauchySumZ Q aInt M2 s + polyCoeffZ Q s * aInt (n2 + r) := by
      simp only [cauchySumZ, show s ≤ M2 by omega, ite_true, show M2 - s = n2 + r by omega]
    have hcs_eq : cauchySumZ Q aInt M1 (s + 1) % (p : Int) = cauchySumZ Q aInt M2 (s + 1) % (p : Int) := by
      have hnn1 : (0 - (0 - cauchySumZ Q aInt M1 (s + 1))) % (p : Int) =
          (0 - (0 - cauchySumZ Q aInt M2 (s + 1))) % (p : Int) := by
        rw [Int.sub_emod, hrest_eq, ← Int.sub_emod]
      simpa [show 0 - (0 - cauchySumZ Q aInt M1 (s + 1)) = cauchySumZ Q aInt M1 (s + 1) by omega,
             show 0 - (0 - cauchySumZ Q aInt M2 (s + 1)) = cauchySumZ Q aInt M2 (s + 1) by omega] using hnn1
    rw [hs1, hs2, Int.add_emod, hlow1, Int.zero_add, Int.emod_emod,
        Int.add_emod, hlow2, Int.zero_add, Int.emod_emod] at hcs_eq
    have hmul_inv : (inv * (polyCoeffZ Q s * aInt (n1 + r))) % (p : Int) =
        (inv * (polyCoeffZ Q s * aInt (n2 + r))) % (p : Int) := by
      rw [Int.mul_emod inv, hcs_eq, ← Int.mul_emod]
    have hlhs : (inv * (polyCoeffZ Q s * aInt (n1 + r))) % (p : Int) = aInt (n1 + r) % (p : Int) := by
      rw [← Int.mul_assoc, Int.mul_emod, hinv, ← Int.mul_emod, Int.one_mul]
    have hrhs : (inv * (polyCoeffZ Q s * aInt (n2 + r))) % (p : Int) = aInt (n2 + r) % (p : Int) := by
      rw [← Int.mul_assoc, Int.mul_emod, hinv, ← Int.mul_emod, Int.one_mul]
    rw [← hlhs, ← hrhs, hmul_inv]
  by_cases hr0 : r = 0
  · refine ⟨N2, 1, by decide, fun n hn => ?_⟩
    have := hstep_det (n + 1) n (by omega) (by omega) (fun _ hj => by omega)
    simpa [hr0] using this
  · let modFin : Int → Fin p := fun z =>
      ⟨(z % (p : Int)).toNat, by
        have hnn : 0 ≤ z % (p : Int) := Int.emod_nonneg z (by omega)
        have hlt : z % (p : Int) < (p : Int) := Int.emod_lt_of_pos z (by omega)
        omega⟩
    have modFin_eq_iff : ∀ z1 z2 : Int, modFin z1 = modFin z2 ↔ z1 % (p : Int) = z2 % (p : Int) := by
      intro z1 z2
      have hnn1 : 0 ≤ z1 % (p : Int) := Int.emod_nonneg z1 (by omega)
      have hnn2 : 0 ≤ z2 % (p : Int) := Int.emod_nonneg z2 (by omega)
      constructor
      · intro h
        have hv : (z1 % (p : Int)).toNat = (z2 % (p : Int)).toNat := congrArg Fin.val h
        have e1 := Int.toNat_of_nonneg hnn1
        have e2 := Int.toNat_of_nonneg hnn2
        omega
      · intro h; apply Fin.ext; dsimp [modFin]; rw [h]
    let stateFn : Nat → { w : Word p // w.length = r } := fun k =>
      ⟨(rangeList r).map (fun j => modFin (aInt (N2 + k + j))), by
        rw [List.length_map, length_rangeList]⟩
    let univSub : List { w : Word p // w.length = r } :=
      attachSubtype (allWords p r) (fun w hw => (mem_allWords_iff p r w).mp hw)
    have hall_sub : ∀ x : { w : Word p // w.length = r }, x ∈ univSub :=
      fun x => mem_attachSubtype _ _ x ((mem_allWords_iff p r x.1).mpr x.2)
    rcases pigeonhole_seq hall_sub stateFn with ⟨i, j, hij, _, heq_state⟩
    have hwin_eq : ∀ u : Nat, u < r →
        aInt (N2 + i + u) % (p : Int) = aInt (N2 + j + u) % (p : Int) := by
      intro u hu
      have hlist_eq : (stateFn i).1 = (stateFn j).1 := congrArg Subtype.val heq_state
      have h1 : listGetD ⟨0, hp_pos⟩ (stateFn i).1 u = modFin (aInt (N2 + i + u)) :=
        listGetD_map_rangeList ⟨0, hp_pos⟩ r u (fun t => modFin (aInt (N2 + i + t))) hu
      have h2 : listGetD ⟨0, hp_pos⟩ (stateFn j).1 u = modFin (aInt (N2 + j + u)) :=
        listGetD_map_rangeList ⟨0, hp_pos⟩ r u (fun t => modFin (aInt (N2 + j + t))) hu
      have hfu : modFin (aInt (N2 + i + u)) = modFin (aInt (N2 + j + u)) := by
        rw [← h1, ← h2, hlist_eq]
      exact (modFin_eq_iff _ _).mp hfu
    let T := j - i
    have hT : 0 < T := by omega
    have hall_m : ∀ m : Nat,
        ∀ u : Nat, u < r →
          aInt (N2 + i + m + u) % (p : Int) = aInt (N2 + i + m + T + u) % (p : Int) := by
      intro m
      induction m with
      | zero =>
        intro u hu
        rw [show N2 + i + 0 + u = N2 + i + u by omega,
            show N2 + i + 0 + T + u = N2 + j + u by omega]
        exact hwin_eq u hu
      | succ m ih =>
        intro u hu
        by_cases hur : u + 1 < r
        · rw [show N2 + i + (m + 1) + u = N2 + i + m + (u + 1) by omega,
              show N2 + i + (m + 1) + T + u = N2 + i + m + T + (u + 1) by omega]
          exact ih (u + 1) hur
        · rw [show N2 + i + (m + 1) + u = (N2 + i + m) + r by omega,
              show N2 + i + (m + 1) + T + u = (N2 + i + m + T) + r by omega]
          exact hstep_det (N2 + i + m) (N2 + i + m + T) (by omega) (by omega) ih
    refine ⟨N2 + i, T, hT, fun n hn => ?_⟩
    have h0 := hall_m (n - (N2 + i)) 0 (by omega)
    rw [show N2 + i + (n - (N2 + i)) + 0 = n by omega,
        show N2 + i + (n - (N2 + i)) + T + 0 = n + T by omega] at h0
    exact h0.symm

/-! ## Section 5: Lipatov's Exact Formula for Binary Balanced Words (`k = 2`) -/

theorem binary_count_sum (w : Word 2) :
    letterCount bit0 w + letterCount bit1 w = w.length := by
  induction w with
  | nil => rfl
  | cons x xs ih =>
    rcases fin2_dichotomy x with rfl | rfl
    · simp only [letterCount_cons, ite_true, bit0_ne_bit1, ite_false, List.length_cons]
      omega
    · have hne : bit1 ≠ bit0 := fun h => bit0_ne_bit1 h.symm
      simp only [letterCount_cons, hne, ite_false, ite_true, List.length_cons]
      omega

/-- Binary balancedness depends only on `1`-counts of equal-length factors. -/
theorem isBalanced_two_iff_ones (w : Word 2) :
    IsBalanced w ↔ ∀ u v : Word 2, IsFactor u w → IsFactor v w → u.length = v.length →
      natDist (letterCount bit1 u) (letterCount bit1 v) ≤ 1 := by
  constructor
  · intro h u v hu hv hlen
    exact h u v hu hv hlen bit1
  · intro h u v hu hv hlen a
    have h1 := h u v hu hv hlen
    rcases fin2_dichotomy a with rfl | rfl
    · have su := binary_count_sum u
      have sv := binary_count_sum v
      rw [natDist_le_one_iff] at h1 ⊢
      omega
    · exact h1

/-- Suffix of length `k` of a word `w`. -/
def suffixOf {α : Type u} (k : Nat) (w : List α) : List α :=
  w.drop (w.length - k)

theorem isFactor_prefix {k : Nat} (m : Nat) (w : Word k) : IsFactor (w.take m) w :=
  ⟨[], w.drop m, by simp [List.take_append_drop]⟩

theorem isFactor_suffix {k : Nat} (m : Nat) (w : Word k) : IsFactor (suffixOf m w) w :=
  ⟨w.take (w.length - m), [], by simp [suffixOf, List.take_append_drop]⟩

theorem length_suffixOf {α : Type u} {m : Nat} {w : List α} (hm : m ≤ w.length) :
    (suffixOf m w).length = m := by
  unfold suffixOf
  rw [List.length_drop]
  omega

/-- Splitting a suffix `suffixOf L1 w` when `L0 ≤ L1 ≤ w.length`. -/
theorem suffixOf_split {α : Type u} {L0 L1 : Nat} {w : List α}
    (h01 : L0 ≤ L1) (h1 : L1 ≤ w.length) :
    ∃ p : List α, p.length = L1 - L0 ∧
      (∃ a b : List α, a ++ p ++ b = w) ∧
      suffixOf L1 w = p ++ suffixOf L0 w := by
  let i1 := w.length - L1
  let d := L1 - L0
  let p := (w.drop i1).take d
  refine ⟨p, ?_, ?_, ?_⟩
  · dsimp [p]; rw [List.length_take, List.length_drop]; omega
  · refine ⟨w.take i1, (w.drop i1).drop d, ?_⟩
    have h := List.take_append_drop d (w.drop i1)
    rw [List.append_assoc, h, List.take_append_drop]
  · unfold suffixOf
    have hdrop : (w.drop i1).drop d = w.drop (w.length - L0) := by
      rw [List.drop_drop, show i1 + d = w.length - L0 by omega]
    have h := List.take_append_drop d (w.drop i1)
    rw [hdrop] at h
    exact h.symm

/-- Splitting a prefix `w.take L1` when `L0 ≤ L1 ≤ w.length`. -/
theorem prefixOf_split {α : Type u} {L0 L1 : Nat} {w : List α}
    (h01 : L0 ≤ L1) (h1 : L1 ≤ w.length) :
    ∃ q : List α, q.length = L1 - L0 ∧
      (∃ a b : List α, a ++ q ++ b = w) ∧
      w.take L1 = w.take L0 ++ q := by
  let q := (w.drop L0).take (L1 - L0)
  refine ⟨q, ?_, ?_, ?_⟩
  · dsimp [q]; rw [List.length_take, List.length_drop]; omega
  · refine ⟨w.take L0, (w.drop L0).drop (L1 - L0), ?_⟩
    have h := List.take_append_drop (L1 - L0) (w.drop L0)
    rw [List.append_assoc, h, List.take_append_drop]
  · have ht : (w.take L1).take L0 = w.take L0 := by
      rw [List.take_take, Nat.min_eq_left h01]
    have hd : (w.take L1).drop L0 = q := by
      dsimp [q]
      have hgen : ∀ (xs : List α) (a b : Nat),
          (xs.take (a + b)).drop a = (xs.drop a).take b := by
        intro xs
        induction xs with
        | nil => intro a b; simp
        | cons _ xs ih =>
          intro a b
          cases a with
          | zero => simp
          | succ a =>
            rw [show a + 1 + b = (a + b) + 1 by omega]
            simp [ih a b]
      conv => lhs; rw [show L1 = L0 + (L1 - L0) by omega]
      exact hgen w L0 (L1 - L0)
    have h := (List.take_append_drop L0 (w.take L1)).symm
    rw [ht, hd] at h
    exact h

/-- Classification of factors of `w ++ [c]`. -/
theorem isFactor_snoc_cases {k : Nat} {u w : Word k} {c : Fin k}
    (hf : IsFactor u (w ++ [c])) :
    IsFactor u w ∨ u = [] ∨ u = w ++ [c] ∨
      (1 ≤ u.length ∧ u.length ≤ w.length ∧ u = suffixOf (u.length - 1) w ++ [c]) := by
  rcases (isFactor_iff_slice u (w ++ [c])).mp hf with ⟨i, hi, hu_eq⟩
  have hlen_wc : (w ++ [c]).length = w.length + 1 := by simp
  by_cases hin : i + u.length ≤ w.length
  · left
    rw [isFactor_iff_slice]
    refine ⟨i, hin, ?_⟩
    have hdrop : (w ++ [c]).drop i = w.drop i ++ [c] :=
      List.drop_append_of_le_length (by omega)
    have hlen_wd : u.length ≤ (w.drop i).length := by rw [List.length_drop]; omega
    rw [hdrop, List.take_append_of_le_length hlen_wd] at hu_eq
    exact hu_eq
  · right
    by_cases hu0 : u.length = 0
    · left; exact List.length_eq_zero_iff.mp hu0
    · right
      by_cases hfull : u.length = w.length + 1
      · left
        have hi0 : i = 0 := by omega
        subst hi0
        rw [List.drop_zero, hfull, ← hlen_wc, List.take_length] at hu_eq
        exact hu_eq.symm
      · right
        have h1 : 1 ≤ u.length := by omega
        have h2 : u.length ≤ w.length := by omega
        have hi_eq : i = w.length - (u.length - 1) := by omega
        refine ⟨h1, h2, ?_⟩
        have hdrop : (w ++ [c]).drop (w.length - (u.length - 1)) =
            suffixOf (u.length - 1) w ++ [c] :=
          List.drop_append_of_le_length (by omega)
        have hlen_suf : (suffixOf (u.length - 1) w ++ [c]).length = u.length := by
          rw [List.length_append, length_suffixOf (by omega), List.length_singleton]
          omega
        calc u
          _ = ((w ++ [c]).drop i).take u.length := hu_eq.symm
          _ = (suffixOf (u.length - 1) w ++ [c]).take u.length := by rw [hi_eq, hdrop]
          _ = (suffixOf (u.length - 1) w ++ [c]).take (suffixOf (u.length - 1) w ++ [c]).length := by
              rw [hlen_suf]
          _ = suffixOf (u.length - 1) w ++ [c] := List.take_length

/-- Classification of factors of `a :: w`. -/
theorem isFactor_cons_cases {k : Nat} {u w : Word k} {a : Fin k}
    (hf : IsFactor u (a :: w)) :
    IsFactor u w ∨ u = [] ∨ u = a :: w ∨
      (1 ≤ u.length ∧ u.length ≤ w.length ∧ u = a :: w.take (u.length - 1)) := by
  rcases (isFactor_iff_slice u (a :: w)).mp hf with ⟨i, hi, hu_eq⟩
  cases i with
  | zero =>
    by_cases hu0 : u.length = 0
    · exact Or.inr (Or.inl (List.length_eq_zero_iff.mp hu0))
    · by_cases hfull : u.length = w.length + 1
      · right; right; left
        simp only [List.drop_zero] at hu_eq
        rw [hfull] at hu_eq
        have hlen_aw : (a :: w).length = w.length + 1 := rfl
        rw [← hlen_aw, List.take_length] at hu_eq
        exact hu_eq.symm
      · right; right; right
        have h1 : 1 ≤ u.length := by omega
        have h2 : u.length ≤ w.length := by simp at hi; omega
        refine ⟨h1, h2, ?_⟩
        let m := u.length - 1
        have hm_eq : u.length = m + 1 := by omega
        calc u
          _ = ((a :: w).drop 0).take u.length := hu_eq.symm
          _ = (a :: w).take (m + 1) := by rw [List.drop_zero, hm_eq]
          _ = a :: w.take m := rfl
  | succ i' =>
    left
    rw [isFactor_iff_slice]
    refine ⟨i', by simp at hi; omega, ?_⟩
    simpa using hu_eq

/-- If `w` is balanced and `w ++ [c]` is NOT balanced, extract the exact suffix obstruction. -/
theorem not_balanced_snoc_obstruction {w : Word 2} {c : Fin 2}
    (hw : IsBalanced w) (hnot : ¬ IsBalanced (w ++ [c])) :
    ∃ (L : Nat) (u : Word 2),
      1 ≤ L ∧ L ≤ w.length ∧ IsFactor u w ∧ u.length = L ∧
      ((c = bit0 ∧ letterCount bit1 u = letterCount bit1 (suffixOf (L - 1) w) + 2) ∨
       (c = bit1 ∧ letterCount bit1 (suffixOf (L - 1) w) = letterCount bit1 u + 1)) := by
  by_cases hex : ∃ (L : Nat) (u : Word 2),
      1 ≤ L ∧ L ≤ w.length ∧ IsFactor u w ∧ u.length = L ∧
      ((c = bit0 ∧ letterCount bit1 u = letterCount bit1 (suffixOf (L - 1) w) + 2) ∨
       (c = bit1 ∧ letterCount bit1 (suffixOf (L - 1) w) = letterCount bit1 u + 1))
  · exact hex
  · exfalso; apply hnot
    rw [isBalanced_two_iff_ones]
    intro x y hx hy hlen
    have check_vs_suf : ∀ (u : Word 2) (L : Nat),
        1 ≤ L → L ≤ w.length → IsFactor u w → u.length = L →
        natDist (letterCount bit1 u) (letterCount bit1 (suffixOf (L - 1) w ++ [c])) ≤ 1 := by
      intro u L hL1 hLw hfu hlu
      rcases suffixOf_split (L0 := L - 1) (L1 := L) (w := w) (by omega) hLw with
        ⟨p, hp_len, _, hsuf_eq⟩
      have hp_le1 : letterCount bit1 p ≤ 1 := by
        have := letterCount_le_length bit1 p; omega
      have hdist_r : natDist (letterCount bit1 u) (letterCount bit1 (suffixOf L w)) ≤ 1 :=
        hw u (suffixOf L w) hfu (isFactor_suffix L w) (by rw [hlu, length_suffixOf hLw]) bit1
      have hsuf_ones : letterCount bit1 (suffixOf L w) =
          letterCount bit1 p + letterCount bit1 (suffixOf (L - 1) w) := by
        rw [hsuf_eq]; exact letterCount_append bit1 _ _
      have hsnoc_ones : letterCount bit1 (suffixOf (L - 1) w ++ [c]) =
          letterCount bit1 (suffixOf (L - 1) w) + letterCount bit1 [c] := letterCount_append bit1 _ _
      rw [natDist_le_one_iff] at hdist_r ⊢
      rcases fin2_dichotomy c with rfl | rfl
      · have hc0 : letterCount bit1 [bit0] = 0 := by simp [letterCount, bit0_ne_bit1]
        by_cases hbad : letterCount bit1 u = letterCount bit1 (suffixOf (L - 1) w) + 2
        · exfalso; exact hex ⟨L, u, hL1, hLw, hfu, hlu, Or.inl ⟨rfl, hbad⟩⟩
        · omega
      · have hc1 : letterCount bit1 [bit1] = 1 := by simp [letterCount]
        by_cases hbad : letterCount bit1 (suffixOf (L - 1) w) = letterCount bit1 u + 1
        · exfalso; exact hex ⟨L, u, hL1, hLw, hfu, hlu, Or.inr ⟨rfl, hbad⟩⟩
        · omega
    rcases isFactor_snoc_cases hx with hfx | rfl | rfl | ⟨hx1, hx2, hxeq⟩
    · rcases isFactor_snoc_cases hy with hfy | rfl | rfl | ⟨_, _, hyeq⟩
      · exact hw x y hfx hfy hlen bit1
      · have hx0 : x = [] := List.length_eq_zero_iff.mp (by simpa using hlen)
        subst hx0; simp [natDist]
      · have := isFactor_length_le hfx; simp at hlen; omega
      · rw [hyeq, ← hlen]
        exact check_vs_suf x x.length (by omega) (by omega) hfx rfl
    · have hy0 : y = [] := List.length_eq_zero_iff.mp (by simpa using hlen.symm)
      subst hy0; simp [natDist]
    · rcases isFactor_snoc_cases hy with hfy | rfl | rfl | ⟨_, hy2, _⟩
      · have := isFactor_length_le hfy; simp at hlen; omega
      · simp at hlen
      · simp [natDist]
      · simp at hlen; omega
    · rcases isFactor_snoc_cases hy with hfy | rfl | rfl | ⟨_, _, hyeq⟩
      · rw [hxeq, hlen]
        have hd := check_vs_suf y y.length (by omega) (by omega) hfy rfl
        rw [natDist_le_one_iff] at hd ⊢; omega
      · simp only [List.length_nil] at hlen; omega
      · simp only [List.length_append, List.length_singleton] at hlen; omega
      · rw [hxeq, hyeq, hlen]; simp [natDist]

/-- **Lemma 1 (Right-Extension of Binary Balanced Words):** Every `w ∈ B_2(n)` extends rightwards! -/
theorem binary_balanced_right_extend {w : Word 2} (hw : IsBalanced w) :
    IsBalanced (w ++ [bit0]) ∨ IsBalanced (w ++ [bit1]) := by
  by_cases h0 : IsBalanced (w ++ [bit0])
  · exact Or.inl h0
  · right
    by_cases h1 : IsBalanced (w ++ [bit1])
    · exact h1
    · exfalso
      rcases not_balanced_snoc_obstruction hw h0 with ⟨L0, u0, hL0_1, hL0_w, hfu0, hlu0, hobs0⟩
      rcases not_balanced_snoc_obstruction hw h1 with ⟨L1, u1, hL1_1, hL1_w, hfu1, hlu1, hobs1⟩
      have ho0 : letterCount bit1 u0 = letterCount bit1 (suffixOf (L0 - 1) w) + 2 := by
        rcases hobs0 with ⟨_, h⟩ | ⟨hc, _⟩
        · exact h
        · exact absurd hc bit0_ne_bit1
      have ho1 : letterCount bit1 (suffixOf (L1 - 1) w) = letterCount bit1 u1 + 1 := by
        rcases hobs1 with ⟨hc, _⟩ | ⟨_, h⟩
        · exact absurd hc.symm bit0_ne_bit1
        · exact h
      by_cases heqL : L0 = L1
      · subst heqL
        have hd := hw u0 u1 hfu0 hfu1 (by omega) bit1
        rw [natDist_le_one_iff] at hd; omega
      · by_cases hlt : L0 < L1
        · rcases suffixOf_split (L0 := L0 - 1) (L1 := L1 - 1) (w := w) (by omega) (by omega) with
            ⟨p, hp_len, hp_fac, hsuf_eq⟩
          have hsuf_ones : letterCount bit1 (suffixOf (L1 - 1) w) =
              letterCount bit1 p + letterCount bit1 (suffixOf (L0 - 1) w) := by
            rw [hsuf_eq]; exact letterCount_append bit1 _ _
          let v := u1.take (L1 - L0)
          let z := u1.drop (L1 - L0)
          have hu1_eq : u1 = v ++ z := (List.take_append_drop _ u1).symm
          have hv_len : v.length = L1 - L0 := by dsimp [v]; rw [List.length_take]; omega
          have hz_len : z.length = L0 := by dsimp [z]; rw [List.length_drop]; omega
          have hfv : IsFactor v w := isFactor_trans (isFactor_prefix _ u1) hfu1
          have hfz : IsFactor z w := isFactor_trans ⟨v, [], by simp [← hu1_eq]⟩ hfu1
          have hvp := hw v p hfv hp_fac (by omega) bit1
          have hzu0 := hw z u0 hfz hfu0 (by omega) bit1
          have hu1_ones : letterCount bit1 u1 = letterCount bit1 v + letterCount bit1 z := by
            conv => lhs; rw [hu1_eq]
            exact letterCount_append bit1 _ _
          rw [natDist_le_one_iff] at hvp hzu0
          omega
        · rcases suffixOf_split (L0 := L1 - 1) (L1 := L0 - 1) (w := w) (by omega) (by omega) with
            ⟨p, hp_len, hp_fac, hsuf_eq⟩
          have hsuf_ones : letterCount bit1 (suffixOf (L0 - 1) w) =
              letterCount bit1 p + letterCount bit1 (suffixOf (L1 - 1) w) := by
            rw [hsuf_eq]; exact letterCount_append bit1 _ _
          let v := u0.take (L0 - L1)
          let z := u0.drop (L0 - L1)
          have hu0_eq : u0 = v ++ z := (List.take_append_drop _ u0).symm
          have hv_len : v.length = L0 - L1 := by dsimp [v]; rw [List.length_take]; omega
          have hz_len : z.length = L1 := by dsimp [z]; rw [List.length_drop]; omega
          have hfv : IsFactor v w := isFactor_trans (isFactor_prefix _ u0) hfu0
          have hfz : IsFactor z w := isFactor_trans ⟨v, [], by simp [← hu0_eq]⟩ hfu0
          have hvp := hw v p hfv hp_fac (by omega) bit1
          have hzu1 := hw z u1 hfz hfu1 (by omega) bit1
          have hu0_ones : letterCount bit1 u0 = letterCount bit1 v + letterCount bit1 z := by
            conv => lhs; rw [hu0_eq]
            exact letterCount_append bit1 _ _
          rw [natDist_le_one_iff] at hvp hzu1
          omega

/-! ### Reversal Symmetry & Sandwich Criterion (`(a :: w) ++ [b]`) -/

theorem letterCount_reverse {k : Nat} (a : Fin k) :
    ∀ w : Word k, letterCount a w.reverse = letterCount a w
  | [] => rfl
  | x :: xs => by
    simp only [List.reverse_cons, letterCount_append, letterCount_cons, letterCount_nil]
    have ih := letterCount_reverse a xs
    omega

theorem isFactor_reverse_iff {k : Nat} (u w : Word k) :
    IsFactor u w.reverse ↔ IsFactor u.reverse w := by
  constructor
  · rintro ⟨p, s, h⟩
    refine ⟨s.reverse, p.reverse, ?_⟩
    have hr := congrArg List.reverse h
    simp only [List.reverse_append, List.reverse_reverse, List.append_assoc] at hr ⊢
    exact hr
  · rintro ⟨p, s, rfl⟩
    refine ⟨s.reverse, p.reverse, ?_⟩
    simp [List.reverse_append, List.append_assoc]

theorem isBalanced_reverse_iff {k : Nat} (w : Word k) :
    IsBalanced w.reverse ↔ IsBalanced w := by
  constructor
  · intro hr u v hu hv hlen a
    have hu' : IsFactor u.reverse w.reverse := (isFactor_reverse_iff u.reverse w).mpr (by simp [hu])
    have hv' : IsFactor v.reverse w.reverse := (isFactor_reverse_iff v.reverse w).mpr (by simp [hv])
    have hd := hr u.reverse v.reverse hu' hv' (by simp [hlen]) a
    simpa [letterCount_reverse] using hd
  · intro hw u v hu hv hlen a
    have hu' : IsFactor u.reverse w := (isFactor_reverse_iff u w).mp hu
    have hv' : IsFactor v.reverse w := (isFactor_reverse_iff v w).mp hv
    have hd := hw u.reverse v.reverse hu' hv' (by simp [hlen]) a
    simpa [letterCount_reverse] using hd

theorem binary_balanced_left_extend {w : Word 2} (hw : IsBalanced w) :
    IsBalanced (bit0 :: w) ∨ IsBalanced (bit1 :: w) := by
  have hrev : IsBalanced w.reverse := (isBalanced_reverse_iff w).mpr hw
  rcases binary_balanced_right_extend hrev with h0 | h1
  · left
    have h0' : IsBalanced (bit0 :: w).reverse := by simpa using h0
    exact (isBalanced_reverse_iff (bit0 :: w)).mp h0'
  · right
    have h1' : IsBalanced (bit1 :: w).reverse := by simpa using h1
    exact (isBalanced_reverse_iff (bit1 :: w)).mp h1'

/-- If `a :: w` is NOT balanced while `w` IS balanced, extract the prefix obstruction. -/
theorem not_balanced_cons_obstruction {w : Word 2} {a : Fin 2}
    (hw : IsBalanced w) (hnot : ¬ IsBalanced (a :: w)) :
    ∃ (L : Nat) (u : Word 2),
      1 ≤ L ∧ L ≤ w.length ∧ IsFactor u w ∧ u.length = L ∧
      ((a = bit0 ∧ letterCount bit1 u = letterCount bit1 (w.take (L - 1)) + 2) ∨
       (a = bit1 ∧ letterCount bit1 (w.take (L - 1)) = letterCount bit1 u + 1)) := by
  have hrev_w : IsBalanced w.reverse := (isBalanced_reverse_iff w).mpr hw
  have hnot_rev : ¬ IsBalanced (w.reverse ++ [a]) := by
    intro h
    have h' : IsBalanced (a :: w).reverse := by simpa using h
    exact hnot ((isBalanced_reverse_iff (a :: w)).mp h')
  rcases not_balanced_snoc_obstruction hrev_w hnot_rev with ⟨L, u, hL1, hLw, hfu, hlu, hobs⟩
  have hlen_rev : w.reverse.length = w.length := List.length_reverse
  have hsuf_rev : (suffixOf (L - 1) w.reverse).reverse = w.take (L - 1) := by
    unfold suffixOf
    rw [List.reverse_drop, List.reverse_reverse, hlen_rev,
        show w.length - (w.length - (L - 1)) = L - 1 by omega]
  have hsuf_ones : letterCount bit1 (suffixOf (L - 1) w.reverse) =
      letterCount bit1 (w.take (L - 1)) := by
    rw [← hsuf_rev, letterCount_reverse]
  refine ⟨L, u.reverse, hL1, by omega, (isFactor_reverse_iff u w).mp hfu,
          by simp [hlu], ?_⟩
  rw [letterCount_reverse bit1 u, ← hsuf_ones]
  exact hobs

/-- **Sandwich Criterion:** Given `IsBalanced (a :: w)` and `IsBalanced (w ++ [b])`, when is `(a :: w) ++ [b]` balanced? -/
theorem sandwich_balanced_iff {w : Word 2} {a b : Fin 2}
    (hl : IsBalanced (a :: w)) (hr : IsBalanced (w ++ [b])) :
    IsBalanced ((a :: w) ++ [b]) ↔
      ∀ k : Nat, 1 ≤ k → k < w.length →
        natDist (letterCount bit1 [a] + letterCount bit1 (w.take k))
                (letterCount bit1 (suffixOf k w) + letterCount bit1 [b]) ≤ 1 := by
  rw [isBalanced_two_iff_ones]
  constructor
  · intro h k hk1 hkw
    have hu : IsFactor (a :: w.take k) ((a :: w) ++ [b]) :=
      ⟨[], w.drop k ++ [b], by
        simp only [List.nil_append, List.cons_append]
        rw [← List.append_assoc, List.take_append_drop]⟩
    have hv : IsFactor (suffixOf k w ++ [b]) ((a :: w) ++ [b]) :=
      ⟨a :: w.take (w.length - k), [], by
        simp only [suffixOf, List.append_nil, List.cons_append]
        rw [← List.append_assoc, List.take_append_drop]⟩
    have hlen : (a :: w.take k).length = (suffixOf k w ++ [b]).length := by
      rw [List.length_cons, List.length_take, Nat.min_eq_left (by omega),
          List.length_append, length_suffixOf (by omega), List.length_singleton]
    have hd := h _ _ hu hv hlen
    have ho1 : letterCount bit1 (a :: w.take k) =
        letterCount bit1 [a] + letterCount bit1 (w.take k) :=
      letterCount_append bit1 [a] (w.take k)
    have ho2 : letterCount bit1 (suffixOf k w ++ [b]) =
        letterCount bit1 (suffixOf k w) + letterCount bit1 [b] :=
      letterCount_append bit1 (suffixOf k w) [b]
    rw [ho1, ho2] at hd
    exact hd
  · intro hcond u v hu hv hlen
    have h_in_aw_or_suf : ∀ z : Word 2, IsFactor z ((a :: w) ++ [b]) →
        IsFactor z (a :: w) ∨ z = (a :: w) ++ [b] ∨
        (1 ≤ z.length ∧ z.length ≤ w.length + 1 ∧ z = suffixOf (z.length - 1) (a :: w) ++ [b]) := by
      intro z hz
      rcases isFactor_snoc_cases hz with h1 | rfl | hfull | ⟨hz1, hz2, hzeq⟩
      · exact Or.inl h1
      · exact Or.inl ⟨[], a :: w, by simp⟩
      · exact Or.inr (Or.inl hfull)
      · exact Or.inr (Or.inr ⟨hz1, by simp at hz2; omega, hzeq⟩)
    have hsuf_in_wb : ∀ z : Word 2,
        1 ≤ z.length → z.length ≤ w.length + 1 →
        z = suffixOf (z.length - 1) (a :: w) ++ [b] →
        IsFactor z (w ++ [b]) ∧
        (z.length ≤ w.length → z = suffixOf (z.length - 1) w ++ [b]) ∧
        (z.length = w.length + 1 → z = w ++ [b]) := by
      intro z hz1 hz2 hzeq
      by_cases hle : z.length ≤ w.length
      · have hs : suffixOf (z.length - 1) (a :: w) = suffixOf (z.length - 1) w := by
          unfold suffixOf
          have hpos : w.length + 1 - (z.length - 1) = (w.length - (z.length - 1)) + 1 := by omega
          simp only [List.length_cons, hpos, List.drop_succ_cons]
        have hz' : z = suffixOf (z.length - 1) w ++ [b] := hzeq.trans (congrArg (· ++ [b]) hs)
        have hfac_wb : IsFactor (suffixOf (z.length - 1) w ++ [b]) (w ++ [b]) :=
          ⟨w.take (w.length - (z.length - 1)), [], by
            rw [suffixOf, List.append_nil, ← List.append_assoc, List.take_append_drop]⟩
        exact ⟨hz' ▸ hfac_wb, fun _ => hz', fun _ => by omega⟩
      · have heq_len : z.length = w.length + 1 := by omega
        have hs : suffixOf (z.length - 1) (a :: w) = w := by
          unfold suffixOf
          rw [List.length_cons, heq_len, show w.length + 1 - (w.length + 1 - 1) = 1 by omega]
          simp
        have hz' : z = w ++ [b] := by rw [hzeq, hs]
        refine ⟨hz' ▸ isFactor_refl _, fun _ => by omega, fun _ => hz'⟩
    have hcross : ∀ x y : Word 2,
        IsFactor x (a :: w) →
        1 ≤ y.length → y.length ≤ w.length + 1 →
        y = suffixOf (y.length - 1) (a :: w) ++ [b] →
        x.length = y.length →
        natDist (letterCount bit1 x) (letterCount bit1 y) ≤ 1 := by
      intro x y hx hy1 hy2 hyeq hxy
      rcases hsuf_in_wb y hy1 hy2 hyeq with ⟨hfy_wb, hy_short, hy_long⟩
      rcases isFactor_cons_cases hx with hfx_w | rfl | hx_aw | ⟨hx1, hx2, hxeq⟩
      · exact hr x y (isFactor_trans hfx_w ⟨[], [b], by simp⟩) hfy_wb hxy bit1
      · simp at hxy; omega
      · have hy' : y = w ++ [b] := hy_long (by simp [hx_aw] at hxy; omega)
        rw [hx_aw, hy']
        have ho1 : letterCount bit1 (a :: w) = letterCount bit1 [a] + letterCount bit1 w :=
          letterCount_append bit1 [a] w
        have ho2 : letterCount bit1 (w ++ [b]) = letterCount bit1 w + letterCount bit1 [b] :=
          letterCount_append bit1 w [b]
        have ha1 : letterCount bit1 [a] ≤ 1 := by have := letterCount_le_length bit1 [a]; simpa using this
        have hb1 : letterCount bit1 [b] ≤ 1 := by have := letterCount_le_length bit1 [b]; simpa using this
        rw [ho1, ho2, natDist_le_one_iff]; omega
      · have hy' : y = suffixOf (x.length - 1) w ++ [b] := by
          rw [hxy]; exact hy_short (by omega)
        by_cases hx_one : x.length = 1
        · have hx_s : x = [a] := by rw [hxeq, hx_one]; simp
          have hy_s : y = [b] := by rw [hy', hx_one]; simp [suffixOf]
          have ha1 : letterCount bit1 [a] ≤ 1 := by have := letterCount_le_length bit1 [a]; simpa using this
          have hb1 : letterCount bit1 [b] ≤ 1 := by have := letterCount_le_length bit1 [b]; simpa using this
          rw [hx_s, hy_s, natDist_le_one_iff]; omega
        · have hk1 : 1 ≤ x.length - 1 := by omega
          have hkw : x.length - 1 < w.length := by omega
          have hc := hcond (x.length - 1) hk1 hkw
          have ho1 : letterCount bit1 x =
              letterCount bit1 [a] + letterCount bit1 (w.take (x.length - 1)) := by
            conv => lhs; rw [hxeq]
            exact letterCount_append bit1 [a] (w.take (x.length - 1))
          have ho2 : letterCount bit1 y =
              letterCount bit1 (suffixOf (x.length - 1) w) + letterCount bit1 [b] := by
            conv => lhs; rw [hy']
            exact letterCount_append bit1 _ [b]
          rw [ho1, ho2]
          exact hc
    rcases h_in_aw_or_suf u hu with hfu_aw | rfl | ⟨hu1, hu2, hueq⟩
    · rcases h_in_aw_or_suf v hv with hfv_aw | rfl | ⟨hv1, hv2, hveq⟩
      · exact hl u v hfu_aw hfv_aw hlen bit1
      · have := isFactor_length_le hfu_aw; simp at hlen this; omega
      · exact hcross u v hfu_aw hv1 hv2 hveq hlen
    · rcases h_in_aw_or_suf v hv with hfv_aw | rfl | ⟨_, hv2, _⟩
      · have := isFactor_length_le hfv_aw; simp at hlen this; omega
      · simp [natDist]
      · simp at hlen; omega
    · rcases h_in_aw_or_suf v hv with hfv_aw | rfl | ⟨hv1, hv2, hveq⟩
      · have hd := hcross v u hfv_aw hu1 hu2 hueq hlen.symm
        rw [natDist_le_one_iff] at hd ⊢; omega
      · simp at hlen; omega
      · rcases hsuf_in_wb u hu1 hu2 hueq with ⟨hfu_wb, _, _⟩
        rcases hsuf_in_wb v hv1 hv2 hveq with ⟨hfv_wb, _, _⟩
        exact hr u v hfu_wb hfv_wb hlen bit1

/-- Same-letter sandwich `(a :: w) ++ [a]` is ALWAYS balanced whenever `a :: w` and `w ++ [a]` are balanced! -/
theorem same_letter_sandwich_balanced {w : Word 2} (a : Fin 2)
    (hl : IsBalanced (a :: w)) (hr : IsBalanced (w ++ [a])) :
    IsBalanced ((a :: w) ++ [a]) := by
  have hw : IsBalanced w := isBalanced_of_isFactor hl ⟨[a], [], by simp⟩
  rw [sandwich_balanced_iff hl hr]
  intro k hk1 hkw
  have hps := hw (w.take k) (suffixOf k w) (isFactor_prefix k w) (isFactor_suffix k w)
    (by rw [List.length_take, Nat.min_eq_left (by omega), length_suffixOf (by omega)]) bit1
  rw [natDist_le_one_iff] at hps ⊢
  omega

/-- **Lemma 2 (Left-Extension of Right-Special Balanced Words):** Every `w ∈ R_2(n)` extends leftwards in `R_2(n+1)`! -/
def IsRightSpecial (w : Word 2) : Prop :=
  IsBalanced (w ++ [bit0]) ∧ IsBalanced (w ++ [bit1])

theorem rightSpecial_isBalanced {w : Word 2} (hr : IsRightSpecial w) : IsBalanced w :=
  isBalanced_of_isFactor hr.1 ⟨[], [bit0], by simp⟩

theorem rightSpecial_left_extend {w : Word 2} (hr : IsRightSpecial w) :
    IsRightSpecial (bit0 :: w) ∨ IsRightSpecial (bit1 :: w) := by
  have hw : IsBalanced w := rightSpecial_isBalanced hr
  by_cases hb0 : IsBalanced (bit0 :: w)
  · by_cases hb1 : IsBalanced (bit1 :: w)
    · have h00 : IsBalanced ((bit0 :: w) ++ [bit0]) := same_letter_sandwich_balanced bit0 hb0 hr.1
      have h11 : IsBalanced ((bit1 :: w) ++ [bit1]) := same_letter_sandwich_balanced bit1 hb1 hr.2
      by_cases h01 : IsBalanced ((bit0 :: w) ++ [bit1])
      · exact Or.inl ⟨h00, h01⟩
      · right
        refine ⟨?_, h11⟩
        by_cases h10 : IsBalanced ((bit1 :: w) ++ [bit0])
        · exact h10
        · exfalso
          have hex0 : ∃ k0 : Nat, 1 ≤ k0 ∧ k0 < w.length ∧
              letterCount bit1 (suffixOf k0 w) = letterCount bit1 (w.take k0) + 1 := by
            by_cases hex : ∃ k0 : Nat, 1 ≤ k0 ∧ k0 < w.length ∧
                letterCount bit1 (suffixOf k0 w) = letterCount bit1 (w.take k0) + 1
            · exact hex
            · exfalso; apply h01
              rw [sandwich_balanced_iff hb0 hr.2]
              intro k hk1 hkw
              have hps := hw (w.take k) (suffixOf k w) (isFactor_prefix k w) (isFactor_suffix k w)
                (by rw [List.length_take, Nat.min_eq_left (by omega), length_suffixOf (by omega)]) bit1
              have ha0 : letterCount bit1 [bit0] = 0 := by simp [letterCount, bit0_ne_bit1]
              have hb1' : letterCount bit1 [bit1] = 1 := by simp [letterCount]
              rw [natDist_le_one_iff] at hps ⊢
              by_cases heq_s : letterCount bit1 (suffixOf k w) = letterCount bit1 (w.take k) + 1
              · exact absurd ⟨k, hk1, hkw, heq_s⟩ hex
              · omega
          have hex1 : ∃ k1 : Nat, 1 ≤ k1 ∧ k1 < w.length ∧
              letterCount bit1 (w.take k1) = letterCount bit1 (suffixOf k1 w) + 1 := by
            by_cases hex : ∃ k1 : Nat, 1 ≤ k1 ∧ k1 < w.length ∧
                letterCount bit1 (w.take k1) = letterCount bit1 (suffixOf k1 w) + 1
            · exact hex
            · exfalso; apply h10
              rw [sandwich_balanced_iff hb1 hr.1]
              intro k hk1 hkw
              have hps := hw (w.take k) (suffixOf k w) (isFactor_prefix k w) (isFactor_suffix k w)
                (by rw [List.length_take, Nat.min_eq_left (by omega), length_suffixOf (by omega)]) bit1
              have ha1 : letterCount bit1 [bit1] = 1 := by simp [letterCount]
              have hb0' : letterCount bit1 [bit0] = 0 := by simp [letterCount, bit0_ne_bit1]
              rw [natDist_le_one_iff] at hps ⊢
              by_cases heq_p : letterCount bit1 (w.take k) = letterCount bit1 (suffixOf k w) + 1
              · exact absurd ⟨k, hk1, hkw, heq_p⟩ hex
              · omega
          rcases hex0 with ⟨k0, hk0_1, hk0_w, h_k0⟩
          rcases hex1 with ⟨k1, hk1_1, hk1_w, h_k1⟩
          by_cases heqk : k0 = k1
          · subst heqk; omega
          · by_cases hlt : k0 < k1
            · rcases prefixOf_split (L0 := k0) (L1 := k1) (w := w) (by omega) (by omega) with
                ⟨r_seg, hr_len, hr_fac, hpre_eq⟩
              rcases suffixOf_split (L0 := k0) (L1 := k1) (w := w) (by omega) (by omega) with
                ⟨q_seg, hq_len, hq_fac, hsuf_eq⟩
              have hpre_ones : letterCount bit1 (w.take k1) =
                  letterCount bit1 (w.take k0) + letterCount bit1 r_seg := by
                rw [hpre_eq]; exact letterCount_append bit1 _ _
              have hsuf_ones : letterCount bit1 (suffixOf k1 w) =
                  letterCount bit1 q_seg + letterCount bit1 (suffixOf k0 w) := by
                rw [hsuf_eq]; exact letterCount_append bit1 _ _
              have hd := hw r_seg q_seg hr_fac hq_fac (by omega) bit1
              rw [natDist_le_one_iff] at hd; omega
            · rcases prefixOf_split (L0 := k1) (L1 := k0) (w := w) (by omega) (by omega) with
                ⟨r_seg, hr_len, hr_fac, hpre_eq⟩
              rcases suffixOf_split (L0 := k1) (L1 := k0) (w := w) (by omega) (by omega) with
                ⟨q_seg, hq_len, hq_fac, hsuf_eq⟩
              have hpre_ones : letterCount bit1 (w.take k0) =
                  letterCount bit1 (w.take k1) + letterCount bit1 r_seg := by
                rw [hpre_eq]; exact letterCount_append bit1 _ _
              have hsuf_ones : letterCount bit1 (suffixOf k0 w) =
                  letterCount bit1 q_seg + letterCount bit1 (suffixOf k1 w) := by
                rw [hsuf_eq]; exact letterCount_append bit1 _ _
              have hd := hw r_seg q_seg hr_fac hq_fac (by omega) bit1
              rw [natDist_le_one_iff] at hd; omega
    · left
      refine ⟨same_letter_sandwich_balanced bit0 hb0 hr.1, ?_⟩
      rw [sandwich_balanced_iff hb0 hr.2]
      intro k hk1 hkw
      have hps := hw (w.take k) (suffixOf k w) (isFactor_prefix k w) (isFactor_suffix k w)
        (by rw [List.length_take, Nat.min_eq_left (by omega), length_suffixOf (by omega)]) bit1
      have ha0 : letterCount bit1 [bit0] = 0 := by simp [letterCount, bit0_ne_bit1]
      have hb1' : letterCount bit1 [bit1] = 1 := by simp [letterCount]
      rw [natDist_le_one_iff] at hps ⊢
      by_cases hbad : letterCount bit1 (suffixOf k w) = letterCount bit1 (w.take k) + 1
      · exfalso
        rcases not_balanced_cons_obstruction hw hb1 with ⟨L1, u1, hL1_1, hL1_w, hfu1, hlu1, hobs1⟩
        have ho1 : letterCount bit1 (w.take (L1 - 1)) = letterCount bit1 u1 + 1 := by
          rcases hobs1 with ⟨hc, _⟩ | ⟨_, h⟩
          · exact absurd hc.symm bit0_ne_bit1
          · exact h
        let s1 := suffixOf k w ++ [bit1]
        have hfs1 : IsFactor s1 (w ++ [bit1]) :=
          ⟨w.take (w.length - k), [], by
            dsimp [s1, suffixOf]
            rw [List.append_nil, ← List.append_assoc, List.take_append_drop]⟩
        have hls1 : s1.length = k + 1 := by
          dsimp [s1]; rw [List.length_append, length_suffixOf (by omega), List.length_singleton]
        have hos1 : letterCount bit1 s1 = letterCount bit1 (w.take k) + 2 := by
          dsimp [s1]; rw [letterCount_append, hb1', hbad]
        have hfu1_wb : IsFactor u1 (w ++ [bit1]) := isFactor_trans hfu1 ⟨[], [bit1], by simp⟩
        by_cases heqL : k + 1 = L1
        · have hk_eq : L1 - 1 = k := by omega
          rw [hk_eq] at ho1
          have hd := hr.2 s1 u1 hfs1 hfu1_wb (by omega) bit1
          rw [natDist_le_one_iff] at hd; omega
        · by_cases hlt : k + 1 < L1
          · rcases prefixOf_split (L0 := k) (L1 := L1 - 1) (w := w) (by omega) (by omega) with
              ⟨p, hp_len, hp_fac, hpre_eq⟩
            have hpre_ones : letterCount bit1 (w.take (L1 - 1)) =
                letterCount bit1 (w.take k) + letterCount bit1 p := by
              rw [hpre_eq]; exact letterCount_append bit1 _ _
            let z := u1.take (k + 1)
            let v := u1.drop (k + 1)
            have hu1_eq : u1 = z ++ v := (List.take_append_drop _ u1).symm
            have hfz : IsFactor z (w ++ [bit1]) := isFactor_trans (isFactor_prefix _ u1) hfu1_wb
            have hfv : IsFactor v w := isFactor_trans ⟨z, [], by simp [← hu1_eq]⟩ hfu1
            have hzs1 := hr.2 z s1 hfz hfs1 (by dsimp [z]; rw [List.length_take]; omega) bit1
            have hvp := hw v p hfv hp_fac (by dsimp [v]; rw [List.length_drop]; omega) bit1
            have hu1_ones : letterCount bit1 u1 = letterCount bit1 z + letterCount bit1 v := by
              conv => lhs; rw [hu1_eq]
              exact letterCount_append bit1 _ _
            rw [natDist_le_one_iff] at hzs1 hvp
            omega
          · rcases prefixOf_split (L0 := L1 - 1) (L1 := k) (w := w) (by omega) (by omega) with
              ⟨p, hp_len, hp_fac, hpre_eq⟩
            have hpre_ones : letterCount bit1 (w.take k) =
                letterCount bit1 (w.take (L1 - 1)) + letterCount bit1 p := by
              rw [hpre_eq]; exact letterCount_append bit1 _ _
            let z := s1.take L1
            let v := s1.drop L1
            have hs1_eq : s1 = z ++ v := (List.take_append_drop _ s1).symm
            have hfz : IsFactor z (w ++ [bit1]) := isFactor_trans (isFactor_prefix _ s1) hfs1
            have hfv : IsFactor v (w ++ [bit1]) := isFactor_trans ⟨z, [], by simp [← hs1_eq]⟩ hfs1
            have hfp_wb : IsFactor p (w ++ [bit1]) := isFactor_trans hp_fac ⟨[], [bit1], by simp⟩
            have hzu1 := hr.2 z u1 hfz hfu1_wb (by dsimp [z]; rw [List.length_take]; omega) bit1
            have hvp := hr.2 v p hfv hfp_wb (by dsimp [v]; rw [List.length_drop]; omega) bit1
            have hs1_ones : letterCount bit1 s1 = letterCount bit1 z + letterCount bit1 v := by
              conv => lhs; rw [hs1_eq]
              exact letterCount_append bit1 _ _
            rw [natDist_le_one_iff] at hzu1 hvp
            omega
      · omega
  · have hb1 : IsBalanced (bit1 :: w) := by
      rcases binary_balanced_left_extend hw with h0 | h1
      · exact absurd h0 hb0
      · exact h1
    right
    refine ⟨?_, same_letter_sandwich_balanced bit1 hb1 hr.2⟩
    rw [sandwich_balanced_iff hb1 hr.1]
    intro k hk1 hkw
    have hps := hw (w.take k) (suffixOf k w) (isFactor_prefix k w) (isFactor_suffix k w)
      (by rw [List.length_take, Nat.min_eq_left (by omega), length_suffixOf (by omega)]) bit1
    have ha1 : letterCount bit1 [bit1] = 1 := by simp [letterCount]
    have hb0' : letterCount bit1 [bit0] = 0 := by simp [letterCount, bit0_ne_bit1]
    rw [natDist_le_one_iff] at hps ⊢
    by_cases hbad : letterCount bit1 (w.take k) = letterCount bit1 (suffixOf k w) + 1
    · exfalso
      rcases not_balanced_cons_obstruction hw hb0 with ⟨L0, u0, hL0_1, hL0_w, hfu0, hlu0, hobs0⟩
      have ho0 : letterCount bit1 u0 = letterCount bit1 (w.take (L0 - 1)) + 2 := by
        rcases hobs0 with ⟨_, h⟩ | ⟨hc, _⟩
        · exact h
        · exact absurd hc bit0_ne_bit1
      let s0 := suffixOf k w ++ [bit0]
      have hfs0 : IsFactor s0 (w ++ [bit0]) :=
        ⟨w.take (w.length - k), [], by
          dsimp [s0, suffixOf]
          rw [List.append_nil, ← List.append_assoc, List.take_append_drop]⟩
      have hls0 : s0.length = k + 1 := by
        dsimp [s0]; rw [List.length_append, length_suffixOf (by omega), List.length_singleton]
      have hos0 : letterCount bit1 s0 + 1 = letterCount bit1 (w.take k) := by
        dsimp [s0]; rw [letterCount_append, hb0']; omega
      have hfu0_wb : IsFactor u0 (w ++ [bit0]) := isFactor_trans hfu0 ⟨[], [bit0], by simp⟩
      by_cases heqL : k + 1 = L0
      · have hk_eq : L0 - 1 = k := by omega
        rw [hk_eq] at ho0
        have hd := hr.1 u0 s0 hfu0_wb hfs0 (by omega) bit1
        rw [natDist_le_one_iff] at hd; omega
      · by_cases hlt : k + 1 < L0
        · rcases prefixOf_split (L0 := k) (L1 := L0 - 1) (w := w) (by omega) (by omega) with
            ⟨p, hp_len, hp_fac, hpre_eq⟩
          have hpre_ones : letterCount bit1 (w.take (L0 - 1)) =
              letterCount bit1 (w.take k) + letterCount bit1 p := by
            rw [hpre_eq]; exact letterCount_append bit1 _ _
          let z := u0.take (k + 1)
          let v := u0.drop (k + 1)
          have hu0_eq : u0 = z ++ v := (List.take_append_drop _ u0).symm
          have hfz : IsFactor z (w ++ [bit0]) := isFactor_trans (isFactor_prefix _ u0) hfu0_wb
          have hfv : IsFactor v w := isFactor_trans ⟨z, [], by simp [← hu0_eq]⟩ hfu0
          have hzs0 := hr.1 z s0 hfz hfs0 (by dsimp [z]; rw [List.length_take]; omega) bit1
          have hvp := hw v p hfv hp_fac (by dsimp [v]; rw [List.length_drop]; omega) bit1
          have hu0_ones : letterCount bit1 u0 = letterCount bit1 z + letterCount bit1 v := by
            conv => lhs; rw [hu0_eq]
            exact letterCount_append bit1 _ _
          rw [natDist_le_one_iff] at hzs0 hvp
          omega
        · rcases prefixOf_split (L0 := L0 - 1) (L1 := k) (w := w) (by omega) (by omega) with
            ⟨p, hp_len, hp_fac, hpre_eq⟩
          have hpre_ones : letterCount bit1 (w.take k) =
              letterCount bit1 (w.take (L0 - 1)) + letterCount bit1 p := by
            rw [hpre_eq]; exact letterCount_append bit1 _ _
          let z := s0.take L0
          let v := s0.drop L0
          have hs0_eq : s0 = z ++ v := (List.take_append_drop _ s0).symm
          have hfz : IsFactor z (w ++ [bit0]) := isFactor_trans (isFactor_prefix _ s0) hfs0
          have hfv : IsFactor v (w ++ [bit0]) := isFactor_trans ⟨z, [], by simp [← hs0_eq]⟩ hfs0
          have hfp_wb : IsFactor p (w ++ [bit0]) := isFactor_trans hp_fac ⟨[], [bit0], by simp⟩
          have hzu0 := hr.1 z u0 hfz hfu0_wb (by dsimp [z]; rw [List.length_take]; omega) bit1
          have hvp := hr.1 v p hfv hfp_wb (by dsimp [v]; rw [List.length_drop]; omega) bit1
          have hs0_ones : letterCount bit1 s0 = letterCount bit1 z + letterCount bit1 v := by
            conv => lhs; rw [hs0_eq]
            exact letterCount_append bit1 _ _
          rw [natDist_le_one_iff] at hzu0 hvp
          omega
    · omega

/-! ### Exact Telescoping of `balancedCount 2`, `rightSpecialCount`, and `centralCount` -/

def rightSpecialBool (w : Word 2) : Bool :=
  isBalancedBool (w ++ [bit0]) && isBalancedBool (w ++ [bit1])

def rightSpecialList (n : Nat) : List (Word 2) :=
  (allWords 2 n).filter rightSpecialBool

def rightSpecialCount (n : Nat) : Nat :=
  (rightSpecialList n).length

def centralBool (w : Word 2) : Bool :=
  rightSpecialBool (bit0 :: w) && rightSpecialBool (bit1 :: w)

def centralList (n : Nat) : List (Word 2) :=
  (allWords 2 n).filter centralBool

def centralCount (n : Nat) : Nat :=
  (centralList n).length

theorem rightSpecialBool_eq_true_iff (w : Word 2) :
    rightSpecialBool w = true ↔ IsRightSpecial w := by
  unfold rightSpecialBool IsRightSpecial
  simp [Bool.and_eq_true, isBalancedBool_eq_true_iff]

def IsCentral (w : Word 2) : Prop :=
  IsRightSpecial (bit0 :: w) ∧ IsRightSpecial (bit1 :: w)

theorem centralBool_eq_true_iff (w : Word 2) :
    centralBool w = true ↔ IsCentral w := by
  unfold centralBool IsCentral
  simp [Bool.and_eq_true, rightSpecialBool_eq_true_iff]

private theorem filter_or_and_sum {α : Type u} (b p q : α → Bool) :
    ∀ (xs : List α), (∀ x ∈ xs, b x = (p x || q x)) →
      (xs.filter p).length + (xs.filter q).length =
      (xs.filter b).length + (xs.filter fun x => p x && q x).length
  | [], _ => rfl
  | x :: xs, h => by
    have hx := h x List.mem_cons_self
    have ih := filter_or_and_sum b p q xs (fun y hy => h y (List.mem_cons_of_mem x hy))
    simp only [List.filter]
    cases hp : p x <;> cases hq : q x <;> simp [hp, hq] at hx ⊢ <;> rw [hx] <;> simp <;> omega

theorem balancedCount_two_succ (n : Nat) :
    balancedCount 2 (n + 1) = balancedCount 2 n + rightSpecialCount n := by
  let L0 := ((allWords 2 n).filter fun u => isBalancedBool (u ++ [bit0])).map (· ++ [bit0])
  let L1 := ((allWords 2 n).filter fun u => isBalancedBool (u ++ [bit1])).map (· ++ [bit1])
  have hnd0 : ListNodup L0 :=
    nodup_map_of_inj (· ++ [bit0]) (fun _ _ h => List.append_cancel_right h)
      (nodup_filter _ (nodup_allWords 2 n))
  have hnd1 : ListNodup L1 :=
    nodup_map_of_inj (· ++ [bit1]) (fun _ _ h => List.append_cancel_right h)
      (nodup_filter _ (nodup_allWords 2 n))
  have hnd01 : ListNodup (L0 ++ L1) := by
    refine nodup_append hnd0 hnd1 ?_
    intro x hx y hy hxy
    rcases List.mem_map.mp hx with ⟨u, _, rfl⟩
    rcases List.mem_map.mp hy with ⟨v, _, rfl⟩
    have hlen_uv : u.length = v.length := by
      have := congrArg List.length hxy; simp at this; exact this
    have heq_pair := List.append_inj hxy hlen_uv
    have hb : [bit0] = [bit1] := heq_pair.2
    injection hb with hb'
    exact bit0_ne_bit1 hb'
  have hnd_lhs : ListNodup (balancedWordsList 2 (n + 1)) :=
    nodup_filter _ (nodup_allWords 2 (n + 1))
  have hsub1 : ∀ w ∈ balancedWordsList 2 (n + 1), w ∈ L0 ++ L1 := by
    intro w hw
    rcases List.mem_filter.mp hw with ⟨hw_all, hw_bal⟩
    have hlen_w : w.length = n + 1 := (mem_allWords_iff 2 (n + 1) w).mp hw_all
    let u := w.take n
    let tail := w.drop n
    have hw_eq : u ++ tail = w := List.take_append_drop n w
    have hu_len : u.length = n := by dsimp [u]; rw [List.length_take]; omega
    have ht_len : tail.length = 1 := by dsimp [tail]; rw [List.length_drop]; omega
    cases htail : tail with
    | nil => rw [htail] at ht_len; simp at ht_len
    | cons c cs =>
      have hcs : cs = [] := by rw [htail] at ht_len; simp at ht_len; exact ht_len
      subst hcs
      have hw_uc : w = u ++ [c] := by rw [← hw_eq, htail]
      rw [hw_uc] at hw_bal ⊢
      have hu_mem : u ∈ allWords 2 n := (mem_allWords_iff 2 n u).mpr hu_len
      rcases fin2_dichotomy c with rfl | rfl
      · exact List.mem_append.mpr (Or.inl (List.mem_map.mpr ⟨u, List.mem_filter.mpr ⟨hu_mem, hw_bal⟩, rfl⟩))
      · exact List.mem_append.mpr (Or.inr (List.mem_map.mpr ⟨u, List.mem_filter.mpr ⟨hu_mem, hw_bal⟩, rfl⟩))
  have hsub2 : ∀ w ∈ L0 ++ L1, w ∈ balancedWordsList 2 (n + 1) := by
    intro w hw
    rcases List.mem_append.mp hw with hw0 | hw1
    · rcases List.mem_map.mp hw0 with ⟨u, hu_f, rfl⟩
      rcases List.mem_filter.mp hu_f with ⟨hu_all, hu_bal⟩
      have hu_len := (mem_allWords_iff 2 n u).mp hu_all
      exact List.mem_filter.mpr ⟨(mem_allWords_iff 2 (n + 1) _).mpr (by simp [hu_len]), hu_bal⟩
    · rcases List.mem_map.mp hw1 with ⟨u, hu_f, rfl⟩
      rcases List.mem_filter.mp hu_f with ⟨hu_all, hu_bal⟩
      have hu_len := (mem_allWords_iff 2 n u).mp hu_all
      exact List.mem_filter.mpr ⟨(mem_allWords_iff 2 (n + 1) _).mpr (by simp [hu_len]), hu_bal⟩
  have hle1 := nodup_length_le_of_subset hnd_lhs hsub1
  have hle2 := nodup_length_le_of_subset hnd01 hsub2
  have hlen_eq : balancedCount 2 (n + 1) = L0.length + L1.length := by
    unfold balancedCount
    rw [List.length_append] at hle1 hle2
    omega
  have hL0 : L0.length = ((allWords 2 n).filter fun u => isBalancedBool (u ++ [bit0])).length :=
    List.length_map _
  have hL1 : L1.length = ((allWords 2 n).filter fun u => isBalancedBool (u ++ [bit1])).length :=
    List.length_map _
  rw [hlen_eq, hL0, hL1]
  apply filter_or_and_sum isBalancedBool
    (fun u => isBalancedBool (u ++ [bit0]))
    (fun u => isBalancedBool (u ++ [bit1]))
    (allWords 2 n)
  intro u _
  by_cases hbu : isBalancedBool u = true
  · have hu : IsBalanced u := (isBalancedBool_eq_true_iff u).mp hbu
    rcases binary_balanced_right_extend hu with h0 | h1
    · have hb0 := (isBalancedBool_eq_true_iff _).mpr h0
      simp [hbu, hb0]
    · have hb1 := (isBalancedBool_eq_true_iff _).mpr h1
      simp [hbu, hb1]
  · have hbu_f : isBalancedBool u = false := Bool.eq_false_iff.mpr hbu
    have hb0_f : isBalancedBool (u ++ [bit0]) = false := by
      apply Bool.eq_false_iff.mpr; intro h
      have hfac : IsFactor u (u ++ [bit0]) := ⟨[], [bit0], by simp⟩
      have := isBalanced_of_isFactor ((isBalancedBool_eq_true_iff _).mp h) hfac
      exact hbu ((isBalancedBool_eq_true_iff u).mpr this)
    have hb1_f : isBalancedBool (u ++ [bit1]) = false := by
      apply Bool.eq_false_iff.mpr; intro h
      have hfac : IsFactor u (u ++ [bit1]) := ⟨[], [bit1], by simp⟩
      have := isBalanced_of_isFactor ((isBalancedBool_eq_true_iff _).mp h) hfac
      exact hbu ((isBalancedBool_eq_true_iff u).mpr this)
    simp [hbu_f, hb0_f, hb1_f]

theorem rightSpecialCount_succ (n : Nat) :
    rightSpecialCount (n + 1) = rightSpecialCount n + centralCount n := by
  have hall2 : allWords 2 (n + 1) =
      (allWords 2 n).map (bit0 :: ·) ++ (allWords 2 n).map (bit1 :: ·) := by
    simp [allWords, finList, bit0, bit1]
  unfold rightSpecialCount rightSpecialList centralCount centralList
  rw [hall2, List.filter_append, List.length_append]
  have hmap_filt : ∀ (a : Fin 2) (xs : List (Word 2)),
      ((xs.map (a :: ·)).filter rightSpecialBool).length =
      (xs.filter fun u => rightSpecialBool (a :: u)).length := by
    intro a xs
    induction xs with
    | nil => rfl
    | cons x xs ih =>
      simp only [List.map_cons, List.filter]
      cases hr : rightSpecialBool (a :: x) <;> simp [hr, ih]
  rw [hmap_filt bit0, hmap_filt bit1]
  apply filter_or_and_sum rightSpecialBool
    (fun u => rightSpecialBool (bit0 :: u))
    (fun u => rightSpecialBool (bit1 :: u))
    (allWords 2 n)
  intro u _
  by_cases hru : rightSpecialBool u = true
  · have hu : IsRightSpecial u := (rightSpecialBool_eq_true_iff u).mp hru
    rcases rightSpecial_left_extend hu with h0 | h1
    · have hb0 := (rightSpecialBool_eq_true_iff _).mpr h0
      simp [hru, hb0]
    · have hb1 := (rightSpecialBool_eq_true_iff _).mpr h1
      simp [hru, hb1]
  · have hru_f : rightSpecialBool u = false := Bool.eq_false_iff.mpr hru
    have h_sub : ∀ a : Fin 2, rightSpecialBool (a :: u) = false := by
      intro a; apply Bool.eq_false_iff.mpr; intro h
      rcases (rightSpecialBool_eq_true_iff _).mp h with ⟨h0, h1⟩
      have hu0 : IsBalanced (u ++ [bit0]) := isBalanced_of_isFactor h0 ⟨[a], [], by simp⟩
      have hu1 : IsBalanced (u ++ [bit1]) := isBalanced_of_isFactor h1 ⟨[a], [], by simp⟩
      exact hru ((rightSpecialBool_eq_true_iff u).mpr ⟨hu0, hu1⟩)
    simp [hru_f, h_sub bit0, h_sub bit1]

/-! ### Mechanical Central Words & `centralCount n = totient (n + 2)` -/

/-- Euler's totient function `φ(m) = #{1 ≤ q ≤ m : gcd(q, m) = 1}`. -/
def coprimeList (m : Nat) : List Nat :=
  ((rangeList m).map (· + 1)).filter fun q => decide (Nat.gcd q m = 1)

def totient (m : Nat) : Nat :=
  (coprimeList m).length

theorem nodup_coprimeList (m : Nat) : ListNodup (coprimeList m) := by
  have hnd_range : ∀ k : Nat, ListNodup (rangeList k) := by
    intro k; induction k with
    | zero => exact .nil
    | succ k ih =>
      refine nodup_append ih (.cons (fun _ h => nomatch h) .nil) ?_
      intro x hx y hy hxy
      simp at hy; subst hy
      have := mem_rangeList.mp hx; omega
  exact nodup_filter _ (nodup_map_of_inj (fun x => x + 1) (fun a b h => by dsimp at h; omega) (hnd_range m))

theorem mem_coprimeList_iff {q m : Nat} :
    q ∈ coprimeList m ↔ 1 ≤ q ∧ q ≤ m ∧ Nat.gcd q m = 1 := by
  unfold coprimeList
  simp only [List.mem_filter, List.mem_map, mem_rangeList, decide_eq_true_eq]
  constructor
  · rintro ⟨⟨i, hi, rfl⟩, hcop⟩
    exact ⟨by omega, by omega, hcop⟩
  · rintro ⟨hq1, hqm, hcop⟩
    exact ⟨⟨q - 1, by omega, by omega⟩, hcop⟩

/-- Mechanical word of slope `q / m`, phase `r`, offset `s`, and length `len`. -/
def mechSlice (m q r : Nat) : Nat → Nat → Word 2
  | _, 0 => []
  | s, len + 1 =>
    let d := (((s + 1) * q + r) / m) - ((s * q + r) / m)
    (if d = 0 then bit0 else bit1) :: mechSlice m q r (s + 1) len

theorem length_mechSlice (m q r : Nat) :
    ∀ s len : Nat, (mechSlice m q r s len).length = len
  | _, 0 => rfl
  | s, len + 1 => by simp [mechSlice, length_mechSlice m q r (s + 1) len]

theorem drop_mechSlice (m q r : Nat) :
    ∀ s i len : Nat, i ≤ len →
      (mechSlice m q r s len).drop i = mechSlice m q r (s + i) (len - i)
  | s, 0, len, _ => by simp
  | _, _ + 1, 0, hi => by omega
  | s, i + 1, len + 1, hi => by
    simp only [mechSlice, List.drop_succ_cons]
    rw [drop_mechSlice m q r (s + 1) i len (by omega),
        show (s + 1) + i = s + (i + 1) by omega,
        show len + 1 - (i + 1) = len - i by omega]

theorem take_mechSlice (m q r : Nat) :
    ∀ s k len : Nat, k ≤ len →
      (mechSlice m q r s len).take k = mechSlice m q r s k
  | _, 0, _, _ => by simp [mechSlice]
  | _, _ + 1, 0, hk => by omega
  | s, k + 1, len + 1, hk => by
    simp only [mechSlice, List.take_succ_cons]
    rw [take_mechSlice m q r (s + 1) k len (by omega)]

private theorem nat_div_mono {a b m : Nat} (hm : 0 < m) (hab : a ≤ b) :
    a / m ≤ b / m := by
  by_cases hle : a / m ≤ b / m
  · exact hle
  · exfalso
    have hgt : b / m + 1 ≤ a / m := by omega
    have hmul : m * (b / m + 1) ≤ m * (a / m) := Nat.mul_le_mul_left m hgt
    have ha_dm := Nat.div_add_mod a m
    have hb_dm := Nat.div_add_mod b m
    have hrem_b : b % m < m := Nat.mod_lt b hm
    rw [Nat.mul_add, Nat.mul_one] at hmul
    omega

private theorem step_diff_zero_or_one {m q r s : Nat} (hq : q ≤ m) (hm : 0 < m) :
    ((s + 1) * q + r) / m - (s * q + r) / m ≤ 1 ∧
    (s * q + r) / m ≤ ((s + 1) * q + r) / m := by
  have heq : (s + 1) * q + r = (s * q + r) + q := by
    rw [Nat.add_mul, Nat.one_mul]; omega
  have hA := Nat.div_add_mod (s * q + r) m
  have hremA : (s * q + r) % m < m := Nat.mod_lt _ hm
  have hdiv_sum : ((s * q + r) % m + q) / m ≤ 1 := by
    by_cases hlt : (s * q + r) % m + q < m
    · rw [Nat.div_eq_of_lt hlt]; omega
    · have hlt2 : (s * q + r) % m + q - m < m := by omega
      have h1 : (s * q + r) % m + q = m * 1 + ((s * q + r) % m + q - m) := by omega
      rw [h1, Nat.mul_add_div hm, Nat.div_eq_of_lt hlt2]; omega
  have htot : ((s * q + r) + q) / m = (s * q + r) / m + ((s * q + r) % m + q) / m := by
    conv => lhs; rw [show (s * q + r) + q = m * ((s * q + r) / m) + ((s * q + r) % m + q) by omega]
    exact Nat.mul_add_div hm _ _
  have hfinal : ((s + 1) * q + r) / m = (s * q + r) / m + ((s * q + r) % m + q) / m := by
    rw [heq, htot]
  rw [hfinal, Nat.add_sub_cancel_left]
  exact ⟨hdiv_sum, Nat.le_add_right _ _⟩

theorem ones_mechSlice (m q r : Nat) (hq : q ≤ m) (hm : 0 < m) :
    ∀ s len : Nat,
      letterCount bit1 (mechSlice m q r s len) = ((s + len) * q + r) / m - (s * q + r) / m
  | s, 0 => by simp [mechSlice, letterCount]
  | s, len + 1 => by
    simp only [mechSlice, letterCount_cons]
    have hstep := step_diff_zero_or_one (m := m) (q := q) (r := r) (s := s) hq hm
    have ih := ones_mechSlice m q r hq hm (s + 1) len
    have hmon : ((s + 1) * q + r) / m ≤ ((s + 1 + len) * q + r) / m := by
      apply nat_div_mono hm
      have : (s + 1) * q ≤ (s + 1 + len) * q := Nat.mul_le_mul_right q (by omega)
      omega
    have hrew : s + (len + 1) = s + 1 + len := by omega
    rw [hrew]
    by_cases hd0 : ((s + 1) * q + r) / m - (s * q + r) / m = 0
    · simp only [hd0, ite_true, bit0_ne_bit1, ite_false, Nat.zero_add]
      omega
    · simp only [hd0, ite_false, ite_true]
      omega

theorem mechSlice_isBalanced (m q r : Nat) (hq : q ≤ m) (hm : 0 < m) (s len : Nat) :
    IsBalanced (mechSlice m q r s len) := by
  rw [isBalanced_two_iff_ones]
  intro u v hu hv hlen
  rcases (isFactor_iff_slice u (mechSlice m q r s len)).mp hu with ⟨i, hi, hu_eq⟩
  rcases (isFactor_iff_slice v (mechSlice m q r s len)).mp hv with ⟨j, hj, hv_eq⟩
  have hmw : (mechSlice m q r s len).length = len := length_mechSlice m q r s len
  have hlu : ((mechSlice m q r s len).drop i).take u.length = mechSlice m q r (s + i) u.length := by
    rw [drop_mechSlice m q r s i len (by omega), take_mechSlice m q r (s + i) u.length (len - i) (by omega)]
  have hlv : ((mechSlice m q r s len).drop j).take v.length = mechSlice m q r (s + j) v.length := by
    rw [drop_mechSlice m q r s j len (by omega), take_mechSlice m q r (s + j) v.length (len - j) (by omega)]
  rw [← hu_eq, ← hv_eq, hlu, hlv, ← hlen]
  have hbound : ∀ t L : Nat,
      (L * q) / m ≤ letterCount bit1 (mechSlice m q r t L) ∧
      letterCount bit1 (mechSlice m q r t L) ≤ (L * q) / m + 1 := by
    intro t L
    have hAB : (t + L) * q + r = (t * q + r) + (L * q) := by rw [Nat.add_mul]; omega
    have hdmA := Nat.div_add_mod (t * q + r) m
    have hdmB := Nat.div_add_mod (L * q) m
    have hrA : (t * q + r) % m < m := Nat.mod_lt _ hm
    have hrB : (L * q) % m < m := Nat.mod_lt _ hm
    have hdiv_rem : ((t * q + r) % m + (L * q) % m) / m ≤ 1 := by
      by_cases hlt : (t * q + r) % m + (L * q) % m < m
      · rw [Nat.div_eq_of_lt hlt]; omega
      · have hlt2 : (t * q + r) % m + (L * q) % m - m < m := by omega
        have h1 : (t * q + r) % m + (L * q) % m = m * 1 + ((t * q + r) % m + (L * q) % m - m) := by omega
        rw [h1, Nat.mul_add_div hm, Nat.div_eq_of_lt hlt2]; omega
    have hdivAB : ((t * q + r) + (L * q)) / m =
        ((t * q + r) / m + (L * q) / m) + ((t * q + r) % m + (L * q) % m) / m := by
      conv => lhs; rw [show (t * q + r) + (L * q) =
        m * ((t * q + r) / m + (L * q) / m) + ((t * q + r) % m + (L * q) % m) by
        rw [Nat.mul_add]; omega]
      exact Nat.mul_add_div hm _ _
    have hones_eq : letterCount bit1 (mechSlice m q r t L) =
        (L * q) / m + ((t * q + r) % m + (L * q) % m) / m := by
      rw [ones_mechSlice m q r hq hm t L, hAB, hdivAB,
          Nat.add_assoc, Nat.add_sub_cancel_left]
    rw [hones_eq]
    exact ⟨Nat.le_add_right _ _, Nat.add_le_add_left hdiv_rem _⟩
  have hb1 := hbound (s + i) u.length
  have hb2 := hbound (s + j) u.length
  generalize hd : (u.length * q) / m = d at hb1 hb2
  rw [natDist_le_one_iff]
  omega

/-- Mechanical central word `c_{m, q}` of length `m - 2` (`1 ≤ q < m`, `gcd(q, m) = 1`). -/
def centralMech (m q : Nat) : Word 2 :=
  mechSlice m q 0 1 (m - 2)

theorem length_centralMech (m q : Nat) : (centralMech m q).length = m - 2 :=
  length_mechSlice m q 0 1 (m - 2)

private theorem mechSlice_snoc (m q r : Nat) :
    ∀ len s : Nat,
      mechSlice m q r s (len + 1) =
        mechSlice m q r s len ++
        [if (((s + len + 1) * q + r) / m) - (((s + len) * q + r) / m) = 0 then bit0 else bit1]
  | 0, s => by simp [mechSlice]
  | len + 1, s => by
    conv => lhs; unfold mechSlice
    conv => rhs; rw [show mechSlice m q r s (len + 1) =
      (if ((s + 1) * q + r) / m - (s * q + r) / m = 0 then bit0 else bit1) ::
      mechSlice m q r (s + 1) len from rfl]
    simp only [List.cons_append]
    rw [mechSlice_snoc m q r len (s + 1),
        show s + 1 + len = s + (len + 1) by omega]

theorem centralMech_in_central (n q : Nat) (hq1 : 1 ≤ q) (hqm : q < n + 2)
    (hcop : Nat.gcd q (n + 2) = 1) :
    centralMech (n + 2) q ∈ centralList n ∧
    letterCount bit1 (centralMech (n + 2) q) + 1 = q := by
  let m := n + 2
  have hm_pos : 0 < m := by omega
  have hq_le : q ≤ m := by omega
  have hmul_1n : (1 + n) * q + q = m * q := by
    calc (1 + n) * q + q
      _ = (1 + n) * q + 1 * q := by rw [Nat.one_mul]
      _ = ((1 + n) + 1) * q := (Nat.add_mul (1 + n) 1 q).symm
      _ = m * q := by rw [show (1 + n) + 1 = m by omega]
  have hmq_split : m * q = m * (q - 1) + m := by
    conv => lhs; rw [show q = (q - 1) + 1 by omega]
    rw [Nat.mul_add, Nat.mul_one]
  have hm1_div : ((1 + n) * q) / m = q - 1 := by
    have h1 : (1 + n) * q = m * (q - 1) + (m - q) := by omega
    calc ((1 + n) * q) / m
      _ = (m * (q - 1) + (m - q)) / m := by rw [h1]
      _ = (q - 1) + (m - q) / m := Nat.mul_add_div hm_pos _ _
      _ = (q - 1) + 0 := by rw [Nat.div_eq_of_lt (by omega)]
      _ = q - 1 := Nat.add_zero _
  have hL_eq : (bit0 :: centralMech m q) ++ [bit1] = mechSlice m q 0 0 m := by
    have h0 : mechSlice m q 0 0 m = (if (q / m) - 0 = 0 then bit0 else bit1) :: mechSlice m q 0 1 (n + 1) := by
      dsimp [m]; simp [mechSlice]
    have hq_div : q / m = 0 := Nat.div_eq_of_lt hqm
    have hlast : mechSlice m q 0 1 (n + 1) = centralMech m q ++
        [if (((1 + n + 1) * q + 0) / m) - (((1 + n) * q + 0) / m) = 0 then bit0 else bit1] := by
      unfold centralMech
      rw [show m - 2 = n by omega]
      exact mechSlice_snoc m q 0 n 1
    have hm_div : ((1 + n + 1) * q) / m = q := by
      rw [show 1 + n + 1 = m by omega, Nat.mul_div_right q hm_pos]
    rw [h0, hq_div, hlast]
    simp only [Nat.sub_zero, ite_true, Nat.add_zero, hm_div, hm1_div,
               show q - (q - 1) = 1 by omega, show (1 : Nat) ≠ 0 by decide, ite_false]
    rfl
  have hshift_div : ∀ j : Nat, 1 ≤ j → j < m →
      (j * q + (m - 1)) / m = (j * q) / m + 1 := by
    intro j hj1 hjm
    have hnot_dvd : (j * q) % m ≠ 0 := by
      intro hrem
      have hdvd : m ∣ q * j := by rw [Nat.mul_comm]; exact Nat.dvd_of_mod_eq_zero hrem
      have hdvd_j : m ∣ j := coprime_dvd_of_dvd_mul (Nat.gcd_comm q m ▸ hcop) hdvd
      have := Nat.le_of_dvd (by omega) hdvd_j
      omega
    have hdm := Nat.div_add_mod (j * q) m
    have hlt_r : (j * q) % m < m := Nat.mod_lt _ hm_pos
    have hpos_r : 1 ≤ (j * q) % m := by omega
    have hlt_r1 : (j * q) % m - 1 < m := by omega
    have h1 : j * q + (m - 1) = m * ((j * q) / m + 1) + ((j * q) % m - 1) := by
      rw [Nat.mul_add, Nat.mul_one]; omega
    calc (j * q + (m - 1)) / m
      _ = (m * ((j * q) / m + 1) + ((j * q) % m - 1)) / m := by rw [h1]
      _ = ((j * q) / m + 1) + ((j * q) % m - 1) / m := Nat.mul_add_div hm_pos _ _
      _ = ((j * q) / m + 1) + 0 := by rw [Nat.div_eq_of_lt hlt_r1]
      _ = (j * q) / m + 1 := Nat.add_zero _
  have hmid_eq : ∀ (len s : Nat), 1 ≤ s → s + len < m →
      mechSlice m q (m - 1) s len = mechSlice m q 0 s len := by
    intro len
    induction len with
    | zero => intro _ _ _; rfl
    | succ len ih =>
      intro s hs1 hslt
      simp only [mechSlice, Nat.add_zero]
      rw [hshift_div (s + 1) (by omega) (by omega), hshift_div s hs1 (by omega),
          show (s + 1) * q / m + 1 - (s * q / m + 1) = (s + 1) * q / m - s * q / m by omega,
          ih (s + 1) (by omega) (by omega)]
  have hU_eq : (bit1 :: centralMech m q) ++ [bit0] = mechSlice m q (m - 1) 0 m := by
    have h0 : mechSlice m q (m - 1) 0 m =
        (if ((1 * q + (m - 1)) / m) - ((0 * q + (m - 1)) / m) = 0 then bit0 else bit1) ::
        mechSlice m q (m - 1) 1 (n + 1) := by
      dsimp [m]; simp [mechSlice]
    have hd_start : ((1 * q + (m - 1)) / m) - ((0 * q + (m - 1)) / m) = 1 := by
      rw [hshift_div 1 (by omega) (by omega), Nat.one_mul, Nat.div_eq_of_lt hqm,
          Nat.zero_mul, Nat.zero_add, Nat.div_eq_of_lt (by omega)]
    have hlast : mechSlice m q (m - 1) 1 (n + 1) =
        mechSlice m q (m - 1) 1 n ++
        [if (((1 + n + 1) * q + (m - 1)) / m) - (((1 + n) * q + (m - 1)) / m) = 0 then bit0 else bit1] :=
      mechSlice_snoc m q (m - 1) n 1
    have hd_end : (((1 + n + 1) * q + (m - 1)) / m) - (((1 + n) * q + (m - 1)) / m) = 0 := by
      have h1 : (1 + n + 1) * q + (m - 1) = m * q + (m - 1) := by
        rw [show 1 + n + 1 = m by omega]
      have hdiv1 : (m * q + (m - 1)) / m = q := by
        rw [Nat.mul_add_div hm_pos, Nat.div_eq_of_lt (by omega), Nat.add_zero]
      have hdiv2 : ((1 + n) * q + (m - 1)) / m = q := by
        rw [hshift_div (1 + n) (by omega) (by omega), hm1_div]
        omega
      rw [h1, hdiv1, hdiv2, Nat.sub_self]
    rw [h0, hd_start, hlast, hd_end, hmid_eq n 1 (by omega) (by omega)]
    simp [centralMech, show m - 2 = n by omega]
  have hbal01 : IsBalanced ((bit0 :: centralMech m q) ++ [bit1]) := by
    rw [hL_eq]; exact mechSlice_isBalanced m q 0 hq_le hm_pos 0 m
  have hbal10 : IsBalanced ((bit1 :: centralMech m q) ++ [bit0]) := by
    rw [hU_eq]; exact mechSlice_isBalanced m q (m - 1) hq_le hm_pos 0 m
  have hbal_0w : IsBalanced (bit0 :: centralMech m q) :=
    isBalanced_of_isFactor hbal01 ⟨[], [bit1], by simp⟩
  have hbal_1w : IsBalanced (bit1 :: centralMech m q) :=
    isBalanced_of_isFactor hbal10 ⟨[], [bit0], by simp⟩
  have hbal_w0 : IsBalanced (centralMech m q ++ [bit0]) :=
    isBalanced_of_isFactor hbal10 ⟨[bit1], [], by simp⟩
  have hbal_w1 : IsBalanced (centralMech m q ++ [bit1]) :=
    isBalanced_of_isFactor hbal01 ⟨[bit0], [], by simp⟩
  have hbal00 : IsBalanced ((bit0 :: centralMech m q) ++ [bit0]) :=
    same_letter_sandwich_balanced bit0 hbal_0w hbal_w0
  have hbal11 : IsBalanced ((bit1 :: centralMech m q) ++ [bit1]) :=
    same_letter_sandwich_balanced bit1 hbal_1w hbal_w1
  have hcent : IsCentral (centralMech m q) := ⟨⟨hbal00, hbal01⟩, ⟨hbal10, hbal11⟩⟩
  refine ⟨?_, ?_⟩
  · exact List.mem_filter.mpr ⟨(mem_allWords_iff 2 n _).mpr (by rw [length_centralMech]; omega),
      (centralBool_eq_true_iff _).mpr hcent⟩
  · unfold centralMech
    rw [ones_mechSlice m q 0 hq_le hm_pos 1 (m - 2),
        show m - 2 = n by omega]
    simp only [Nat.add_zero, Nat.one_mul, Nat.div_eq_of_lt (show q < m by omega), hm1_div]
    omega

/-- Converse: Every `w ∈ centralList n` has `gcd(ones w + 1, n + 2) = 1` and equals `centralMech (n + 2) (ones w + 1)`! -/
theorem central_unique_and_coprime (n : Nat) {w : Word 2} (hw_mem : w ∈ centralList n) :
    let m := n + 2
    let q := letterCount bit1 w + 1
    1 ≤ q ∧ q < m ∧ Nat.gcd q m = 1 ∧ w = centralMech m q := by
  intro m q
  rcases List.mem_filter.mp hw_mem with ⟨hw_all, hw_cb⟩
  have hlen : w.length = n := (mem_allWords_iff 2 n w).mp hw_all
  rcases (centralBool_eq_true_iff w).mp hw_cb with ⟨⟨h00, h01⟩, ⟨h10, h11⟩⟩
  have h0w : IsBalanced (bit0 :: w) := isBalanced_of_isFactor h00 ⟨[], [bit0], by simp⟩
  have h1w : IsBalanced (bit1 :: w) := isBalanced_of_isFactor h10 ⟨[], [bit0], by simp⟩
  have hw0 : IsBalanced (w ++ [bit0]) := isBalanced_of_isFactor h00 ⟨[bit0], [], by simp⟩
  have hw1 : IsBalanced (w ++ [bit1]) := isBalanced_of_isFactor h01 ⟨[bit0], [], by simp⟩
  have hw : IsBalanced w := isBalanced_of_isFactor h0w ⟨[bit0], [], by simp⟩
  have hq1 : 1 ≤ q := by omega
  have hqm : q < m := by
    have := letterCount_le_length bit1 w
    dsimp [q, m]; omega
  have hps_eq : ∀ k : Nat, k ≤ n → letterCount bit1 (w.take k) = letterCount bit1 (suffixOf k w) := by
    intro k hk
    by_cases hk0 : k = 0
    · subst hk0
      unfold suffixOf
      rw [Nat.sub_zero, List.drop_length, List.take_zero]
    · by_cases hkn : k = n
      · subst hkn
        unfold suffixOf
        rw [← hlen, Nat.sub_self, List.drop_zero, List.take_length]
      · have hc01 := (sandwich_balanced_iff h0w hw1).mp h01 k (by omega) (by omega)
        have hc10 := (sandwich_balanced_iff h1w hw0).mp h10 k (by omega) (by omega)
        have ho0 : letterCount bit1 [bit0] = 0 := by simp [letterCount, bit0_ne_bit1]
        have ho1 : letterCount bit1 [bit1] = 1 := by simp [letterCount]
        rw [ho0, ho1, natDist_le_one_iff] at hc01 hc10
        omega
  let f : Nat → Nat := fun j => if j = 0 then 0 else letterCount bit1 (w.take (j - 1))
  have hcase1 : ∀ a b : Nat, 1 ≤ a → 1 ≤ b → a + b ≤ m - 1 →
      f a + f b ≤ f (a + b) ∧ f (a + b) ≤ f a + f b + 1 := by
    intro a b ha1 hb1 hab
    rcases prefixOf_split (L0 := a) (L1 := a + b) (w := bit0 :: w) (by omega)
        (by simp [hlen]; omega) with ⟨v, hv_len, _, hpre_split⟩
    have hv_eq_w : v = (w.drop (a - 1)).take b := by
      have hgen : ∀ (xs : List (Fin 2)) (x y : Nat),
          (xs.take (x + y)).drop x = (xs.drop x).take y := by
        intro xs; induction xs with
        | nil => intro x y; simp
        | cons _ xs ih =>
          intro x y; cases x with
          | zero => simp
          | succ x => rw [show x + 1 + y = (x + y) + 1 by omega]; simp [ih x y]
      have hd1 : ((bit0 :: w).take (a + b)).drop a = ((bit0 :: w).drop a).take b := hgen (bit0 :: w) a b
      have hd2 : ((bit0 :: w).take (a + b)).drop a = v := by
        rw [hpre_split]
        have hlen_ta : ((bit0 :: w).take a).length = a := by
          rw [List.length_take]; simp [hlen]; omega
        rw [← hlen_ta]; simp
      have hd3 : (bit0 :: w).drop a = w.drop (a - 1) := by
        conv => lhs; rw [show a = (a - 1) + 1 by omega]
        rfl
      rw [← hd2, hd1, hd3]
    have hfv_w : IsFactor v w := hv_eq_w ▸ isFactor_take_drop w (a - 1) b
    have hpre_ones : letterCount bit1 ((bit0 :: w).take (a + b)) =
        letterCount bit1 ((bit0 :: w).take a) + letterCount bit1 v := by
      rw [hpre_split]; exact letterCount_append bit1 _ _
    have htake_0w : ∀ j : Nat, 1 ≤ j → letterCount bit1 ((bit0 :: w).take j) = f j := by
      intro j hj
      have hj' : j ≠ 0 := by omega
      dsimp [f]; simp only [hj', ite_false]
      conv => lhs; rw [show j = (j - 1) + 1 by omega]
      simp [letterCount_cons, bit0_ne_bit1]
    have htake_1w : ∀ j : Nat, 1 ≤ j → letterCount bit1 ((bit1 :: w).take j) = f j + 1 := by
      intro j hj
      have hj' : j ≠ 0 := by omega
      dsimp [f]; simp only [hj', ite_false]
      conv => lhs; rw [show j = (j - 1) + 1 by omega]
      simp [letterCount_cons]; omega
    have hd0 := h0w v ((bit0 :: w).take b)
      (isFactor_trans hfv_w ⟨[bit0], [], by simp⟩)
      (isFactor_prefix b (bit0 :: w))
      (by rw [hv_len, List.length_take, Nat.min_eq_left (by simp [hlen]; omega)]; omega) bit1
    have hd1 := h1w v ((bit1 :: w).take b)
      (isFactor_trans hfv_w ⟨[bit1], [], by simp⟩)
      (isFactor_prefix b (bit1 :: w))
      (by rw [hv_len, List.length_take, Nat.min_eq_left (by simp [hlen]; omega)]; omega) bit1
    rw [htake_0w (a + b) (by omega), htake_0w a ha1] at hpre_ones
    rw [htake_0w b hb1, natDist_le_one_iff] at hd0
    rw [htake_1w b hb1, natDist_le_one_iff] at hd1
    omega
  have hcase2 : ∀ a : Nat, 1 ≤ a → a ≤ m - 1 → f a + f (m - a) = q - 1 := by
    intro a ha1 ham
    have ha_nz : a ≠ 0 := by omega
    have hma_nz : m - a ≠ 0 := by omega
    dsimp [f]; simp only [ha_nz, hma_nz, ite_false]
    have hw_split : w = w.take (a - 1) ++ suffixOf (m - a - 1) w := by
      unfold suffixOf
      rw [show w.length - (m - a - 1) = a - 1 by omega]
      exact (List.take_append_drop (a - 1) w).symm
    have hones_w : letterCount bit1 w =
        letterCount bit1 (w.take (a - 1)) + letterCount bit1 (suffixOf (m - a - 1) w) := by
      conv => lhs; rw [hw_split]
      exact letterCount_append bit1 _ _
    rw [← hps_eq (m - a - 1) (by omega)] at hones_w
    dsimp [q]; omega
  let F : Nat → Nat := fun x => (x / m) * q + f (x % m)
  have hm_pos : 0 < m := by omega
  have hF_step : ∀ x y : Nat, F x + F y ≤ F (x + y) ∧ F (x + y) ≤ F x + F y + 1 := by
    intro x y
    let a := x % m
    let b := y % m
    have ha_lt : a < m := Nat.mod_lt x hm_pos
    have hb_lt : b < m := Nat.mod_lt y hm_pos
    have hx_dm := Nat.div_add_mod x m
    have hy_dm := Nat.div_add_mod y m
    by_cases ha0 : a = 0
    · have hf0 : f a = 0 := by dsimp [f]; simp [ha0]
      have hdiv : (x + y) / m = x / m + y / m := by
        conv => lhs; rw [show x + y = m * (x / m + y / m) + b by rw [Nat.mul_add]; omega]
        rw [Nat.mul_add_div hm_pos, Nat.div_eq_of_lt hb_lt, Nat.add_zero]
      have hmod : (x + y) % m = b := by
        conv => lhs; rw [show x + y = m * (x / m + y / m) + b by rw [Nat.mul_add]; omega]
        rw [Nat.mul_add_mod, Nat.mod_eq_of_lt hb_lt]
      dsimp [F]; rw [hdiv, hmod, Nat.add_mul]; dsimp [a, b] at hf0 ⊢; rw [hf0]; omega
    · by_cases hb0 : b = 0
      · have hf0 : f b = 0 := by dsimp [f]; simp [hb0]
        have hdiv : (x + y) / m = x / m + y / m := by
          conv => lhs; rw [show x + y = m * (x / m + y / m) + a by rw [Nat.mul_add]; omega]
          rw [Nat.mul_add_div hm_pos, Nat.div_eq_of_lt ha_lt, Nat.add_zero]
        have hmod : (x + y) % m = a := by
          conv => lhs; rw [show x + y = m * (x / m + y / m) + a by rw [Nat.mul_add]; omega]
          rw [Nat.mul_add_mod, Nat.mod_eq_of_lt ha_lt]
        dsimp [F]; rw [hdiv, hmod, Nat.add_mul]; dsimp [a, b] at hf0 ⊢; rw [hf0]; omega
      · by_cases hab_lt : a + b < m
        · have hdiv : (x + y) / m = x / m + y / m := by
            conv => lhs; rw [show x + y = m * (x / m + y / m) + (a + b) by rw [Nat.mul_add]; omega]
            rw [Nat.mul_add_div hm_pos, Nat.div_eq_of_lt hab_lt, Nat.add_zero]
          have hmod : (x + y) % m = a + b := by
            conv => lhs; rw [show x + y = m * (x / m + y / m) + (a + b) by rw [Nat.mul_add]; omega]
            rw [Nat.mul_add_mod, Nat.mod_eq_of_lt hab_lt]
          have hc1 := hcase1 a b (by omega) (by omega) (by omega)
          dsimp [F]; rw [hdiv, hmod, Nat.add_mul]; dsimp [a, b] at hc1 ⊢; omega
        · by_cases hab_eq : a + b = m
          · have hdiv : (x + y) / m = x / m + y / m + 1 := by
              conv => lhs; rw [show x + y = m * (x / m + y / m + 1) by
                rw [Nat.mul_add, Nat.mul_add, Nat.mul_one]; omega]
              exact Nat.mul_div_right _ hm_pos
            have hmod : (x + y) % m = 0 := by
              conv => lhs; rw [show x + y = m * (x / m + y / m + 1) by
                rw [Nat.mul_add, Nat.mul_add, Nat.mul_one]; omega]
              exact Nat.mul_mod_right _ _
            have hc2 := hcase2 a (by omega) (by omega)
            rw [show m - a = b by omega] at hc2
            have hf0 : f 0 = 0 := rfl
            dsimp [F]; rw [hdiv, hmod, hf0, Nat.add_mul, Nat.add_mul, Nat.one_mul]
            dsimp [a, b] at hc2; omega
          · let r := a + b - m
            have hr_lt : r < m := by omega
            have hr_1 : 1 ≤ r := by omega
            have hdiv : (x + y) / m = x / m + y / m + 1 := by
              conv => lhs; rw [show x + y = m * (x / m + y / m + 1) + r by
                rw [Nat.mul_add, Nat.mul_add, Nat.mul_one]; omega]
              rw [Nat.mul_add_div hm_pos, Nat.div_eq_of_lt hr_lt, Nat.add_zero]
            have hmod : (x + y) % m = r := by
              conv => lhs; rw [show x + y = m * (x / m + y / m + 1) + r by
                rw [Nat.mul_add, Nat.mul_add, Nat.mul_one]; omega]
              rw [Nat.mul_add_mod, Nat.mod_eq_of_lt hr_lt]
            have hc1' := hcase1 (m - a) (m - b) (by omega) (by omega) (by omega)
            rw [show (m - a) + (m - b) = m - r by omega] at hc1'
            have hc2a := hcase2 a (by omega) (by omega)
            have hc2b := hcase2 b (by omega) (by omega)
            have hc2r := hcase2 r hr_1 (by omega)
            dsimp [F]; rw [hdiv, hmod, Nat.add_mul, Nat.add_mul, Nat.one_mul]
            dsimp [a, b] at hc1' hc2a hc2b hc2r; omega
  have hF_iter : ∀ (t j : Nat), 1 ≤ t →
      t * F j ≤ F (t * j) ∧ F (t * j) ≤ t * F j + (t - 1) := by
    intro t j ht
    induction t with
    | zero => omega
    | succ t ih =>
      by_cases ht0 : t = 0
      · subst ht0; simp
      · have ih' := ih (by omega)
        have hst := hF_step (t * j) j
        rw [show (t + 1) * j = t * j + j by rw [Nat.add_mul, Nat.one_mul]]
        rw [Nat.add_mul, Nat.one_mul]
        omega
  have hf_formula : ∀ j : Nat, 1 ≤ j → j < m → f j = (j * q) / m := by
    intro j hj1 hjm
    have h1 := hF_iter m j (by omega)
    have hFj : F j = f j := by
      dsimp [F]; rw [Nat.div_eq_of_lt hjm, Nat.zero_mul, Nat.zero_add, Nat.mod_eq_of_lt hjm]
    have hFmj : F (m * j) = j * q := by
      dsimp [F]
      rw [Nat.mul_div_right j hm_pos, Nat.mul_mod_right m j]
      simp [f]
    rw [hFj, hFmj] at h1
    have heq_jq : j * q = m * f j + (j * q - m * f j) := by omega
    rw [heq_jq, Nat.mul_add_div hm_pos, Nat.div_eq_of_lt (by omega), Nat.add_zero]
  have hcop : Nat.gcd q m = 1 := by
    let g := Nat.gcd q m
    have hg_dvd_q : g ∣ q := Nat.gcd_dvd_left q m
    have hg_dvd_m : g ∣ m := Nat.gcd_dvd_right q m
    have hg_pos : 0 < g := Nat.pos_of_ne_zero (fun h0 => by
      rw [h0] at hg_dvd_m; rcases hg_dvd_m with ⟨_, hk⟩; omega)
    by_cases hg1 : g = 1
    · exact hg1
    · exfalso
      rcases hg_dvd_m with ⟨j, hj_mul_r⟩
      have hj_mul : j * g = m := by rw [Nat.mul_comm]; exact hj_mul_r.symm
      have hj1 : 1 ≤ j := by
        by_cases hj0 : j = 0
        · rw [hj0, Nat.zero_mul] at hj_mul; omega
        · omega
      have hjm : j < m := by
        have hg_ge2 : 2 ≤ g := by omega
        have : j * 2 ≤ j * g := Nat.mul_le_mul_left j hg_ge2
        omega
      rcases hg_dvd_q with ⟨q', hq'⟩
      have hfj : f j = q' := by
        rw [hf_formula j hj1 hjm]
        have hjq : j * q = m * q' := by
          calc j * q = j * (g * q') := by rw [hq']
            _ = (j * g) * q' := (Nat.mul_assoc j g q').symm
            _ = m * q' := by rw [hj_mul]
        rw [hjq, Nat.mul_div_right q' hm_pos]
      have hfmj : f (m - j) = q - q' := by
        rw [hf_formula (m - j) (by omega) (by omega)]
        have hmjq : (m - j) * q = m * (q - q') := by
          have h1 : (m - j) * q + j * q = m * q := by
            rw [← Nat.add_mul, show m - j + j = m by omega]
          have h2 : j * q = m * q' := by
            calc j * q = j * (g * q') := by rw [hq']
              _ = (j * g) * q' := (Nat.mul_assoc j g q').symm
              _ = m * q' := by rw [hj_mul]
          have h3 : m * (q - q') + m * q' = m * q := by
            rw [← Nat.mul_add, show q - q' + q' = q by
              have : 1 * q' ≤ g * q' := Nat.mul_le_mul_right q' (by omega)
              omega]
          omega
        rw [hmjq, Nat.mul_div_right _ hm_pos]
      have hc2 := hcase2 j hj1 (by omega)
      have hq'_le : q' ≤ q := by
        have : 1 * q' ≤ g * q' := Nat.mul_le_mul_right q' (by omega)
        omega
      omega
  have htake_eq : ∀ k : Nat, k ≤ n → letterCount bit1 (w.take k) = ((k + 1) * q) / m := by
    intro k hk
    have := hf_formula (k + 1) (by omega) (by omega)
    simpa [f] using this
  have hword_eq_of_prefix_ones : ∀ (u v : Word 2),
      u.length = v.length →
      (∀ k : Nat, k ≤ u.length → letterCount bit1 (u.take k) = letterCount bit1 (v.take k)) → u = v := by
    intro u
    induction u with
    | nil =>
      intro v hlv _
      exact (List.length_eq_zero_iff.mp hlv.symm).symm
    | cons x xs ih =>
      intro v hlv hp_all
      cases v with
      | nil => simp at hlv
      | cons y ys =>
        have hp1 := hp_all 1 (by simp)
        simp only [List.take_succ_cons, List.take_zero] at hp1
        have hxy : x = y := by
          rcases fin2_dichotomy x with rfl | rfl <;> rcases fin2_dichotomy y with rfl | rfl
          · rfl
          · simp [letterCount, bit0_ne_bit1] at hp1
          · have hne : bit1 ≠ bit0 := fun h => bit0_ne_bit1 h.symm
            simp [letterCount, bit0_ne_bit1, hne] at hp1
          · rfl
        subst hxy
        congr 1
        apply ih ys (by simp at hlv; exact hlv)
        intro k hk
        have hpk := hp_all (k + 1) (by simp; omega)
        simp only [List.take_succ_cons, letterCount_cons] at hpk
        omega
  have hcm_len : (centralMech m q).length = n := by rw [length_centralMech]; omega
  have hw_eq_cm : w = centralMech m q := by
    apply hword_eq_of_prefix_ones w (centralMech m q) (by omega)
    intro k hk
    rw [hlen] at hk
    rw [htake_eq k hk]
    unfold centralMech
    rw [take_mechSlice m q 0 1 k (m - 2) (by omega),
        ones_mechSlice m q 0 (by omega) hm_pos 1 k]
    have hq_div : (1 * q + 0) / m = 0 := by simp [Nat.div_eq_of_lt hqm]
    rw [hq_div, Nat.sub_zero, Nat.add_zero ((1 + k) * q), show 1 + k = k + 1 by omega]
  exact ⟨hq1, hqm, hcop, hw_eq_cm⟩

theorem centralCount_eq_totient (n : Nat) :
    centralCount n = totient (n + 2) := by
  let mapped := (coprimeList (n + 2)).map (centralMech (n + 2))
  have hcop_lt : ∀ q ∈ coprimeList (n + 2), 1 ≤ q ∧ q < n + 2 ∧ Nat.gcd q (n + 2) = 1 := by
    intro q hq
    rcases mem_coprimeList_iff.mp hq with ⟨hq1, hqm, hcop⟩
    have hne : q ≠ n + 2 := by
      intro heq; subst heq; rw [Nat.gcd_self] at hcop; omega
    exact ⟨hq1, by omega, hcop⟩
  have hnd_mapped : ListNodup mapped := by
    have haux : ∀ qs : List Nat, ListNodup qs →
        (∀ q ∈ qs, 1 ≤ q ∧ q < n + 2 ∧ Nat.gcd q (n + 2) = 1) →
        ListNodup (qs.map (centralMech (n + 2))) := by
      intro qs hnd hqs
      induction qs with
      | nil => exact .nil
      | cons q qs ih =>
        cases hnd with
        | cons hnot hnd_qs =>
          refine .cons ?_ (ih hnd_qs (fun x hx => hqs x (List.mem_cons_of_mem q hx)))
          intro w hw heq
          rcases List.mem_map.mp hw with ⟨q', hq'_in, rfl⟩
          rcases hqs q List.mem_cons_self with ⟨hq1, hqm, hcop⟩
          rcases hqs q' (List.mem_cons_of_mem q hq'_in) with ⟨hq'1, hq'm, hcop'⟩
          have ho1 := (centralMech_in_central n q hq1 hqm hcop).2
          have ho2 := (centralMech_in_central n q' hq'1 hq'm hcop').2
          rw [heq] at ho1
          exact hnot q' hq'_in (by omega)
    exact haux (coprimeList (n + 2)) (nodup_coprimeList (n + 2)) hcop_lt
  have hnd_cent : ListNodup (centralList n) := nodup_filter _ (nodup_allWords 2 n)
  have hsub1 : ∀ w ∈ mapped, w ∈ centralList n := by
    intro w hw
    rcases List.mem_map.mp hw with ⟨q, hq_in, rfl⟩
    rcases hcop_lt q hq_in with ⟨hq1, hqm, hcop⟩
    exact (centralMech_in_central n q hq1 hqm hcop).1
  have hsub2 : ∀ w ∈ centralList n, w ∈ mapped := by
    intro w hw
    rcases central_unique_and_coprime n hw with ⟨hq1, hqm, hcop, hw_eq⟩
    refine List.mem_map.mpr ⟨letterCount bit1 w + 1,
      mem_coprimeList_iff.mpr ⟨hq1, by omega, hcop⟩, hw_eq.symm⟩
  have hle1 := nodup_length_le_of_subset hnd_mapped hsub1
  have hle2 := nodup_length_le_of_subset hnd_cent hsub2
  unfold centralCount totient
  have hlen_m : mapped.length = (coprimeList (n + 2)).length := List.length_map _
  omega

/-- Lipatov sum `∑_{i=1}^n (n + 1 - i) * φ(i)`. -/
def lipatovSum (n : Nat) : Nat → Nat
  | 0 => 0
  | m + 1 => lipatovSum n m + (n - m) * totient (m + 1)

def totientSum : Nat → Nat
  | 0 => 0
  | m + 1 => totientSum m + totient (m + 1)

theorem rightSpecialCount_eq_totientSum :
    ∀ n : Nat, rightSpecialCount n = totientSum (n + 1)
  | 0 => by decide
  | n + 1 => by
    rw [rightSpecialCount_succ n, rightSpecialCount_eq_totientSum n,
        centralCount_eq_totient n]
    rfl

private theorem lipatovSum_succ_step (n : Nat) :
    ∀ m : Nat, m ≤ n → lipatovSum (n + 1) m = lipatovSum n m + totientSum m
  | 0, _ => rfl
  | m + 1, hm => by
    simp only [lipatovSum, totientSum]
    rw [lipatovSum_succ_step n m (by omega)]
    have hsub : (n + 1 - m) * totient (m + 1) = (n - m) * totient (m + 1) + totient (m + 1) := by
      rw [show n + 1 - m = (n - m) + 1 by omega, Nat.add_mul, Nat.one_mul]
    omega

/--
  **Lipatov's Exact Formula (1982):**
  For every `n ≥ 0`, `b_2(n) = 1 + ∑_{i=1}^n (n + 1 - i) φ(i)`.
-/
theorem balancedCount_two_eq_lipatov :
    ∀ n : Nat, balancedCount 2 n = 1 + lipatovSum n n
  | 0 => by decide
  | n + 1 => by
    rw [balancedCount_two_succ n, balancedCount_two_eq_lipatov n,
        rightSpecialCount_eq_totientSum n]
    simp only [lipatovSum]
    rw [show n + 1 - n = 1 by omega, Nat.one_mul,
        lipatovSum_succ_step n n (Nat.le_refl n)]
    simp only [totientSum]
    omega

/-- **Exact Second Difference of `b_2(n)`:** `b_2(n + 2) + b_2(n) = 2 * b_2(n + 1) + φ(n + 2)`. -/
theorem delta2_balancedCount_two (n : Nat) :
    balancedCount 2 (n + 2) + balancedCount 2 n =
      2 * balancedCount 2 (n + 1) + totient (n + 2) := by
  have h1 := balancedCount_two_succ n
  have h2 : balancedCount 2 (n + 2) = balancedCount 2 (n + 1) + rightSpecialCount (n + 1) :=
    balancedCount_two_succ (n + 1)
  have hr := rightSpecialCount_succ n
  have hc := centralCount_eq_totient n
  omega

private theorem eq_replicate_of_all_eq {α : Type u} (b : α) :
    ∀ (xs : List α), (∀ x ∈ xs, x = b) → xs = List.replicate xs.length b
  | [], _ => rfl
  | c :: cs, h => by
    have hc : c = b := h c List.mem_cons_self
    have ih := eq_replicate_of_all_eq b cs (fun d hd => h d (List.mem_cons_of_mem c hd))
    rw [hc, List.length_cons, List.replicate_succ, ← ih]

/-- For `n ≥ 1`, `surj_2(n) + 2 = b_2(n)` (the only non-surjective binary words are `0^n` and `1^n`). -/
theorem surjBalancedCount_two_add_two {n : Nat} (hn : 1 ≤ n) :
    surjBalancedCount 2 n + 2 = balancedCount 2 n := by
  let w0 := List.replicate n bit0
  let w1 := List.replicate n bit1
  have hpart : ∀ (xs : List (Word 2)),
      xs.length = (xs.filter (usesAllLettersBool 2)).length +
                  (xs.filter fun w => !usesAllLettersBool 2 w).length := by
    intro xs; induction xs with
    | nil => rfl
    | cons x xs ih =>
      simp only [List.filter]
      cases h : usesAllLettersBool 2 x <;> simp [h] <;> omega
  let nonSurj := (balancedWordsList 2 n).filter fun w => !usesAllLettersBool 2 w
  have hnd_ns : ListNodup nonSurj := nodup_filter _ (nodup_filter _ (nodup_allWords 2 n))
  have hw0_ne_w1 : w0 ≠ w1 := by
    cases n with
    | zero => omega
    | succ m =>
      intro h; dsimp [w0, w1] at h
      injection h with hbit _; exact bit0_ne_bit1 hbit
  have hnd_01 : ListNodup [w0, w1] :=
    .cons (fun y hy heq => by simp at hy; subst hy; exact hw0_ne_w1 heq)
      (.cons (fun _ hy => nomatch hy) .nil)
  have hbal_rep : ∀ b : Fin 2, IsBalanced (List.replicate n b) := by
    intro b; rw [isBalanced_two_iff_ones]
    intro u v hu hv hlen
    have hall_eq : ∀ z : Word 2, IsFactor z (List.replicate n b) → z = List.replicate z.length b := by
      intro z ⟨p, s, hp⟩
      apply eq_replicate_of_all_eq b z
      intro c hc
      have hmem_app : c ∈ p ++ z ++ s :=
        List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inr hc)))
      rw [hp] at hmem_app
      exact List.eq_of_mem_replicate hmem_app
    rw [hall_eq u hu, hall_eq v hv, hlen]; simp [natDist]
  have hmem_ns : ∀ b : Fin 2, List.replicate n b ∈ nonSurj := by
    intro b
    have hnot_surj : usesAllLettersBool 2 (List.replicate n b) = false := by
      apply Bool.eq_false_iff.mpr; intro hs
      have hall := (usesAllLettersBool_eq_true_iff 2 _).mp hs
      rcases fin2_dichotomy b with rfl | rfl
      · have := List.eq_of_mem_replicate (hall bit1)
        exact bit0_ne_bit1 this.symm
      · have := List.eq_of_mem_replicate (hall bit0)
        exact bit0_ne_bit1 this
    exact List.mem_filter.mpr ⟨List.mem_filter.mpr
      ⟨(mem_allWords_iff 2 n _).mpr List.length_replicate,
       (isBalancedBool_eq_true_iff _).mpr (hbal_rep b)⟩,
      by simp [hnot_surj]⟩
  have hsub1 : ∀ w ∈ [w0, w1], w ∈ nonSurj := by
    intro w hw; simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl
    · exact hmem_ns bit0
    · exact hmem_ns bit1
  have hsub2 : ∀ w ∈ nonSurj, w ∈ [w0, w1] := by
    intro w hw
    rcases List.mem_filter.mp hw with ⟨hw_b, hw_ns⟩
    rcases List.mem_filter.mp hw_b with ⟨hw_all, _⟩
    have hlen_w : w.length = n := (mem_allWords_iff 2 n w).mp hw_all
    by_cases h0_in : bit0 ∈ w
    · by_cases h1_in : bit1 ∈ w
      · exfalso
        have hsurj : UsesAllLetters 2 w := by
          intro a; rcases fin2_dichotomy a with rfl | rfl <;> assumption
        have hb_true := (usesAllLettersBool_eq_true_iff 2 w).mpr hsurj
        simp [hb_true] at hw_ns
      · have hw_rep : w = w0 := by
          dsimp [w0]; rw [← hlen_w]
          apply eq_replicate_of_all_eq bit0 w
          intro x hx; rcases fin2_dichotomy x with rfl | rfl
          · rfl
          · exact absurd hx h1_in
        simp [hw_rep]
    · have hw_rep : w = w1 := by
        dsimp [w1]; rw [← hlen_w]
        apply eq_replicate_of_all_eq bit1 w
        intro x hx; rcases fin2_dichotomy x with rfl | rfl
        · exact absurd hx h0_in
        · rfl
      simp [hw_rep]
  have hle1 := nodup_length_le_of_subset hnd_01 hsub1
  have hle2 := nodup_length_le_of_subset hnd_ns hsub2
  have hns_len : nonSurj.length = 2 := by simp at hle1 hle2; omega
  have hp := hpart (balancedWordsList 2 n)
  unfold surjBalancedCount surjBalancedWordsList balancedCount
  dsimp [nonSurj] at hns_len
  omega

/-! ## Section 5D: Non-Periodicity of `φ(m) mod p` and Binary (`k = 2`) Non-Rationality -/

def fact : Nat → Nat
  | 0 => 1
  | n + 1 => (n + 1) * fact n

theorem fact_pos : ∀ n : Nat, 0 < fact n
  | 0 => by decide
  | n + 1 => Nat.mul_pos (by omega) (fact_pos n)

theorem dvd_fact {k n : Nat} (hk1 : 1 ≤ k) : k ≤ n → k ∣ fact n := by
  induction n with
  | zero => intro hle; omega
  | succ n ih =>
    intro hle
    simp only [fact]
    by_cases hkn : k ≤ n
    · exact Nat.dvd_trans (ih hkn) (Nat.dvd_mul_left (fact n) (n + 1))
    · have heq : k = n + 1 := by omega
      rw [heq]
      exact Nat.dvd_mul_right (n + 1) (fact n)

theorem exists_prime_dvd {n : Nat} (hn : 2 ≤ n) : ∃ q : Nat, IsPrime q ∧ q ∣ n := by
  let cand := (rangeList (n + 1)).filter fun d => decide (2 ≤ d ∧ d ∣ n)
  have hn_mem : n ∈ cand :=
    List.mem_filter.mpr ⟨mem_rangeList.mpr (by omega), decide_eq_true ⟨hn, Nat.dvd_refl n⟩⟩
  have hne : cand ≠ [] := fun h => by rw [h] at hn_mem; nomatch hn_mem
  let q := listMinDefault n cand
  rcases listMinDefault_mem_and_le n cand hne with ⟨hq_mem, hq_min⟩
  rcases List.mem_filter.mp hq_mem with ⟨_, hq_dec⟩
  rcases of_decide_eq_true hq_dec with ⟨hq2, hqn⟩
  refine ⟨q, ⟨hq2, fun d hdq => ?_⟩, hqn⟩
  have hd_pos : 0 < d := Nat.pos_of_ne_zero (fun h0 => by
    rw [h0] at hdq; rcases hdq with ⟨_, hk⟩; omega)
  by_cases hd1 : d = 1
  · exact Or.inl hd1
  · right
    have hd2 : 2 ≤ d := by omega
    have hdn : d ∣ n := Nat.dvd_trans hdq hqn
    have hd_le_q : d ≤ q := Nat.le_of_dvd (by omega) hdq
    have hd_le_n : d ≤ n := Nat.le_of_dvd (by omega) hdn
    have hd_mem : d ∈ cand :=
      List.mem_filter.mpr ⟨mem_rangeList.mpr (by omega), decide_eq_true ⟨hd2, hdn⟩⟩
    have hq_le_d : q ≤ d := hq_min d hd_mem
    omega

theorem gcd_prime_eq_one_of_not_dvd {p a : Nat} (hp : IsPrime p) (hnd : ¬ (p ∣ a)) :
    Nat.gcd p a = 1 := by
  rcases hp.2 (Nat.gcd p a) (Nat.gcd_dvd_left p a) with hg1 | hgp
  · exact hg1
  · exfalso
    apply hnd
    have := Nat.gcd_dvd_right p a
    rwa [hgp] at this

theorem prime_dvd_mul {p a b : Nat} (hp : IsPrime p) (h : p ∣ a * b) : p ∣ a ∨ p ∣ b := by
  by_cases ha : p ∣ a
  · exact Or.inl ha
  · exact Or.inr (coprime_dvd_of_dvd_mul (gcd_prime_eq_one_of_not_dvd hp ha) h)

theorem prime_dvd_pow {p a : Nat} (hp : IsPrime p) : ∀ e : Nat, p ∣ a ^ e → p ∣ a
  | 0, h => by
    have hle : p ≤ 1 := Nat.le_of_dvd (by decide) h
    have := hp.1
    omega
  | e + 1, h => by
    rw [Nat.pow_succ] at h
    rcases prime_dvd_mul hp h with h1 | h2
    · exact prime_dvd_pow hp e h1
    · exact h2

theorem isPrime_two : IsPrime 2 := by
  refine ⟨by decide, fun d hd => ?_⟩
  have hd_pos : 0 < d := Nat.pos_of_ne_zero (fun h0 => by
    rw [h0] at hd; rcases hd with ⟨_, hk⟩; omega)
  have hd_le : d ≤ 2 := Nat.le_of_dvd (by decide) hd
  omega

theorem isPrime_three : IsPrime 3 := by
  refine ⟨by decide, fun d hd => ?_⟩
  have hd_pos : 0 < d := Nat.pos_of_ne_zero (fun h0 => by
    rw [h0] at hd; rcases hd with ⟨_, hk⟩; omega)
  have hd_le : d ≤ 3 := Nat.le_of_dvd (by decide) hd
  by_cases hd2 : d = 2
  · subst hd2; rcases hd with ⟨k, hk⟩; omega
  · omega

private theorem pow_two_pos : ∀ k : Nat, 0 < 2 ^ k
  | 0 => by decide
  | k + 1 => by rw [Nat.pow_succ]; have := pow_two_pos k; omega

private theorem le_pow_two_succ : ∀ k : Nat, k + 1 ≤ 2 ^ k
  | 0 => by decide
  | k + 1 => by
    have ih := le_pow_two_succ k
    rw [Nat.pow_succ]
    omega

private theorem nodup_rangeList : ∀ n : Nat, ListNodup (rangeList n)
  | 0 => .nil
  | n + 1 => by
    refine nodup_append (nodup_rangeList n) (.cons (fun _ hm => nomatch hm) .nil) ?_
    intro x hx y hy hxy
    simp at hy; subst hy
    have := mem_rangeList.mp hx; omega

private theorem nodup_map_rangeList_of_lt {β : Type u} (f : Nat → β) :
    ∀ n : Nat, (∀ i j : Nat, i < j → j < n → f i ≠ f j) → ListNodup ((rangeList n).map f)
  | 0, _ => .nil
  | n + 1, hinj => by
    simp only [rangeList, List.map_append, List.map]
    refine nodup_append
      (nodup_map_rangeList_of_lt f n (fun i j hij hjn => hinj i j hij (by omega)))
      (.cons (fun _ hm => nomatch hm) .nil) ?_
    intro x hx y hy hxy
    simp at hy; subst hy
    rcases List.mem_map.mp hx with ⟨i, hi_mem, rfl⟩
    exact hinj i n (mem_rangeList.mp hi_mem) (by omega) hxy

theorem totient_pow_two {e : Nat} (he : 1 ≤ e) : totient (2 ^ e) = 2 ^ (e - 1) := by
  have he_eq : 2 ^ e = 2 ^ (e - 1) * 2 := by
    conv => lhs; rw [show e = (e - 1) + 1 by omega]
    exact Nat.pow_succ 2 (e - 1)
  have hgcd_odd : ∀ x : Nat, Nat.gcd x (2 ^ e) = 1 ↔ x % 2 = 1 := by
    intro x
    constructor
    · intro hcop
      by_cases hodd : x % 2 = 1
      · exact hodd
      · exfalso
        have hx2 : 2 ∣ x := ⟨x / 2, by omega⟩
        have he2 : 2 ∣ 2 ^ e := ⟨2 ^ (e - 1), by rw [he_eq, Nat.mul_comm]⟩
        have hg2 : 2 ∣ Nat.gcd x (2 ^ e) := Nat.dvd_gcd hx2 he2
        rw [hcop] at hg2
        have := Nat.le_of_dvd (by decide) hg2
        omega
    · intro hodd
      let g := Nat.gcd x (2 ^ e)
      have hg_pos : 0 < g := Nat.pos_of_ne_zero (fun h0 => by
        have hd : g ∣ 2 ^ e := Nat.gcd_dvd_right x (2 ^ e)
        rw [h0] at hd; rcases hd with ⟨_, hk⟩; have := pow_two_pos e; omega)
      by_cases hg1 : g = 1
      · exact hg1
      · exfalso
        rcases exists_prime_dvd (n := g) (by omega) with ⟨r, hr, hrg⟩
        have hr_pow : r ∣ 2 ^ e := Nat.dvd_trans hrg (Nat.gcd_dvd_right x (2 ^ e))
        have hr2 : r ∣ 2 := prime_dvd_pow hr e hr_pow
        have hr_eq2 : r = 2 := by
          rcases isPrime_two.2 r hr2 with rfl | rfl
          · have := hr.1; omega
          · rfl
        have h2x : 2 ∣ x := hr_eq2 ▸ Nat.dvd_trans hrg (Nat.gcd_dvd_left x (2 ^ e))
        rcases h2x with ⟨k, hk⟩
        omega
  let odds := (rangeList (2 ^ (e - 1))).map fun i => 2 * i + 1
  have hnd_odds : ListNodup odds :=
    nodup_map_rangeList_of_lt (fun i => 2 * i + 1) (2 ^ (e - 1))
      (fun i j hij _ h => by dsimp at h; omega)
  have hsub1 : ∀ q ∈ odds, q ∈ coprimeList (2 ^ e) := by
    intro q hq
    rcases List.mem_map.mp hq with ⟨i, hi_mem, rfl⟩
    have hi_lt : i < 2 ^ (e - 1) := mem_rangeList.mp hi_mem
    exact mem_coprimeList_iff.mpr ⟨by omega, by omega, (hgcd_odd (2 * i + 1)).mpr (by omega)⟩
  have hsub2 : ∀ q ∈ coprimeList (2 ^ e), q ∈ odds := by
    intro q hq
    rcases mem_coprimeList_iff.mp hq with ⟨hq1, hqle, hcop⟩
    have hodd : q % 2 = 1 := (hgcd_odd q).mp hcop
    refine List.mem_map.mpr ⟨(q - 1) / 2, mem_rangeList.mpr (by omega), by omega⟩
  have hle1 := nodup_length_le_of_subset hnd_odds hsub1
  have hle2 := nodup_length_le_of_subset (nodup_coprimeList (2 ^ e)) hsub2
  have hlen_odds : odds.length = 2 ^ (e - 1) := by
    dsimp [odds]; rw [List.length_map, length_rangeList]
  unfold totient
  omega

private theorem dvd_of_add_mod_eq {X Y q : Nat} (hq : 0 < q) (h : (X + Y) % q = X % q) :
    q ∣ Y := by
  have h1 := Nat.div_add_mod (X + Y) q
  have h2 := Nat.div_add_mod X q
  have hle : X / q ≤ (X + Y) / q := nat_div_mono hq (Nat.le_add_right X Y)
  refine ⟨(X + Y) / q - X / q, ?_⟩
  rw [Nat.mul_sub_left_distrib]
  generalize hd1 : (X + Y) / q = d1 at h1 hle
  generalize hd2 : X / q = d2 at h2 hle
  generalize hr1 : (X + Y) % q = r1 at h1 h
  generalize hr2 : X % q = r2 at h2 h
  have hmul_le : q * d2 ≤ q * d1 := Nat.mul_le_mul_left q hle
  omega

private theorem filter_ne_length_of_nodup_mem {x0 : Nat} :
    ∀ {xs : List Nat}, ListNodup xs → x0 ∈ xs →
      (xs.filter fun x => decide (x ≠ x0)).length + 1 = xs.length
  | [], _, hm => nomatch hm
  | x :: xs, .cons hnot hnd, hm => by
    simp only [List.filter]
    by_cases hxx0 : x = x0
    · subst hxx0
      have hfalse : decide (x ≠ x) = false := decide_eq_false (fun h => h rfl)
      rw [hfalse]
      simp only [Bool.false_eq_true, ↓reduceIte, List.length_cons]
      have hall_ne : ∀ y ∈ xs, y ≠ x := fun y hy heq => hnot y hy heq.symm
      have hfilt_all : xs.filter (fun y => decide (y ≠ x)) = xs := by
        clear hnot hnd hm
        induction xs with
        | nil => rfl
        | cons z zs ih =>
          have hz : decide (z ≠ x) = true := decide_eq_true (hall_ne z List.mem_cons_self)
          simp only [List.filter, hz, ↓reduceIte,
                     ih (fun y hy => hall_ne y (List.mem_cons_of_mem z hy))]
      rw [hfilt_all]
    · cases hm with
      | head _ => exact absurd rfl hxx0
      | tail _ hmem =>
        have ih := filter_ne_length_of_nodup_mem hnd hmem
        have htrue : decide (x ≠ x0) = true := decide_eq_true hxx0
        rw [htrue]
        simp only [↓reduceIte, List.length_cons]
        omega

private theorem ap_mod_surj_and_nodup {q a b : Nat} (hq : IsPrime q) (hnd : ¬ (q ∣ b)) :
    let resList := (rangeList q).map fun k => (k * b + a) % q
    ListNodup resList ∧ ∀ r : Nat, r < q → r ∈ resList := by
  have hq_pos : 0 < q := by have := hq.1; omega
  let resList := (rangeList q).map fun k => (k * b + a) % q
  have hnodup : ListNodup resList := by
    apply nodup_map_rangeList_of_lt
    intro i j hij _ heq
    have hrew : j * b + a = (i * b + a) + (j - i) * b := by
      have : (j - i) * b + i * b = j * b := by
        rw [← Nat.add_mul, show j - i + i = j by omega]
      omega
    rw [hrew] at heq
    have hdvd : q ∣ (j - i) * b := dvd_of_add_mod_eq hq_pos heq.symm
    rcases prime_dvd_mul hq hdvd with hji | hb
    · have hle : q ≤ j - i := Nat.le_of_dvd (by omega) hji
      omega
    · exact hnd hb
  refine ⟨hnodup, fun r hr => ?_⟩
  by_cases hmem : r ∈ resList
  · exact hmem
  · exfalso
    let withoutR := (rangeList q).filter fun x => decide (x ≠ r)
    have hlen_wr : withoutR.length + 1 = q := by
      have := filter_ne_length_of_nodup_mem (x0 := r) (nodup_rangeList q) (mem_rangeList.mpr hr)
      rw [length_rangeList] at this
      exact this
    have hsub : ∀ x ∈ resList, x ∈ withoutR := by
      intro x hx
      rcases List.mem_map.mp hx with ⟨k, _, rfl⟩
      have hlt : (k * b + a) % q < q := Nat.mod_lt _ hq_pos
      have hne : (k * b + a) % q ≠ r := fun heq => hmem (heq ▸ hx)
      exact List.mem_filter.mpr ⟨mem_rangeList.mpr hlt, decide_eq_true hne⟩
    have hle := nodup_length_le_of_subset hnodup hsub
    have hres_len : resList.length = q := by dsimp [resList]; rw [List.length_map, length_rangeList]
    omega

private theorem exists_ap_dvd {q a b : Nat} (hq : IsPrime q) (hnd : ¬ (q ∣ b)) :
    ∃ k : Nat, k < q ∧ q ∣ (k * b + a) := by
  have hq_pos : 0 < q := by have := hq.1; omega
  rcases ap_mod_surj_and_nodup (a := a) hq hnd with ⟨_, hsurj⟩
  have h0 := hsurj 0 hq_pos
  rcases List.mem_map.mp h0 with ⟨k, hk_mem, hk_mod⟩
  exact ⟨k, mem_rangeList.mp hk_mem, Nat.dvd_of_mod_eq_zero hk_mod⟩

private theorem count_ap_coprime_eq_pred {q a b : Nat} (hq : IsPrime q) (hnd : ¬ (q ∣ b)) :
    ((rangeList q).filter fun k => decide (Nat.gcd (k * b + a) q = 1)).length = q - 1 := by
  have hq_pos : 0 < q := by have := hq.1; omega
  rcases ap_mod_surj_and_nodup (a := a) hq hnd with ⟨hnodup, hsurj⟩
  have hgcd_iff : ∀ y : Nat, Nat.gcd y q = 1 ↔ y % q ≠ 0 := by
    intro y
    constructor
    · intro hcop hmod0
      have hdvd : q ∣ y := Nat.dvd_of_mod_eq_zero hmod0
      have hgy : q ∣ Nat.gcd y q := Nat.dvd_gcd hdvd (Nat.dvd_refl q)
      rw [hcop] at hgy
      have := Nat.le_of_dvd (by decide) hgy
      have := hq.1; omega
    · intro hmod_nz
      have hnd_y : ¬ (q ∣ y) := fun hd => hmod_nz (Nat.mod_eq_zero_of_dvd hd)
      rw [Nat.gcd_comm]
      exact gcd_prime_eq_one_of_not_dvd hq hnd_y
  have hfilt_eq : ((rangeList q).filter fun k => decide (Nat.gcd (k * b + a) q = 1)) =
      ((rangeList q).filter fun k => decide ((k * b + a) % q ≠ 0)) := by
    congr 1
    funext k
    apply Bool.eq_iff_iff.mpr
    simp only [decide_eq_true_eq, hgcd_iff]
  have hmap_filt : ∀ (xs : List Nat),
      ((xs.map fun k => (k * b + a) % q).filter fun r => decide (r ≠ 0)).length =
      (xs.filter fun k => decide ((k * b + a) % q ≠ 0)).length := by
    intro xs; induction xs with
    | nil => rfl
    | cons x xs ih =>
      simp only [List.map_cons, List.filter]
      cases hd : decide (((x * b + a) % q) ≠ 0) <;>
        simp only [hd, Bool.false_eq_true, ↓reduceIte, List.length_cons, ih]
  rw [hfilt_eq, ← hmap_filt]
  have h0_mem := hsurj 0 hq_pos
  have hlen_sub := filter_ne_length_of_nodup_mem (x0 := 0) hnodup h0_mem
  rw [List.length_map, length_rangeList] at hlen_sub
  omega

private theorem gcd_mul_right_eq_one_iff {x a b : Nat} (ha : 0 < a) (hb : 0 < b) :
    Nat.gcd x (a * b) = 1 ↔ Nat.gcd x a = 1 ∧ Nat.gcd x b = 1 := by
  constructor
  · intro hcop
    have h1 : Nat.gcd x a = 1 := by
      let d := Nat.gcd x a
      have hd_pos : 0 < d := Nat.pos_of_ne_zero (fun h0 => by
        have hd : d ∣ a := Nat.gcd_dvd_right x a
        rw [h0] at hd; rcases hd with ⟨_, hk⟩; omega)
      have hd_ab : d ∣ a * b := Nat.dvd_trans (Nat.gcd_dvd_right x a) (Nat.dvd_mul_right a b)
      have hd_g : d ∣ Nat.gcd x (a * b) := Nat.dvd_gcd (Nat.gcd_dvd_left x a) hd_ab
      rw [hcop] at hd_g
      have := Nat.le_of_dvd (by decide) hd_g
      omega
    have h2 : Nat.gcd x b = 1 := by
      let d := Nat.gcd x b
      have hd_pos : 0 < d := Nat.pos_of_ne_zero (fun h0 => by
        have hd : d ∣ b := Nat.gcd_dvd_right x b
        rw [h0] at hd; rcases hd with ⟨_, hk⟩; omega)
      have hd_ab : d ∣ a * b := Nat.dvd_trans (Nat.gcd_dvd_right x b) (Nat.dvd_mul_left b a)
      have hd_g : d ∣ Nat.gcd x (a * b) := Nat.dvd_gcd (Nat.gcd_dvd_left x b) hd_ab
      rw [hcop] at hd_g
      have := Nat.le_of_dvd (by decide) hd_g
      omega
    exact ⟨h1, h2⟩
  · rintro ⟨ha1, hb1⟩
    let g := Nat.gcd x (a * b)
    have hg_pos : 0 < g := Nat.pos_of_ne_zero (fun h0 => by
      have hd : g ∣ a * b := Nat.gcd_dvd_right x (a * b)
      rw [h0] at hd; rcases hd with ⟨_, hk⟩
      have hpos : 0 < a * b := Nat.mul_pos ha hb
      omega)
    by_cases hg1 : g = 1
    · exact hg1
    · exfalso
      rcases exists_prime_dvd (n := g) (by omega) with ⟨r, hr, hrg⟩
      have hrx : r ∣ x := Nat.dvd_trans hrg (Nat.gcd_dvd_left x (a * b))
      have hrab : r ∣ a * b := Nat.dvd_trans hrg (Nat.gcd_dvd_right x (a * b))
      rcases prime_dvd_mul hr hrab with hra | hrb
      · have hgxa : r ∣ Nat.gcd x a := Nat.dvd_gcd hrx hra
        rw [ha1] at hgxa
        have := Nat.le_of_dvd (by decide) hgxa; have := hr.1; omega
      · have hgxb : r ∣ Nat.gcd x b := Nat.dvd_gcd hrx hrb
        rw [hb1] at hgxb
        have := Nat.le_of_dvd (by decide) hgxb; have := hr.1; omega

private theorem gcd_mul_add_self (u s : Nat) : ∀ k : Nat, Nat.gcd (k * u + s) u = Nat.gcd s u
  | 0 => by simp
  | k + 1 => by
    rw [Nat.add_mul, Nat.one_mul, show k * u + u + s = (k * u + s) + u by omega,
        Nat.gcd_comm, Nat.gcd_add_self_right, Nat.gcd_comm]
    exact gcd_mul_add_self u s k

private theorem nodup_flatMap_disj {α β : Type u} {xs : List α} (f : α → List β)
    (hxs : ListNodup xs)
    (hf_nd : ∀ a ∈ xs, ListNodup (f a))
    (hdisj : ∀ a ∈ xs, ∀ b ∈ xs, a ≠ b → ∀ x ∈ f a, ∀ y ∈ f b, x ≠ y) :
    ListNodup (xs.flatMap f) := by
  induction xs with
  | nil => exact .nil
  | cons a xs ih =>
    cases hxs with
    | cons hnot hnd_xs =>
      simp only [List.flatMap_cons]
      refine nodup_append (hf_nd a List.mem_cons_self)
        (ih hnd_xs (fun b hb => hf_nd b (List.mem_cons_of_mem a hb))
            (fun b1 hb1 b2 hb2 hne =>
              hdisj b1 (List.mem_cons_of_mem a hb1) b2 (List.mem_cons_of_mem a hb2) hne)) ?_
      intro x hx y hy
      rcases List.mem_flatMap.mp hy with ⟨b, hb_in, hy_in⟩
      exact hdisj a List.mem_cons_self b (List.mem_cons_of_mem a hb_in) (hnot b hb_in) x hx y hy_in

theorem totient_mul_prime_of_not_dvd {q u : Nat} (hq : IsPrime q) (hnd : ¬ (q ∣ u)) (hu : 1 ≤ u) :
    totient (q * u) = (q - 1) * totient u := by
  have hq_pos : 0 < q := by have := hq.1; omega
  let fiber : Nat → List Nat := fun s =>
    ((rangeList q).filter fun k => decide (Nat.gcd (k * u + s) q = 1)).map fun k => k * u + s
  have hfiber_len : ∀ s : Nat, (fiber s).length = q - 1 := by
    intro s
    dsimp [fiber]
    rw [List.length_map]
    exact count_ap_coprime_eq_pred hq hnd
  have hfiber_nd : ∀ s : Nat, ListNodup (fiber s) := by
    intro s
    dsimp [fiber]
    refine nodup_map_of_inj (fun k => k * u + s) ?_
      (nodup_filter _ (nodup_rangeList q))
    intro k1 k2 heq
    dsimp at heq
    have hku : k1 * u = k2 * u := by omega
    by_cases hlt : k1 < k2
    · have : 1 * u ≤ (k2 - k1) * u := Nat.mul_le_mul_right u (by omega)
      rw [Nat.sub_mul] at this; omega
    · by_cases hgt : k2 < k1
      · have : 1 * u ≤ (k1 - k2) * u := Nat.mul_le_mul_right u (by omega)
        rw [Nat.sub_mul] at this; omega
      · omega
  let allCand := (coprimeList u).flatMap fiber
  have hall_nd : ListNodup allCand := by
    refine nodup_flatMap_disj fiber (nodup_coprimeList u) (fun s _ => hfiber_nd s) ?_
    intro s1 hs1 s2 hs2 hs_ne x hx y hy hxy
    rcases mem_coprimeList_iff.mp hs1 with ⟨hs1_ge, hs1_le, _⟩
    rcases mem_coprimeList_iff.mp hs2 with ⟨hs2_ge, hs2_le, _⟩
    rcases List.mem_map.mp hx with ⟨k1, _, rfl⟩
    rcases List.mem_map.mp hy with ⟨k2, _, rfl⟩
    by_cases hk : k1 ≤ k2
    · by_cases hkeq : k1 = k2
      · subst hkeq; exact hs_ne (by omega)
      · have : 1 * u ≤ (k2 - k1) * u := Nat.mul_le_mul_right u (by omega)
        rw [Nat.sub_mul] at this; omega
    · have : 1 * u ≤ (k1 - k2) * u := Nat.mul_le_mul_right u (by omega)
      rw [Nat.sub_mul] at this; omega
  have hall_len : allCand.length = (q - 1) * totient u := by
    have haux : ∀ ss : List Nat, (ss.flatMap fiber).length = (q - 1) * ss.length := by
      intro ss; induction ss with
      | nil => simp
      | cons s ss ih =>
        simp only [List.flatMap_cons, List.length_append, List.length_cons,
                   hfiber_len s, ih, Nat.mul_add, Nat.mul_one]
        omega
    exact haux (coprimeList u)
  have hsub1 : ∀ x ∈ allCand, x ∈ coprimeList (q * u) := by
    intro x hx
    rcases List.mem_flatMap.mp hx with ⟨s, hs_in, hx_fib⟩
    rcases mem_coprimeList_iff.mp hs_in with ⟨hs1, hsu, hcop_su⟩
    rcases List.mem_map.mp hx_fib with ⟨k, hk_filt, rfl⟩
    rcases List.mem_filter.mp hk_filt with ⟨hk_range, hk_gcd_dec⟩
    have hk_lt : k < q := mem_rangeList.mp hk_range
    have hk_gcd : Nat.gcd (k * u + s) q = 1 := of_decide_eq_true hk_gcd_dec
    have hle_qu : k * u + s ≤ q * u := by
      have : k * u ≤ (q - 1) * u := Nat.mul_le_mul_right u (by omega)
      have hqu : (q - 1) * u + 1 * u = q * u := by
        rw [← Nat.add_mul, show q - 1 + 1 = q by omega]
      rw [Nat.one_mul] at hqu
      omega
    have hcop_all : Nat.gcd (k * u + s) (q * u) = 1 :=
      (gcd_mul_right_eq_one_iff hq_pos hu).mpr ⟨hk_gcd, by rw [gcd_mul_add_self]; exact hcop_su⟩
    exact mem_coprimeList_iff.mpr ⟨by omega, hle_qu, hcop_all⟩
  have hsub2 : ∀ x ∈ coprimeList (q * u), x ∈ allCand := by
    intro x hx
    rcases mem_coprimeList_iff.mp hx with ⟨hx1, hxle, hcop_all⟩
    rcases (gcd_mul_right_eq_one_iff hq_pos hu).mp hcop_all with ⟨hcop_xq, hcop_xu⟩
    let k := (x - 1) / u
    let s := (x - 1) % u + 1
    have hdm := Nat.div_add_mod (x - 1) u
    have hrem : (x - 1) % u < u := Nat.mod_lt (x - 1) hu
    have hx_eq : k * u + s = x := by
      dsimp [k, s]
      rw [Nat.mul_comm ((x - 1) / u) u]
      generalize hd : (x - 1) / u = d at hdm ⊢
      generalize hr : (x - 1) % u = r at hdm hrem ⊢
      omega
    have hk_lt : k < q := by
      by_cases hlt : k < q
      · exact hlt
      · exfalso
        have hmul : q * u ≤ k * u := Nat.mul_le_mul_right u (by omega)
        omega
    have hcop_su : Nat.gcd s u = 1 := by
      rw [← gcd_mul_add_self u s k, hx_eq]
      exact hcop_xu
    have hs_in : s ∈ coprimeList u := mem_coprimeList_iff.mpr ⟨by omega, by omega, hcop_su⟩
    refine List.mem_flatMap.mpr ⟨s, hs_in, ?_⟩
    dsimp [fiber]
    refine List.mem_map.mpr ⟨k, ?_, hx_eq⟩
    exact List.mem_filter.mpr ⟨mem_rangeList.mpr hk_lt, decide_eq_true (hx_eq ▸ hcop_xq)⟩
  have hle1 := nodup_length_le_of_subset hall_nd hsub1
  have hle2 := nodup_length_le_of_subset (nodup_coprimeList (q * u)) hsub2
  unfold totient at hall_len ⊢
  omega

private def prodList : List Nat → Nat
  | [] => 1
  | x :: xs => x * prodList xs

private theorem prodList_eraseFirst (a : Nat) :
    ∀ {ys : List Nat}, a ∈ ys → prodList ys = a * prodList (eraseFirst a ys)
  | [], h => nomatch h
  | x :: xs, h => by
    simp only [eraseFirst]
    by_cases hax : a = x
    · subst hax; simp [prodList]
    · cases h with
      | head _ => exact absurd rfl hax
      | tail _ hmem =>
        simp only [hax, ↓reduceIte, prodList, prodList_eraseFirst a hmem]
        simp [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]

private theorem prodList_eq_of_nodup_eq_len :
    ∀ {xs ys : List Nat}, ListNodup xs → xs.length = ys.length →
      (∀ x ∈ xs, x ∈ ys) → prodList xs = prodList ys
  | [], [], _, _, _ => rfl
  | [], _ :: _, _, hlen, _ => by simp at hlen
  | x :: xs, ys, .cons hnot hnd, hlen, hsub => by
    have hx : x ∈ ys := hsub x List.mem_cons_self
    have hlen_er : ys.length = (eraseFirst x ys).length + 1 := length_eraseFirst_of_mem x hx
    have hsub' : ∀ z ∈ xs, z ∈ eraseFirst x ys := fun z hz =>
      mem_eraseFirst_of_ne (fun hzx => hnot z hz hzx.symm) (hsub z (List.mem_cons_of_mem x hz))
    have ih := prodList_eq_of_nodup_eq_len hnd (by simp at hlen; omega) hsub'
    rw [prodList_eraseFirst x hx, ← ih, prodList]

theorem fermat_little {q N : Nat} (hq : IsPrime q) (hnd : ¬ (q ∣ N)) :
    (N ^ (q - 1)) % q = 1 := by
  have hq2 : 2 ≤ q := hq.1
  have hN_pos : 0 < N := Nat.pos_of_ne_zero (fun h0 => hnd (h0 ▸ Nat.dvd_zero q))
  let posRes := (rangeList (q - 1)).map (· + 1)
  have hlen_posRes : posRes.length = q - 1 := by
    dsimp [posRes]; rw [List.length_map, length_rangeList]
  have hmem_posRes : ∀ x : Nat, x ∈ posRes ↔ 1 ≤ x ∧ x < q := by
    intro x; dsimp [posRes]
    simp only [List.mem_map, mem_rangeList]
    exact ⟨fun ⟨i, hi, heq⟩ => ⟨by omega, by omega⟩,
           fun ⟨hx1, hxq⟩ => ⟨x - 1, by omega, by omega⟩⟩
  let mulRes := posRes.map fun x => (N * x) % q
  have hnd_mulRes : ListNodup mulRes := by
    dsimp [mulRes, posRes]
    rw [List.map_map]
    apply nodup_map_rangeList_of_lt
    intro i j hij _ heq
    dsimp at heq
    have hrew : N * (j + 1) = N * (i + 1) + N * (j - i) := by
      rw [← Nat.mul_add, show i + 1 + (j - i) = j + 1 by omega]
    rw [hrew] at heq
    have hdvd : q ∣ N * (j - i) := dvd_of_add_mod_eq (by omega) heq.symm
    rcases prime_dvd_mul hq hdvd with hN | hji
    · exact hnd hN
    · have := Nat.le_of_dvd (by omega) hji; omega
  have hsub_mul : ∀ y ∈ mulRes, y ∈ posRes := by
    intro y hy
    rcases List.mem_map.mp hy with ⟨x, hx_in, rfl⟩
    rcases (hmem_posRes x).mp hx_in with ⟨hx1, hxq⟩
    have hlt : (N * x) % q < q := Nat.mod_lt _ (by omega)
    have hnz : (N * x) % q ≠ 0 := by
      intro h0
      rcases prime_dvd_mul hq (Nat.dvd_of_mod_eq_zero h0) with hN | hqx
      · exact hnd hN
      · have := Nat.le_of_dvd (by omega) hqx; omega
    exact (hmem_posRes _).mpr ⟨by omega, hlt⟩
  have hprod_eq : prodList mulRes = prodList posRes :=
    prodList_eq_of_nodup_eq_len hnd_mulRes (by dsimp [mulRes]; rw [List.length_map]) hsub_mul
  have hprod_mod : ∀ xs : List Nat,
      (prodList (xs.map fun x => (N * x) % q)) % q = (N ^ xs.length * prodList xs) % q := by
    intro xs; induction xs with
    | nil => simp [prodList]
    | cons x xs ih =>
      simp only [List.map_cons, prodList, List.length_cons]
      rw [Nat.mul_mod, ih, ← Nat.mul_mod]
      have hrew : (N * x) % q * (N ^ xs.length * prodList xs) % q =
          ((N * x) * (N ^ xs.length * prodList xs)) % q := by
        rw [Nat.mul_mod ((N * x) % q), Nat.mod_mod, ← Nat.mul_mod]
      rw [hrew]
      have halg : (N * x) * (N ^ xs.length * prodList xs) =
          N ^ (xs.length + 1) * (x * prodList xs) := by
        rw [Nat.pow_succ]
        simp [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
      rw [halg]
  have hmod_eq : (N ^ (q - 1) * prodList posRes) % q = (prodList posRes) % q := by
    rw [← hlen_posRes, ← hprod_mod posRes, hprod_eq]
  have hpow_pos : 1 ≤ N ^ (q - 1) := by
    have : ∀ k : Nat, 1 ≤ N ^ k := by
      intro k; induction k with
      | zero => exact Nat.le_refl 1
      | succ k ih =>
        rw [Nat.pow_succ]
        have := Nat.mul_le_mul ih hN_pos
        omega
    exact this (q - 1)
  have hsplit : N ^ (q - 1) * prodList posRes =
      prodList posRes + (N ^ (q - 1) - 1) * prodList posRes := by
    have : 1 * prodList posRes + (N ^ (q - 1) - 1) * prodList posRes =
        N ^ (q - 1) * prodList posRes := by
      rw [← Nat.add_mul, show 1 + (N ^ (q - 1) - 1) = N ^ (q - 1) by omega]
    omega
  rw [hsplit] at hmod_eq
  have hdvd_prod : q ∣ (N ^ (q - 1) - 1) * prodList posRes :=
    dvd_of_add_mod_eq (by omega) hmod_eq
  have hnot_dvd_fact : ¬ (q ∣ prodList posRes) := by
    have haux : ∀ xs : List Nat, (∀ x ∈ xs, ¬ (q ∣ x)) → ¬ (q ∣ prodList xs) := by
      intro xs; induction xs with
      | nil =>
        intro _ hd
        dsimp [prodList] at hd
        have := Nat.le_of_dvd (by decide) hd; omega
      | cons x xs ih =>
        intro hall hd
        rcases prime_dvd_mul hq hd with hqx | hqxs
        · exact hall x List.mem_cons_self hqx
        · exact ih (fun y hy => hall y (List.mem_cons_of_mem x hy)) hqxs
    apply haux posRes
    intro x hx
    rcases (hmem_posRes x).mp hx with ⟨hx1, hxq⟩
    intro hqx
    have := Nat.le_of_dvd hx1 hqx; omega
  rcases prime_dvd_mul hq hdvd_prod with hdvd_pow | hdvd_f
  · rcases hdvd_pow with ⟨m, hm⟩
    have hN_eq : N ^ (q - 1) = q * m + 1 := by omega
    rw [hN_eq, Nat.mul_add_mod, Nat.mod_eq_of_lt (by omega)]
  · exact absurd hdvd_f hnot_dvd_fact

private theorem pow_gcd_mod_eq_one {q N a b : Nat}
    (ha : (N ^ a) % q = 1) (hb : (N ^ b) % q = 1) :
    (N ^ (Nat.gcd a b)) % q = 1 := by
  have hcancel : ∀ X A : Nat, (X * A) % q = 1 → A % q = 1 → X % q = 1 := by
    intro X A hXA hA
    rw [Nat.mul_mod, hA, Nat.mul_one, Nat.mod_mod] at hXA
    exact hXA
  have haux : ∀ (s a b : Nat), a + b ≤ s →
      (N ^ a) % q = 1 → (N ^ b) % q = 1 → (N ^ (Nat.gcd a b)) % q = 1 := by
    intro s; induction s with
    | zero =>
      intro a b hle ha' _
      have ha0 : a = 0 := by omega
      have hb0 : b = 0 := by omega
      subst ha0; subst hb0; simpa using ha'
    | succ s ih =>
      intro a b hle ha' hb'
      by_cases ha0 : a = 0
      · subst ha0; rw [Nat.gcd_zero_left]; exact hb'
      · by_cases hb0 : b = 0
        · subst hb0; rw [Nat.gcd_zero_right]; exact ha'
        · by_cases hab : a ≤ b
          · by_cases heq : a = b
            · subst heq; rw [Nat.gcd_self]; exact ha'
            · have hgcd : Nat.gcd a b = Nat.gcd a (b - a) := by
                conv => lhs; rw [show b = (b - a) + a by omega]
                exact Nat.gcd_add_self_right a (b - a)
              have hpow : N ^ b = N ^ (b - a) * N ^ a := by
                rw [← Nat.pow_add, show b - a + a = b by omega]
              rw [hpow] at hb'
              rw [hgcd]
              exact ih a (b - a) (by omega) ha' (hcancel _ _ hb' ha')
          · have hgcd : Nat.gcd a b = Nat.gcd (a - b) b := by
              conv => lhs; rw [show a = (a - b) + b by omega, Nat.gcd_comm]
              rw [Nat.gcd_add_self_right, Nat.gcd_comm]
            have hpow : N ^ a = N ^ (a - b) * N ^ b := by
              rw [← Nat.pow_add, show a - b + b = a by omega]
            rw [hpow] at ha'
            rw [hgcd]
            exact ih (a - b) b (by omega) (hcancel _ _ ha' hb') hb'
  exact haux (a + b) a b (Nat.le_refl _) ha hb

private def geomSum (N : Nat) : Nat → Nat
  | 0 => 0
  | k + 1 => geomSum N k + N ^ k

private theorem geomSum_mul_pred (N : Nat) (hN : 1 ≤ N) :
    ∀ k : Nat, (N - 1) * geomSum N k + 1 = N ^ k
  | 0 => by simp [geomSum]
  | k + 1 => by
    simp only [geomSum, Nat.mul_add]
    have ih := geomSum_mul_pred N hN k
    have hstep : N ^ k + (N - 1) * N ^ k = N ^ (k + 1) := by
      have h1 : 1 * N ^ k + (N - 1) * N ^ k = N * N ^ k := by
        rw [← Nat.add_mul, show 1 + (N - 1) = N by omega]
      rw [Nat.one_mul] at h1
      rw [h1, Nat.pow_succ, Nat.mul_comm]
    omega

theorem exists_prime_gt_dvd_pred {p : Nat} (hp : IsPrime p) (B : Nat) :
    ∃ q : Nat, IsPrime q ∧ B < q ∧ p ∣ (q - 1) := by
  have hp2 : 2 ≤ p := hp.1
  let N := p * fact (B + p)
  have hf_pos : 0 < fact (B + p) := fact_pos (B + p)
  have hN2 : 2 ≤ N := by
    have : 2 * 1 ≤ p * fact (B + p) := Nat.mul_le_mul hp2 hf_pos
    omega
  let G := geomSum N p
  have hG_ge : 2 ≤ G := by
    have hmon : ∀ k : Nat, 2 ≤ k → 1 + N ≤ geomSum N k := by
      intro k hk
      induction k with
      | zero => omega
      | succ k ih =>
        by_cases hk2 : 2 ≤ k
        · have := ih hk2; simp only [geomSum]; omega
        · have hk1 : k = 1 := by omega
          subst hk1
          simp [geomSum]
    have := hmon p hp2
    omega
  rcases exists_prime_dvd hG_ge with ⟨q, hq, hqG⟩
  have hq2 : 2 ≤ q := hq.1
  have hmod_one_of_dvdN : ∀ d : Nat, d ∣ N → ∀ k : Nat, 1 ≤ k → (geomSum N k) % d = 1 % d := by
    intro d hdN k hk
    induction k with
    | zero => omega
    | succ k ih =>
      by_cases hk0 : k = 0
      · subst hk0; simp [geomSum]
      · have ih' := ih (by omega)
        have hd_pow : d ∣ N ^ k := by
          rw [show k = (k - 1) + 1 by omega, Nat.pow_succ]
          exact Nat.dvd_trans hdN (Nat.dvd_mul_left N (N ^ (k - 1)))
        simp only [geomSum]
        rw [Nat.add_mod, ih', Nat.mod_eq_zero_of_dvd hd_pow, Nat.add_zero, Nat.mod_mod]
  have hnot_qN : ¬ (q ∣ N) := by
    intro hqN
    have h1 := hmod_one_of_dvdN q hqN p (by omega)
    have h0 : G % q = 0 := Nat.mod_eq_zero_of_dvd hqG
    rw [h0, Nat.mod_eq_of_lt hq2] at h1
    omega
  have hBq : B < q := by
    by_cases hlt : B < q
    · exact hlt
    · exfalso; apply hnot_qN
      have hqf : q ∣ fact (B + p) := dvd_fact (by omega) (by omega)
      exact Nat.dvd_trans hqf (Nat.dvd_mul_left _ p)
  have hqp_ne : q ≠ p := by
    intro heq; subst heq
    exact hnot_qN (Nat.dvd_mul_right q _)
  have hNp_mod : (N ^ p) % q = 1 := by
    have hid : (N - 1) * G + 1 = N ^ p := geomSum_mul_pred N (by omega) p
    rcases hqG with ⟨m, hm⟩
    have hNp_eq : N ^ p = q * ((N - 1) * m) + 1 := by
      rw [hm] at hid
      have hcomm : (N - 1) * (q * m) = q * ((N - 1) * m) := by
        simp [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
      rw [hcomm] at hid
      exact hid.symm
    rw [hNp_eq, Nat.mul_add_mod, Nat.mod_eq_of_lt hq2]
  have hp_dvd_q1 : p ∣ (q - 1) := by
    by_cases hdvd : p ∣ (q - 1)
    · exact hdvd
    · exfalso
      have hcop : Nat.gcd p (q - 1) = 1 := gcd_prime_eq_one_of_not_dvd hp hdvd
      have hflt : (N ^ (q - 1)) % q = 1 := fermat_little hq hnot_qN
      have hg1 : (N ^ (Nat.gcd p (q - 1))) % q = 1 := pow_gcd_mod_eq_one hNp_mod hflt
      rw [hcop, Nat.pow_one] at hg1
      have hpow1 : ∀ k : Nat, (N ^ k) % q = 1 := by
        intro k; induction k with
        | zero => exact Nat.mod_eq_of_lt hq2
        | succ k ih =>
          rw [Nat.pow_succ, Nat.mul_mod, ih, hg1, Nat.mul_one, Nat.mod_eq_of_lt hq2]
      have hgeom_mod : ∀ k : Nat, (geomSum N k) % q = k % q := by
        intro k; induction k with
        | zero => simp [geomSum]
        | succ k ih =>
          simp only [geomSum]
          rw [Nat.add_mod, ih, hpow1 k]
          have h1mod : 1 = 1 % q := (Nat.mod_eq_of_lt hq2).symm
          conv => lhs; rw [h1mod]
          rw [← Nat.add_mod k 1 q]
      have hG0 : G % q = 0 := Nat.mod_eq_zero_of_dvd hqG
      have hp0 : p % q = 0 := by rw [← hgeom_mod p]; exact hG0
      rcases hp.2 q (Nat.dvd_of_mod_eq_zero hp0) with rfl | hqp
      · omega
      · exact hqp_ne hqp
  exact ⟨q, hq, hBq, hp_dvd_q1⟩

/--
  **Non-Periodicity of Euler's Totient Modulo Every Odd Prime:**
  For every odd prime `p`, `(φ(m) mod p)_{m ≥ 0}` is NOT eventually periodic.
-/
theorem not_eventuallyPeriodicMod_totient (p : Nat) (hp : IsPrime p) (hodd : p % 2 = 1) :
    ¬ EventuallyPeriodicMod p (fun m => (totient m : Int)) := by
  rintro ⟨N0, T, hT, hstep⟩
  have hp2 : 2 ≤ p := hp.1
  have hiter : ∀ (r n : Nat), N0 ≤ n →
      (totient (n + r * T) : Int) % (p : Int) = (totient n : Int) % (p : Int) := by
    intro r; induction r with
    | zero => intro n _; simp
    | succ r ih =>
      intro n hn
      rw [Nat.add_mul, Nat.one_mul, ← Nat.add_assoc, hstep (n + r * T) (by omega), ih n hn]
  let e := N0 + 1
  let M := 2 ^ e
  have hM_ge : N0 ≤ M := by
    have := le_pow_two_succ e
    dsimp [M]; omega
  have hM_ge2 : 2 ≤ M := by
    have := le_pow_two_succ e
    dsimp [M, e] at *; omega
  have htot_M : totient M = 2 ^ N0 := by
    have := totient_pow_two (e := e) (by omega)
    simpa [M, e] using this
  have hnot_p_totM : (totient M : Int) % (p : Int) ≠ 0 := by
    intro h0
    have hdvd_int : (p : Int) ∣ (totient M : Int) := Int.dvd_of_emod_eq_zero h0
    have hdvd_nat : p ∣ totient M := Int.ofNat_dvd.mp hdvd_int
    rw [htot_M] at hdvd_nat
    have hp_dvd2 : p ∣ 2 := prime_dvd_pow hp N0 hdvd_nat
    have hple2 : p ≤ 2 := Nat.le_of_dvd (by decide) hp_dvd2
    have hpeq2 : p = 2 := by omega
    subst hpeq2; omega
  rcases exists_prime_gt_dvd_pred hp T with ⟨q, hq, hTq, hp_dvd_q1⟩
  have hq_pos : 0 < q := by have := hq.1; omega
  have hnot_qT : ¬ (q ∣ T) := fun hd => by
    have := Nat.le_of_dvd hT hd; omega
  rcases exists_ap_dvd (a := M) hq hnot_qT with ⟨r0, _, hq_dvd_r0⟩
  have hr0_comm : M + r0 * T = r0 * T + M := Nat.add_comm _ _
  rw [← hr0_comm] at hq_dvd_r0
  let r := if decide ((q * q) ∣ (M + r0 * T)) then r0 + q else r0
  have hq_dvd_X : q ∣ (M + r * T) ∧ ¬ ((q * q) ∣ (M + r * T)) := by
    dsimp [r]
    by_cases hqq : (q * q) ∣ (M + r0 * T)
    · simp only [decide_eq_true hqq, ↓reduceIte]
      have hexp : M + (r0 + q) * T = (M + r0 * T) + q * T := by
        rw [Nat.add_mul]; omega
      rw [hexp]
      refine ⟨Nat.dvd_add hq_dvd_r0 (Nat.dvd_mul_right q T), fun hqq_sum => ?_⟩
      rcases hqq with ⟨a1, ha1⟩
      rcases hqq_sum with ⟨a2, ha2⟩
      have hsub : q * T = q * q * (a2 - a1) := by
        rw [Nat.mul_sub_left_distrib]
        have hle : a1 ≤ a2 := by
          by_cases hle' : a1 ≤ a2
          · exact hle'
          · exfalso
            have hqq_pos : 0 < q * q := Nat.mul_pos hq_pos hq_pos
            have hmul : (q * q) * (a2 + 1) ≤ (q * q) * a1 :=
              Nat.mul_le_mul_left (q * q) (by omega)
            rw [Nat.mul_add, Nat.mul_one] at hmul
            generalize hqq_v : q * q = qq at ha1 ha2 hqq_pos hmul
            omega
        omega
      have hT_eq : q * (q * (a2 - a1)) = q * T := by
        rw [← Nat.mul_assoc]; exact hsub.symm
      have hdiv_q : q * (a2 - a1) = T := Nat.eq_of_mul_eq_mul_left hq_pos hT_eq
      exact hnot_qT ⟨a2 - a1, hdiv_q.symm⟩
    · simp only [decide_eq_false hqq, Bool.false_eq_true, ↓reduceIte]
      exact ⟨hq_dvd_r0, hqq⟩
  rcases hq_dvd_X.1 with ⟨u, hXu⟩
  have hu1 : 1 ≤ u := by
    by_cases hu0 : u = 0
    · rw [hu0, Nat.mul_zero] at hXu; omega
    · omega
  have hnot_qu : ¬ (q ∣ u) := by
    rintro ⟨v, rfl⟩
    exact hq_dvd_X.2 ⟨v, by rw [hXu, Nat.mul_assoc]⟩
  have htot_X : totient (M + r * T) = (q - 1) * totient u := by
    rw [hXu]
    exact totient_mul_prime_of_not_dvd hq hnot_qu hu1
  have hp_dvd_totX : p ∣ totient (M + r * T) := by
    rw [htot_X]
    exact Nat.dvd_trans hp_dvd_q1 (Nat.dvd_mul_right (q - 1) (totient u))
  have hmod0 : (totient (M + r * T) : Int) % (p : Int) = 0 := by
    rcases hp_dvd_totX with ⟨k, hk⟩
    rw [hk, Int.ofNat_mul, Int.mul_emod_right]
  have hper_eq := hiter r M hM_ge
  rw [hmod0] at hper_eq
  exact hnot_p_totM hper_eq.symm

theorem not_eventuallyPeriodicMod_balancedCount_two (p : Nat) (hp : IsPrime p) (hodd : p % 2 = 1) :
    ¬ EventuallyPeriodicMod p (fun n => (balancedCount 2 n : Int)) := by
  intro hper
  have hd2 := eventuallyPeriodicMod_delta2 hper
  rcases hd2 with ⟨N0, T, hT, hstep⟩
  apply not_eventuallyPeriodicMod_totient p hp hodd
  refine ⟨N0 + 2, T, hT, fun m hm => ?_⟩
  have hd_eq : ∀ n : Nat,
      (balancedCount 2 (n + 2) : Int) - 2 * (balancedCount 2 (n + 1) : Int) +
      (balancedCount 2 n : Int) = (totient (n + 2) : Int) := by
    intro n
    have h := delta2_balancedCount_two n
    omega
  have hs := hstep (m - 2) (by omega)
  dsimp only at hs
  rw [hd_eq (m - 2 + T), hd_eq (m - 2),
      show m - 2 + T + 2 = m + T by omega,
      show m - 2 + 2 = m by omega] at hs
  exact hs

/--
  **Main Theorem (Binary All Balanced Words):**
  The ordinary generating function `∑_{n ≥ 0} b_2(n) x^n` is NOT rational over `ℚ`.
-/
theorem not_isRationalGF_balancedCount_two :
    ¬ IsRationalGF (balancedCount 2) := by
  intro hrat
  exact not_eventuallyPeriodicMod_balancedCount_two 3 isPrime_three rfl
    (isRationalGF_implies_eventuallyPeriodicMod isPrime_three hrat)

/--
  **Main Theorem (Binary Surjective / 2-Letter Balanced Words):**
  The ordinary generating function `∑_{n ≥ 0} surj_2(n) x^n` is NOT rational over `ℚ`.
-/
theorem not_isRationalGF_surjBalancedCount_two :
    ¬ IsRationalGF (surjBalancedCount 2) := by
  intro hrat
  have hper := isRationalGF_implies_eventuallyPeriodicMod isPrime_three hrat
  rcases hper with ⟨N0, T, hT, hstep⟩
  apply not_eventuallyPeriodicMod_balancedCount_two 3 isPrime_three rfl
  refine ⟨N0 + 1, T, hT, fun n hn => ?_⟩
  have hs1 := surjBalancedCount_two_add_two (n := n + T) (by omega)
  have hs2 := surjBalancedCount_two_add_two (n := n) (by omega)
  have h1 : (balancedCount 2 (n + T) : Int) = (surjBalancedCount 2 (n + T) : Int) + 2 := by omega
  have h2 : (balancedCount 2 n : Int) = (surjBalancedCount 2 n : Int) + 2 := by omega
  dsimp only at hstep ⊢
  rw [h1, h2, Int.add_emod, hstep n (by omega), ← Int.add_emod]

theorem surjBalancedCount_two_eq_atLeast2 (n : Nat) :
    atLeastBalancedCount 2 2 n = surjBalancedCount 2 n := by
  unfold atLeastBalancedCount atLeastBalancedWordsList surjBalancedCount surjBalancedWordsList
  congr 1
  congr 1
  funext w
  apply Bool.eq_iff_iff.mpr
  rw [hasAtLeastLettersBool_eq_true_iff, usesAllLettersBool_eq_true_iff]
  constructor
  · rintro ⟨L, hndL, hlenL, hsubL⟩ a
    have hnot : ¬ (∀ x ∈ L, x ≠ a) := by
      intro hall_ne
      let rest := (finList 2).filter fun x => decide (x ≠ a)
      have hsub_r : ∀ x ∈ L, x ∈ rest := fun x hx =>
        List.mem_filter.mpr ⟨mem_finList x, decide_eq_true (hall_ne x hx)⟩
      have hle := nodup_length_le_of_subset hndL hsub_r
      have hrest_le : rest.length ≤ 1 := by
        rcases fin2_dichotomy a with rfl | rfl <;> decide
      omega
    by_cases ha_in : a ∈ w
    · exact ha_in
    · exfalso; apply hnot
      intro x hx hxa; subst hxa; exact ha_in (hsubL x hx)
  · intro hsurj
    refine ⟨finList 2, nodup_finList 2, length_finList 2, fun a _ => hsurj a⟩

theorem not_isRationalGF_atLeast2BalancedCount_two :
    ¬ IsRationalGF (atLeastBalancedCount 2 2) := by
  have heq : atLeastBalancedCount 2 2 = surjBalancedCount 2 :=
    funext surjBalancedCount_two_eq_atLeast2
  rw [heq]
  exact not_isRationalGF_surjBalancedCount_two

/-! ## Section 6A: Strict Multiletter (`k ≥ 3`) Univariate Non-Rationality via Prime-Cycle Orbits -/

def iterFn {α : Type u} (f : α → α) : Nat → α → α
  | 0, x => x
  | t + 1, x => f (iterFn f t x)

theorem iterFn_add {α : Type u} (f : α → α) :
    ∀ (a b : Nat) (x : α), iterFn f (a + b) x = iterFn f a (iterFn f b x)
  | 0, b, x => by simp [iterFn]
  | a + 1, b, x => by
    rw [Nat.add_right_comm a 1 b, iterFn, iterFn, iterFn_add f a b x]

theorem iterFn_comm_apply {α : Type u} (f : α → α) :
    ∀ (t : Nat) (x : α), iterFn f t (f x) = f (iterFn f t x)
  | 0, _ => rfl
  | t + 1, x => by simp only [iterFn, iterFn_comm_apply f t x]

theorem iterFn_mod_of_period {α : Type u} (f : α → α) {p : Nat} {x : α}
    (hper : iterFn f p x = x) (m : Nat) :
    iterFn f m x = iterFn f (m % p) x := by
  have haux : ∀ k r : Nat, iterFn f (r + p * k) x = iterFn f r x := by
    intro k; induction k with
    | zero => intro r; simp
    | succ k ih =>
      intro r
      rw [Nat.mul_add, Nat.mul_one, ← Nat.add_assoc, iterFn_add f (r + p * k) p x, hper, ih r]
  have hdm := Nat.div_add_mod m p
  conv => lhs; rw [← hdm, Nat.add_comm]
  exact haux (m / p) (m % p)

theorem iterFn_gcd_eq {α : Type u} (f : α → α) {x : α} :
    ∀ {a b : Nat}, iterFn f a x = x → iterFn f b x = x → iterFn f (Nat.gcd a b) x = x := by
  have haux : ∀ (s a b : Nat), a + b ≤ s →
      iterFn f a x = x → iterFn f b x = x → iterFn f (Nat.gcd a b) x = x := by
    intro s; induction s with
    | zero =>
      intro a b hle ha _
      have ha0 : a = 0 := by omega
      have hb0 : b = 0 := by omega
      subst ha0; subst hb0; exact ha
    | succ s ih =>
      intro a b hle ha hb
      by_cases ha0 : a = 0
      · subst ha0; rw [Nat.gcd_zero_left]; exact hb
      · by_cases hb0 : b = 0
        · subst hb0; rw [Nat.gcd_zero_right]; exact ha
        · by_cases hab : a ≤ b
          · by_cases heq : a = b
            · subst heq; rw [Nat.gcd_self]; exact ha
            · have hgcd : Nat.gcd a b = Nat.gcd a (b - a) := by
                conv => lhs; rw [show b = (b - a) + a by omega]
                exact Nat.gcd_add_self_right a (b - a)
              have hba : iterFn f (b - a) x = x := by
                have hb' := hb
                conv at hb' => lhs; rw [show b = (b - a) + a by omega]
                rw [iterFn_add f (b - a) a x, ha] at hb'
                exact hb'
              rw [hgcd]
              exact ih a (b - a) (by omega) ha hba
          · have hgcd : Nat.gcd a b = Nat.gcd (a - b) b := by
              conv => lhs; rw [show a = (a - b) + b by omega, Nat.gcd_comm]
              rw [Nat.gcd_add_self_right, Nat.gcd_comm]
            have hab' : iterFn f (a - b) x = x := by
              have ha' := ha
              conv at ha' => lhs; rw [show a = (a - b) + b by omega]
              rw [iterFn_add f (a - b) b x, hb] at ha'
              exact ha'
            rw [hgcd]
            exact ih (a - b) b (by omega) hab' hb
  intro a b ha hb
  exact haux (a + b) a b (Nat.le_refl _) ha hb

/--
  **General Prime-Orbit Divisibility Lemma:**
  If `f : α → α` preserves a duplicate-free finite list `xs` and satisfies `f^[p](x) = x` on `xs`
  for a prime `p`, then the number of non-fixed elements `{x ∈ xs : f x ≠ x}` is divisible by `p`.
-/
theorem prime_orbit_dvd_nonfixed {α : Type u} [DecidableEq α] {p : Nat} (hp : IsPrime p)
    (f : α → α) {xs : List α} (hnd : ListNodup xs)
    (hclosed : ∀ x ∈ xs, f x ∈ xs)
    (hper : ∀ x ∈ xs, iterFn f p x = x) :
    p ∣ ((xs.filter fun x => decide (f x ≠ x)).length) := by
  have hp_pos : 0 < p := by have := hp.1; omega
  let S0 := xs.filter fun x => decide (f x ≠ x)
  have hS0_nd : ListNodup S0 := nodup_filter _ hnd
  have hS0_closed : ∀ x ∈ S0, f x ∈ S0 := by
    intro x hx
    rcases List.mem_filter.mp hx with ⟨hx_xs, hx_ne_dec⟩
    have hx_ne : f x ≠ x := of_decide_eq_true hx_ne_dec
    refine List.mem_filter.mpr ⟨hclosed x hx_xs, decide_eq_true ?_⟩
    intro hff
    have hconst : ∀ t : Nat, iterFn f t (f x) = f x := by
      intro t; induction t with
      | zero => rfl
      | succ t ih => simp only [iterFn, ih, hff]
    have hpx : iterFn f (p - 1) (f x) = iterFn f p x := by
      rw [iterFn_comm_apply f (p - 1) x]
      change iterFn f ((p - 1) + 1) x = iterFn f p x
      rw [show (p - 1) + 1 = p by omega]
    have heq : f x = x := by rw [← hconst (p - 1), hpx, hper x hx_xs]
    exact hx_ne heq
  have hS0_per : ∀ x ∈ S0, iterFn f p x = x := fun x hx => hper x (List.mem_filter.mp hx).1
  have hS0_nfix : ∀ x ∈ S0, f x ≠ x := fun x hx => of_decide_eq_true (List.mem_filter.mp hx).2
  have hstrong : ∀ (bound : Nat) (S : List α),
      S.length ≤ bound → ListNodup S →
      (∀ x ∈ S, f x ∈ S) → (∀ x ∈ S, iterFn f p x = x) → (∀ x ∈ S, f x ≠ x) →
      p ∣ S.length := by
    intro bound; induction bound with
    | zero =>
      intro S hle _ _ _ _
      have h0 : S.length = 0 := by omega
      rw [h0]; exact Nat.dvd_zero p
    | succ b ih =>
      intro S hle hndS hclS hperS hnfixS
      cases S with
      | nil => simp
      | cons x0 rest =>
        let S' := x0 :: rest
        have hx0_in : x0 ∈ S' := List.mem_cons_self
        let orb := (rangeList p).map fun i => iterFn f i x0
        have horb_in_S : ∀ i : Nat, iterFn f i x0 ∈ S' := by
          intro i; induction i with
          | zero => exact hx0_in
          | succ i ihi => exact hclS _ ihi
        have horb_nd : ListNodup orb := by
          apply nodup_map_rangeList_of_lt
          intro i j hij hjp heq
          let d := j - i
          have hd_pos : 0 < d := by omega
          have hd_lt : d < p := by omega
          have hshift : iterFn f (p - j) (iterFn f i x0) = iterFn f (p - j) (iterFn f j x0) :=
            congrArg (iterFn f (p - j)) heq
          rw [← iterFn_add, ← iterFn_add,
              show p - j + j = p by omega,
              hperS x0 hx0_in] at hshift
          have hd_fix : iterFn f d x0 = x0 := by
            have := congrArg (iterFn f d) hshift
            rw [← iterFn_add, show d + (p - j + i) = p by omega, hperS x0 hx0_in] at this
            exact this.symm
          have hcop : Nat.gcd p d = 1 := gcd_prime_eq_one_of_not_dvd hp (fun hpd => by
            have := Nat.le_of_dvd hd_pos hpd; omega)
          have h1 := iterFn_gcd_eq f (hperS x0 hx0_in) hd_fix
          rw [hcop] at h1
          exact hnfixS x0 hx0_in h1
        have hpart : ∀ zs : List α,
            zs.length = (zs.filter fun y => decide (y ∈ orb)).length +
                        (zs.filter fun y => !decide (y ∈ orb)).length := by
          intro zs; induction zs with
          | nil => rfl
          | cons z zs ihz =>
            simp only [List.filter]
            cases hd : decide (z ∈ orb) <;> simp [hd] <;> omega
        let inOrb := S'.filter fun y => decide (y ∈ orb)
        let outOrb := S'.filter fun y => !decide (y ∈ orb)
        have hin_nd : ListNodup inOrb := nodup_filter _ hndS
        have hsub1 : ∀ y ∈ orb, y ∈ inOrb := by
          intro y hy
          rcases List.mem_map.mp hy with ⟨i, _, rfl⟩
          exact List.mem_filter.mpr ⟨horb_in_S i, decide_eq_true hy⟩
        have hsub2 : ∀ y ∈ inOrb, y ∈ orb := fun y hy => of_decide_eq_true (List.mem_filter.mp hy).2
        have hle1 := nodup_length_le_of_subset horb_nd hsub1
        have hle2 := nodup_length_le_of_subset hin_nd hsub2
        have horb_len : orb.length = p := by dsimp [orb]; rw [List.length_map, length_rangeList]
        have hin_len : inOrb.length = p := by omega
        have hS_split : S'.length = p + outOrb.length := by
          have hp_s := hpart S'
          dsimp [inOrb, outOrb] at hin_len ⊢
          omega
        have hout_closed : ∀ y ∈ outOrb, f y ∈ outOrb := by
          intro y hy
          rcases List.mem_filter.mp hy with ⟨hyS, hynot⟩
          refine List.mem_filter.mpr ⟨hclS y hyS, ?_⟩
          rw [Bool.not_eq_true']
          apply Bool.eq_false_iff.mpr
          intro hfy_orb_dec
          have hfy_orb : f y ∈ orb := of_decide_eq_true hfy_orb_dec
          rcases List.mem_map.mp hfy_orb with ⟨i, _, hfy_eq⟩
          have hy_eq : iterFn f (p - 1) (f y) = iterFn f (p - 1) (iterFn f i x0) :=
            congrArg (iterFn f (p - 1)) hfy_eq.symm
          have hlhs : iterFn f (p - 1) (f y) = y := by
            rw [iterFn_comm_apply f (p - 1) y]
            change iterFn f ((p - 1) + 1) y = y
            rw [show (p - 1) + 1 = p by omega, hperS y hyS]
          rw [hlhs, ← iterFn_add,
              iterFn_mod_of_period f (hperS x0 hx0_in) (p - 1 + i)] at hy_eq
          have hy_in_orb : y ∈ orb := by
            rw [hy_eq]
            exact List.mem_map.mpr ⟨(p - 1 + i) % p, mem_rangeList.mpr (Nat.mod_lt _ hp_pos), rfl⟩
          simp [hy_in_orb] at hynot
        have hdvd_out : p ∣ outOrb.length := ih outOrb (by have := hp.1; dsimp [S'] at hS_split hle; omega)
          (nodup_filter _ hndS)
          hout_closed
          (fun y hy => hperS y (List.mem_filter.mp hy).1)
          (fun y hy => hnfixS y (List.mem_filter.mp hy).1)
        change p ∣ S'.length
        rw [hS_split]
        exact Nat.dvd_add (Nat.dvd_refl p) hdvd_out
  exact hstrong S0.length S0 (Nat.le_refl _) hS0_nd hS0_closed hS0_per hS0_nfix

/-- Canonical embedding of `{0, 1}` as the first two letters `{0, 1}` of `Fin k` (`k ≥ 2`). -/
def embedBinToK {k : Nat} (hk : 2 ≤ k) : Fin 2 → Fin k :=
  fun b => ⟨b.val, by have := b.isLt; omega⟩

theorem embedBinToK_inj {k : Nat} (hk : 2 ≤ k) :
    ∀ x y : Fin 2, embedBinToK hk x = embedBinToK hk y → x = y := by
  intro x y h
  have hv : (embedBinToK hk x).val = (embedBinToK hk y).val := congrArg Fin.val h
  dsimp [embedBinToK] at hv
  exact Fin.ext hv

private theorem list_take_map {α β : Type u} (f : α → β) :
    ∀ (n : Nat) (xs : List α), (xs.take n).map f = (xs.map f).take n
  | 0, _ => rfl
  | _ + 1, [] => rfl
  | n + 1, x :: xs => by simp [List.take_succ_cons, list_take_map f n xs]

private theorem list_drop_map {α β : Type u} (f : α → β) :
    ∀ (n : Nat) (xs : List α), (xs.drop n).map f = (xs.map f).drop n
  | 0, _ => rfl
  | _ + 1, [] => rfl
  | n + 1, _ :: xs => by simp [List.drop_succ_cons, list_drop_map f n xs]

theorem letterCount_map_inj {k1 k2 : Nat} (f : Fin k1 → Fin k2)
    (hinj : ∀ x y, f x = f y → x = y) (a : Fin k1) :
    ∀ u : Word k1, letterCount (f a) (u.map f) = letterCount a u
  | [] => rfl
  | x :: xs => by
    simp only [List.map_cons, letterCount_cons, letterCount_map_inj f hinj a xs]
    by_cases hxa : x = a
    · subst hxa; simp
    · have hfxa : f x ≠ f a := fun h => hxa (hinj x a h)
      simp [hxa, hfxa]

theorem letterCount_eq_zero_of_forall_ne {k : Nat} (b : Fin k) :
    ∀ w : Word k, (∀ x ∈ w, x ≠ b) → letterCount b w = 0
  | [], _ => rfl
  | x :: xs, h => by
    have hxb : x ≠ b := h x List.mem_cons_self
    simp [letterCount_cons, hxb,
          letterCount_eq_zero_of_forall_ne b xs (fun y hy => h y (List.mem_cons_of_mem x hy))]

theorem isBalanced_map_bij {k : Nat} (f g : Fin k → Fin k)
    (hgf : ∀ a : Fin k, g (f a) = a) (hfg : ∀ b : Fin k, f (g b) = b)
    {w : Word k} (hw : IsBalanced w) :
    IsBalanced (w.map f) := by
  have hinj : ∀ x y : Fin k, f x = f y → x = y := fun x y h => by
    rw [← hgf x, ← hgf y, h]
  intro u' v' hu' hv' hlen' b
  rcases (isFactor_iff_slice u' (w.map f)).mp hu' with ⟨i, hi, hu_eq⟩
  rcases (isFactor_iff_slice v' (w.map f)).mp hv' with ⟨j, hj, hv_eq⟩
  rw [List.length_map] at hi hj
  let u := (w.drop i).take u'.length
  let v := (w.drop j).take v'.length
  have hu_map : u.map f = u' := by
    dsimp [u]; rw [list_take_map, list_drop_map]; exact hu_eq
  have hv_map : v.map f = v' := by
    dsimp [v]; rw [list_take_map, list_drop_map]; exact hv_eq
  have hlu : u.length = u'.length := by dsimp [u]; rw [List.length_take, List.length_drop]; omega
  have hlv : v.length = v'.length := by dsimp [v]; rw [List.length_take, List.length_drop]; omega
  rw [← hu_map, ← hv_map, ← hfg b,
      letterCount_map_inj f hinj (g b) u,
      letterCount_map_inj f hinj (g b) v]
  exact hw u v (isFactor_take_drop w i u'.length) (isFactor_take_drop w j v'.length)
    (by omega) (g b)

/-- Bijection between binary balanced words of length `n` and `{0,1}`-supported balanced words over `Fin k`. -/
theorem binarySupported_balanced_count_eq {k : Nat} (hk : 2 ≤ k) (n : Nat) :
    ((balancedWordsList k n).filter fun w => decide (∀ a ∈ w, a.val < 2)).length =
      balancedCount 2 n := by
  let mapped := (balancedWordsList 2 n).map fun u => u.map (embedBinToK hk)
  let target := (balancedWordsList k n).filter fun w => decide (∀ a ∈ w, a.val < 2)
  have hmap_inj : ∀ u1 u2 : Word 2, u1.map (embedBinToK hk) = u2.map (embedBinToK hk) → u1 = u2 := by
    intro u1; induction u1 with
    | nil => intro u2 h; cases u2 <;> simp at h; rfl
    | cons x xs ih =>
      intro u2 h
      cases u2 with
      | nil => simp at h
      | cons y ys =>
        simp only [List.map_cons, List.cons.injEq] at h
        rw [embedBinToK_inj hk x y h.1, ih ys h.2]
  have hnd_mapped : ListNodup mapped :=
    nodup_map_of_inj _ hmap_inj (nodup_filter _ (nodup_allWords 2 n))
  have hnd_target : ListNodup target :=
    nodup_filter _ (nodup_filter _ (nodup_allWords k n))
  have hbal_emb : ∀ u : Word 2, IsBalanced u → IsBalanced (u.map (embedBinToK hk)) := by
    intro u hu x' y' hx' hy' hlen' b
    rcases (isFactor_iff_slice x' (u.map (embedBinToK hk))).mp hx' with ⟨i, hi, hx_eq⟩
    rcases (isFactor_iff_slice y' (u.map (embedBinToK hk))).mp hy' with ⟨j, hj, hy_eq⟩
    rw [List.length_map] at hi hj
    let x := (u.drop i).take x'.length
    let y := (u.drop j).take y'.length
    have hx_map : x.map (embedBinToK hk) = x' := by
      dsimp [x]; rw [list_take_map, list_drop_map]; exact hx_eq
    have hy_map : y.map (embedBinToK hk) = y' := by
      dsimp [y]; rw [list_take_map, list_drop_map]; exact hy_eq
    rw [← hx_map, ← hy_map]
    by_cases hb2 : b.val < 2
    · let b2 : Fin 2 := ⟨b.val, hb2⟩
      have hb_eq : embedBinToK hk b2 = b := Fin.ext rfl
      rw [← hb_eq,
          letterCount_map_inj (embedBinToK hk) (embedBinToK_inj hk) b2 x,
          letterCount_map_inj (embedBinToK hk) (embedBinToK_inj hk) b2 y]
      have hlx : x.length = x'.length := by dsimp [x]; rw [List.length_take, List.length_drop]; omega
      have hly : y.length = y'.length := by dsimp [y]; rw [List.length_take, List.length_drop]; omega
      exact hu x y (isFactor_take_drop u i x'.length) (isFactor_take_drop u j y'.length)
        (by omega) b2
    · have h0x : letterCount b (x.map (embedBinToK hk)) = 0 := by
        apply letterCount_eq_zero_of_forall_ne
        intro c hc; rcases List.mem_map.mp hc with ⟨d, _, rfl⟩
        intro heq; have := congrArg Fin.val heq; dsimp [embedBinToK] at this; have := d.isLt; omega
      have h0y : letterCount b (y.map (embedBinToK hk)) = 0 := by
        apply letterCount_eq_zero_of_forall_ne
        intro c hc; rcases List.mem_map.mp hc with ⟨d, _, rfl⟩
        intro heq; have := congrArg Fin.val heq; dsimp [embedBinToK] at this; have := d.isLt; omega
      rw [h0x, h0y]; simp [natDist]
  have hsub1 : ∀ w ∈ mapped, w ∈ target := by
    intro w hw
    rcases List.mem_map.mp hw with ⟨u, hu_in, rfl⟩
    rcases List.mem_filter.mp hu_in with ⟨hu_all, hu_bal_b⟩
    have hu_len : u.length = n := (mem_allWords_iff 2 n u).mp hu_all
    have hu_bal : IsBalanced u := (isBalancedBool_eq_true_iff u).mp hu_bal_b
    refine List.mem_filter.mpr ⟨List.mem_filter.mpr ⟨?_, ?_⟩, decide_eq_true ?_⟩
    · exact (mem_allWords_iff k n _).mpr (by rw [List.length_map, hu_len])
    · exact (isBalancedBool_eq_true_iff _).mpr (hbal_emb u hu_bal)
    · intro a ha; rcases List.mem_map.mp ha with ⟨b, _, rfl⟩; exact b.isLt
  have hsub2 : ∀ w ∈ target, w ∈ mapped := by
    intro w hw
    rcases List.mem_filter.mp hw with ⟨hw_b, hw_lt2_dec⟩
    rcases List.mem_filter.mp hw_b with ⟨hw_all, hw_bal_b⟩
    have hw_lt2 : ∀ a ∈ w, a.val < 2 := of_decide_eq_true hw_lt2_dec
    have hw_len : w.length = n := (mem_allWords_iff k n w).mp hw_all
    have hw_bal : IsBalanced w := (isBalancedBool_eq_true_iff w).mp hw_bal_b
    let proj : Fin k → Fin 2 := fun a => if h : a.val < 2 then ⟨a.val, h⟩ else bit0
    let u := w.map proj
    have hu_map_eq : u.map (embedBinToK hk) = w := by
      have haux : ∀ z : Word k, (∀ a ∈ z, a.val < 2) → (z.map proj).map (embedBinToK hk) = z := by
        intro z; induction z with
        | nil => intro _; rfl
        | cons a zs ih =>
          intro hall
          have ha2 : a.val < 2 := hall a List.mem_cons_self
          have ha_eq : embedBinToK hk (proj a) = a := by
            apply Fin.ext; dsimp [proj, embedBinToK]; rw [dif_pos ha2]
          simp [ha_eq, ih (fun b hb => hall b (List.mem_cons_of_mem a hb))]
      exact haux w hw_lt2
    have hu_bal : IsBalanced u := by
      intro x y hx hy hlen b
      have hfx : IsFactor (x.map (embedBinToK hk)) (u.map (embedBinToK hk)) := by
        rcases hx with ⟨p1, s1, hpu⟩
        exact ⟨p1.map (embedBinToK hk), s1.map (embedBinToK hk), by rw [← hpu]; simp [List.map_append]⟩
      have hfy : IsFactor (y.map (embedBinToK hk)) (u.map (embedBinToK hk)) := by
        rcases hy with ⟨p1, s1, hpu⟩
        exact ⟨p1.map (embedBinToK hk), s1.map (embedBinToK hk), by rw [← hpu]; simp [List.map_append]⟩
      rw [hu_map_eq] at hfx hfy
      have hdist := hw_bal _ _ hfx hfy (by simp [hlen]) (embedBinToK hk b)
      rwa [letterCount_map_inj (embedBinToK hk) (embedBinToK_inj hk) b x,
           letterCount_map_inj (embedBinToK hk) (embedBinToK_inj hk) b y] at hdist
    refine List.mem_map.mpr ⟨u, List.mem_filter.mpr ⟨?_, ?_⟩, hu_map_eq⟩
    · exact (mem_allWords_iff 2 n u).mpr (by dsimp [u]; rw [List.length_map, hw_len])
    · exact (isBalancedBool_eq_true_iff u).mpr hu_bal
  have hle1 := nodup_length_le_of_subset hnd_mapped hsub1
  have hle2 := nodup_length_le_of_subset hnd_target hsub2
  have hlen_m : mapped.length = balancedCount 2 n := List.length_map _
  dsimp [target] at hle1 hle2
  omega

private theorem block_shift_lt {m p x s : Nat} (hp : 0 < p) (hdvd : p ∣ m) (hx : x < m) :
    (x / p) * p + s % p < m := by
  rcases hdvd with ⟨q, rfl⟩
  have hdiv_lt : x / p < q := by
    by_cases hlt : x / p < q
    · exact hlt
    · exfalso
      have hmul : p * q ≤ p * (x / p) := Nat.mul_le_mul_left p (by omega)
      have hdm := Nat.div_add_mod x p
      generalize hd : x / p = d at hmul hdm
      generalize hr : x % p = r at hdm
      omega
  have hs_lt : s % p < p := Nat.mod_lt s hp
  have hbound : (x / p + 1) * p ≤ q * p := Nat.mul_le_mul_right p (by omega)
  rw [Nat.add_mul, Nat.one_mul] at hbound
  rw [Nat.mul_comm p q]
  generalize hd : x / p = d at hbound ⊢
  generalize hr : s % p = r at hs_lt ⊢
  omega

/-- Disjoint `p`-cycles on `{2, ..., k - 1}` fixing `{0, 1}` when `p ∣ (k - 2)`. -/
def cyclePerm (k p : Nat) (hp : 0 < p) (hdvd : p ∣ (k - 2)) (a : Fin k) : Fin k :=
  if h2 : a.val < 2 then a
  else
    let x := a.val - 2
    ⟨2 + ((x / p) * p + (x % p + 1) % p), by
      have hx : x < k - 2 := by have := a.isLt; omega
      have hlt := block_shift_lt (s := x % p + 1) hp hdvd hx
      omega⟩

def cyclePermInv (k p : Nat) (hp : 0 < p) (hdvd : p ∣ (k - 2)) (a : Fin k) : Fin k :=
  if h2 : a.val < 2 then a
  else
    let x := a.val - 2
    ⟨2 + ((x / p) * p + (x % p + p - 1) % p), by
      have hx : x < k - 2 := by have := a.isLt; omega
      have hlt := block_shift_lt (s := x % p + p - 1) hp hdvd hx
      omega⟩

private theorem block_div_mod (p b r : Nat) (hp : 0 < p) (hr : r < p) :
    (b * p + r) / p = b ∧ (b * p + r) % p = r := by
  have h1 : (p * b + r) / p = b + r / p := Nat.mul_add_div hp b r
  have h2 : (p * b + r) % p = r % p := Nat.mul_add_mod p b r
  rw [Nat.mul_comm p b, Nat.div_eq_of_lt hr, Nat.add_zero] at h1
  rw [Nat.mul_comm p b, Nat.mod_eq_of_lt hr] at h2
  exact ⟨h1, h2⟩

private theorem cyclePerm_left_inv (k p : Nat) (hp : 0 < p) (hdvd : p ∣ (k - 2)) (a : Fin k) :
    cyclePermInv k p hp hdvd (cyclePerm k p hp hdvd a) = a := by
  by_cases h2 : a.val < 2
  · simp [cyclePerm, cyclePermInv, h2]
  · have hc_val : (cyclePerm k p hp hdvd a).val =
        2 + ((a.val - 2) / p * p + ((a.val - 2) % p + 1) % p) := by
      unfold cyclePerm; rw [dif_neg h2]
    have h2' : ¬ ((cyclePerm k p hp hdvd a).val < 2) := by rw [hc_val]; omega
    unfold cyclePermInv
    rw [dif_neg h2']
    apply Fin.ext
    dsimp only
    rw [hc_val]
    let x := a.val - 2
    let r1 := (x % p + 1) % p
    have hr1 : r1 < p := Nat.mod_lt _ hp
    have hsub : 2 + (x / p * p + r1) - 2 = x / p * p + r1 := by omega
    change 2 + ((2 + (x / p * p + r1) - 2) / p * p + ((2 + (x / p * p + r1) - 2) % p + p - 1) % p) = a.val
    rw [hsub]
    rcases block_div_mod p (x / p) r1 hp hr1 with ⟨hd, hm⟩
    rw [hd, hm]
    have hrem_back : (r1 + p - 1) % p = x % p := by
      dsimp [r1]
      have hrx : x % p < p := Nat.mod_lt x hp
      by_cases htop : x % p + 1 = p
      · have h0 : (x % p + 1) % p = 0 := by rw [htop, Nat.mod_self]
        rw [h0, Nat.zero_add, Nat.mod_eq_of_lt (by omega)]
        omega
      · have hlt : x % p + 1 < p := by omega
        rw [Nat.mod_eq_of_lt hlt, show x % p + 1 + p - 1 = p * 1 + x % p by omega,
            Nat.mul_add_mod, Nat.mod_eq_of_lt hrx]
    rw [hrem_back]
    have hdm := Nat.div_add_mod x p
    rw [Nat.mul_comm p (x / p)] at hdm
    have : x / p * p + x % p = a.val - 2 := hdm
    omega

private theorem cyclePerm_right_inv (k p : Nat) (hp : 0 < p) (hdvd : p ∣ (k - 2)) (a : Fin k) :
    cyclePerm k p hp hdvd (cyclePermInv k p hp hdvd a) = a := by
  by_cases h2 : a.val < 2
  · simp [cyclePerm, cyclePermInv, h2]
  · have hc_val : (cyclePermInv k p hp hdvd a).val =
        2 + ((a.val - 2) / p * p + ((a.val - 2) % p + p - 1) % p) := by
      unfold cyclePermInv; rw [dif_neg h2]
    have h2' : ¬ ((cyclePermInv k p hp hdvd a).val < 2) := by rw [hc_val]; omega
    unfold cyclePerm
    rw [dif_neg h2']
    apply Fin.ext
    dsimp only
    rw [hc_val]
    let x := a.val - 2
    let r1 := (x % p + p - 1) % p
    have hr1 : r1 < p := Nat.mod_lt _ hp
    have hsub : 2 + (x / p * p + r1) - 2 = x / p * p + r1 := by omega
    change 2 + ((2 + (x / p * p + r1) - 2) / p * p + ((2 + (x / p * p + r1) - 2) % p + 1) % p) = a.val
    rw [hsub]
    rcases block_div_mod p (x / p) r1 hp hr1 with ⟨hd, hm⟩
    rw [hd, hm]
    have hrem_fwd : (r1 + 1) % p = x % p := by
      have hrx : x % p < p := Nat.mod_lt x hp
      by_cases hx0 : x % p = 0
      · have hr1_eq : r1 = p - 1 := by
          dsimp [r1]; rw [hx0, Nat.zero_add]; exact Nat.mod_eq_of_lt (by omega)
        rw [hr1_eq, show p - 1 + 1 = p by omega, Nat.mod_self, hx0]
      · have hr1_eq : r1 = x % p - 1 := by
          dsimp [r1]
          rw [show x % p + p - 1 = p * 1 + (x % p - 1) by omega, Nat.mul_add_mod]
          exact Nat.mod_eq_of_lt (by omega)
        rw [hr1_eq, show x % p - 1 + 1 = x % p by omega, Nat.mod_eq_of_lt hrx]
    rw [hrem_fwd]
    have hdm := Nat.div_add_mod x p
    rw [Nat.mul_comm p (x / p)] at hdm
    have : x / p * p + x % p = a.val - 2 := hdm
    omega

private theorem iterFn_cyclePerm_val (k p : Nat) (hp : 0 < p) (hdvd : p ∣ (k - 2))
    (a : Fin k) (hge : ¬ (a.val < 2)) :
    ∀ t : Nat,
      ¬ ((iterFn (cyclePerm k p hp hdvd) t a).val < 2) ∧
      (iterFn (cyclePerm k p hp hdvd) t a).val =
        2 + (((a.val - 2) / p) * p + ((a.val - 2) % p + t) % p)
  | 0 => by
    simp only [iterFn, hge, not_false_eq_true, true_and]
    rw [Nat.add_zero, Nat.mod_eq_of_lt (Nat.mod_lt _ hp)]
    have hdm := Nat.div_add_mod (a.val - 2) p
    rw [Nat.mul_comm p ((a.val - 2) / p)] at hdm
    have : (a.val - 2) / p * p + (a.val - 2) % p = a.val - 2 := hdm
    omega
  | t + 1 => by
    rcases iterFn_cyclePerm_val k p hp hdvd a hge t with ⟨hge_t, hval_t⟩
    simp only [iterFn]
    have hcp_ge : ∀ y : Fin k, ¬ (y.val < 2) →
        (cyclePerm k p hp hdvd y).val = 2 + ((y.val - 2) / p * p + ((y.val - 2) % p + 1) % p) := by
      intro y hy; unfold cyclePerm; rw [dif_neg hy]
    have hstep_val := hcp_ge (iterFn (cyclePerm k p hp hdvd) t a) hge_t
    rw [hstep_val, hval_t]
    refine ⟨by omega, ?_⟩
    let b := (a.val - 2) / p
    let rt := ((a.val - 2) % p + t) % p
    have hrt : rt < p := Nat.mod_lt _ hp
    have hsub : 2 + (b * p + rt) - 2 = b * p + rt := by omega
    change 2 + ((2 + (b * p + rt) - 2) / p * p + ((2 + (b * p + rt) - 2) % p + 1) % p) =
      2 + (b * p + ((a.val - 2) % p + (t + 1)) % p)
    rw [hsub]
    rcases block_div_mod p b rt hp hrt with ⟨hd, hm⟩
    rw [hd, hm]
    have hmod_step : (rt + 1) % p = ((a.val - 2) % p + (t + 1)) % p := by
      dsimp [rt]
      rw [Nat.add_mod (((a.val - 2) % p + t) % p) 1 p, Nat.mod_mod, ← Nat.add_mod, Nat.add_assoc]
    rw [hmod_step]

private theorem iterFn_cyclePerm_period (k p : Nat) (hp : 0 < p) (hdvd : p ∣ (k - 2)) (a : Fin k) :
    iterFn (cyclePerm k p hp hdvd) p a = a := by
  by_cases h2 : a.val < 2
  · have hfix : ∀ t : Nat, iterFn (cyclePerm k p hp hdvd) t a = a := by
      intro t; induction t with
      | zero => rfl
      | succ t ih => simp [iterFn, ih, cyclePerm, h2]
    exact hfix p
  · apply Fin.ext
    rw [(iterFn_cyclePerm_val k p hp hdvd a h2 p).2]
    have hmod : ((a.val - 2) % p + p) % p = (a.val - 2) % p := by
      rw [Nat.add_mod_right, Nat.mod_mod]
    rw [hmod]
    have hdm := Nat.div_add_mod (a.val - 2) p
    rw [Nat.mul_comm p ((a.val - 2) / p)] at hdm
    have : (a.val - 2) / p * p + (a.val - 2) % p = a.val - 2 := hdm
    omega

private theorem cyclePerm_fixed_iff (k p : Nat) (hp2 : 2 ≤ p) (hdvd : p ∣ (k - 2)) (a : Fin k) :
    cyclePerm k p (by omega) hdvd a = a ↔ a.val < 2 := by
  constructor
  · intro hfix
    by_cases h2 : a.val < 2
    · exact h2
    · exfalso
      have hv := congrArg Fin.val hfix
      unfold cyclePerm at hv
      rw [dif_neg h2] at hv
      dsimp only at hv
      let x := a.val - 2
      have hdm := Nat.div_add_mod x p
      rw [Nat.mul_comm p (x / p)] at hdm
      have hx_eq : x / p * p + x % p = a.val - 2 := hdm
      have hrem_eq : (x % p + 1) % p = x % p := by
        change 2 + (x / p * p + (x % p + 1) % p) = a.val at hv
        generalize hd : x / p * p = bp at hv hx_eq
        generalize hr1 : (x % p + 1) % p = r1 at hv
        generalize hr0 : x % p = r0 at hx_eq ⊢
        omega
      have hrx : x % p < p := Nat.mod_lt x (by omega)
      by_cases htop : x % p + 1 = p
      · rw [htop, Nat.mod_self] at hrem_eq; omega
      · rw [Nat.mod_eq_of_lt (by omega)] at hrem_eq; omega
  · intro h2; simp [cyclePerm, h2]

/--
  **Prime-Cycle Orbit Theorem:**
  Whenever a prime `p` divides `k - 2` (`k ≥ 2`), `b_k(n) ≡ b_2(n) (mod p)` for every length `n ≥ 0`.
-/
theorem balancedCount_mod_eq_two_of_prime_dvd_sub_two {k p : Nat} (hk : 2 ≤ k)
    (hp : IsPrime p) (hdvd : p ∣ (k - 2)) (n : Nat) :
    (balancedCount k n : Int) % (p : Int) = (balancedCount 2 n : Int) % (p : Int) := by
  have hp_pos : 0 < p := by have := hp.1; omega
  let σ := cyclePerm k p hp_pos hdvd
  let σ_inv := cyclePermInv k p hp_pos hdvd
  let f : Word k → Word k := List.map σ
  have hclosed : ∀ w ∈ balancedWordsList k n, f w ∈ balancedWordsList k n := by
    intro w hw
    rcases List.mem_filter.mp hw with ⟨hw_all, hw_bal_b⟩
    have hw_len : w.length = n := (mem_allWords_iff k n w).mp hw_all
    have hw_bal : IsBalanced w := (isBalancedBool_eq_true_iff w).mp hw_bal_b
    exact List.mem_filter.mpr ⟨(mem_allWords_iff k n (f w)).mpr (by dsimp [f]; rw [List.length_map, hw_len]),
      (isBalancedBool_eq_true_iff (f w)).mpr
        (isBalanced_map_bij σ σ_inv (cyclePerm_left_inv k p hp_pos hdvd)
          (cyclePerm_right_inv k p hp_pos hdvd) hw_bal)⟩
  have hper_w : ∀ w : Word k, iterFn f p w = w := by
    have hmap_iter : ∀ (t : Nat) (w : Word k), iterFn f t w = w.map (iterFn σ t) := by
      intro t; induction t with
      | zero => intro w; simp [iterFn]
      | succ t ih =>
        intro w
        simp only [iterFn, ih w, f, List.map_map]
        rfl
    intro w
    rw [hmap_iter p w]
    have hid : iterFn σ p = id := funext (iterFn_cyclePerm_period k p hp_pos hdvd)
    simp [hid]
  have hdvd_nf := prime_orbit_dvd_nonfixed hp f
    (nodup_filter _ (nodup_allWords k n)) hclosed (fun w _ => hper_w w)
  have hfix_iff : ∀ w : Word k, f w = w ↔ ∀ a ∈ w, a.val < 2 := by
    intro w; induction w with
    | nil => simp [f]
    | cons a ws ih =>
      simp only [f, List.map_cons, List.cons.injEq, List.mem_cons, forall_eq_or_imp]
      rw [cyclePerm_fixed_iff k p hp.1 hdvd a, ih]
  have hpart : ∀ xs : List (Word k),
      xs.length = (xs.filter fun w => decide (f w = w)).length +
                  (xs.filter fun w => decide (f w ≠ w)).length := by
    intro xs; induction xs with
    | nil => rfl
    | cons x xs ih =>
      simp only [List.filter]
      by_cases hfx : f x = x
      · have ht : decide (f x = x) = true := decide_eq_true hfx
        have hf : decide (f x ≠ x) = false := decide_eq_false (fun h => h hfx)
        rw [ht, hf]; simp only [↓reduceIte, Bool.false_eq_true, List.length_cons]; omega
      · have hf : decide (f x = x) = false := decide_eq_false hfx
        have ht : decide (f x ≠ x) = true := decide_eq_true hfx
        rw [hf, ht]; simp only [↓reduceIte, Bool.false_eq_true, List.length_cons]; omega
  have hfix_filt_eq :
      ((balancedWordsList k n).filter fun w => decide (f w = w)) =
      ((balancedWordsList k n).filter fun w => decide (∀ a ∈ w, a.val < 2)) := by
    congr 1; funext w
    apply Bool.eq_iff_iff.mpr
    simp only [decide_eq_true_eq, hfix_iff]
  have hsplit := hpart (balancedWordsList k n)
  rw [hfix_filt_eq, binarySupported_balanced_count_eq hk n] at hsplit
  rcases hdvd_nf with ⟨m, hm⟩
  change ((balancedWordsList k n).filter fun w => decide (f w ≠ w)).length = p * m at hm
  rw [hm] at hsplit
  have hsplit' : balancedCount k n = balancedCount 2 n + p * m := hsplit
  rw [hsplit', Int.ofNat_add, Int.ofNat_mul, Int.add_mul_emod_self_left]

/-- For every `k ≥ 0` and `n ≥ 1`, `m_{k, ≥ 2}(n) + k = b_k(n)`. -/
theorem atLeast2BalancedCount_add_k {k n : Nat} (hn : 1 ≤ n) :
    atLeastBalancedCount k 2 n + k = balancedCount k n := by
  have hpart : ∀ xs : List (Word k),
      xs.length = (xs.filter (hasAtLeastLettersBool 2)).length +
                  (xs.filter fun w => !hasAtLeastLettersBool 2 w).length := by
    intro xs; induction xs with
    | nil => rfl
    | cons x xs ih =>
      simp only [List.filter]
      cases hd : hasAtLeastLettersBool 2 x <;> simp [hd] <;> omega
  let mono := (balancedWordsList k n).filter fun w => !hasAtLeastLettersBool 2 w
  let reps := (finList k).map fun a => List.replicate n a
  have hrep_inj : ∀ a b : Fin k, List.replicate n a = List.replicate n b → a = b := by
    cases n with
    | zero => omega
    | succ _ => intro a b h; simp at h; exact h
  have hnd_reps : ListNodup reps := nodup_map_of_inj _ hrep_inj (nodup_finList k)
  have hnd_mono : ListNodup mono := nodup_filter _ (nodup_filter _ (nodup_allWords k n))
  have hbal_rep : ∀ a : Fin k, IsBalanced (List.replicate n a) := by
    intro a u v hu hv hlen b
    have hall_rep : ∀ z : Word k, IsFactor z (List.replicate n a) → z = List.replicate z.length a := by
      intro z ⟨p1, s1, hp1⟩
      apply eq_replicate_of_all_eq a z
      intro c hc
      have hm : c ∈ p1 ++ z ++ s1 := List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inr hc)))
      rw [hp1] at hm
      exact List.eq_of_mem_replicate hm
    rw [hall_rep u hu, hall_rep v hv, hlen]; simp [natDist]
  have hnot_atLeast2_rep : ∀ a : Fin k, hasAtLeastLettersBool 2 (List.replicate n a) = false := by
    intro a; apply Bool.eq_false_iff.mpr; intro htrue
    rcases (hasAtLeastLettersBool_eq_true_iff 2 _).mp htrue with ⟨L, hndL, hlenL, hsubL⟩
    cases L with
    | nil => simp at hlenL
    | cons x xs =>
      cases xs with
      | nil => simp at hlenL
      | cons y _ =>
        cases hndL with
        | cons hnot _ =>
          have hx : x = a := List.eq_of_mem_replicate (hsubL x List.mem_cons_self)
          have hy : y = a := List.eq_of_mem_replicate (hsubL y (List.mem_cons_of_mem x List.mem_cons_self))
          exact hnot y List.mem_cons_self (hx.trans hy.symm)
  have hsub1 : ∀ w ∈ reps, w ∈ mono := by
    intro w hw
    rcases List.mem_map.mp hw with ⟨a, _, rfl⟩
    exact List.mem_filter.mpr ⟨List.mem_filter.mpr
      ⟨(mem_allWords_iff k n _).mpr List.length_replicate,
       (isBalancedBool_eq_true_iff _).mpr (hbal_rep a)⟩,
      by simp [hnot_atLeast2_rep a]⟩
  have hsub2 : ∀ w ∈ mono, w ∈ reps := by
    intro w hw
    rcases List.mem_filter.mp hw with ⟨hw_b, hw_not2⟩
    rcases List.mem_filter.mp hw_b with ⟨hw_all, _⟩
    have hw_len : w.length = n := (mem_allWords_iff k n w).mp hw_all
    cases w with
    | nil => simp at hw_len; omega
    | cons a ws =>
      have hall_a : ∀ x ∈ (a :: ws), x = a := by
        intro x hx
        by_cases hxa : x = a
        · exact hxa
        · exfalso
          have h2 : HasAtLeastLetters 2 (a :: ws) :=
            ⟨[a, x],
             .cons (fun z hz hza => by simp at hz; subst hz; exact hxa hza.symm)
               (.cons (fun _ hz => nomatch hz) .nil),
             rfl,
             fun z hz => by
               simp at hz
               rcases hz with rfl | rfl
               · exact List.mem_cons_self
               · exact hx⟩
          have hb := (hasAtLeastLettersBool_eq_true_iff 2 (a :: ws)).mpr h2
          simp [hb] at hw_not2
      have hrep := eq_replicate_of_all_eq a (a :: ws) hall_a
      rw [hw_len] at hrep
      exact List.mem_map.mpr ⟨a, mem_finList a, hrep.symm⟩
  have hle1 := nodup_length_le_of_subset hnd_reps hsub1
  have hle2 := nodup_length_le_of_subset hnd_mono hsub2
  have hreps_len : reps.length = k := by dsimp [reps]; rw [List.length_map, length_finList]
  have hmono_len : mono.length = k := by omega
  have hp := hpart (balancedWordsList k n)
  unfold atLeastBalancedCount atLeastBalancedWordsList balancedCount
  dsimp [mono] at hmono_len
  omega

/--
  **Main Univariate Multiletter Non-Rationality Theorem:**
  For every alphabet size `k ≥ 5` such that an odd prime `p` divides `k - 2`
  (including `k = 5, 7, 8, 9, 11, 12, ...`), NEITHER `b_k(n)` NOR `m_{k, ≥ 2}(n)`
  has a rational ordinary generating function over `ℚ`.
-/
theorem not_isRationalGF_balancedCount_of_odd_prime_dvd_sub_two {k p : Nat}
    (hk : 2 ≤ k) (hp : IsPrime p) (hodd : p % 2 = 1) (hdvd : p ∣ (k - 2)) :
    ¬ IsRationalGF (balancedCount k) := by
  intro hrat
  have hper := isRationalGF_implies_eventuallyPeriodicMod hp hrat
  rcases hper with ⟨N0, T, hT, hstep⟩
  apply not_eventuallyPeriodicMod_balancedCount_two p hp hodd
  refine ⟨N0, T, hT, fun n hn => ?_⟩
  dsimp only at hstep ⊢
  rw [← balancedCount_mod_eq_two_of_prime_dvd_sub_two hk hp hdvd (n + T),
      ← balancedCount_mod_eq_two_of_prime_dvd_sub_two hk hp hdvd n]
  exact hstep n hn

theorem not_isRationalGF_atLeast2BalancedCount_of_odd_prime_dvd_sub_two {k p : Nat}
    (hk : 2 ≤ k) (hp : IsPrime p) (hodd : p % 2 = 1) (hdvd : p ∣ (k - 2)) :
    ¬ IsRationalGF (atLeastBalancedCount k 2) := by
  intro hrat
  have hper := isRationalGF_implies_eventuallyPeriodicMod hp hrat
  rcases hper with ⟨N0, T, hT, hstep⟩
  apply not_eventuallyPeriodicMod_balancedCount_two p hp hodd
  refine ⟨N0 + 1, T, hT, fun n hn => ?_⟩
  have ha1 := atLeast2BalancedCount_add_k (k := k) (n := n + T) (by omega)
  have ha2 := atLeast2BalancedCount_add_k (k := k) (n := n) (by omega)
  have h1 : (balancedCount k (n + T) : Int) = (atLeastBalancedCount k 2 (n + T) : Int) + (k : Int) := by omega
  have h2 : (balancedCount k n : Int) = (atLeastBalancedCount k 2 n : Int) + (k : Int) := by omega
  dsimp only at hstep ⊢
  rw [← balancedCount_mod_eq_two_of_prime_dvd_sub_two hk hp hdvd (n + T),
      ← balancedCount_mod_eq_two_of_prime_dvd_sub_two hk hp hdvd n,
      h1, h2, Int.add_emod, hstep n (by omega), ← Int.add_emod]

/-- Concrete `k = 5` (`5 ≥ 3`) strict multiletter univariate disproofs. -/
theorem not_isRationalGF_balancedCount_five :
    ¬ IsRationalGF (balancedCount 5) :=
  not_isRationalGF_balancedCount_of_odd_prime_dvd_sub_two (k := 5) (p := 3)
    (by decide) isPrime_three rfl ⟨1, by decide⟩

theorem not_isRationalGF_atLeast2BalancedCount_five :
    ¬ IsRationalGF (atLeastBalancedCount 5 2) :=
  not_isRationalGF_atLeast2BalancedCount_of_odd_prime_dvd_sub_two (k := 5) (p := 3)
    (by decide) isPrime_three rfl ⟨1, by decide⟩

/-! ## Section 6B: Multivariate (Parikh) Generating Function Non-Rationality for ALL `k ≥ 2` -/

abbrev MultiIdx (k : Nat) : Type := Fin k → Nat
abbrev MPolyQ (k : Nat) : Type := List (MultiIdx k × RatQ)
abbrev MSeriesQ (k : Nat) : Type := MultiIdx k → RatQ
abbrev MPolyZ (k : Nat) : Type := List (MultiIdx k × Int)

def eqMultiIdx {k : Nat} (α β : MultiIdx k) : Bool :=
  (finList k).all fun a => decide (α a = β a)

theorem eqMultiIdx_eq_true_iff {k : Nat} (α β : MultiIdx k) :
    eqMultiIdx α β = true ↔ α = β := by
  unfold eqMultiIdx
  simp only [List.all_eq_true, decide_eq_true_eq]
  exact ⟨fun h => funext (fun a => h a (mem_finList a)), fun h a _ => h ▸ rfl⟩

def leMultiIdx {k : Nat} (β α : MultiIdx k) : Bool :=
  (finList k).all fun a => decide (β a ≤ α a)

theorem leMultiIdx_eq_true_iff {k : Nat} (β α : MultiIdx k) :
    leMultiIdx β α = true ↔ ∀ a : Fin k, β a ≤ α a := by
  unfold leMultiIdx
  simp only [List.all_eq_true, decide_eq_true_eq]
  exact ⟨fun h a => h a (mem_finList a), fun h a _ => h a⟩

def subMultiIdx {k : Nat} (α β : MultiIdx k) : MultiIdx k :=
  fun a => α a - β a

def zeroMultiIdx (k : Nat) : MultiIdx k :=
  fun _ => 0

def totalMultiIdx {k : Nat} (α : MultiIdx k) : Nat :=
  (finList k).foldr (fun a acc => α a + acc) 0

def mPolyCoeffQ {k : Nat} (P : MPolyQ k) (α : MultiIdx k) : RatQ :=
  P.foldr (fun bc acc => ratAdd acc (if eqMultiIdx bc.1 α then bc.2 else ratZero)) ratZero

def mulMPolySeriesQ {k : Nat} (Q : MPolyQ k) (F : MSeriesQ k) : MSeriesQ k :=
  fun α => Q.foldr (fun bc acc =>
    ratAdd acc (if leMultiIdx bc.1 α then ratMul bc.2 (F (subMultiIdx α bc.1)) else ratZero)) ratZero

/-- Exact count of balanced words over `Fin k` with Parikh vector `α`. -/
def parikhBalancedCount (k : Nat) (α : MultiIdx k) : Nat :=
  ((balancedWordsList k (totalMultiIdx α)).filter fun w =>
    (finList k).all fun a => decide (letterCount a w = α a)).length

def parikhBalancedSeries (k : Nat) : MSeriesQ k :=
  fun α => ratOfNat (parikhBalancedCount k α)

/--
  **Multivariate (Parikh) Rational Generating Function Predicate (`ℚ[[x_0, ..., x_{k-1}]]`):**
  `F_k(x_0, ..., x_{k-1}) = ∑_{w ∈ B_k} x_0^{|w|_0} ⋯ x_{k-1}^{|w|_{k-1}}` is rational in `ℚ[[x_0, ..., x_{k-1}]]`
  iff `Q · F_k = P` for polynomials `P, Q ∈ ℚ[x_0, ..., x_{k-1}]` with invertible constant term `Q(0, ..., 0) ≠ 0`.
-/
def IsRationalParikhGF (k : Nat) : Prop :=
  ∃ P Q : MPolyQ k, mPolyCoeffQ Q (zeroMultiIdx k) ≠ ratZero ∧
    mulMPolySeriesQ Q (parikhBalancedSeries k) = mPolyCoeffQ P

/-- Positive non-vacuity witness: for `k = 1`, `IsRationalParikhGF 1` holds (`1 / (1 - x_0)`). -/
theorem unary_parikh_isRationalParikhGF : IsRationalParikhGF 1 := by
  let f0 : Fin 1 := ⟨0, by decide⟩
  let e0 : MultiIdx 1 := zeroMultiIdx 1
  let e1 : MultiIdx 1 := fun _ => 1
  let P : MPolyQ 1 := [(e0, ratOne)]
  let Q : MPolyQ 1 := [(e0, ratOne), (e1, ratOfInt (-1))]
  have hfin1 : ∀ a : Fin 1, a = f0 := fun a => Fin.ext (by have := a.isLt; dsimp [f0]; omega)
  have hcount1 : ∀ α : MultiIdx 1, parikhBalancedCount 1 α = 1 := by
    intro α
    have htot : totalMultiIdx α = α f0 := by simp [totalMultiIdx, finList, f0]
    unfold parikhBalancedCount
    rw [htot]
    have hall_filt : ∀ n : Nat,
        ((balancedWordsList 1 n).filter fun w =>
          (finList 1).all fun a => decide (letterCount a w = n)) = balancedWordsList 1 n := by
      intro n
      have haux : ∀ ws : List (Word 1),
          (∀ w ∈ ws, w.length = n) →
          (ws.filter fun w => (finList 1).all fun a => decide (letterCount a w = n)) = ws := by
        intro ws; induction ws with
        | nil => intro _; rfl
        | cons w ws ih =>
          intro hlen
          have hw_len : w.length = n := hlen w List.mem_cons_self
          have hcnt : letterCount f0 w = w.length := by
            clear hlen ih ws hw_len
            induction w with
            | nil => rfl
            | cons x xs ihw =>
              rw [hfin1 x]
              simp only [letterCount_cons, ↓reduceIte, ihw, List.length_cons]
              omega
          have hall_t : ((finList 1).all fun a => decide (letterCount a w = n)) = true := by
            rw [List.all_eq_true]
            intro a _; rw [hfin1 a, decide_eq_true_eq, hcnt, hw_len]
          simp [hall_t, ih (fun u hu => hlen u (List.mem_cons_of_mem w hu))]
      apply haux
      intro w hw
      exact (mem_allWords_iff 1 n w).mp (List.mem_filter.mp hw).1
    have hsimp_filt : (fun w : Word 1 => (finList 1).all fun a => decide (letterCount a w = α a)) =
        (fun w : Word 1 => (finList 1).all fun a => decide (letterCount a w = α f0)) := by
      funext w
      apply Bool.eq_iff_iff.mpr
      simp only [List.all_eq_true, decide_eq_true_eq]
      exact ⟨fun h a ha => by rw [hfin1 a]; exact h f0 (mem_finList f0),
             fun h a ha => by rw [hfin1 a]; exact h f0 (mem_finList f0)⟩
    rw [hsimp_filt, hall_filt]
    exact unary_balancedCount_eq_one (α f0)
  refine ⟨P, Q, ?_, ?_⟩
  · intro hz
    have hq0 : mPolyCoeffQ Q e0 = ratOne := by
      dsimp [Q, mPolyCoeffQ, e0, e1, zeroMultiIdx, eqMultiIdx, finList]
      simp [ratZero, ratOne, ratOfInt_add]
    rw [hq0] at hz
    have := ratOfInt_inj hz
    omega
  · funext α
    have hser : ∀ β : MultiIdx 1, parikhBalancedSeries 1 β = ratOne := by
      intro β; simp [parikhBalancedSeries, hcount1 β, ratOfNat, ratOne]
    by_cases h0 : α f0 = 0
    · have heq0 : eqMultiIdx e0 α = true := by
        rw [eqMultiIdx_eq_true_iff]; funext a; rw [hfin1 a]; dsimp [e0, zeroMultiIdx]; exact h0.symm
      have hle0 : leMultiIdx e0 α = true := by
        rw [leMultiIdx_eq_true_iff]; intro a; dsimp [e0, zeroMultiIdx]; exact Nat.zero_le _
      have hle1 : leMultiIdx e1 α = false := by
        apply Bool.eq_false_iff.mpr; intro ht
        have := (leMultiIdx_eq_true_iff e1 α).mp ht f0
        dsimp [e1] at this; omega
      dsimp [mulMPolySeriesQ, mPolyCoeffQ, P, Q]
      rw [heq0, hle0, hle1]
      simp [hser, ratOne, ratZero, ratOfInt_mul, ratOfInt_add]
    · have heq0 : eqMultiIdx e0 α = false := by
        apply Bool.eq_false_iff.mpr; intro ht
        have := congrFun ((eqMultiIdx_eq_true_iff e0 α).mp ht) f0
        dsimp [e0, zeroMultiIdx] at this; exact h0 this.symm
      have hle0 : leMultiIdx e0 α = true := by
        rw [leMultiIdx_eq_true_iff]; intro a; dsimp [e0, zeroMultiIdx]; exact Nat.zero_le _
      have hle1 : leMultiIdx e1 α = true := by
        rw [leMultiIdx_eq_true_iff]; intro a; rw [hfin1 a]; dsimp [e1]
        generalize hv : α f0 = v at h0 ⊢; omega
      dsimp [mulMPolySeriesQ, mPolyCoeffQ, P, Q]
      rw [heq0, hle0, hle1]
      simp [hser, ratOne, ratZero, ratOfInt_mul, ratOfInt_add]

private def mPolyCoeffZ {k : Nat} (P : MPolyZ k) (α : MultiIdx k) : Int :=
  P.foldr (fun bc acc => acc + (if eqMultiIdx bc.1 α then bc.2 else 0)) 0

private theorem mPolyCoeffZ_cons {k : Nat} (bc : MultiIdx k × Int) (P : MPolyZ k) (α : MultiIdx k) :
    mPolyCoeffZ (bc :: P) α = mPolyCoeffZ P α + (if eqMultiIdx bc.1 α then bc.2 else 0) := rfl

private theorem mPolyCoeffQ_cons {k : Nat} (bc : MultiIdx k × RatQ) (P : MPolyQ k) (α : MultiIdx k) :
    mPolyCoeffQ (bc :: P) α = ratAdd (mPolyCoeffQ P α) (if eqMultiIdx bc.1 α then bc.2 else ratZero) := rfl

private def mulMPolySeriesZ {k : Nat} (Q : MPolyZ k) (F : MultiIdx k → Int) (α : MultiIdx k) : Int :=
  Q.foldr (fun bc acc =>
    acc + (if leMultiIdx bc.1 α then bc.2 * F (subMultiIdx α bc.1) else 0)) 0

private theorem mulMPolySeriesZ_cons {k : Nat} (bc : MultiIdx k × Int) (Q : MPolyZ k)
    (F : MultiIdx k → Int) (α : MultiIdx k) :
    mulMPolySeriesZ (bc :: Q) F α =
      mulMPolySeriesZ Q F α + (if leMultiIdx bc.1 α then bc.2 * F (subMultiIdx α bc.1) else 0) := rfl

private theorem mulMPolySeriesQ_cons {k : Nat} (bc : MultiIdx k × RatQ) (Q : MPolyQ k)
    (F : MSeriesQ k) (α : MultiIdx k) :
    mulMPolySeriesQ (bc :: Q) F α =
      ratAdd (mulMPolySeriesQ Q F α)
        (if leMultiIdx bc.1 α then ratMul bc.2 (F (subMultiIdx α bc.1)) else ratZero) := rfl

private noncomputable def scaleMPoly (D : Nat) {k : Nat} (P : MPolyQ k) : MPolyZ k :=
  P.map fun bc => (bc.1, (chooseRaw bc.2).num * ((D / (chooseRaw bc.2).den : Nat) : Int))

private theorem scaleMPoly_cons (D : Nat) {k : Nat} (bc : MultiIdx k × RatQ) (P : MPolyQ k) :
    scaleMPoly D (bc :: P) =
      (bc.1, (chooseRaw bc.2).num * ((D / (chooseRaw bc.2).den : Nat) : Int)) :: scaleMPoly D P := rfl

private theorem rawDen_dvd_prodDenRaw {r : RawRat} :
    ∀ {rs : List RawRat}, r ∈ rs → r.den ∣ prodDenRaw rs
  | [], h => nomatch h
  | _ :: xs, h => by
    simp only [prodDenRaw]
    cases h with
    | head _ => exact Nat.dvd_mul_right r.den (prodDenRaw xs)
    | tail _ hm => exact Nat.dvd_trans (rawDen_dvd_prodDenRaw hm) (Nat.dvd_mul_left _ _)

private theorem mPolyCoeffQ_scale {k : Nat} (D : Nat) (hD : 0 < D) (P : MPolyQ k)
    (hdvd : ∀ bc ∈ P, (chooseRaw bc.2).den ∣ D) (α : MultiIdx k) :
    mPolyCoeffQ P α = ratMk (mPolyCoeffZ (scaleMPoly D P) α) D hD := by
  induction P with
  | nil =>
    unfold mPolyCoeffQ mPolyCoeffZ scaleMPoly ratZero ratOfInt ratMk
    apply Quot.sound; unfold RawRatEq; simp
  | cons bc P ih =>
    rw [mPolyCoeffQ_cons, scaleMPoly_cons, mPolyCoeffZ_cons,
        ih (fun x hx => hdvd x (List.mem_cons_of_mem bc hx))]
    by_cases heq : eqMultiIdx bc.1 α = true
    · simp only [heq, ↓reduceIte]
      have hbc : bc.2 = ratMk ((chooseRaw bc.2).num * ((D / (chooseRaw bc.2).den : Nat) : Int)) D hD :=
        (chooseRaw_spec bc.2).symm.trans (ratMk_scale_eq hD (hdvd bc List.mem_cons_self))
      conv => lhs; rw [hbc]
      rw [ratMk_same_den_add]
    · simp only [heq, Bool.false_eq_true, ↓reduceIte]
      have hz : ratZero = ratMk 0 D hD := by
        unfold ratZero ratOfInt ratMk; apply Quot.sound; unfold RawRatEq; simp
      rw [hz, ratMk_same_den_add, Int.add_zero]

private theorem mulMPolySeriesQ_scale {k : Nat} (D : Nat) (hD : 0 < D) (Q : MPolyQ k)
    (a : MultiIdx k → Nat) (hdvd : ∀ bc ∈ Q, (chooseRaw bc.2).den ∣ D) (α : MultiIdx k) :
    mulMPolySeriesQ Q (fun β => ratOfNat (a β)) α =
      ratMk (mulMPolySeriesZ (scaleMPoly D Q) (fun β => (a β : Int)) α) D hD := by
  induction Q with
  | nil =>
    unfold mulMPolySeriesQ mulMPolySeriesZ scaleMPoly ratZero ratOfInt ratMk
    apply Quot.sound; unfold RawRatEq; simp
  | cons bc Q ih =>
    rw [mulMPolySeriesQ_cons, scaleMPoly_cons, mulMPolySeriesZ_cons,
        ih (fun x hx => hdvd x (List.mem_cons_of_mem bc hx))]
    by_cases hle : leMultiIdx bc.1 α = true
    · simp only [hle, ↓reduceIte]
      have hbc : bc.2 = ratMk ((chooseRaw bc.2).num * ((D / (chooseRaw bc.2).den : Nat) : Int)) D hD :=
        (chooseRaw_spec bc.2).symm.trans (ratMk_scale_eq hD (hdvd bc List.mem_cons_self))
      have hmul : ratMul bc.2 (ratOfNat (a (subMultiIdx α bc.1))) =
          ratMk (((chooseRaw bc.2).num * ((D / (chooseRaw bc.2).den : Nat) : Int)) *
            (a (subMultiIdx α bc.1) : Int)) D hD := by
        conv => lhs; rw [hbc]
        unfold ratMul ratOfNat ratOfInt ratMk
        apply Quot.sound; unfold RawRatEq rawMul; simp
      rw [hmul, ratMk_same_den_add]
    · simp only [hle, Bool.false_eq_true, ↓reduceIte]
      have hz : ratZero = ratMk 0 D hD := by
        unfold ratZero ratOfInt ratMk; apply Quot.sound; unfold RawRatEq; simp
      rw [hz, ratMk_same_den_add, Int.add_zero]

/-- Binary multi-index `(i, j, 0, ..., 0)` on `Fin k`. -/
def binMultiIdx (k : Nat) (i j : Nat) : MultiIdx k :=
  fun a => if a.val = 0 then i else if a.val = 1 then j else 0

private def isBinSupp {k : Nat} (β : MultiIdx k) : Bool :=
  (finList k).all fun a => decide (2 ≤ a.val → β a = 0)

private theorem isBinSupp_eq_true_iff {k : Nat} (β : MultiIdx k) :
    isBinSupp β = true ↔ ∀ a : Fin k, 2 ≤ a.val → β a = 0 := by
  unfold isBinSupp
  simp only [List.all_eq_true, decide_eq_true_eq]
  exact ⟨fun h a => h a (mem_finList a), fun h a _ => h a⟩

private theorem isBinSupp_total {k : Nat} (hk : 2 ≤ k) (β : MultiIdx k)
    (hsupp : ∀ a : Fin k, 2 ≤ a.val → β a = 0) :
    totalMultiIdx β = β ⟨0, by omega⟩ + β ⟨1, by omega⟩ := by
  cases k with
  | zero => omega
  | succ k1 =>
    cases k1 with
    | zero => omega
    | succ m =>
      unfold totalMultiIdx
      simp only [finList, List.map_cons, List.foldr_cons]
      have htail : (((finList m).map Fin.succ).map Fin.succ).foldr (fun a acc => β a + acc) 0 = 0 := by
        have hzero : ∀ zs : List (Fin (m + 2)),
            (∀ z ∈ zs, 2 ≤ z.val) → zs.foldr (fun a acc => β a + acc) 0 = 0 := by
          intro zs; induction zs with
          | nil => intro _; rfl
          | cons z zs ih =>
            intro hz
            rw [List.foldr_cons, hsupp z (hz z List.mem_cons_self),
                ih (fun y hy => hz y (List.mem_cons_of_mem z hy)), Nat.zero_add]
        apply hzero
        intro z hz
        rcases List.mem_map.mp hz with ⟨y, hy, rfl⟩
        rcases List.mem_map.mp hy with ⟨_, _, rfl⟩
        simp [Fin.succ]
      change β ⟨0, by omega⟩ + (β ⟨1, by omega⟩ +
        (((finList m).map Fin.succ).map Fin.succ).foldr (fun a acc => β a + acc) 0) =
        β ⟨0, by omega⟩ + β ⟨1, by omega⟩
      rw [htail]
      rfl

private theorem totalMultiIdx_binMultiIdx {k : Nat} (hk : 2 ≤ k) (i j : Nat) :
    totalMultiIdx (binMultiIdx k i j) = i + j := by
  have hsupp : ∀ a : Fin k, 2 ≤ a.val → binMultiIdx k i j a = 0 := by
    intro a ha; dsimp [binMultiIdx]
    have h0 : a.val ≠ 0 := by omega
    have h1 : a.val ≠ 1 := by omega
    simp [h0, h1]
  rw [isBinSupp_total hk (binMultiIdx k i j) hsupp]
  dsimp [binMultiIdx]

private def sumRangeInt (M : Nat) (f : Nat → Int) : Int :=
  (rangeList M).foldr (fun i acc => f i + acc) 0

private theorem sumRangeInt_succ (M : Nat) (f : Nat → Int) :
    sumRangeInt (M + 1) f = sumRangeInt M f + f M := by
  simp only [sumRangeInt, rangeList, List.foldr_append, List.foldr, Int.add_zero]
  have haux : ∀ (xs : List Nat) (c : Int),
      xs.foldr (fun i acc => f i + acc) c = xs.foldr (fun i acc => f i + acc) 0 + c := by
    intro xs c; induction xs with
    | nil => simp
    | cons x xs ih => simp only [List.foldr_cons, ih]; omega
  exact haux (rangeList M) (f M)

private theorem sumRangeInt_zero : ∀ M : Nat, sumRangeInt M (fun _ => 0) = 0
  | 0 => rfl
  | M + 1 => by rw [sumRangeInt_succ, sumRangeInt_zero M]; rfl

private theorem sumRangeInt_add (M : Nat) (f g : Nat → Int) :
    sumRangeInt M (fun i => f i + g i) = sumRangeInt M f + sumRangeInt M g := by
  induction M with
  | zero => simp [sumRangeInt, rangeList]
  | succ M ih =>
    rw [sumRangeInt_succ, sumRangeInt_succ, sumRangeInt_succ, ih]
    omega

private theorem sumRangeInt_mul_const (M : Nat) (c : Int) (f : Nat → Int) :
    sumRangeInt M (fun i => c * f i) = c * sumRangeInt M f := by
  induction M with
  | zero => simp [sumRangeInt, rangeList]
  | succ M ih =>
    rw [sumRangeInt_succ, sumRangeInt_succ, ih, Int.mul_add]

private theorem sumRangeInt_congr {M : Nat} {f g : Nat → Int}
    (h : ∀ i : Nat, i < M → f i = g i) :
    sumRangeInt M f = sumRangeInt M g := by
  induction M with
  | zero => rfl
  | succ M ih =>
    rw [sumRangeInt_succ, sumRangeInt_succ, ih (fun i hi => h i (by omega)), h M (by omega)]

private theorem sumRangeInt_single {M i0 : Nat} (c : Int) (hi0 : i0 < M) :
    sumRangeInt M (fun i => if i = i0 then c else 0) = c := by
  induction M with
  | zero => omega
  | succ M ih =>
    rw [sumRangeInt_succ]
    by_cases heq : M = i0
    · subst heq
      have h0 : sumRangeInt M (fun i => if i = M then c else 0) = 0 := by
        rw [sumRangeInt_congr (g := fun _ => 0) (fun i hi => by simp [show i ≠ M by omega])]
        exact sumRangeInt_zero M
      simp [h0]
    · rw [ih (by omega)]
      simp [heq]

private theorem sumRangeInt_shift_sub (b0 L : Nat) (g : Nat → Int) :
    sumRangeInt (b0 + L + 1)
      (fun i => if b0 ≤ i ∧ i ≤ b0 + L then g (i - b0) else 0) =
    sumRangeInt (L + 1) g := by
  induction L with
  | zero =>
    simp only [Nat.add_zero]
    rw [sumRangeInt_succ, Nat.zero_add, sumRangeInt_succ]
    have h0g : sumRangeInt 0 g = 0 := rfl
    rw [h0g]
    have h0 : sumRangeInt b0 (fun i => if b0 ≤ i ∧ i ≤ b0 then g (i - b0) else 0) = 0 := by
      rw [sumRangeInt_congr (g := fun _ => 0) (fun i hi => by
        have hnot : ¬ (b0 ≤ i ∧ i ≤ b0) := by omega
        simp [hnot])]
      exact sumRangeInt_zero b0
    rw [h0]
    simp
  | succ L ih =>
    rw [show b0 + (L + 1) + 1 = (b0 + L + 1) + 1 by omega,
        sumRangeInt_succ, sumRangeInt_succ (L + 1) g, ← ih]
    have hleft : sumRangeInt (b0 + L + 1)
        (fun i => if b0 ≤ i ∧ i ≤ b0 + (L + 1) then g (i - b0) else 0) =
        sumRangeInt (b0 + L + 1)
        (fun i => if b0 ≤ i ∧ i ≤ b0 + L then g (i - b0) else 0) := by
      apply sumRangeInt_congr
      intro i hi
      by_cases hb : b0 ≤ i
      · have h1 : i ≤ b0 + (L + 1) := by omega
        have h2 : i ≤ b0 + L := by omega
        simp [hb, h1, h2]
      · simp [hb]
    rw [hleft]
    have htop : b0 ≤ b0 + L + 1 ∧ b0 + L + 1 ≤ b0 + (L + 1) := by omega
    simp [htop, show b0 + L + 1 - b0 = L + 1 by omega]

private theorem filter_double {α : Type u} (p q : α → Bool) :
    ∀ xs : List α, (xs.filter p).filter q = xs.filter (fun x => p x && q x)
  | [] => rfl
  | x :: xs => by
    simp only [List.filter]
    cases hp : p x
    · simp only [Bool.false_and, Bool.false_eq_true, ↓reduceIte, filter_double p q xs]
    · cases hq : q x <;>
        simp only [List.filter, hq, Bool.true_and, Bool.false_eq_true, ↓reduceIte, filter_double p q xs]

private theorem filter_congr_mem {α : Type u} {p q : α → Bool} :
    ∀ {xs : List α}, (∀ x ∈ xs, p x = q x) → xs.filter p = xs.filter q
  | [], _ => rfl
  | x :: xs, h => by
    simp only [List.filter, h x List.mem_cons_self,
               filter_congr_mem (fun y hy => h y (List.mem_cons_of_mem x hy))]

private theorem length_eq_sumRange_buckets {α : Type u} (key : α → Nat) (M : Nat) :
    ∀ (xs : List α), (∀ x ∈ xs, key x < M) →
      (xs.length : Int) = sumRangeInt M (fun i => ((xs.filter fun x => decide (key x = i)).length : Int))
  | [], _ => (sumRangeInt_zero M).symm
  | x :: xs, hM => by
    have hx_lt : key x < M := hM x List.mem_cons_self
    have ih := length_eq_sumRange_buckets key M xs (fun y hy => hM y (List.mem_cons_of_mem x hy))
    have hfilt_step : ∀ i : Nat,
        (((x :: xs).filter fun z => decide (key z = i)).length : Int) =
        ((xs.filter fun z => decide (key z = i)).length : Int) + (if i = key x then 1 else 0) := by
      intro i
      simp only [List.filter]
      by_cases hki : key x = i
      · subst hki; simp only [decide_true, ↓reduceIte, List.length_cons]; omega
      · have hik : i ≠ key x := fun h => hki h.symm
        simp [hki, hik]
    rw [sumRangeInt_congr (fun i _ => hfilt_step i),
        sumRangeInt_add,
        ← ih,
        sumRangeInt_single 1 hx_lt,
        List.length_cons]
    omega

private theorem parikh_binSlice_eq_balancedCount_two {k : Nat} (hk : 2 ≤ k) (n : Nat) :
    sumRangeInt (n + 1) (fun i => (parikhBalancedCount k (binMultiIdx k i (n - i)) : Int)) =
      (balancedCount 2 n : Int) := by
  let a0 : Fin k := ⟨0, by omega⟩
  let a1 : Fin k := ⟨1, by omega⟩
  have ha0_val : a0.val = 0 := rfl
  have ha1_val : a1.val = 1 := rfl
  have ha0_ne_a1 : a0 ≠ a1 := fun h => by
    have := congrArg Fin.val h; rw [ha0_val, ha1_val] at this; omega
  have ha1_ne_a0 : a1 ≠ a0 := fun h => ha0_ne_a1 h.symm
  let binWords := (balancedWordsList k n).filter fun w => decide (∀ a ∈ w, a.val < 2)
  have hlen_bw : binWords.length = balancedCount 2 n := binarySupported_balanced_count_eq hk n
  have hkey_lt : ∀ w ∈ binWords, letterCount a0 w < n + 1 := by
    intro w hw
    rcases List.mem_filter.mp hw with ⟨hw_b, _⟩
    have hw_len : w.length = n := (mem_allWords_iff k n w).mp (List.mem_filter.mp hw_b).1
    have hle := letterCount_le_length a0 w
    omega
  have hsum_bw := length_eq_sumRange_buckets (letterCount a0) (n + 1) binWords hkey_lt
  rw [hlen_bw] at hsum_bw
  rw [hsum_bw]
  apply sumRangeInt_congr
  intro i hi
  have htot_eq : totalMultiIdx (binMultiIdx k i (n - i)) = n := by
    rw [totalMultiIdx_binMultiIdx hk i (n - i)]; omega
  unfold parikhBalancedCount
  rw [htot_eq]
  congr 1
  congr 1
  dsimp [binWords]
  rw [filter_double]
  symm
  apply filter_congr_mem
  intro w hw
  have hw_len : w.length = n := (mem_allWords_iff k n w).mp (List.mem_filter.mp hw).1
  apply Bool.eq_iff_iff.mpr
  simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq]
  have hsum01 : ∀ z : Word k, (∀ x ∈ z, x.val < 2) →
      letterCount a0 z + letterCount a1 z = z.length := by
    intro z; induction z with
    | nil => intro _; rfl
    | cons x zs ih =>
      intro hall
      have hx2 : x.val < 2 := hall x List.mem_cons_self
      have ih' := ih (fun y hy => hall y (List.mem_cons_of_mem x hy))
      by_cases hx0 : x.val = 0
      · have hxa0 : x = a0 := Fin.ext hx0
        rw [hxa0]
        simp only [letterCount_cons, ↓reduceIte, ha0_ne_a1, List.length_cons]; omega
      · have hx1 : x.val = 1 := by omega
        have hxa1 : x = a1 := Fin.ext hx1
        rw [hxa1]
        simp only [letterCount_cons, ↓reduceIte, ha1_ne_a0, List.length_cons]; omega
  constructor
  · rintro ⟨hall2, hc0⟩ a _
    dsimp [binMultiIdx]
    by_cases ha0 : a.val = 0
    · have heq : a = a0 := Fin.ext ha0
      simp only [ha0, ↓reduceIte]
      rw [heq, hc0]
    · by_cases ha1 : a.val = 1
      · have heq : a = a1 := Fin.ext ha1
        have hs := hsum01 w hall2
        simp only [ha1, ↓reduceIte, show ¬ (1 = 0) by decide]
        rw [heq]; omega
      · simp only [ha0, ha1, ↓reduceIte]
        apply letterCount_eq_zero_of_forall_ne
        intro x hx hxa; subst hxa
        have := hall2 x hx; omega
  · intro hall_eq
    refine ⟨?_, ?_⟩
    · intro x hx
      by_cases hx2 : x.val < 2
      · exact hx2
      · exfalso
        have hpos : 0 < letterCount x w := (letterCount_pos_iff_mem x w).mpr hx
        have h0 := hall_eq x (mem_finList x)
        dsimp [binMultiIdx] at h0
        have hx_ne0 : x.val ≠ 0 := by omega
        have hx_ne1 : x.val ≠ 1 := by omega
        simp [hx_ne0, hx_ne1] at h0
        omega
    · have h0 := hall_eq a0 (mem_finList a0)
      simpa [binMultiIdx, a0] using h0

private def maxDegMPolyZ {k : Nat} : MPolyZ k → Nat
  | [] => 0
  | bc :: rest => Nat.max (totalMultiIdx bc.1) (maxDegMPolyZ rest)

private theorem le_maxDegMPolyZ {k : Nat} {bc : MultiIdx k × Int} :
    ∀ {R : MPolyZ k}, bc ∈ R → totalMultiIdx bc.1 ≤ maxDegMPolyZ R
  | [], h => nomatch h
  | _ :: _, h => by
    simp only [maxDegMPolyZ]
    cases h with
    | head _ => exact Nat.le_max_left _ _
    | tail _ hm => exact Nat.le_trans (le_maxDegMPolyZ hm) (Nat.le_max_right _ _)

private def specCoeffAt {k : Nat} (hk : 2 ≤ k) (R : MPolyZ k) (d : Nat) : Int :=
  R.foldr (fun bc acc =>
    acc + (if isBinSupp bc.1 && decide (bc.1 ⟨0, by omega⟩ + bc.1 ⟨1, by omega⟩ = d) then bc.2 else 0)) 0

private theorem specCoeffAt_cons {k : Nat} (hk : 2 ≤ k) (bc : MultiIdx k × Int)
    (R : MPolyZ k) (d : Nat) :
    specCoeffAt hk (bc :: R) d =
      specCoeffAt hk R d +
      (if isBinSupp bc.1 && decide (bc.1 ⟨0, by omega⟩ + bc.1 ⟨1, by omega⟩ = d) then bc.2 else 0) := rfl

private def specMPolyZ {k : Nat} (hk : 2 ≤ k) (R : MPolyZ k) : PolyZ :=
  (rangeList (maxDegMPolyZ R + 1)).map (specCoeffAt hk R)

private theorem polyCoeffZ_specMPolyZ {k : Nat} (hk : 2 ≤ k) (R : MPolyZ k) (d : Nat) :
    polyCoeffZ (specMPolyZ hk R) d = specCoeffAt hk R d := by
  unfold specMPolyZ polyCoeffZ
  by_cases hlt : d < maxDegMPolyZ R + 1
  · exact listGetD_map_rangeList 0 (maxDegMPolyZ R + 1) d (specCoeffAt hk R) hlt
  · rw [listGetD_eq_default 0 _ d (by rw [List.length_map, length_rangeList]; omega)]
    have hzero : ∀ S : MPolyZ k,
        (∀ bc ∈ S, totalMultiIdx bc.1 < d) → specCoeffAt hk S d = 0 := by
      intro S; induction S with
      | nil => intro _; rfl
      | cons bc S ih =>
        intro hbd
        rw [specCoeffAt_cons, ih (fun x hx => hbd x (List.mem_cons_of_mem bc hx))]
        by_cases hbs : isBinSupp bc.1 = true
        · have htot := isBinSupp_total hk bc.1 ((isBinSupp_eq_true_iff bc.1).mp hbs)
          have hlt_bc : totalMultiIdx bc.1 < d := hbd bc List.mem_cons_self
          have hne : bc.1 ⟨0, by omega⟩ + bc.1 ⟨1, by omega⟩ ≠ d := by omega
          simp [hbs, hne]
        · simp [hbs]
    exact (hzero R (fun bc hbc => by have := le_maxDegMPolyZ hbc; omega)).symm

private theorem specCoeffAt_zero {k : Nat} (hk : 2 ≤ k) (R : MPolyZ k) :
    specCoeffAt hk R 0 = mPolyCoeffZ R (zeroMultiIdx k) := by
  induction R with
  | nil => rfl
  | cons bc R ih =>
    rw [specCoeffAt_cons, mPolyCoeffZ_cons, ih]
    have hcond : (isBinSupp bc.1 && decide (bc.1 ⟨0, by omega⟩ + bc.1 ⟨1, by omega⟩ = 0)) =
        eqMultiIdx bc.1 (zeroMultiIdx k) := by
      apply Bool.eq_iff_iff.mpr
      simp only [Bool.and_eq_true, isBinSupp_eq_true_iff, decide_eq_true_eq, eqMultiIdx_eq_true_iff]
      constructor
      · rintro ⟨hbs, h01⟩
        funext a
        dsimp [zeroMultiIdx]
        by_cases ha0 : a.val = 0
        · have heq : a = ⟨0, by omega⟩ := Fin.ext ha0
          rw [heq]; omega
        · by_cases ha1 : a.val = 1
          · have heq : a = ⟨1, by omega⟩ := Fin.ext ha1
            rw [heq]; omega
          · exact hbs a (by omega)
      · intro heq
        rw [heq]; dsimp [zeroMultiIdx]; exact ⟨fun _ _ => rfl, rfl⟩
    rw [hcond]

private theorem binSlice_mPolyCoeffZ {k : Nat} (hk : 2 ≤ k) (R : MPolyZ k) (n : Nat) :
    sumRangeInt (n + 1) (fun i => mPolyCoeffZ R (binMultiIdx k i (n - i))) =
      specCoeffAt hk R n := by
  induction R with
  | nil =>
    unfold mPolyCoeffZ specCoeffAt
    exact sumRangeInt_zero (n + 1)
  | cons bc R ih =>
    simp only [mPolyCoeffZ_cons, specCoeffAt_cons]
    rw [sumRangeInt_add, ih]
    congr 1
    by_cases hbs : isBinSupp bc.1 = true
    · have hsupp := (isBinSupp_eq_true_iff bc.1).mp hbs
      by_cases hsum : bc.1 ⟨0, by omega⟩ + bc.1 ⟨1, by omega⟩ = n
      · simp only [hbs, hsum, decide_true, Bool.and_self, ↓reduceIte]
        let i0 := bc.1 ⟨0, by omega⟩
        have hi0_lt : i0 < n + 1 := by dsimp [i0]; omega
        rw [sumRangeInt_congr (g := fun i => if i = i0 then bc.2 else 0) ?_]
        · exact sumRangeInt_single bc.2 hi0_lt
        · intro i hi
          have heq_iff : eqMultiIdx bc.1 (binMultiIdx k i (n - i)) = true ↔ i = i0 := by
            rw [eqMultiIdx_eq_true_iff]
            constructor
            · intro hfn
              have h0 := congrFun hfn ⟨0, by omega⟩
              simpa [binMultiIdx, i0] using h0.symm
            · intro hi_eq; subst hi_eq
              funext a; dsimp [binMultiIdx]
              by_cases ha0 : a.val = 0
              · have heq : a = ⟨0, by omega⟩ := Fin.ext ha0
                rw [heq]; simp [ha0, i0]
              · by_cases ha1 : a.val = 1
                · have heq : a = ⟨1, by omega⟩ := Fin.ext ha1
                  rw [heq]; simp [ha0, ha1]; dsimp [i0] at *; omega
                · simp [ha0, ha1, hsupp a (by omega)]
          by_cases hii0 : i = i0
          · rw [(heq_iff.mpr hii0)]; simp [hii0]
          · have hfalse : eqMultiIdx bc.1 (binMultiIdx k i (n - i)) = false :=
              Bool.eq_false_iff.mpr (fun ht => hii0 (heq_iff.mp ht))
            simp [hfalse, hii0]
      · simp only [hbs, decide_eq_false hsum, Bool.and_false, Bool.false_eq_true, ↓reduceIte]
        rw [sumRangeInt_congr (g := fun _ => 0) ?_, sumRangeInt_zero]
        intro i hi
        have hfalse : eqMultiIdx bc.1 (binMultiIdx k i (n - i)) = false := by
          apply Bool.eq_false_iff.mpr; intro ht
          have hfn := (eqMultiIdx_eq_true_iff _ _).mp ht
          have h0 : bc.1 ⟨0, by omega⟩ = i := by
            have := congrFun hfn ⟨0, by omega⟩; simpa [binMultiIdx] using this
          have h1 : bc.1 ⟨1, by omega⟩ = n - i := by
            have := congrFun hfn ⟨1, by omega⟩; simpa [binMultiIdx] using this
          omega
        simp [hfalse]
    · simp only [hbs, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
      rw [sumRangeInt_congr (g := fun _ => 0) ?_, sumRangeInt_zero]
      intro i _
      have hfalse : eqMultiIdx bc.1 (binMultiIdx k i (n - i)) = false := by
        apply Bool.eq_false_iff.mpr; intro ht
        have hfn := (eqMultiIdx_eq_true_iff _ _).mp ht
        apply hbs
        apply (isBinSupp_eq_true_iff bc.1).mpr
        intro a ha2
        rw [hfn]; dsimp [binMultiIdx]
        have hne0 : a.val ≠ 0 := by omega
        have hne1 : a.val ≠ 1 := by omega
        simp [hne0, hne1]
      simp [hfalse]

private theorem cauchySumZ_eq_sumRange (Q : PolyZ) (g : Nat → Int) (n : Nat) :
    ∀ m : Nat, cauchySumZ Q g n m =
      sumRangeInt m (fun d => if d ≤ n then polyCoeffZ Q d * g (n - d) else 0)
  | 0 => by simp [cauchySumZ, sumRangeInt, rangeList]
  | m + 1 => by
    simp only [cauchySumZ, sumRangeInt_succ, cauchySumZ_eq_sumRange Q g n m]

private theorem binSlice_mulMPolySeriesZ {k : Nat} (hk : 2 ≤ k) (Q : MPolyZ k)
    (F : MultiIdx k → Int) (n : Nat) :
    sumRangeInt (n + 1) (fun i => mulMPolySeriesZ Q F (binMultiIdx k i (n - i))) =
      mulPolySeriesZ (specMPolyZ hk Q)
        (fun m => sumRangeInt (m + 1) (fun t => F (binMultiIdx k t (m - t)))) n := by
  let g : Nat → Int := fun m => sumRangeInt (m + 1) (fun t => F (binMultiIdx k t (m - t)))
  have hmonom : ∀ bc : MultiIdx k × Int,
      sumRangeInt (n + 1) (fun i =>
        if leMultiIdx bc.1 (binMultiIdx k i (n - i)) then
          bc.2 * F (subMultiIdx (binMultiIdx k i (n - i)) bc.1)
        else 0) =
      (if isBinSupp bc.1 && decide (bc.1 ⟨0, by omega⟩ + bc.1 ⟨1, by omega⟩ ≤ n) then
        bc.2 * g (n - (bc.1 ⟨0, by omega⟩ + bc.1 ⟨1, by omega⟩))
       else 0) := by
    intro bc
    let b0 := bc.1 ⟨0, by omega⟩
    let b1 := bc.1 ⟨1, by omega⟩
    by_cases hbs : isBinSupp bc.1 = true
    · have hsupp := (isBinSupp_eq_true_iff bc.1).mp hbs
      by_cases hle_n : b0 + b1 ≤ n
      · simp only [hbs, show bc.1 ⟨0, by omega⟩ + bc.1 ⟨1, by omega⟩ ≤ n from hle_n,
                   decide_true, Bool.and_self, ↓reduceIte]
        let L := n - (b0 + b1)
        have hstep_congr : sumRangeInt (n + 1) (fun i =>
            if leMultiIdx bc.1 (binMultiIdx k i (n - i)) then
              bc.2 * F (subMultiIdx (binMultiIdx k i (n - i)) bc.1)
            else 0) =
            sumRangeInt (n + 1) (fun i =>
              if b0 ≤ i ∧ i ≤ b0 + L then
                bc.2 * F (binMultiIdx k (i - b0) (L - (i - b0)))
              else 0) := by
          apply sumRangeInt_congr
          intro i hi
          have hle_iff : leMultiIdx bc.1 (binMultiIdx k i (n - i)) = true ↔ b0 ≤ i ∧ i ≤ b0 + L := by
            rw [leMultiIdx_eq_true_iff]
            constructor
            · intro hall
              have h0 : b0 ≤ i := by have := hall ⟨0, by omega⟩; simpa [binMultiIdx, b0] using this
              have h1 : b1 ≤ n - i := by have := hall ⟨1, by omega⟩; simpa [binMultiIdx, b1] using this
              exact ⟨h0, by omega⟩
            · rintro ⟨hi_ge, hi_le⟩ a
              dsimp [binMultiIdx]
              by_cases ha0 : a.val = 0
              · have heq : a = ⟨0, by omega⟩ := Fin.ext ha0
                rw [heq]; simp [ha0, b0, hi_ge]
              · by_cases ha1 : a.val = 1
                · have heq : a = ⟨1, by omega⟩ := Fin.ext ha1
                  rw [heq]; simp [ha0, ha1]; dsimp [b1, L] at *; omega
                · simp [ha0, ha1, hsupp a (by omega)]
          by_cases hcond : b0 ≤ i ∧ i ≤ b0 + L
          · rw [hle_iff.mpr hcond]
            simp only [↓reduceIte, hcond, and_self]
            have hsub_eq : subMultiIdx (binMultiIdx k i (n - i)) bc.1 =
                binMultiIdx k (i - b0) (L - (i - b0)) := by
              funext a; dsimp [subMultiIdx, binMultiIdx]
              by_cases ha0 : a.val = 0
              · have heq : a = ⟨0, by omega⟩ := Fin.ext ha0
                rw [heq]; simp [ha0, b0]
              · by_cases ha1 : a.val = 1
                · have heq : a = ⟨1, by omega⟩ := Fin.ext ha1
                  rw [heq]; simp [ha0, ha1]; dsimp [b1, L] at *; omega
                · simp [ha0, ha1, hsupp a (by omega)]
            rw [hsub_eq]
          · have hfalse : leMultiIdx bc.1 (binMultiIdx k i (n - i)) = false :=
              Bool.eq_false_iff.mpr (fun ht => hcond (hle_iff.mp ht))
            simp [hfalse, hcond]
        rw [hstep_congr]
        have htrim : sumRangeInt (n + 1) (fun i =>
              if b0 ≤ i ∧ i ≤ b0 + L then
                bc.2 * F (binMultiIdx k (i - b0) (L - (i - b0)))
              else 0) =
            sumRangeInt (b0 + L + 1) (fun i =>
              if b0 ≤ i ∧ i ≤ b0 + L then
                bc.2 * F (binMultiIdx k (i - b0) (L - (i - b0)))
              else 0) := by
          have hrem : ∀ extra : Nat,
              sumRangeInt (b0 + L + 1 + extra) (fun i =>
                if b0 ≤ i ∧ i ≤ b0 + L then
                  bc.2 * F (binMultiIdx k (i - b0) (L - (i - b0)))
                else 0) =
              sumRangeInt (b0 + L + 1) (fun i =>
                if b0 ≤ i ∧ i ≤ b0 + L then
                  bc.2 * F (binMultiIdx k (i - b0) (L - (i - b0)))
                else 0) := by
            intro extra; induction extra with
            | zero => simp
            | succ e ihe =>
              rw [show b0 + L + 1 + (e + 1) = (b0 + L + 1 + e) + 1 by omega,
                  sumRangeInt_succ, ihe]
              have hnot : ¬ (b0 ≤ b0 + L + 1 + e ∧ b0 + L + 1 + e ≤ b0 + L) := by omega
              simp [hnot]
          have hn_split : n + 1 = (b0 + L + 1) + b1 := by dsimp [L]; omega
          rw [hn_split]
          exact hrem b1
        rw [htrim,
            sumRangeInt_shift_sub b0 L (fun t => bc.2 * F (binMultiIdx k t (L - t))),
            sumRangeInt_mul_const]
      · simp only [hbs, show ¬ (bc.1 ⟨0, by omega⟩ + bc.1 ⟨1, by omega⟩ ≤ n) from hle_n,
                   decide_false, Bool.and_false, Bool.false_eq_true, ↓reduceIte]
        rw [sumRangeInt_congr (g := fun _ => 0) ?_, sumRangeInt_zero]
        intro i hi
        have hfalse : leMultiIdx bc.1 (binMultiIdx k i (n - i)) = false := by
          apply Bool.eq_false_iff.mpr; intro ht
          have hall := (leMultiIdx_eq_true_iff _ _).mp ht
          have h0 : b0 ≤ i := by have := hall ⟨0, by omega⟩; simpa [binMultiIdx, b0] using this
          have h1 : b1 ≤ n - i := by have := hall ⟨1, by omega⟩; simpa [binMultiIdx, b1] using this
          omega
        simp [hfalse]
    · simp only [hbs, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
      rw [sumRangeInt_congr (g := fun _ => 0) ?_, sumRangeInt_zero]
      intro i _
      have hfalse : leMultiIdx bc.1 (binMultiIdx k i (n - i)) = false := by
        apply Bool.eq_false_iff.mpr; intro ht
        have hall := (leMultiIdx_eq_true_iff _ _).mp ht
        apply hbs
        apply (isBinSupp_eq_true_iff bc.1).mpr
        intro a ha2
        have ha := hall a
        dsimp [binMultiIdx] at ha
        have hne0 : a.val ≠ 0 := by omega
        have hne1 : a.val ≠ 1 := by omega
        simp [hne0, hne1] at ha
        exact ha
      simp [hfalse]
  let B := maxDegMPolyZ Q + 1
  have hlen_spec : (specMPolyZ hk Q).length = B := by
    dsimp [specMPolyZ, B]; rw [List.length_map, length_rangeList]
  unfold mulPolySeriesZ
  rw [hlen_spec, cauchySumZ_eq_sumRange]
  have hcongr_rhs : sumRangeInt B (fun d => if d ≤ n then polyCoeffZ (specMPolyZ hk Q) d * g (n - d) else 0) =
      sumRangeInt B (fun d => if d ≤ n then specCoeffAt hk Q d * g (n - d) else 0) :=
    sumRangeInt_congr (fun d _ => by rw [polyCoeffZ_specMPolyZ])
  rw [hcongr_rhs]
  have hind : ∀ S : MPolyZ k, (∀ bc ∈ S, totalMultiIdx bc.1 < B) →
      sumRangeInt (n + 1) (fun i => mulMPolySeriesZ S F (binMultiIdx k i (n - i))) =
      sumRangeInt B (fun d => if d ≤ n then specCoeffAt hk S d * g (n - d) else 0) := by
    intro S; induction S with
    | nil =>
      intro _
      unfold mulMPolySeriesZ specCoeffAt
      simp only [List.foldr_nil]
      rw [sumRangeInt_zero]
      rw [sumRangeInt_congr (g := fun _ => 0) (fun _ _ => by split <;> simp), sumRangeInt_zero]
    | cons bc S ih =>
      intro hbd
      simp only [mulMPolySeriesZ_cons, specCoeffAt_cons]
      rw [sumRangeInt_add, ih (fun x hx => hbd x (List.mem_cons_of_mem bc hx)), hmonom bc]
      have hsplit_rhs : sumRangeInt B (fun d =>
          if d ≤ n then
            (specCoeffAt hk S d +
              (if isBinSupp bc.1 && decide (bc.1 ⟨0, by omega⟩ + bc.1 ⟨1, by omega⟩ = d) then bc.2 else 0)) *
              g (n - d)
          else 0) =
          sumRangeInt B (fun d => if d ≤ n then specCoeffAt hk S d * g (n - d) else 0) +
          sumRangeInt B (fun d =>
            if d ≤ n then
              (if isBinSupp bc.1 && decide (bc.1 ⟨0, by omega⟩ + bc.1 ⟨1, by omega⟩ = d) then bc.2 else 0) *
                g (n - d)
            else 0) := by
        rw [← sumRangeInt_add]
        apply sumRangeInt_congr
        intro d _
        by_cases hdn : d ≤ n
        · simp [hdn, Int.add_mul]
        · simp [hdn]
      rw [hsplit_rhs]
      congr 1
      let d0 := bc.1 ⟨0, by omega⟩ + bc.1 ⟨1, by omega⟩
      by_cases hbs : isBinSupp bc.1 = true
      · have htot := isBinSupp_total hk bc.1 ((isBinSupp_eq_true_iff bc.1).mp hbs)
        have hd0_lt : d0 < B := by
          have := hbd bc List.mem_cons_self
          dsimp [d0]; omega
        by_cases hd0_le : d0 ≤ n
        · simp only [hbs, show bc.1 ⟨0, by omega⟩ + bc.1 ⟨1, by omega⟩ ≤ n from hd0_le,
                     decide_true, Bool.and_self, ↓reduceIte]
          rw [sumRangeInt_congr (g := fun d => if d = d0 then bc.2 * g (n - d0) else 0) ?_]
          · exact (sumRangeInt_single (bc.2 * g (n - d0)) hd0_lt).symm
          · intro d _
            by_cases hdd0 : d = d0
            · subst hdd0
              have hd0_eq : bc.1 ⟨0, by omega⟩ + bc.1 ⟨1, by omega⟩ = d0 := rfl
              simp [hbs, hd0_eq, hd0_le]
            · have hne : bc.1 ⟨0, by omega⟩ + bc.1 ⟨1, by omega⟩ ≠ d := fun h => hdd0 h.symm
              simp [hbs, hne, hdd0]
        · simp only [hbs, show ¬ (bc.1 ⟨0, by omega⟩ + bc.1 ⟨1, by omega⟩ ≤ n) from hd0_le,
                     decide_false, Bool.and_false, Bool.false_eq_true, ↓reduceIte]
          symm
          rw [sumRangeInt_congr (g := fun _ => 0) ?_, sumRangeInt_zero]
          intro d _
          by_cases hdd0 : d = d0
          · subst hdd0; simp [hd0_le]
          · have hne : bc.1 ⟨0, by omega⟩ + bc.1 ⟨1, by omega⟩ ≠ d := fun h => hdd0 h.symm
            simp [hbs, hne]
      · simp only [hbs, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
        symm
        rw [sumRangeInt_congr (g := fun _ => 0) ?_, sumRangeInt_zero]
        intro d _
        simp [hbs]
  exact hind Q (fun bc hbc => by have := le_maxDegMPolyZ hbc; dsimp [B]; omega)

/--
  **Main Multivariate (Parikh) Non-Rationality Theorem:**
  For EVERY alphabet size `k ≥ 2` (specifically including `k = 3`, `k = 4`, `k = 5`, ...),
  the `k`-variate letter-count (Parikh) formal power series of balanced words over `Fin k`
  is NOT rational in `ℚ[[x_0, ..., x_{k-1}]]`.
-/
theorem not_isRationalParikhGF (k : Nat) (hk : 2 ≤ k) :
    ¬ IsRationalParikhGF k := by
  rintro ⟨P, Q, hQ0_nz, heq⟩
  let rP := P.map fun bc => chooseRaw bc.2
  let rQ := Q.map fun bc => chooseRaw bc.2
  let D := prodDenRaw rP * prodDenRaw rQ
  have hD : 0 < D := Nat.mul_pos (prodDenRaw_pos rP) (prodDenRaw_pos rQ)
  have hdvdP : ∀ bc ∈ P, (chooseRaw bc.2).den ∣ D := fun bc hbc =>
    Nat.dvd_trans
      (rawDen_dvd_prodDenRaw (List.mem_map_of_mem (f := fun x : MultiIdx k × RatQ => chooseRaw x.2) hbc))
      (Nat.dvd_mul_right (prodDenRaw rP) (prodDenRaw rQ))
  have hdvdQ : ∀ bc ∈ Q, (chooseRaw bc.2).den ∣ D := fun bc hbc =>
    Nat.dvd_trans
      (rawDen_dvd_prodDenRaw (List.mem_map_of_mem (f := fun x : MultiIdx k × RatQ => chooseRaw x.2) hbc))
      (Nat.dvd_mul_left (prodDenRaw rQ) (prodDenRaw rP))
  let PZ := scaleMPoly D P
  let QZ := scaleMPoly D Q
  have hQZ0_nz : mPolyCoeffZ QZ (zeroMultiIdx k) ≠ 0 := by
    intro hz
    apply hQ0_nz
    rw [mPolyCoeffQ_scale D hD Q hdvdQ (zeroMultiIdx k)]
    change ratMk (mPolyCoeffZ QZ (zeroMultiIdx k)) D hD = ratZero
    rw [hz]
    unfold ratZero ratOfInt ratMk
    apply Quot.sound; unfold RawRatEq; simp
  have heqZ : ∀ α : MultiIdx k,
      mulMPolySeriesZ QZ (fun β => (parikhBalancedCount k β : Int)) α = mPolyCoeffZ PZ α := by
    intro α
    have hα : mulMPolySeriesQ Q (parikhBalancedSeries k) α = mPolyCoeffQ P α := congrFun heq α
    unfold parikhBalancedSeries at hα
    rw [mulMPolySeriesQ_scale D hD Q (parikhBalancedCount k) hdvdQ α,
        mPolyCoeffQ_scale D hD P hdvdP α] at hα
    have hraw := ratMk_eq_iff.mp hα
    unfold RawRatEq at hraw
    dsimp only at hraw
    change mulMPolySeriesZ QZ (fun β => (parikhBalancedCount k β : Int)) α * (D : Int) =
      mPolyCoeffZ PZ α * (D : Int) at hraw
    have hdiff0 : (mulMPolySeriesZ QZ (fun β => (parikhBalancedCount k β : Int)) α - mPolyCoeffZ PZ α) *
        (D : Int) = 0 := by rw [Int.sub_mul, hraw]; simp
    have hsub := int_eq_zero_of_mul_nat_pos hD hdiff0
    omega
  let P_uni := specMPolyZ hk PZ
  let Q_uni := specMPolyZ hk QZ
  have hQ_uni_nz : ¬ IsZeroPolyZ Q_uni := by
    intro hz
    have h0 := hz 0
    dsimp [Q_uni] at h0
    rw [polyCoeffZ_specMPolyZ, specCoeffAt_zero] at h0
    exact hQZ0_nz h0
  have heq_uni : ∀ n : Nat, mulPolySeriesZ Q_uni (fun m => (balancedCount 2 m : Int)) n =
      polyCoeffZ P_uni n := by
    intro n
    have hslice : sumRangeInt (n + 1)
        (fun i => mulMPolySeriesZ QZ (fun β => (parikhBalancedCount k β : Int)) (binMultiIdx k i (n - i))) =
        sumRangeInt (n + 1) (fun i => mPolyCoeffZ PZ (binMultiIdx k i (n - i))) :=
      sumRangeInt_congr (fun i _ => heqZ (binMultiIdx k i (n - i)))
    rw [binSlice_mulMPolySeriesZ hk QZ (fun β => (parikhBalancedCount k β : Int)) n,
        binSlice_mPolyCoeffZ hk PZ n,
        ← polyCoeffZ_specMPolyZ hk PZ n] at hslice
    have hg_eq : (fun m : Nat => sumRangeInt (m + 1)
        (fun t => (parikhBalancedCount k (binMultiIdx k t (m - t)) : Int))) =
        (fun m : Nat => (balancedCount 2 m : Int)) :=
      funext (parikh_binSlice_eq_balancedCount_two hk)
    rw [hg_eq] at hslice
    exact hslice
  have hrat2 : IsRationalGF (balancedCount 2) :=
    isRationalGF_of_Z ⟨P_uni, Q_uni, hQ_uni_nz, heq_uni⟩
  exact not_isRationalGF_balancedCount_two hrat2

theorem not_isRationalParikhGF_three : ¬ IsRationalParikhGF 3 :=
  not_isRationalParikhGF 3 (by decide)

/-! ## Section 7: Formal Statements & Complete Disproofs of Conjecture 00000004719 -/

/-- Reading 1: Total count of strictly `k`-letter balanced words over `Fin k` (`k ≥ 3`) is finite. -/
def Conjecture4719_TotalCountFinite_Multiletter : Prop :=
  ∀ k : Nat, 3 ≤ k → IsFiniteType { w : Word k // IsBalanced w ∧ UsesAllLetters k w }

theorem disproof_Conjecture4719_TotalCountFinite_Multiletter :
    ¬ Conjecture4719_TotalCountFinite_Multiletter := by
  intro h
  exact not_finite_surjBalancedWords 3 (by decide) (h 3 (by decide))

/-- Reading 2A (`k ≥ 2`, all balanced words): `∑ b_k(n) x^n` is rational for every `k ≥ 2`. -/
def Conjecture4719_UnivariateRational_Ge2 : Prop :=
  ∀ k : Nat, 2 ≤ k → IsRationalGF (balancedCount k)

theorem disproof_Conjecture4719_UnivariateRational_Ge2 :
    ¬ Conjecture4719_UnivariateRational_Ge2 := by
  intro h
  exact not_isRationalGF_balancedCount_two (h 2 (by decide))

/-- Reading 2B (`k ≥ 2`, surjective `k`-letter balanced words): `∑ surj_k(n) x^n` is rational for every `k ≥ 2`. -/
def Conjecture4719_SurjUnivariateRational_Ge2 : Prop :=
  ∀ k : Nat, 2 ≤ k → IsRationalGF (surjBalancedCount k)

theorem disproof_Conjecture4719_SurjUnivariateRational_Ge2 :
    ¬ Conjecture4719_SurjUnivariateRational_Ge2 := by
  intro h
  exact not_isRationalGF_surjBalancedCount_two (h 2 (by decide))

/-- Reading 2C (strict multiletter `k ≥ 3`, all balanced words): `∑ b_k(n) x^n` is rational for every `k ≥ 3`. -/
def Conjecture4719_UnivariateRational_Ge3 : Prop :=
  ∀ k : Nat, 3 ≤ k → IsRationalGF (balancedCount k)

theorem disproof_Conjecture4719_UnivariateRational_Ge3 :
    ¬ Conjecture4719_UnivariateRational_Ge3 := by
  intro h
  exact not_isRationalGF_balancedCount_five (h 5 (by decide))

/-- Reading 2D (strict multiletter `k ≥ 3`, genuinely `≥ 2`-letter balanced words): `∑ m_{k,≥2}(n) x^n` is rational for every `k ≥ 3`. -/
def Conjecture4719_MultiletterAtLeast2Rational_Ge3 : Prop :=
  ∀ k : Nat, 3 ≤ k → IsRationalGF (atLeastBalancedCount k 2)

theorem disproof_Conjecture4719_MultiletterAtLeast2Rational_Ge3 :
    ¬ Conjecture4719_MultiletterAtLeast2Rational_Ge3 := by
  intro h
  exact not_isRationalGF_atLeast2BalancedCount_five (h 5 (by decide))

/-- Reading 2E (strict multiletter `k ≥ 3`, multivariate Parikh OGF): `F_k(x_0, ..., x_{k-1})` is rational for every `k ≥ 3`. -/
def Conjecture4719_ParikhRational_Ge3 : Prop :=
  ∀ k : Nat, 3 ≤ k → IsRationalParikhGF k

theorem disproof_Conjecture4719_ParikhRational_Ge3 :
    ¬ Conjecture4719_ParikhRational_Ge3 := by
  intro h
  exact not_isRationalParikhGF_three (h 3 (by decide))

/--
  Reading 3 (Full Conjecture with Explicit Christoffel-Type Denominator Clause):
  Refuted uniformly for ANY predicate `IsChristoffelDenominator : PolyQ → Prop`, since no nonzero
  polynomial denominator `Q ∈ ℚ[x]` exists at all.
-/
def Conjecture4719_FullWithChristoffel (IsChristoffelDenominator : PolyQ → Prop) : Prop :=
  ∀ k : Nat, 3 ≤ k →
    ∃ P Q : PolyQ, ¬ IsZeroPolyQ Q ∧ IsChristoffelDenominator Q ∧
      mulPolySeriesQ Q (ofNatSeriesQ (balancedCount k)) = polyToSeriesQ P

theorem disproof_Conjecture4719_FullWithChristoffel
    (IsChristoffelDenominator : PolyQ → Prop) :
    ¬ Conjecture4719_FullWithChristoffel IsChristoffelDenominator := by
  intro h
  rcases h 5 (by decide) with ⟨P, Q, hQnz, _, heq⟩
  exact not_isRationalGF_balancedCount_five ⟨P, Q, hQnz, heq⟩

end Conjecture4719

/-! ## Axiom Verification Audit -/

#print axioms Conjecture4719.unary_balanced_isRationalGF
#print axioms Conjecture4719.arith_seq_isRationalGF
#print axioms Conjecture4719.fraenkel7_balanced_surj_witness
#print axioms Conjecture4719.word_0011_not_balanced_witness
#print axioms Conjecture4719.unary_parikh_isRationalParikhGF
#print axioms Conjecture4719.balancedCount_spec
#print axioms Conjecture4719.surjBalancedCount_spec
#print axioms Conjecture4719.hubertSplit_isBalanced
#print axioms Conjecture4719.hubertSplit_usesAllLetters
#print axioms Conjecture4719.isRationalGF_implies_eventuallyPeriodicMod
#print axioms Conjecture4719.balancedCount_two_eq_lipatov
#print axioms Conjecture4719.delta2_balancedCount_two
#print axioms Conjecture4719.not_eventuallyPeriodicMod_totient
#print axioms Conjecture4719.not_finite_surjBalancedWords
#print axioms Conjecture4719.not_finite_balancedWords
#print axioms Conjecture4719.not_isRationalGF_balancedCount_two
#print axioms Conjecture4719.not_isRationalGF_surjBalancedCount_two
#print axioms Conjecture4719.not_isRationalGF_balancedCount_five
#print axioms Conjecture4719.not_isRationalGF_atLeast2BalancedCount_five
#print axioms Conjecture4719.not_isRationalParikhGF
#print axioms Conjecture4719.disproof_Conjecture4719_TotalCountFinite_Multiletter
#print axioms Conjecture4719.disproof_Conjecture4719_UnivariateRational_Ge2
#print axioms Conjecture4719.disproof_Conjecture4719_SurjUnivariateRational_Ge2
#print axioms Conjecture4719.disproof_Conjecture4719_UnivariateRational_Ge3
#print axioms Conjecture4719.disproof_Conjecture4719_MultiletterAtLeast2Rational_Ge3
#print axioms Conjecture4719.disproof_Conjecture4719_ParikhRational_Ge3
#print axioms Conjecture4719.disproof_Conjecture4719_FullWithChristoffel
