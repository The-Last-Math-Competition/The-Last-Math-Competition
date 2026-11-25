import Std

namespace C163

abbrev Edge := Nat × Nat

/-- Each undirected edge is listed once, with its endpoints in increasing order. -/
def completeEdges : Nat → List Edge
  | 0 => []
  | n + 1 => completeEdges n ++ (List.range n).map (fun i => (i, n))

theorem complete_edge_membership (n a b : Nat) : (a, b) ∈ completeEdges n ↔ a < b ∧ b < n := by
  induction n with
  | zero => simp [completeEdges]
  | succ n ih =>
    simp only [completeEdges, List.mem_append, ih, List.mem_map, List.mem_range, Prod.mk.injEq]
    constructor
    · rintro (⟨hab, hbn⟩ | ⟨i, hin, hia, hnb⟩) <;> omega
    · intro h
      by_cases atLast : b = n
      · exact Or.inr ⟨a, by omega, rfl, atLast.symm⟩
      · exact Or.inl ⟨h.1, by omega⟩

theorem complete_edges_nodup (n : Nat) : (completeEdges n).Nodup := by
  induction n with
  | zero => exact List.nodup_nil
  | succ n ih =>
    change List.Pairwise (· ≠ ·) (completeEdges n ++ (List.range n).map (fun i => (i, n)))
    rw [List.pairwise_append]
    refine ⟨ih, List.Pairwise.map _ (fun a b h equal => h (congrArg Prod.fst equal))
      List.nodup_range, ?_⟩
    rintro ⟨a, b⟩ old _ new equal
    have less := ((complete_edge_membership n a b).mp old).2
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp new
    have impossible : b = n := congrArg Prod.snd equal
    omega

private theorem edge_count_square (n : Nat) : 2 * (completeEdges n).length + n = n * n := by
  induction n with
  | zero => decide
  | succ n ih =>
    have square : (n + 1) * (n + 1) = n * n + 2 * n + 1 := by
      simp only [Nat.add_mul, Nat.mul_add, Nat.mul_one, Nat.one_mul]
      omega
    rw [square]
    simp only [completeEdges, List.length_append, List.length_map, List.length_range]
    omega

theorem double_complete_edge_count (n : Nat) : 2 * (completeEdges n).length = n * (n - 1) := by
  have count := edge_count_square n
  cases n with
  | zero => decide
  | succ n =>
    rw [Nat.succ_sub_one]
    rw [Nat.mul_succ] at count
    omega

private theorem nodup_included_length {A : Type} [BEq A] [LawfulBEq A]
    (target source : List A) (distinct : target.Nodup)
    (covered : ∀ x ∈ target, x ∈ source) : target.length ≤ source.length := by
  induction target generalizing source with
  | nil => simp
  | cons a rest ih =>
    obtain ⟨notInRest, restDistinct⟩ := List.nodup_cons.mp distinct
    have inSource := covered a (by simp)
    have remainderCovered : ∀ x ∈ rest, x ∈ source.erase a := by
      intro x present
      have unequal : x ≠ a := fun h => notInRest (h ▸ present)
      exact (List.mem_erase_of_ne unequal).mpr (covered x (List.mem_cons_of_mem a present))
    have reducedBound := ih (source.erase a) restDistinct remainderCovered
    rw [List.length_erase_of_mem inSource] at reducedBound
    have sourceNonempty : 0 < source.length := List.length_pos_of_mem inSource
    simp only [List.length_cons]
    omega

private theorem layer_sum_bound (layers : List (List Edge)) (capacity : Nat)
    (each : ∀ l ∈ layers, l.length ≤ capacity) : layers.flatten.length ≤ capacity * layers.length := by
  induction layers with
  | nil => simp
  | cons l rest ih =>
    have headBound := each l (by simp)
    have tailBound := ih (fun layer member => each layer (List.mem_cons_of_mem l member))
    simp only [List.flatten_cons, List.length_append, List.length_cons, Nat.mul_succ]
    omega

theorem planar_cover_count (p : Nat) (layers : List (List Edge))
    (covered : ∀ e ∈ completeEdges p, e ∈ layers.flatten)
    (capacity : ∀ l ∈ layers, l.length ≤ 3 * (p - 2)) :
    p * (p - 1) ≤ 6 * (p - 2) * layers.length := by
  have count := nodup_included_length _ _ (complete_edges_nodup p) covered
  have sumBound := layer_sum_bound layers (3 * (p - 2)) capacity
  rw [← double_complete_edge_count]
  have bound := Nat.mul_le_mul_left 2 (Nat.le_trans count sumBound)
  simpa only [← Nat.mul_assoc] using bound

def Prime (p : Nat) : Prop := 2 ≤ p ∧ ∀ d, d ∣ p → d = 1 ∨ d = p

theorem prime_residues {p : Nat} (hp : Prime p) (notTwo : p ≠ 2) (notThree : p ≠ 3) :
    p = 6 * (p / 6) + 1 ∨ p = 6 * (p / 6) + 5 := by
  have odd : p % 2 ≠ 0 := by
    intro even
    rcases hp.2 2 (Nat.dvd_iff_mod_eq_zero.mpr even) with h | h
    · omega
    · exact notTwo h.symm
  have notDivThree : p % 3 ≠ 0 := by
    intro zero
    rcases hp.2 3 (Nat.dvd_iff_mod_eq_zero.mpr zero) with h | h
    · omega
    · exact notThree h.symm
  omega

private theorem first_layer_lower {p m t : Nat} (pLarge : 3 ≤ p) (shape : p = 6 * m + 1)
    (count : p * (p - 1) ≤ 6 * (p - 2) * t) : m + 1 ≤ t := by
  by_cases enough : m + 1 ≤ t
  · exact enough
  · exfalso
    have bound := Nat.le_trans count (Nat.mul_le_mul_left (6 * (p - 2)) (show t ≤ m by omega))
    have factor : 6 * (p - 2) * m = (p - 2) * (p - 1) := by
      calc
        6 * (p - 2) * m = (p - 2) * (6 * m) := by ac_rfl
        _ = (p - 2) * (p - 1) := by rw [show 6 * m = p - 1 by omega]
    rw [factor] at bound
    exact (Nat.not_lt_of_ge bound) (Nat.mul_lt_mul_of_pos_right (by omega) (by omega))

private theorem second_factor_strict {p : Nat} (large : 2 ≤ p) :
    (p - 2) * (p + 1) < p * (p - 1) := by
  let q := p - 2
  have left : p + 1 = q + 3 := by dsimp [q]; omega
  have first : p = q + 2 := by dsimp [q]; omega
  have second : p - 1 = q + 1 := by dsimp [q]; omega
  calc
    (p - 2) * (p + 1) = q * (q + 3) := by rw [left]
    _ < (q + 2) * (q + 1) := by
      simp only [Nat.mul_add, Nat.add_mul, Nat.mul_one]
      omega
    _ = p * (p - 1) := by rw [← first, ← second]

private theorem second_layer_lower {p m t : Nat} (pLarge : 3 ≤ p) (shape : p = 6 * m + 5)
    (count : p * (p - 1) ≤ 6 * (p - 2) * t) : m + 2 ≤ t := by
  by_cases enough : m + 2 ≤ t
  · exact enough
  · exfalso
    have bound := Nat.le_trans count (Nat.mul_le_mul_left (6 * (p - 2))
      (show t ≤ m + 1 by omega))
    have factor : 6 * (p - 2) * (m + 1) = (p - 2) * (p + 1) := by
      calc
        6 * (p - 2) * (m + 1) = (p - 2) * (6 * (m + 1)) := by ac_rfl
        _ = (p - 2) * (p + 1) := by rw [show 6 * (m + 1) = p + 1 by omega]
    rw [factor] at bound
    exact (Nat.not_lt_of_ge bound) (second_factor_strict (by omega))

def ceilSix (n : Nat) : Nat := (n + 5) / 6

theorem ceil_six_is_least (n : Nat) :
    n ≤ 6 * ceilSix n ∧ ∀ k, n ≤ 6 * k → ceilSix n ≤ k := by
  unfold ceilSix
  constructor
  · omega
  · intro k bound
    omega

def HasCover (planar : Nat → List Edge → Prop) (n t : Nat) : Prop :=
  ∃ layers : List (List Edge), layers.length = t ∧
    (∀ e ∈ completeEdges n, e ∈ layers.flatten) ∧ (∀ l ∈ layers, planar n l)

private theorem nonempty_cover {planar : Nat → List Edge → Prop} {p t : Nat}
    (large : 2 ≤ p) (cover : HasCover planar p t) : 1 ≤ t := by
  obtain ⟨layers, rfl, covered, _⟩ := cover
  cases layers with
  | nil =>
    have impossible := covered (0, 1) ((complete_edge_membership p 0 1).mpr (by omega))
    simp at impossible
  | cons head tail => simp

theorem prime_thickness {p : Nat} (hp : Prime p) (planar : Nat → List Edge → Prop)
    (euler : ∀ n l, 3 ≤ n → planar n l → l.length ≤ 3 * (n - 2))
    (smallTwo : HasCover planar 2 1) (smallThree : HasCover planar 3 1)
    (beinekeHarary : ∀ r, 1 ≤ r → HasCover planar (6 * r + 2) (r + 1))
    (restriction : ∀ n N t, n ≤ N → HasCover planar N t → HasCover planar n t) :
    HasCover planar p (ceilSix (p + 2)) ∧
      ∀ t, HasCover planar p t → ceilSix (p + 2) ≤ t := by
  by_cases two : p = 2
  · subst p
    exact ⟨smallTwo, fun _ cover => nonempty_cover (by decide) cover⟩
  by_cases three : p = 3
  · subst p
    exact ⟨smallThree, fun _ cover => nonempty_cover (by decide) cover⟩
  let m := p / 6
  have cases : p = 6 * m + 1 ∨ p = 6 * m + 5 := prime_residues hp two three
  have pLarge : 3 ≤ p := by have := hp.1; omega
  have count {t : Nat} (cover : HasCover planar p t) : p * (p - 1) ≤ 6 * (p - 2) * t := by
    obtain ⟨layers, rfl, covered, each⟩ := cover
    exact planar_cover_count p layers covered (fun l member => euler p l pLarge (each l member))
  rcases cases with first | second
  · have one : 1 ≤ m := by omega
    have rounded : ceilSix (p + 2) = m + 1 := by unfold ceilSix; omega
    rw [rounded]
    exact ⟨restriction p (6 * m + 2) (m + 1) (by omega) (beinekeHarary m one),
      fun _ cover => first_layer_lower pLarge first (count cover)⟩
  · have rounded : ceilSix (p + 2) = m + 2 := by unfold ceilSix; omega
    rw [rounded]
    exact ⟨restriction p (6 * (m + 1) + 2) (m + 2) (by omega)
        (beinekeHarary (m + 1) (by omega)),
      fun _ cover => second_layer_lower pLarge second (count cover)⟩

#print axioms complete_edges_nodup
#print axioms planar_cover_count
#print axioms prime_thickness

end C163
