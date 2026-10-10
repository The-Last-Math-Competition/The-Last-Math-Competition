import Std
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace TLMC2222

def Vertex (n x : Nat) : Prop := 0 < x ∧ x < n ∧ ∃ y, 0 < y ∧ y < n ∧ (x*y)%n = 0

def IsColoring (n : Nat) (C : List (List Nat)) : Prop :=
  (∀ x, Vertex n x → ∃ c, c ∈ C ∧ x ∈ c) ∧
  ∀ c, c ∈ C → ∀ x, x ∈ c → ∀ y, y ∈ c → x ≠ y → (x*y)%n ≠ 0

def IsClique (n : Nat) (K : List Nat) : Prop :=
  (∀ x, x ∈ K → Vertex n x) ∧ K.Pairwise (fun x y => x ≠ y ∧ (x*y)%n = 0)

-- This universal optimality statement says exactly that both the minimum
-- number of color classes and the maximum clique cardinality are k.
def EqualChromaticClique (n : Nat) : Prop := ∃ k,
  (∃ C, IsColoring n C ∧ C.length = k) ∧
  (∀ C, IsColoring n C → k ≤ C.length) ∧
  (∃ K, IsClique n K ∧ K.length = k) ∧
  (∀ K, IsClique n K → K.length ≤ k)

theorem nodup_length_le {α : Type} [BEq α] [LawfulBEq α]
    (L R : List α) (h : L.Nodup) (hs : ∀ x, x ∈ L → x ∈ R) : L.length ≤ R.length := by
  induction L generalizing R with
  | nil => simp
  | cons a L ih =>
    have hn := List.nodup_cons.mp h
    have ha := hs a (by simp)
    have ht : ∀ x, x ∈ L → x ∈ R.erase a := by
      intro x hx
      have hne : x ≠ a := by intro he; subst x; exact hn.1 hx
      exact (List.mem_erase_of_ne hne).mpr (hs x (by simp [hx]))
    have hh := ih (R.erase a) hn.2 ht
    rw [List.length_erase_of_mem ha] at hh
    simp only [List.length_cons]
    have hp : 0 < R.length := List.length_pos_of_mem ha
    omega

theorem clique_le_coloring {n : Nat} {K : List Nat} {C : List (List Nat)}
    (hk : IsClique n K) (hc : IsColoring n C) : K.length ≤ C.length := by
  classical
  let f (x : Nat) : List Nat := if hx : Vertex n x then Classical.choose (hc.1 x hx) else []
  have hf (x : Nat) (hx : x ∈ K) : f x ∈ C ∧ x ∈ f x := by
    have hv := hk.1 x hx
    simpa [f, hv] using Classical.choose_spec (hc.1 x hv)
  have hn : (K.map f).Nodup := by
    apply List.pairwise_map.mpr
    apply hk.2.imp_of_mem
    intro x y hx hy hxy he
    exact hc.2 (f x) (hf x hx).1 x (hf x hx).2 y (he ▸ (hf y hy).2) hxy.1 hxy.2
  have hh := nodup_length_le (K.map f) C hn (by
    intro c hc'
    obtain ⟨x,hx,rfl⟩ := List.mem_map.mp hc'
    exact (hf x hx).1)
  simpa using hh

theorem matching_certificates {n : Nat} {K : List Nat} {C : List (List Nat)}
    (hk : IsClique n K) (hc : IsColoring n C) (he : K.length = C.length) : EqualChromaticClique n := by
  refine ⟨K.length, ⟨C,hc,he.symm⟩, ?_, ⟨K,hk,rfl⟩, ?_⟩
  · intro D hd; exact clique_le_coloring hk hd
  · intro L hl; rw [he]; exact clique_le_coloring hl hc

-- The graph is the usual nonzero-zero-divisor graph, not a graph with
-- zero or units as extra vertices. This proves the gcd enumeration bridge.
theorem vertex_iff_gcd (hn : 0 < n) : Vertex n x ↔ 0 < x ∧ x < n ∧ 1 < Nat.gcd n x := by
  constructor
  · rintro ⟨hx,hxn,y,hy,hyn,hxy⟩
    refine ⟨hx,hxn,?_⟩
    have hp := Nat.gcd_pos_of_pos_left x hn
    by_cases hh : 1 < Nat.gcd n x
    · exact hh
    apply False.elim
    have hg : Nat.gcd n x = 1 := by omega
    have hd := (Nat.dvd_gcd_mul_iff_dvd_mul).mpr (Nat.dvd_of_mod_eq_zero hxy)
    rw [hg, Nat.one_mul] at hd
    have := Nat.le_of_dvd hy hd
    omega
  · rintro ⟨hx,hxn,hg⟩
    let d := Nat.gcd n x
    have hd : d ∣ n := Nat.gcd_dvd_left n x
    have dp : 0 < d := by dsimp [d]; omega
    have dl : d ≤ n := Nat.le_of_dvd hn hd
    refine ⟨hx,hxn,n/d,Nat.div_pos dl dp,Nat.div_lt_self hn hg,?_⟩
    apply Nat.mod_eq_zero_of_dvd
    apply (Nat.dvd_gcd_mul_iff_dvd_mul).mp
    change n ∣ d * (n / d)
    rw [Nat.mul_div_cancel' hd]
    exact Nat.dvd_refl n

-- Compact checker: remove the first member of a color class, then check
-- only the distinct gcd types of the remaining members. The gcd-product
-- equivalence below proves this compression loses no possible edge.
def independentCheck (n : Nat) (c : List Nat) : Bool := match c with
  | [] => true
  | a::xs =>
    xs.all (fun x => (a*x)%n != 0) &&
    let ds := (xs.map (Nat.gcd n)).eraseDups
    ds.all (fun d => ds.all (fun e => (d*e)%n != 0))

theorem independentCheck_sound {n : Nat} {c : List Nat} (h : independentCheck n c = true) :
    ∀ x, x ∈ c → ∀ y, y ∈ c → x ≠ y → (x*y)%n ≠ 0 := by
  cases c with
  | nil => simp
  | cons a xs =>
    simp only [independentCheck, Bool.and_eq_true, List.all_eq_true, bne_iff_ne] at h
    intro x hx y hy hne
    simp only [List.mem_cons] at hx hy
    rcases hx with rfl | hx
    · rcases hy with rfl | hy
      · exact False.elim (hne rfl)
      · exact h.1 y hy
    · rcases hy with rfl | hy
      · simpa [Nat.mul_comm] using h.1 x hx
      · intro hxy
        have hxg : Nat.gcd n x ∈ (xs.map (Nat.gcd n)).eraseDups := by
          simp only [List.mem_eraseDups, List.mem_map]; exact ⟨x,hx,rfl⟩
        have hyg : Nat.gcd n y ∈ (xs.map (Nat.gcd n)).eraseDups := by
          simp only [List.mem_eraseDups, List.mem_map]; exact ⟨y,hy,rfl⟩
        apply h.2 _ hxg _ hyg
        exact Nat.mod_eq_zero_of_dvd (Nat.dvd_gcd_mul_gcd_iff_dvd_mul.mpr (Nat.dvd_of_mod_eq_zero hxy))

-- Structurally recursive merge sort. At zero fuel concatenation is used;
-- membership preservation holds for all fuel, independently of sorting.
def mergeFuel : Nat → List Nat → List Nat → List Nat
  | 0, xs, ys => xs ++ ys
  | _+1, [], ys => ys
  | _+1, xs, [] => xs
  | k+1, a::xs, b::ys =>
      if a ≤ b then a :: mergeFuel k xs (b::ys)
      else b :: mergeFuel k (a::xs) ys

def sortFuel : Nat → List Nat → List Nat
  | 0, xs => xs
  | k+1, xs => if xs.length ≤ 1 then xs else
      mergeFuel xs.length (sortFuel k (xs.take (xs.length/2)))
        (sortFuel k (xs.drop (xs.length/2)))

def sortNat (xs : List Nat) : List Nat := sortFuel xs.length xs

theorem mem_mergeFuel : x ∈ mergeFuel k xs ys ↔ x ∈ xs ∨ x ∈ ys := by
  induction k generalizing xs ys with
  | zero => simp [mergeFuel]
  | succ k ih =>
    cases xs with
    | nil => simp [mergeFuel]
    | cons a xs =>
      cases ys with
      | nil => simp [mergeFuel]
      | cons b ys =>
        simp only [mergeFuel]
        split <;> simp [List.mem_cons, ih, or_assoc, or_left_comm]

theorem mem_sortFuel : x ∈ sortFuel k xs ↔ x ∈ xs := by
  induction k generalizing xs with
  | zero => rfl
  | succ k ih =>
    simp only [sortFuel]
    split
    · rfl
    · rw [mem_mergeFuel, ih, ih, ← List.mem_append, List.take_append_drop]

theorem mem_sortNat : x ∈ sortNat xs ↔ x ∈ xs := mem_sortFuel

def vertices (n : Nat) : List Nat := (List.range n).filter (fun x => 0 < x && 1 < Nat.gcd n x)
def check (n : Nat) (C : List (List Nat)) (K : List Nat) : Prop :=
  sortNat C.flatten = vertices n ∧
  C.all (independentCheck n) = true ∧
  (∀ x ∈ K, x ∈ vertices n) ∧
  K.Pairwise (fun x y => x ≠ y ∧ (x*y)%n = 0) ∧
  K.length = C.length
instance (n : Nat) (C : List (List Nat)) (K : List Nat) : Decidable (check n C K) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _ ∧ _))

theorem mem_vertices (hn : 0 < n) : x ∈ vertices n ↔ Vertex n x := by
  rw [vertex_iff_gcd hn]
  simp only [vertices, List.mem_filter, List.mem_range, Bool.and_eq_true, decide_eq_true_eq]
  omega

theorem check_sound (hn : 0 < n) {C : List (List Nat)} {K : List Nat} (h : check n C K) : EqualChromaticClique n := by
  apply matching_certificates (K := K) (C := C) _ _ h.2.2.2.2
  · exact ⟨fun x hx => (mem_vertices hn).mp (h.2.2.1 x hx),h.2.2.2.1⟩
  · constructor
    · intro x hx
      apply List.mem_flatten.mp
      apply mem_sortNat.mp
      rw [h.1]
      exact (mem_vertices hn).mpr hx
    · intro c hc
      exact independentCheck_sound ((List.all_eq_true.mp h.2.1) c hc)
end TLMC2222
