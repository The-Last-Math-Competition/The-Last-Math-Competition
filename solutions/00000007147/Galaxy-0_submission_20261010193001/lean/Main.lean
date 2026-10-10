import Std

namespace Associahedron7147

inductive Tree where
  | leaf : Tree
  | node : Tree → Tree → Tree
  deriving DecidableEq, Repr

def Tree.nodes : Tree → Nat
  | .leaf => 0
  | .node l r => l.nodes + r.nodes + 1

def Tree.leaves : Tree → Nat
  | .leaf => 1
  | .node l r => l.leaves + r.leaves

theorem leaves_eq_nodes_add_one (t : Tree) : t.leaves = t.nodes + 1 := by
  induction t with
  | leaf => rfl
  | node l r ihl ihr => simp only [Tree.leaves, Tree.nodes, ihl, ihr]; omega

theorem four_leaves_iff (t : Tree) : t.leaves = 4 ↔ t.nodes = 3 := by
  have h := leaves_eq_nodes_add_one t
  omega

def trees : (n : Nat) → List Tree
  | 0 => [.leaf]
  | n + 1 => (List.finRange (n+1)).flatMap fun i =>
      (trees i.val).flatMap fun l => (trees (n-i.val)).map fun r => .node l r
termination_by n => n
decreasing_by all_goals omega

 theorem mem_trees (n : Nat) (t : Tree) : t ∈ trees n ↔ t.nodes = n := by
  induction n using Nat.strongRecOn generalizing t with
  | ind n ih =>
    cases n with
    | zero => cases t <;> simp [trees, Tree.nodes]
    | succ n =>
      cases t with
      | leaf => simp [trees, Tree.nodes]
      | node l r =>
        simp only [trees, List.mem_flatMap, List.mem_finRange, List.mem_map, Tree.node.injEq]
        constructor
        · rintro ⟨i, hi, l', hl', r', hr', h1, h2⟩
          subst l'; subst r'
          have hl := (ih i.val i.isLt l).mp hl'
          have hr := (ih (n-i) (by omega) r).mp hr'
          simp [Tree.nodes, hl, hr]; omega
        · intro ht
          have hsize : l.nodes + r.nodes = n := by simpa [Tree.nodes] using ht
          refine ⟨⟨l.nodes, by omega⟩, trivial, l, (ih l.nodes (by omega) l).mpr rfl,
            r, (ih (n-l.nodes) (by omega) r).mpr (by omega), rfl, rfl⟩

 theorem three_tree_count : (trees 3).length = 5 := by simp [trees, List.finRange_succ, List.finRange_zero]
 theorem three_tree_nodup : (trees 3).Nodup := by simp [trees, List.finRange_succ, List.finRange_zero]

-- Vertices 0,...,4 occur in cyclic order on the convex pentagon.
abbrev Vertex := Fin 5
abbrev Diagonal := Vertex × Vertex

def IsDiagonal (d : Diagonal) : Prop :=
  d.1 < d.2 ∧ d.2.val ≠ d.1.val + 1 ∧ ¬(d.1.val = 0 ∧ d.2.val = 4)
instance (d : Diagonal) : Decidable (IsDiagonal d) := inferInstanceAs (Decidable (_ ∧ _ ∧ _))

def diagonal : Fin 5 → Diagonal
  | 0 => (0,2)
  | 1 => (0,3)
  | 2 => (1,3)
  | 3 => (1,4)
  | 4 => (2,4)

theorem diagonal_complete : ∀ d : Diagonal, IsDiagonal d ↔ ∃ i, diagonal i = d := by
  have h : ∀ a b : Vertex, IsDiagonal (a,b) ↔ ∃ i, diagonal i = (a,b) := by decide
  intro ⟨a,b⟩; exact h a b
theorem diagonal_injective : ∀ i j, diagonal i = diagonal j → i = j := by decide

def Crosses (a b : Diagonal) : Prop :=
  (a.1 < b.1 ∧ b.1 < a.2 ∧ a.2 < b.2) ∨
  (b.1 < a.1 ∧ a.1 < b.2 ∧ b.2 < a.2)
instance (a b : Diagonal) : Decidable (Crosses a b) := inferInstanceAs (Decidable (_ ∨ _))

abbrev Mask := Fin 32

def selected (m : Mask) (i : Fin 5) : Bool := m.val.testBit i.val

def Compatible (m : Mask) : Prop :=
  ∀ i j : Fin 5, selected m i = true → selected m j = true → ¬Crosses (diagonal i) (diagonal j)
instance (m : Mask) : Decidable (Compatible m) := inferInstanceAs (Decidable (∀ _ _ : Fin 5, _))

-- Each mask denotes an actual subset, not a multiset or ordered sequence.
theorem mask_extensional : ∀ a b : Mask, (∀ i, selected a i = selected b i) → a = b := by decide

theorem mask_surjective (s : Fin 5 → Bool) : ∃ m : Mask, ∀ i, selected m i = s i := by
  have h : ∀ a b c d e : Bool, ∃ m : Mask,
      selected m 0 = a ∧ selected m 1 = b ∧ selected m 2 = c ∧
      selected m 3 = d ∧ selected m 4 = e := by decide
  obtain ⟨m, h0, h1, h2, h3, h4⟩ := h (s 0) (s 1) (s 2) (s 3) (s 4)
  refine ⟨m, ?_⟩
  intro i
  have hi : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 := by omega
  rcases hi with rfl | rfl | rfl | rfl | rfl <;> assumption

def masks : List Mask := (List.finRange 32).filter fun m => decide (Compatible m)
theorem mem_masks (m : Mask) : m ∈ masks ↔ Compatible m := by simp [masks]

def diagonalCount (m : Mask) : Nat := ((List.finRange 5).filter fun i => selected m i).length

theorem face_counts :
  (masks.filter fun m => diagonalCount m == 0).length = 1 ∧
  (masks.filter fun m => diagonalCount m == 1).length = 5 ∧
  (masks.filter fun m => diagonalCount m == 2).length = 5 ∧
  (∀ m ∈ masks, diagonalCount m ≤ 2) := by decide

theorem nonempty_face_count : masks.length = 11 := by decide

abbrev Face := {m : Mask // Compatible m}

def faceLe (a b : Face) : Prop := ∀ i, selected b.val i = true → selected a.val i = true

theorem faceLe_refl (a : Face) : faceLe a a := by intro i hi; exact hi
theorem faceLe_trans (a b c : Face) : faceLe a b → faceLe b c → faceLe a c := by
  intro hab hbc i hi; exact hab i (hbc i hi)
theorem faceLe_antisymm (a b : Face) : faceLe a b → faceLe b a → a = b := by
  intro hab hba
  apply Subtype.ext
  apply mask_extensional
  intro i
  have h1 := hab i
  have h2 := hba i
  cases ha : selected a.val i <;> cases hb : selected b.val i <;> simp_all

def wholeFace : Face := ⟨0, by decide⟩
theorem wholeFace_top (a : Face) : faceLe a wholeFace := by
  intro i hi
  have hf : ∀ i : Fin 5, selected 0 i = false := by decide
  simp [wholeFace, hf] at hi

-- The empty polytope face is added separately: it is NOT mask zero.
abbrev FullFace := Option Face

def fullFaceLe : FullFace → FullFace → Prop
  | none, _ => True
  | some _, none => False
  | some a, some b => faceLe a b

def allFaces : List Face := masks.attach.map fun m => ⟨m.val, (mem_masks m.val).mp m.property⟩
theorem allFaces_count : allFaces.length = 11 := by simp [allFaces, nonempty_face_count]
theorem allFaces_nodup : allFaces.Nodup := by decide

theorem mem_allFaces (a : Face) : a ∈ allFaces := by
  apply List.mem_map.mpr
  refine ⟨⟨a.val, (mem_masks a.val).mpr a.property⟩, ?_, ?_⟩
  · exact List.mem_attach _ _
  · rfl

def fullFaces : List FullFace := none :: allFaces.map some
theorem full_face_count : fullFaces.length = 12 := by simp [fullFaces, allFaces_count]

theorem mem_fullFaces (a : FullFace) : a ∈ fullFaces := by
  cases a with
  | none => simp [fullFaces]
  | some a => simp [fullFaces, mem_allFaces a]

theorem fullFaces_nodup : fullFaces.Nodup := by decide

-- Finite cardinal comparison, proved here rather than trusting an enumeration of maps.
theorem nodup_length_le {α : Type} [DecidableEq α] (a b : List α)
    (ha : a.Nodup) (hsub : ∀ x ∈ a, x ∈ b) : a.length ≤ b.length := by
  induction a generalizing b with
  | nil => simp
  | cons x xs ih =>
    have hx : x ∈ b := hsub x (by simp)
    have hn := List.nodup_cons.mp ha
    have hs : ∀ y ∈ xs, y ∈ b.erase x := by
      intro y hy
      apply (List.mem_erase_of_ne (by intro he; subst y; exact hn.1 hy)).mpr
      exact hsub y (by simp [hy])
    have h := ih (b.erase x) hn.2 hs
    have he := List.length_erase_of_mem hx
    have hb : 0 < b.length := List.length_pos_of_mem hx
    simp only [List.length_cons]
    omega

theorem nodup_map_of_injective {α β : Type} (f : α → β) (hf : ∀ a b, f a = f b → a = b)
    (l : List α) (hl : l.Nodup) : (l.map f).Nodup := by
  apply List.pairwise_map.mpr
  exact List.Pairwise.imp (fun {a b} hab he => hab (hf a b he)) hl

abbrev BinaryFour := {t : Tree // t.nodes = 3}

theorem no_injection_faces_to_binary :
    ¬ ∃ f : Face → BinaryFour, ∀ a b, f a = f b → a = b := by
  rintro ⟨f, hf⟩
  let g : Face → Tree := fun a => (f a).val
  have hg : ∀ a b, g a = g b → a = b := by
    intro a b h; exact hf a b (Subtype.ext h)
  have hnd := nodup_map_of_injective g hg allFaces allFaces_nodup
  have hsub : ∀ t ∈ allFaces.map g, t ∈ trees 3 := by
    intro t ht
    obtain ⟨a, _, rfl⟩ := List.mem_map.mp ht
    exact (mem_trees 3 (g a)).mpr (f a).property
  have hlen := nodup_length_le (allFaces.map g) (trees 3) hnd hsub
  simp only [List.length_map, allFaces_count, three_tree_count] at hlen
  omega

-- Any face-poset isomorphism, in particular, would give this impossible injection.
theorem no_face_tamari_bijection :
  ¬ ∃ f : Face → BinaryFour, ∃ g : BinaryFour → Face, ∀ a, g (f a) = a := by
  rintro ⟨f, g, hgf⟩
  apply no_injection_faces_to_binary
  refine ⟨f, ?_⟩
  intro a b he
  have h := congrArg g he
  simpa [hgf] using h

theorem no_full_face_tamari_bijection :
  ¬ ∃ f : FullFace → BinaryFour, ∃ g : BinaryFour → FullFace, ∀ a, g (f a) = a := by
  rintro ⟨f, g, hgf⟩
  apply no_injection_faces_to_binary
  refine ⟨fun a => f (some a), ?_⟩
  intro a b he
  have h := congrArg g he
  simp only [hgf] at h
  exact Option.some.inj h

theorem conjectured_count_false : masks.length ≠ (trees 3).length ∧
    fullFaces.length ≠ (trees 3).length := by
  rw [nonempty_face_count, full_face_count, three_tree_count]
  decide

#print axioms mask_surjective
#print axioms no_full_face_tamari_bijection
#print axioms conjectured_count_false
#print axioms mem_trees
#print axioms diagonal_complete
#print axioms face_counts
#print axioms faceLe_antisymm
#print axioms no_injection_faces_to_binary
#print axioms no_face_tamari_bijection

end Associahedron7147
