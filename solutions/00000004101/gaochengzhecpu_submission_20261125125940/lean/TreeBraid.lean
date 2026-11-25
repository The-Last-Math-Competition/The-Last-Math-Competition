import Std

namespace C4101

private instance decidableFinForall {n : Nat} {P : Fin n → Prop}
    [dec : (i : Fin n) → Decidable (P i)] : Decidable (∀ i, P i) := by
  induction n with
  | zero => exact isTrue (fun i => Fin.elim0 i)
  | succ n ih =>
    letI : Decidable (∀ i : Fin n, P i.succ) := ih
    exact decidable_of_iff _ Fin.forall_fin_succ.symm

abbrev Vertex := Fin 12

def edges : List (Vertex × Vertex) :=
  [(0, 1), (1, 2), (2, 3), (3, 4), (4, 5), (5, 6),
   (0, 7), (0, 8), (3, 9), (6, 10), (6, 11)]

def Adjacent (u v : Vertex) : Prop := (u, v) ∈ edges ∨ (v, u) ∈ edges

private instance (u v : Vertex) : Decidable (Adjacent u v) := by
  unfold Adjacent
  infer_instance

theorem no_loops : ∀ v : Vertex, ¬ Adjacent v v := by decide

def parent (v : Vertex) : Vertex :=
  (#[0, 0, 1, 2, 3, 4, 5, 0, 0, 3, 6, 6] : Array Vertex)[v.val]'v.isLt

theorem parent_properties : ∀ v : Vertex, v ≠ 0 →
    parent v < v ∧ Adjacent (parent v) v ∧
      ∀ u, u < v → Adjacent u v → u = parent v := by decide

inductive Walk : Vertex → Vertex → Prop where
  | stay (v : Vertex) : Walk v v
  | step {u v w : Vertex} : Adjacent u v → Walk v w → Walk u w

private theorem walk_append {u v w : Vertex} (a : Walk u v) (b : Walk v w) : Walk u w := by
  induction a with
  | stay => exact b
  | step edge _ ih => exact Walk.step edge (ih b)

private theorem walk_reverse {u v : Vertex} (path : Walk u v) : Walk v u := by
  induction path with
  | stay v => exact Walk.stay v
  | step edge _ ih => exact walk_append ih (Walk.step edge.symm (Walk.stay _))

private theorem walk_to_root (v : Vertex) : Walk v 0 := by
  have bounded : ∀ n, ∀ u : Vertex, u.val ≤ n → Walk u 0 := by
    intro n
    induction n with
    | zero =>
      intro u bound
      have equal : u = 0 := Fin.ext (by omega)
      rw [equal]
      exact Walk.stay 0
    | succ n ih =>
      intro u bound
      by_cases root : u = 0
      · rw [root]
        exact Walk.stay 0
      · have facts := parent_properties u root
        have smaller : (parent u).val < u.val := facts.1
        exact Walk.step facts.2.1.symm (ih (parent u) (by omega))
  exact bounded v.val v (Nat.le_refl _)

theorem connected (u v : Vertex) : Walk u v :=
  walk_append (walk_to_root u) (walk_reverse (walk_to_root v))

private theorem finite_maximum {n : Nat} (f : Fin (n + 1) → Nat) :
    ∃ i, ∀ j, f j ≤ f i := by
  induction n with
  | zero =>
    refine ⟨0, fun j => ?_⟩
    have equal : j = 0 := Fin.ext (by have := j.isLt; omega)
    rw [equal]
    exact Nat.le_refl _
  | succ n ih =>
    obtain ⟨i, maximum⟩ := ih (fun j => f j.succ)
    by_cases top : f 0 ≤ f i.succ
    · exact ⟨i.succ, Fin.cases top maximum⟩
    · exact ⟨0, Fin.cases (Nat.le_refl _) (fun j =>
        Nat.le_trans (maximum j) (Nat.le_of_lt (Nat.lt_of_not_ge top)))⟩

def nextIndex (n i : Nat) : Nat := if i + 1 < n then i + 1 else 0

def SimpleCycle (v : Fin n → Vertex) : Prop :=
  (∀ i j, v i = v j → i = j) ∧
    ∀ i j, j.val = nextIndex n i.val → Adjacent (v i) (v j)

private theorem lower_of_maximal {u v : Vertex} (bound : u.val ≤ v.val) (distinct : u ≠ v) :
    u < v := by
  have distinctValues : u.val ≠ v.val := fun h => distinct (Fin.ext h)
  change u.val < v.val
  omega

theorem acyclic (n : Nat) (long : 3 ≤ n) (v : Fin n → Vertex) : ¬ SimpleCycle v := by
  intro cyc
  cases n with
  | zero => omega
  | succ n =>
    obtain ⟨i, maximum⟩ := finite_maximum (fun j => (v j).val)
    let a := if i.val = 0 then n else i.val - 1
    let b := nextIndex (n + 1) i.val
    have bound := i.isLt
    have aValid : a < n + 1 := by dsimp [a]; split <;> omega
    have bValid : b < n + 1 := by dsimp [b, nextIndex]; split <;> omega
    let previous : Fin (n + 1) := ⟨a, aValid⟩
    let following : Fin (n + 1) := ⟨b, bValid⟩
    have backward : i.val = nextIndex (n + 1) previous.val := by
      change i.val = nextIndex (n + 1) a
      dsimp [a, nextIndex]
      split <;> split <;> omega
    have previous_ne : previous ≠ i := by
      intro equal
      have vals : a = i.val := congrArg Fin.val equal
      dsimp [a] at vals
      split at vals <;> omega
    have following_ne : following ≠ i := by
      intro equal
      have vals : b = i.val := congrArg Fin.val equal
      dsimp [b, nextIndex] at vals
      split at vals <;> omega
    have disjoint : previous ≠ following := by
      intro equal
      have vals : a = b := congrArg Fin.val equal
      dsimp [a, b, nextIndex] at vals
      split at vals <;> split at vals <;> omega
    have prevLower := lower_of_maximal (maximum previous) (fun h => previous_ne (cyc.1 _ _ h))
    have nextLower := lower_of_maximal (maximum following) (fun h => following_ne (cyc.1 _ _ h))
    have nonroot : v i ≠ 0 := by
      intro equal
      rw [equal] at prevLower
      have impossible : (v previous).val < 0 := prevLower
      omega
    have unique := (parent_properties (v i) nonroot).2.2
    have first := unique (v previous) prevLower (cyc.2 previous i backward)
    have second := unique (v following) nextLower (cyc.2 i following rfl).symm
    exact disjoint (cyc.1 _ _ (first.trans second.symm))

def degree (v : Vertex) : Nat := (List.finRange 12).countP (fun u => decide (Adjacent v u))

def essential (i : Fin 3) : Vertex :=
  (#[0, 3, 6] : Array Vertex)[i.val]'i.isLt

theorem essential_vertices : ∀ v : Vertex,
    3 ≤ degree v ↔ v = 0 ∨ v = 3 ∨ v = 6 := by decide

theorem essential_degree_three : ∀ i : Fin 3, degree (essential i) = 3 := by decide

def ClosedStar (v u : Vertex) : Prop := u = v ∨ Adjacent v u

private instance (v u : Vertex) : Decidable (ClosedStar v u) := by
  unfold ClosedStar
  infer_instance

theorem essential_stars_disjoint : ∀ i j : Fin 3, i ≠ j →
    ∀ u : Vertex, ClosedStar (essential i) u → ¬ ClosedStar (essential j) u := by decide

/-- Subdivide the two edges joining distinct closed stars. -/
def refinedEdges : List (Fin 14 × Fin 14) :=
  [(0, 1), (1, 12), (12, 2), (2, 3), (3, 4), (4, 13), (13, 5), (5, 6),
   (0, 7), (0, 8), (3, 9), (6, 10), (6, 11)]

def refinedDegree (v : Fin 14) : Nat := (List.finRange 14).countP (fun u =>
  decide ((u, v) ∈ refinedEdges ∨ (v, u) ∈ refinedEdges))

def basepointVertices : List (Fin 14) := [1, 2, 4, 5, 12, 13]

theorem bivalent_basepoint : basepointVertices.Nodup ∧ basepointVertices.length = 6 ∧
    ∀ v : Fin 14, v ∈ basepointVertices → refinedDegree v = 2 := by decide

def blockOf (p : Fin 6) : Fin 3 := ⟨p.val / 2, by have := p.isLt; omega⟩

def particlePair (i : Fin 3) : List (Fin 6) :=
  (List.finRange 6).filter (fun p => decide (blockOf p = i))

theorem binary_partition :
    (∀ i : Fin 3, (particlePair i).length = 2) ∧
    (∀ p : Fin 6, p ∈ particlePair (blockOf p)) ∧
    (∀ i j : Fin 3, ∀ p : Fin 6, p ∈ particlePair i → p ∈ particlePair j → i = j) := by decide

abbrev IntegerTriple := Int × Int × Int

def addTriple (a b : IntegerTriple) : IntegerTriple :=
  (a.1 + b.1, a.2.1 + b.2.1, a.2.2 + b.2.2)

def OneToOne {A B : Type} (f : A → B) : Prop := ∀ a b, f a = f b → a = b

/-- Once the two maps are group homomorphisms, an injective toric detection
composite and the covering injection imply the claimed dimension bound. -/
theorem braid_dimension_lower_bound {Pure Braid Detection : Type}
    (mulPure : Pure → Pure → Pure) (mulBraid : Braid → Braid → Braid)
    (toric : IntegerTriple → Pure) (detect : Pure → Detection) (cover : Pure → Braid)
    (toricHom : ∀ a b, toric (addTriple a b) = mulPure (toric a) (toric b))
    (coverHom : ∀ a b, cover (mulPure a b) = mulBraid (cover a) (cover b))
    (detected : OneToOne (detect ∘ toric)) (covered : OneToOne cover)
    (cdBraid : Nat)
    (monotone : ∀ f : IntegerTriple → Braid,
      (∀ a b, f (addTriple a b) = mulBraid (f a) (f b)) → OneToOne f → 3 ≤ cdBraid) :
    ¬ cdBraid ≤ 2 := by
  have lower := monotone (cover ∘ toric)
    (fun a b => by exact (congrArg cover (toricHom a b)).trans (coverHom (toric a) (toric b)))
    (fun a b equal => detected a b (congrArg detect (covered (toric a) (toric b) equal)))
  omega

#print axioms connected
#print axioms acyclic
#print axioms essential_stars_disjoint
#print axioms bivalent_basepoint
#print axioms binary_partition
#print axioms braid_dimension_lower_bound

end C4101
