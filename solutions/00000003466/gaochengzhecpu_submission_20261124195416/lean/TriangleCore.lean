import Std

namespace C3466

structure SimpleGraph (V : Type) where
  adj : V → V → Prop
  symm : ∀ {x y}, adj x y → adj y x
  loopless : ∀ x, ¬ adj x x

def IsCycle {V : Type} (G : SimpleGraph V) {n : Nat} (v : Fin n → V) : Prop :=
  (∀ i j, v i = v j → i = j) ∧
    ∀ i j, j.val = (i.val + 1) % n → G.adj (v i) (v j)

def HasChord {V : Type} (G : SimpleGraph V) {n : Nat} (v : Fin n → V) : Prop :=
  ∃ i j, i ≠ j ∧ j.val ≠ (i.val + 1) % n ∧ i.val ≠ (j.val + 1) % n ∧
    G.adj (v i) (v j)

def Chordal {V : Type} (G : SimpleGraph V) : Prop :=
  ∀ n, 4 ≤ n → ∀ v : Fin n → V, IsCycle G v → HasChord G v

def Triangle {V : Type} (G : SimpleGraph V) (a b c : V) : Prop :=
  G.adj a b ∧ G.adj a c ∧ G.adj b c

def InTriangle {V : Type} (a b c x : V) : Prop := x = a ∨ x = b ∨ x = c

/-- The quotient is onto and merges exactly the three specified vertices. -/
def TriangleQuotient {V W : Type} (q : V → W) (a b c : V) : Prop :=
  (∀ y, ∃ x, q x = y) ∧
    ∀ x y, q x = q y ↔ x = y ∨ (InTriangle a b c x ∧ InTriangle a b c y)

/-- Simple-graph contraction keeps edges between distinct quotient classes. -/
def contract {V W : Type} (G : SimpleGraph V) (q : V → W) : SimpleGraph W where
  adj x y := x ≠ y ∧ ∃ u v, q u = x ∧ q v = y ∧ G.adj u v
  symm := by
    rintro x y ⟨hne, u, v, hu, hv, hadj⟩
    exact ⟨Ne.symm hne, v, u, hv, hu, G.symm hadj⟩
  loopless := fun x h => h.1 rfl

def ProperColoring {V : Type} (G : SimpleGraph V) {k : Nat} (color : V → Fin k) : Prop :=
  ∀ {x y}, G.adj x y → color x ≠ color y

def Colorable {V : Type} (G : SimpleGraph V) (k : Nat) : Prop :=
  ∃ color : V → Fin k, ProperColoring G color

def ChromaticNumber {V : Type} (G : SimpleGraph V) (k : Nat) : Prop :=
  Colorable G k ∧ ∀ l, l < k → ¬ Colorable G l

def PreservesChromaticNumber {V W : Type} (G : SimpleGraph V) (H : SimpleGraph W) : Prop :=
  ∀ k, ChromaticNumber G k ↔ ChromaticNumber H k

def LosesAtMostOne {V W : Type} (G : SimpleGraph V) (H : SimpleGraph W) : Prop :=
  ∀ k l, ChromaticNumber G k → ChromaticNumber H l → k ≤ l + 1

def completeGraph (V : Type) : SimpleGraph V where
  adj x y := x ≠ y
  symm := Ne.symm
  loopless := fun _ h => h rfl

theorem completeGraph_chordal (V : Type) : Chordal (completeGraph V) := by
  intro n hn v hcycle
  let i : Fin n := ⟨0, by omega⟩
  let j : Fin n := ⟨2, by omega⟩
  have hne : i ≠ j := fun h => by
    have hval : i.val = j.val := congrArg Fin.val h
    change 0 = 2 at hval
    omega
  refine ⟨i, j, hne, ?_, ?_, fun h => hne (hcycle.1 i j h)⟩
  · change 2 ≠ 1 % n
    rw [Nat.mod_eq_of_lt (by omega : 1 < n)]
    decide
  · change 0 ≠ 3 % n
    rw [Nat.mod_eq_of_lt (by omega : 3 < n)]
    decide

def K3 := completeGraph (Fin 3)

def collapseTriangle (_ : Fin 3) : Fin 1 := 0

theorem K3_triangle : Triangle K3 0 1 2 := by
  change (0 : Fin 3) ≠ 1 ∧ (0 : Fin 3) ≠ 2 ∧ (1 : Fin 3) ≠ 2
  decide

private theorem K3_allVerticesInTriangle (x : Fin 3) : InTriangle 0 1 2 x := by
  have hx := x.isLt
  have hval : x.val = 0 ∨ x.val = 1 ∨ x.val = 2 := by omega
  rcases hval with h | h | h
  · exact Or.inl (Fin.ext h)
  · exact Or.inr (Or.inl (Fin.ext h))
  · exact Or.inr (Or.inr (Fin.ext h))

theorem collapseTriangle_quotient : TriangleQuotient collapseTriangle 0 1 2 := by
  constructor
  · intro y
    exact ⟨0, Subsingleton.elim _ _⟩
  · intro x y
    exact ⟨fun _ => Or.inr ⟨K3_allVerticesInTriangle x, K3_allVerticesInTriangle y⟩,
      fun _ => rfl⟩

theorem K3_chromaticNumber : ChromaticNumber K3 3 := by
  constructor
  · exact ⟨id, fun h => h⟩
  · intro k hk hcolor
    obtain ⟨c, proper⟩ := hcolor
    have h01 : (c 0).val ≠ (c 1).val := fun h => proper K3_triangle.1 (Fin.ext h)
    have h02 : (c 0).val ≠ (c 2).val := fun h => proper K3_triangle.2.1 (Fin.ext h)
    have h12 : (c 1).val ≠ (c 2).val := fun h => proper K3_triangle.2.2 (Fin.ext h)
    have h0 := (c 0).isLt
    have h1 := (c 1).isLt
    have h2 := (c 2).isLt
    omega

theorem contracted_K3_chromaticNumber : ChromaticNumber (contract K3 collapseTriangle) 1 := by
  constructor
  · exact ⟨fun _ => 0, fun h => False.elim (h.1 (Subsingleton.elim _ _))⟩
  · intro k hk ⟨c, _⟩
    have hc := (c 0).isLt
    omega

theorem counterexample :
    Chordal K3 ∧ Triangle K3 0 1 2 ∧ TriangleQuotient collapseTriangle 0 1 2 ∧
      ¬ PreservesChromaticNumber K3 (contract K3 collapseTriangle) ∧
      ¬ LosesAtMostOne K3 (contract K3 collapseTriangle) := by
  refine ⟨completeGraph_chordal _, K3_triangle, collapseTriangle_quotient, ?_, ?_⟩
  · intro preserves
    exact K3_chromaticNumber.2 1 (by decide) ((preserves 1).mpr contracted_K3_chromaticNumber).1
  · intro losesAtMostOne
    have loss := losesAtMostOne 3 1 K3_chromaticNumber contracted_K3_chromaticNumber
    omega

#print axioms counterexample

end C3466
