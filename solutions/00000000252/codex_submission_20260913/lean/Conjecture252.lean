import Std

/- Finite undirected simple graphs with enumerated vertices and edges.
   Each edge is represented once by its two endpoints. -/
namespace Conjecture252

structure Graph (n m : Nat) where
  src : Fin m → Fin n
  dst : Fin m → Fin n
  loopFree : ∀ e, src e ≠ dst e
  simple : ∀ e f, ((src e = src f ∧ dst e = dst f) ∨
    (src e = dst f ∧ dst e = src f)) → e = f

def Adj {n m : Nat} (G : Graph n m) (u v : Fin n) : Prop :=
  ∃ e, (G.src e = u ∧ G.dst e = v) ∨ (G.src e = v ∧ G.dst e = u)

inductive Reach {n m : Nat} (G : Graph n m) : Fin n → Fin n → Prop where
  | refl (u) : Reach G u u
  | step {u v w} : Adj G u v → Reach G v w → Reach G u w

def Connected {n m : Nat} (G : Graph n m) : Prop := ∀ u v, Reach G u v
def NoIsolated {n m : Nat} (G : Graph n m) : Prop := ∀ u, ∃ v, Adj G u v

def VertexSum {n m : Nat} (G : Graph n m) (label : Fin m → Nat)
    (v : Fin n) : Nat :=
  (List.ofFn (fun e : Fin m =>
    if G.src e = v ∨ G.dst e = v then label e else 0)).sum

def Antimagic {n m : Nat} (G : Graph n m) : Prop :=
  ∃ label : Fin m → Nat,
    (∀ e, 1 ≤ label e ∧ label e ≤ m) ∧
    (∀ e f, label e = label f → e = f) ∧
    (∀ u v, VertexSum G label u = VertexSum G label v → u = v)

def conjecture : Prop := ∀ n m (G : Graph n m),
  Connected G → NoIsolated G → Antimagic G

def K2 : Graph 2 1 where
  src := fun _ => 0
  dst := fun _ => 1
  loopFree := by decide
  simple := by decide

theorem k2_connected : Connected K2 := by
  intro u v
  have hu : u = 0 ∨ u = 1 := by omega
  have hv : v = 0 ∨ v = 1 := by omega
  rcases hu with rfl | rfl <;> rcases hv with rfl | rfl
  · exact Reach.refl 0
  · exact Reach.step ⟨0, Or.inl ⟨rfl, rfl⟩⟩ (Reach.refl 1)
  · exact Reach.step ⟨0, Or.inr ⟨rfl, rfl⟩⟩ (Reach.refl 0)
  · exact Reach.refl 1

theorem k2_no_isolated : NoIsolated K2 := by
  intro u
  have hu : u = 0 ∨ u = 1 := by omega
  rcases hu with rfl | rfl
  · exact ⟨1, 0, Or.inl ⟨rfl, rfl⟩⟩
  · exact ⟨0, 0, Or.inr ⟨rfl, rfl⟩⟩

theorem k2_equal_sums (label : Fin 1 → Nat) :
    VertexSum K2 label 0 = VertexSum K2 label 1 := by
  rfl

theorem k2_not_antimagic : ¬ Antimagic K2 := by
  intro ⟨label, _, _, hinj⟩
  have h : (0 : Fin 2) = 1 := hinj 0 1 (k2_equal_sums label)
  have hne : (0 : Fin 2) ≠ 1 := by decide
  exact hne h

theorem conjecture_false : ¬ conjecture := by
  intro h
  exact k2_not_antimagic (h 2 1 K2 k2_connected k2_no_isolated)

#print axioms conjecture_false
end Conjecture252
