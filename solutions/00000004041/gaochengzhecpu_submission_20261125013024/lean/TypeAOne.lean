import Std

namespace TypeAOne

/-- In the derived orbit by [2], a scalar component between the two simple
    representatives is indexed by an integer period satisfying this equation. -/
def orbitDegree (i j : Fin 2) (m : Int) : Prop :=
  (i.val : Int) = (j.val : Int) + 2*m

theorem orbit_degree_iff (i j : Fin 2) (m : Int) :
    orbitDegree i j m ↔ i = j ∧ m = 0 := by
  have hi := i.isLt
  have hj := j.isLt
  simp only [orbitDegree, Fin.ext_iff]
  omega

structure Object where
  even : Nat
  odd : Nat
  deriving DecidableEq

def s₀ : Object := ⟨1, 0⟩
def s₁ : Object := ⟨0, 1⟩

def shift (x : Object) : Object := ⟨x.odd, x.even⟩

/-- The two scalar Hom spaces on simples give block-diagonal matrices. -/
def homDimension (x y : Object) : Nat := x.even*y.even + x.odd*y.odd
def extDimension (x y : Object) : Nat := homDimension x (shift y)

def inAdd (t x : Object) : Prop :=
  (t.even = 0 → x.even = 0) ∧ (t.odd = 0 → x.odd = 0)

def basicTilting (t : Object) : Prop := t.even ≤ 1 ∧ t.odd ≤ 1 ∧
  ∀ x : Object, extDimension t x = 0 ↔ inAdd t x

theorem all_basic_tiltings (t : Object) : basicTilting t ↔ t = s₀ ∨ t = s₁ := by
  constructor
  · intro ht
    have hs : t.odd = 0 ↔ t.even ≠ 0 := by
      simpa [s₀, extDimension, homDimension, shift, inAdd] using ht.2.2 s₀
    have he := ht.1
    have ho := ht.2.1
    cases t with
    | mk e o =>
      simp only at hs he ho
      have h : (e = 1 ∧ o = 0) ∨ (e = 0 ∧ o = 1) := by omega
      rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · left; rfl
      · right; rfl
  · rintro (rfl | rfl)
    · simp [basicTilting, s₀, extDimension, homDimension, shift, inAdd]
    · simp [basicTilting, s₁, extDimension, homDimension, shift, inAdd]

/-- In rank one, a mutation exchanges the distinct basic complements of the
    zero object. The two vertices and their single undirected edge follow. -/
def mutates (t u : Object) : Prop := basicTilting t ∧ basicTilting u ∧ t ≠ u

theorem all_mutations (t u : Object) : mutates t u ↔
    (t = s₀ ∧ u = s₁) ∨ (t = s₁ ∧ u = s₀) := by
  have hn : s₀ ≠ s₁ := by decide
  constructor
  · rintro ⟨ht, hu, hn'⟩
    rcases (all_basic_tiltings t).mp ht with rfl | rfl <;>
      rcases (all_basic_tiltings u).mp hu with rfl | rfl <;> simp_all
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · exact ⟨(all_basic_tiltings _).mpr (Or.inl rfl),
        (all_basic_tiltings _).mpr (Or.inr rfl), hn⟩
    · exact ⟨(all_basic_tiltings _).mpr (Or.inr rfl),
        (all_basic_tiltings _).mpr (Or.inl rfl), Ne.symm hn⟩

theorem scalar_endomorphisms : homDimension s₀ s₀ = 1 := by decide

def leastDimension (occurs : Nat → Prop) (d : Nat) : Prop :=
  occurs d ∧ ∀ e, occurs e → d ≤ e

theorem repdim_zero (occurs : Nat → Prop) (witness : occurs 0) :
    leastDimension occurs 0 := ⟨witness, fun _ _ => Nat.zero_le _⟩

/-- `occurs` records the endomorphism global dimensions of generator-
    cogenerators. The semisimple witness contributes dimension zero. -/
theorem counterexample (occurs : Nat → Prop) (witness : occurs 0) :
    (∀ t, basicTilting t ↔ t = s₀ ∨ t = s₁) ∧
    (∀ t u, mutates t u ↔ (t = s₀ ∧ u = s₁) ∨ (t = s₁ ∧ u = s₀)) ∧
    homDimension s₀ s₀ = 1 ∧ leastDimension occurs 0 ∧
    ¬ (leastDimension occurs 2 ∨ leastDimension occurs 3) := by
  refine ⟨all_basic_tiltings, all_mutations, scalar_endomorphisms, repdim_zero occurs witness, ?_⟩
  rintro (h | h)
  · have impossible := h.2 0 witness
    omega
  · have impossible := h.2 0 witness
    omega

#print axioms orbit_degree_iff
#print axioms counterexample

end TypeAOne
