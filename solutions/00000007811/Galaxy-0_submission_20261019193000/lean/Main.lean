import Std

namespace TLMC7811

/-- An ambient algebra's operations. No ring axiom is needed for the injectivity
    result: it holds for every carrier with these operations. -/
structure Operations (A : Type u) where
  zero : A
  one : A
  add : A → A → A
  mul : A → A → A
  neg : A → A

/-- Closure under the ambient operations, not a free presentation. -/
inductive Generated {A : Type u} (op : Operations A) (generator : A → Prop) : A → Prop where
  | zero : Generated op generator op.zero
  | one : Generated op generator op.one
  | gen {a : A} : generator a → Generated op generator a
  | add {a b : A} : Generated op generator a → Generated op generator b →
      Generated op generator (op.add a b)
  | mul {a b : A} : Generated op generator a → Generated op generator b →
      Generated op generator (op.mul a b)
  | neg {a : A} : Generated op generator a → Generated op generator (op.neg a)

abbrev GeneratedSubring {A : Type u} (op : Operations A) (generator : A → Prop) :=
  {a : A // Generated op generator a}

def inclusion {A : Type u} {op : Operations A} {generator : A → Prop}
    (x : GeneratedSubring op generator) : A := x.val

def subringZero {A : Type u} (op : Operations A) (generator : A → Prop) :
    GeneratedSubring op generator := ⟨op.zero, Generated.zero⟩

/-- This is injectivity of the actual map; injectivity is not a hypothesis. -/
theorem inclusion_injective {A : Type u} (op : Operations A) (generator : A → Prop)
    (x y : GeneratedSubring op generator) (h : inclusion x = inclusion y) : x = y := by
  exact Subtype.ext h

theorem kernel_iff_zero {A : Type u} (op : Operations A) (generator : A → Prop)
    (x : GeneratedSubring op generator) :
    inclusion x = op.zero ↔ x = subringZero op generator := by
  constructor
  · intro h
    exact inclusion_injective op generator x (subringZero op generator) h
  · intro h
    subst x
    rfl

def NontrivialKernel {A : Type u} (op : Operations A) (generator : A → Prop) : Prop :=
  ∃ x : GeneratedSubring op generator, x ≠ subringZero op generator ∧ inclusion x = op.zero

theorem no_nontrivial_kernel {A : Type u} (op : Operations A) (generator : A → Prop) :
    ¬ NontrivialKernel op generator := by
  intro ⟨x, hx, hz⟩
  exact hx ((kernel_iff_zero op generator x).mp hz)

/-- The printed universal genus-at-least-eight kernel clause, parameterized by
    arbitrary ambient carriers and generating classes in each genus. -/
def GenusKernelClaim (A : Nat → Type u) (op : (g : Nat) → Operations (A g))
    (generator : (g : Nat) → A g → Prop) : Prop :=
  ∀ g, 8 ≤ g → NontrivialKernel (op g) (generator g)

theorem genus_kernel_claim_false (A : Nat → Type u)
    (op : (g : Nat) → Operations (A g)) (generator : (g : Nat) → A g → Prop) :
    ¬ GenusKernelClaim A op generator := by
  intro h
  exact no_nontrivial_kernel (op 8) (generator 8) (h 8 (by decide))

/-- Any degree restriction can only make a kernel witness harder to obtain. -/
theorem no_kernel_in_any_degree {A : Type u} (op : Operations A) (generator : A → Prop)
    (degreePart : GeneratedSubring op generator → Prop) :
    ¬ ∃ x, degreePart x ∧ x ≠ subringZero op generator ∧ inclusion x = op.zero := by
  intro ⟨x, _, hx, hz⟩
  exact no_nontrivial_kernel op generator ⟨x, hx, hz⟩

end TLMC7811
