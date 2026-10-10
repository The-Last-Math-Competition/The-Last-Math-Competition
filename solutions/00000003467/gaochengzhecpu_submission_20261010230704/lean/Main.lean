import Mathlib.Data.ZMod.Basic
import Mathlib.Combinatorics.SimpleGraph.Coloring
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Path
import Mathlib.Algebra.Group.Subgroup.Lattice
import Mathlib.Tactic.NormNum

set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace Conjecture3467

open SimpleGraph

abbrev V := ZMod 12
abbrev K (n : ℕ) : SimpleGraph (Fin n) := ⊤

def S₁ : Finset V := {1, 11, 3, 9}
def S₂ : Finset V := {1, 11, 2, 10}

def cayley (S : Finset V) (hs : ∀ x ∈ S, -x ∈ S) (h0 : (0 : V) ∉ S) :
    SimpleGraph V where
  Adj x y := y - x ∈ S
  symm := by
    intro x y h
    simpa only [neg_sub] using hs (y - x) h
  loopless := by
    intro x
    simpa only [sub_self] using h0

def A : SimpleGraph V := cayley S₁ (by decide +kernel) (by decide)
def B : SimpleGraph V := cayley S₂ (by decide +kernel) (by decide)

instance : DecidableRel A.Adj := fun _ _ => inferInstanceAs (Decidable (_ ∈ S₁))
instance : DecidableRel B.Adj := fun _ _ => inferInstanceAs (Decidable (_ ∈ S₂))

theorem same_generator_count : S₁.card = 4 ∧ S₂.card = 4 := by decide +kernel

theorem generated_by_one (S : Finset V) (h1 : (1 : V) ∈ S) :
    AddSubgroup.closure (S : Set V) = ⊤ := by
  apply top_unique
  intro x _
  have h := (AddSubgroup.closure (S : Set V)).nsmul_mem
    (AddSubgroup.subset_closure h1) x.val
  simpa only [nsmul_eq_mul, ZMod.natCast_zmod_val, mul_one] using h

theorem both_sets_generate :
    AddSubgroup.closure (S₁ : Set V) = ⊤ ∧
    AddSubgroup.closure (S₂ : Set V) = ⊤ :=
  ⟨generated_by_one S₁ (by decide), generated_by_one S₂ (by decide)⟩

theorem connected_of_unit_steps (H : SimpleGraph V) (hstep : ∀ x : V, H.Adj x (x + 1)) :
    H.Connected := by
  have hr : ∀ n : ℕ, H.Reachable 0 (n : V) := by
    intro n
    induction n with
    | zero => exact Reachable.rfl
    | succ n ih =>
      simpa only [Nat.cast_add, Nat.cast_one] using ih.trans (hstep (n : V)).reachable
  apply (connected_iff_exists_forall_reachable H).mpr
  refine ⟨0, fun x => ?_⟩
  simpa only [ZMod.natCast_zmod_val] using hr x.val

theorem both_connected : A.Connected ∧ B.Connected :=
  ⟨connected_of_unit_steps A (by decide +kernel),
   connected_of_unit_steps B (by decide +kernel)⟩

def colorTwo (x : V) : Fin 2 := ⟨x.val % 2, Nat.mod_lt _ (by decide)⟩
def colorThree (x : V) : Fin 3 := ⟨x.val % 3, Nat.mod_lt _ (by decide)⟩

def retractTwo : A →g K 2 where
  toFun := colorTwo
  map_rel' := by
    have h : ∀ x y : V, A.Adj x y → colorTwo x ≠ colorTwo y := by decide +kernel
    exact fun {x y} hxy => h x y hxy

def retractThree : B →g K 3 where
  toFun := colorThree
  map_rel' := by
    have h : ∀ x y : V, B.Adj x y → colorThree x ≠ colorThree y := by decide +kernel
    exact fun {x y} hxy => h x y hxy

def includeTwo : K 2 →g A where
  toFun i := (i.val : V)
  map_rel' := by
    have h : ∀ i j : Fin 2, i ≠ j → A.Adj (i.val : V) (j.val : V) := by decide +kernel
    exact fun {i j} hij => h i j hij

def includeThree : K 3 →g B where
  toFun i := (i.val : V)
  map_rel' := by
    have h : ∀ i j : Fin 3, i ≠ j → B.Adj (i.val : V) (j.val : V) := by decide +kernel
    exact fun {i j} hij => h i j hij

theorem left_inverse_two : Function.LeftInverse retractTwo includeTwo := by decide +kernel
theorem left_inverse_three : Function.LeftInverse retractThree includeThree := by decide +kernel

/-- For finite graphs, this is the standard endomorphism characterization of a core. -/
def IsCore {W : Type} (H : SimpleGraph W) : Prop :=
  ∀ f : H →g H, Function.Injective f

/-- A core of a graph is a retract which is itself a core. -/
def IsCoreOf {W X : Type} (H : SimpleGraph W) (G : SimpleGraph X) : Prop :=
  IsCore H ∧ ∃ i : H →g G, ∃ r : G →g H, Function.LeftInverse r i

theorem retraction_reflects_adjacency {W X : Type}
    {H : SimpleGraph W} {G : SimpleGraph X} (i : H →g G) (r : G →g H)
    (hr : Function.LeftInverse r i) (u v : W) : G.Adj (i u) (i v) ↔ H.Adj u v := by
  constructor
  · intro h
    simpa only [hr u, hr v] using r.map_adj h
  · exact fun h => i.map_adj h

theorem complete_is_core (n : ℕ) : IsCore (K n) :=
  fun f => f.injective_of_top_hom

theorem cores : IsCoreOf (K 2) A ∧ IsCoreOf (K 3) B :=
  ⟨⟨complete_is_core 2, includeTwo, retractTwo, left_inverse_two⟩,
   ⟨complete_is_core 3, includeThree, retractThree, left_inverse_three⟩⟩

/-- The retraction definition implies the usual minimum-vertex characterization. -/
theorem core_minimal {W X Y : Type} [Fintype W] [Fintype Y]
    {H : SimpleGraph W} {G : SimpleGraph X} (hc : IsCoreOf H G)
    (J : SimpleGraph Y) (f : G →g J) (j : J →g G) :
    Fintype.card W ≤ Fintype.card Y := by
  obtain ⟨hcore, i, r, _⟩ := hc
  have hinj := hcore (r.comp (j.comp (f.comp i)))
  apply Fintype.card_le_of_injective (f.comp i)
  intro x y hxy
  apply hinj
  exact congrArg (fun z => r (j z)) hxy

/-- Every finite core in these examples is isomorphic to the displayed complete graph. -/
theorem complete_core_unique {W X : Type} [Finite W] {n : ℕ}
    {H : SimpleGraph W} {G : SimpleGraph X}
    (hn : IsCoreOf (K n) G) (hH : IsCoreOf H G) : Nonempty (K n ≃g H) := by
  obtain ⟨_, iK, rK, _⟩ := hn
  obtain ⟨hcore, iH, rH, _⟩ := hH
  let g : K n →g H := rH.comp iK
  let f : H →g K n := rK.comp iH
  have hi : Function.Injective g := g.injective_of_top_hom
  have hs0 : Function.Surjective (g.comp f) :=
    Finite.surjective_of_injective (hcore (g.comp f))
  have hs : Function.Surjective g := by
    intro y
    obtain ⟨x, hx⟩ := hs0 y
    exact ⟨f x, hx⟩
  refine ⟨{ toEquiv := Equiv.ofBijective g ⟨hi, hs⟩, map_rel_iff' := ?_ }⟩
  intro u v
  constructor
  · intro huv hsame
    exact (H.ne_of_adj huv) (congrArg g hsame)
  · exact fun h => g.map_adj h

theorem complete_core_edge_count {W X : Type} [Fintype W] [DecidableEq W] {n : ℕ}
    {H : SimpleGraph W} [DecidableRel H.Adj] {G : SimpleGraph X}
    (hn : IsCoreOf (K n) G) (hH : IsCoreOf H G) :
    H.edgeFinset.card = n.choose 2 := by
  obtain ⟨e⟩ := complete_core_unique hn hH
  rw [H.edgeFinset_card, ← Fintype.card_congr e.mapEdgeSet,
    ← (K n).edgeFinset_card, card_edgeFinset_top_eq_card_choose_two, Fintype.card_fin]

theorem core_edge_counts : (K 2).edgeFinset.card = 1 ∧ (K 3).edgeFinset.card = 3 := by
  constructor <;> rw [card_edgeFinset_top_eq_card_choose_two, Fintype.card_fin] <;> decide

theorem no_function_of_generator_count :
    ¬ ∃ F : ℕ → ℕ,
      F S₁.card = (K 2).edgeFinset.card ∧ F S₂.card = (K 3).edgeFinset.card := by
  rw [same_generator_count.1, same_generator_count.2, core_edge_counts.1, core_edge_counts.2]
  rintro ⟨F, h1, h3⟩
  omega

theorem counterexample :
    S₁.card = S₂.card ∧ A.Connected ∧ B.Connected ∧
    IsCoreOf (K 2) A ∧ IsCoreOf (K 3) B ∧
    (K 2).edgeFinset.card ≠ (K 3).edgeFinset.card := by
  refine ⟨same_generator_count.1.trans same_generator_count.2.symm,
    both_connected.1, both_connected.2, cores.1, cores.2, ?_⟩
  rw [core_edge_counts.1, core_edge_counts.2]
  decide

end Conjecture3467

#print axioms Conjecture3467.both_sets_generate
#print axioms Conjecture3467.both_connected
#print axioms Conjecture3467.cores
#print axioms Conjecture3467.core_minimal
#print axioms Conjecture3467.complete_core_unique
#print axioms Conjecture3467.complete_core_edge_count
#print axioms Conjecture3467.no_function_of_generator_count
#print axioms Conjecture3467.counterexample
