import Mathlib.Combinatorics.SimpleGraph.Star
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Tactic.NormNum

/-! Standard branch-set graph minors, actual k by k grids and actual stars.
The target is the source's literal edge-count upper bound depending only on k,
not the genuine grid theorem concerning treewidth. -/
namespace TLMC1674
open SimpleGraph

/-- Standard branch-set minor model, with all usual conditions retained. -/
structure MinorModel {V W : Type*} (A : SimpleGraph V) (B : SimpleGraph W) where
  branch : V → Set W
  nonempty : ∀ v, (branch v).Nonempty
  connected : ∀ v, (B.induce (branch v)).Connected
  disjoint : Pairwise (fun u v => Disjoint (branch u) (branch v))
  cross_edge : ∀ u v, A.Adj u v →
    ∃ x∈branch u, ∃ y∈branch v, B.Adj x y

def IsMinor {V W : Type*} (A : SimpleGraph V) (B : SimpleGraph W) : Prop :=
  Nonempty (MinorModel A B)

/-- The ordinary square grid: horizontal or vertical consecutive coordinates. -/
def grid (k : ℕ) : SimpleGraph (Fin k × Fin k) where
  Adj u v := (u.1=v.1 ∧ (u.2.val+1=v.2.val ∨ v.2.val+1=u.2.val)) ∨
    (u.2=v.2 ∧ (u.1.val+1=v.1.val ∨ v.1.val+1=u.1.val))
  symm := ⟨by
    intro u v h
    rcases h with ⟨h,h'⟩|⟨h,h'⟩
    · exact Or.inl ⟨h.symm,h'.symm⟩
    · exact Or.inr ⟨h.symm,h'.symm⟩⟩
  loopless := ⟨by intro u; simp⟩

instance gridDecidable (k : ℕ) : DecidableRel (grid k).Adj := by
  intro u v
  change Decidable ((u.1=v.1 ∧ (u.2.val+1=v.2.val ∨ v.2.val+1=u.2.val)) ∨
    (u.2=v.2 ∧ (u.1.val+1=v.1.val ∨ v.1.val+1=u.1.val)))
  infer_instance

/-- Actual Mathlib star, with n leaves and the distinguished Option.none center. -/
abbrev star (n : ℕ) : SimpleGraph (Option (Fin n)) := starGraph none

theorem actual_star_tree (n : ℕ) : (star n).IsTree := isTree_starGraph none

theorem actual_star_edge_count (n : ℕ) : (star n).edgeFinset.card=n := by
  have h := (actual_star_tree n).card_edgeFinset
  simpa using h

theorem center_unique {V W : Type*} {A : SimpleGraph V} {r : W}
    (m : MinorModel A (starGraph r)) {u v : V}
    (hu : r∈m.branch u) (hv : r∈m.branch v) : u=v := by
  by_contra h
  exact Set.disjoint_left.mp (m.disjoint h) hu hv

theorem cross_edge_uses_center {V W : Type*} {A : SimpleGraph V} {r : W}
    (m : MinorModel A (starGraph r)) {u v : V} (h : A.Adj u v) :
    r∈m.branch u ∨ r∈m.branch v := by
  obtain ⟨x,hx,y,hy,hxy⟩ := m.cross_edge u v h
  rcases (starGraph_adj.mp hxy).2 with h|h
  · exact Or.inl (h ▸ hx)
  · exact Or.inr (h ▸ hy)

/-- Stronger than needed: a star minor cannot have two endpoint-disjoint edges. -/
theorem no_two_disjoint_edges {V W : Type*} {A : SimpleGraph V} (r : W)
    {a b c d : V} (hab : A.Adj a b) (hcd : A.Adj c d)
    (hac : a≠c) (had : a≠d) (hbc : b≠c) (hbd : b≠d) :
    ¬ IsMinor A (starGraph r) := by
  rintro ⟨m⟩
  rcases cross_edge_uses_center m hab with ha|hb <;>
    rcases cross_edge_uses_center m hcd with hc|hd
  · exact hac (center_unique m ha hc)
  · exact had (center_unique m ha hd)
  · exact hbc (center_unique m hb hc)
  · exact hbd (center_unique m hb hd)

theorem different_rows {k : ℕ} {a b : Fin k} (h : a≠b) (x y : Fin k) :
    (a,x)≠(b,y) := fun he => h (congrArg Prod.fst he)

theorem no_grid_minor (k n : ℕ) (hk : 2≤k) : ¬ IsMinor (grid k) (star n) := by
  let a : Fin k := ⟨0,by omega⟩
  let b : Fin k := ⟨1,by omega⟩
  have hab : a≠b := by
    intro h
    have hh := congrArg Fin.val h
    norm_num [a,b] at hh
  have h0 : (grid k).Adj (a,a) (a,b) := Or.inl ⟨rfl,by norm_num [a,b]⟩
  have h1 : (grid k).Adj (b,a) (b,b) := Or.inl ⟨rfl,by norm_num [a,b]⟩
  exact no_two_disjoint_edges none h0 h1
    (different_rows hab a a) (different_rows hab a b)
    (different_rows hab b a) (different_rows hab b b)

theorem unbounded_edge_counts (k B : ℕ) (hk : 2≤k) :
    ∃ n : ℕ, (star n).IsTree ∧ ¬ IsMinor (grid k) (star n) ∧
      B < (star n).edgeFinset.card := by
  exact ⟨B+1,actual_star_tree _,no_grid_minor k _ hk,by rw [actual_star_edge_count]; omega⟩

theorem arbitrarily_large_real_excess (F : ℕ → ℝ) (K : ℕ) :
    ∃ k n : ℕ, K≤k ∧ 2≤k ∧ (star n).IsTree ∧
      ¬ IsMinor (grid k) (star n) ∧ F k < ((star n).edgeFinset.card : ℝ) := by
  let k := max K 2
  obtain ⟨n,hn⟩ := exists_nat_gt (F k)
  exact ⟨k,n,le_max_left _ _,le_max_right _ _,actual_star_tree _,
    no_grid_minor k n (le_max_right _ _),by simpa only [actual_star_edge_count] using hn⟩

def EventualEdgeBound (F : ℕ → ℝ) : Prop :=
  ∃ K : ℕ, ∀ k : ℕ, K≤k → ∀ n : ℕ,
    ¬ IsMinor (grid k) (star n) → ((star n).edgeFinset.card : ℝ)≤F k

theorem no_eventual_edge_bound (F : ℕ → ℝ) : ¬ EventualEdgeBound F := by
  rintro ⟨K,h⟩
  obtain ⟨k,n,hK,_,_,hn,hgt⟩ := arbitrarily_large_real_excess F K
  exact (not_le_of_gt hgt) (h k hK n hn)

theorem no_k_only_finite_bound : ¬ ∃ F : ℕ → ℝ, EventualEdgeBound F := by
  rintro ⟨F,hF⟩
  exact no_eventual_edge_bound F hF

/-- A literal upper bound over all actual finite graphs would restrict to stars. -/
theorem no_finite_graph_upper_bound :
    ¬ ∃ (F : ℕ → ℝ) (K : ℕ), ∀ k : ℕ, K≤k →
      ∀ (V : Type) [Fintype V] [DecidableEq V] (A : SimpleGraph V)
        [DecidableRel A.Adj],
      ¬ IsMinor (grid k) A → (A.edgeFinset.card : ℝ)≤F k := by
  rintro ⟨F,K,h⟩
  apply no_eventual_edge_bound F
  refine ⟨K,?_⟩
  intro k hk n hn
  exact h k hk (Option (Fin n)) (star n) hn

end TLMC1674
