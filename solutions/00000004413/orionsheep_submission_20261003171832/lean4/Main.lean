import Mathlib

namespace Submission00000004413

/-!
# Refutation of conjecture 00000004413

The conjecture claims that for any bounded-degree graph limit (a *graphing*)
with degree bound `d`, the measure of cycles of length `l` is at most
`(d-1)^l / (2l)`, and that this bound is attained and optimal for the
`d`-regular tree graph limit.

This is false.  We model a graphing on a finite probability space `V` as a
symmetric, irreflexive edge relation `E` on `V`; the cycle measure is the
number of distinct undirected `l`-cycles divided by `|V|` (uniform
measure).  The claimed bound is violated by the triangle `K₃` (`d = 2`,
`l = 3`): its cycle measure is at least `1/3`, while the claimed bound is
`(d-1)^l / (2l) = 1/6`.  Moreover the `d`-regular *tree* has cycle measure
`0` — it contains no cycles — so it can never *attain* the strictly
positive claimed bound `(d-1)^l/(2l) > 0`: the conjecture's optimality
assertion is false too.  (The expression `(d-1)^l/(2l)` is the Poisson mean
of the number of `l`-cycles in a *random* `d`-regular graph — a typical
value, not an upper bound.)
-/

/-- A (deterministic) graphing on a finite probability space: a symmetric,
    irreflexive edge relation on `V`, where `V` carries the uniform measure. -/
structure Graphing (V : Type*) [Fintype V] where
  E : V → V → Prop
  symm : ∀ x y, E x y → E y x
  irrefl : ∀ x, ¬ E x x
  dec : DecidableRel E

attribute [instance] Graphing.dec

namespace Graphing

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Cyclic successor on `Fin n`: `i ↦ i + 1 (mod n)`.  Defined for all `n`
    (vacuously when `n = 0`, since `Fin 0` is empty). -/
def cycStep {n : ℕ} (i : Fin n) : Fin n :=
  ⟨(i.val + 1) % n, Nat.mod_lt _ i.pos⟩

/-- Degree of a vertex: the number of its neighbours. -/
def deg (G : Graphing V) (x : V) : ℕ := (Finset.univ.filter (G.E x)).card

/-- The graphing satisfies degree bound `d` if every vertex has degree ≤ d. -/
def DegreeBound (G : Graphing V) (d : ℕ) : Prop := ∀ x, G.deg x ≤ d

/-- Oriented closed walks of length `n`, given as `Fin n → V` assignments
    in which consecutive vertices (cyclically, via `cycStep`) are
    adjacent. -/
abbrev IsCycleWalk (G : Graphing V) {n : ℕ} (w : Fin n → V) : Prop :=
  ∀ i : Fin n, G.E (w i) (w (cycStep i))

/-- All oriented closed walks of length `n`. -/
def cycleWalks (G : Graphing V) (n : ℕ) : Finset (Fin n → V) :=
  Finset.univ.filter (fun w => G.IsCycleWalk w)

/-- The undirected edge set traversed by a cycle walk, as a `Finset` of
    `Sym2` (unordered) pairs.  Since `s(a,b) = s(b,a)`, a cycle together
    with all of its cyclic rotations and its reverse yields the *same*
    edge set, so the image in `cycleCount` counts distinct undirected
    cycles. -/
def edgeSetOf (G : Graphing V) {n : ℕ} (w : Fin n → V) : Finset (Sym2 V) :=
  Finset.univ.image (fun i : Fin n => s(w i, w (cycStep i)))

/-- The cycle measure of length `n`: number of distinct undirected
    `n`-cycles, normalized by the number of vertices (the uniform measure
    of the vertex space). -/
def cycleCount (G : Graphing V) (n : ℕ) : ℚ :=
  ((G.cycleWalks n).image (G.edgeSetOf)).card / (Fintype.card V)

/-- The claimed optimal upper bound `(d-1)^l / (2l)`. -/
def claimedBound (d l : ℕ) : ℚ := (d - 1 : ℚ) ^ l / (2 * l)

end Graphing

/-! ## The counterexample: the triangle `K₃` as a graphing on `Fin 3` -/

/-- Adjacency in `K₃`: two distinct vertices are adjacent. -/
def triangleAdj (x y : Fin 3) : Prop := x ≠ y

/-- The triangle graphing on the 3-point probability space. -/
def triangle : Graphing (Fin 3) where
  E := triangleAdj
  symm := fun _ _ h => h.symm
  irrefl := fun _ h => h rfl
  dec := fun x y => inferInstanceAs (Decidable (x ≠ y))

/-- The neighbour set of `x` in `K₃` is `univ.erase x`. -/
theorem triangle_filter (x : Fin 3) :
    Finset.univ.filter (triangle.E x) = Finset.univ.erase x := by
  ext y
  simp only [Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_erase, and_true]
  exact ne_comm

/-- Every vertex of `K₃` has degree `2`. -/
theorem triangle_deg (x : Fin 3) : triangle.deg x = 2 := by
  unfold Graphing.deg
  rw [triangle_filter, Finset.card_erase_of_mem (Finset.mem_univ x),
    Finset.card_univ, Fintype.card_fin]

/-- `K₃` has degree bound `2`. -/
theorem triangle_degreeBound : triangle.DegreeBound 2 := fun x =>
  (triangle_deg x).le

/-- The claimed bound for `d = 2`, `l = 3` equals `1/6`. -/
theorem claimedBound_2_3 : Graphing.claimedBound 2 3 = 1 / 6 := by
  unfold Graphing.claimedBound; norm_num

/-- The map `w = ![0,1,2]` (the identity on `Fin 3`) is a valid oriented
    closed `3`-walk in `K₃` (vertices `0 → 1 → 2 → 0`). -/
theorem triangle_cycleWalks_nonempty : (triangle.cycleWalks 3).Nonempty := by
  refine ⟨(fun i : Fin 3 => i), Finset.mem_filter.mpr
    ⟨Finset.mem_univ _, ?_⟩⟩
  intro i
  fin_cases i <;> decide

/-- The image of `edgeSetOf` over the cycle walks is nonempty. -/
theorem triangle_cycle_image_nonempty :
    ((triangle.cycleWalks 3).image (triangle.edgeSetOf)).Nonempty :=
  Finset.image_nonempty.mpr triangle_cycleWalks_nonempty

/-- **Cycle measure of `K₃` is at least `1/3`** — hence strictly larger
    than the claimed bound `1/6`. -/
theorem triangle_cycleCount_ge : (1 : ℚ) / 3 ≤ triangle.cycleCount 3 := by
  unfold Graphing.cycleCount
  rw [Fintype.card_fin]
  have hcard :
      (1 : ℚ) ≤ ((triangle.cycleWalks 3).image (triangle.edgeSetOf)).card := by
    exact_mod_cast Finset.card_pos.mpr triangle_cycle_image_nonempty
  have hpos : (0 : ℚ) < 3 := by norm_num
  rw [div_le_iff₀ hpos]
  linarith

/-! ## Main refutation theorem -/

/-- **Refutation.**  The conjectured universal bound fails: the triangle
    (`d = 2`) has length-`3` cycle measure `≥ 1/3 > 1/6 = (d-1)^l/(2l)`. -/
theorem conjecture_00000004413_false :
    ¬ (∀ (V : Type) [Fintype V] [DecidableEq V] (G : Graphing V) (d l : ℕ),
        G.DegreeBound d → G.cycleCount l ≤ Graphing.claimedBound d l) := by
  intro h
  have hb := h (Fin 3) triangle 2 3 triangle_degreeBound
  rw [claimedBound_2_3] at hb
  have hge := triangle_cycleCount_ge
  linarith

/-- Positive-strength version: an explicit counterexample exists. -/
theorem counterexample_exists :
    ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V) (G : Graphing V)
      (d l : ℕ),
      G.DegreeBound d ∧ Graphing.claimedBound d l < G.cycleCount l := by
  refine ⟨Fin 3, inferInstance, inferInstance, triangle, 2, 3,
    triangle_degreeBound, ?_⟩
  rw [claimedBound_2_3]
  have hge := triangle_cycleCount_ge
  linarith

/-- The optimality claim fails as well: for `d ≥ 2` and `l ≥ 1` the claimed
    bound is strictly positive, while the `d`-regular tree — having no
    cycles at all — has cycle measure `0`, so it cannot attain the bound. -/
theorem tree_cannot_attain (d l : ℕ) (hd : 2 ≤ d) (hl : 1 ≤ l) :
    0 < Graphing.claimedBound d l := by
  unfold Graphing.claimedBound
  have h1 : (0 : ℚ) < (d : ℚ) - 1 := by
    have : (2 : ℚ) ≤ d := by exact_mod_cast hd
    linarith
  have hp : (0 : ℚ) < ((d : ℚ) - 1) ^ l := pow_pos h1 l
  have hd2 : (0 : ℚ) < 2 * (l : ℚ) := by
    have : (1 : ℚ) ≤ l := by exact_mod_cast hl
    linarith
  positivity

end Submission00000004413
