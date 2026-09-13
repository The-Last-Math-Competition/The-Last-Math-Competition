/-
  Disproof of conjecture `00000001682`: formalisation.

  Conjecture (as filed):

    "The pancyclicity threshold of generalized Petersen graphs G(n, 2) has a
     complete classification for n ≥ 11 (G(n,2) pancyclic)."

    (中文) 广义 Petersen 图 G(n, 2) 的满圈泛环性(pancyclic)阈值为
           n ≥ 11 的完全分类(G(n,2) 泛环)。

  Refutation.  The generalized Petersen graph G(11, 2) is triangle-free, hence
  not pancyclic: a pancyclic graph on |V| = 22 vertices must contain a cycle of
  every length 3, 4, …, 22, in particular a triangle.

  Model.  Vertices are `Fin 2 × Fin n`.  The first coordinate selects the outer
  layer (`0` = `u`) or the inner layer (`1` = `v`); the second coordinate is the
  index read modulo `n`:

      u_i = (0, i),      v_i = (1, i).

  Edges of `GP(n, k)` (indices modulo `n`):

      outer:  u_i — u_{i+1}
      spoke:  u_i — v_i
      inner:  v_i — v_{i+k}

  For `n = 11`, `k = 2` the outer graph is an 11-cycle and the inner graph is
  also an 11-cycle (since `gcd(11, 2) = 1`); the two layers interact only
  through spokes, and every vertex has exactly one neighbour in the other
  layer.  Consequently no triangle exists.

  This file uses CORE LEAN ONLY (`import Std`); no Mathlib, no `Finset`, no
  `ZMod`, no `SimpleGraph`, no `sorry`.  All finite facts are discharged by
  kernel reduction (`decide`); the cycle/pancyclicity argument is constructive.
-/

import Std

set_option maxRecDepth 1000000

namespace Tlmc1682

/-! ## The generalized Petersen graph `GP(n, k)` -/

/-- The vertex set `Fin 2 × Fin n` of `GP(n, k)`: the first coordinate is `0`
for an outer vertex `u` and `1` for an inner vertex `v`; the second coordinate
is the index modulo `n`. -/
abbrev V (n : Nat) : Type := Fin 2 × Fin n

/-- The outer vertex `u_i = (0, i)`. -/
def u {n : Nat} (i : Fin n) : V n := (0, i)

/-- The inner vertex `v_i = (1, i)`. -/
def v {n : Nat} (i : Fin n) : V n := (1, i)

/-- Adjacency of the generalized Petersen graph `GP(n, k)`, as a decidable
`Bool` predicate.  All indices are read modulo `n`:
* outer edges `u_i — u_{i+1}`,
* spokes `u_i — v_i`,
* inner edges `v_i — v_{i+k}`. -/
def gp (n k : Nat) : V n → V n → Bool :=
  fun x y =>
    if x.1 == 0 then
      if y.1 == 0 then
        ((x.2.val + 1) % n == y.2.val) || ((y.2.val + 1) % n == x.2.val)
      else
        x.2 == y.2
    else
      if y.1 == 0 then
        x.2 == y.2
      else
        ((x.2.val + k) % n == y.2.val) || ((y.2.val + k) % n == x.2.val)

/-- `GP(11, 2)`, the witness of the refutation. -/
def gp11 : V 11 → V 11 → Bool := gp 11 2

/-- Boolean test for a triangle: three pairwise adjacent vertices. -/
def isTriangle {n : Nat} (G : V n → V n → Bool) (x y z : V n) : Bool :=
  G x y && G y z && G z x

/-- A triangle in `G`: three pairwise adjacent vertices. -/
def Triangle {n : Nat} (G : V n → V n → Bool) (x y z : V n) : Prop :=
  isTriangle G x y z = true

/-- Exhaustive triangle-freeness check for `GP(n, k)`: every ordered triple of
vertices (drawn from `Fin 2 × Fin n`) fails to be a triangle. -/
def triangleFreeCheck (n k : Nat) : Bool :=
  (List.finRange 2).all fun a =>
    (List.finRange 2).all fun b =>
      (List.finRange 2).all fun c =>
        (List.finRange n).all fun i =>
          (List.finRange n).all fun j =>
            (List.finRange n).all fun z => !(isTriangle (gp n k) (a, i) (b, j) (c, z))

/-- Every vertex of `GP(n, k)`: the `n` outer vertices followed by the `n`
inner vertices. -/
def allVertices (n : Nat) : List (V n) :=
  (List.finRange n).map (fun i => ((0 : Fin 2), i)) ++
  (List.finRange n).map (fun i => ((1 : Fin 2), i))

/-- A total index of a vertex, used to enumerate unordered triples once. -/
def ordIdx {n : Nat} (x : V n) : Nat := x.1.val * n + x.2.val

/-- The number of (unordered) triangles of `GP(n, k)`, computed by exhaustive
enumeration of the `C(2n, 3)` vertex triples. -/
def triangleCount (n k : Nat) : Nat :=
  (allVertices n).foldl (fun a x =>
    a + (allVertices n).foldl (fun b y =>
      b + (allVertices n).foldl (fun c z =>
        c + (if ordIdx x < ordIdx y then
               (if ordIdx y < ordIdx z then
                  (isTriangle (gp n k) x y z).toNat
                else 0)
             else 0)) 0) 0) 0

/-! ## The witness `G(11, 2)` is triangle-free -/

/-- The exhaustive check certifies `G(11, 2)` is triangle-free: all
`2 · 2 · 2 · 11 · 11 · 11` ordered triples of vertices are non-triangles. -/
theorem gp11_triangleFreeCheck : triangleFreeCheck 11 2 = true := by
  decide

/-- `G(11, 2)` has no triangle, extracted from the exhaustive `Bool` check by
kernel reduction. -/
theorem gp11_triangle_free (a b c : Fin 2) (i j k : Fin 11) :
    ¬ Triangle (gp 11 2) (a, i) (b, j) (c, k) := by
  intro hcon
  have h := gp11_triangleFreeCheck
  simp only [triangleFreeCheck] at h
  have h1 := (List.all_eq_true.mp h) a (List.mem_finRange a)
  have h2 := (List.all_eq_true.mp h1) b (List.mem_finRange b)
  have h3 := (List.all_eq_true.mp h2) c (List.mem_finRange c)
  have h4 := (List.all_eq_true.mp h3) i (List.mem_finRange i)
  have h5 := (List.all_eq_true.mp h4) j (List.mem_finRange j)
  have h6 := (List.all_eq_true.mp h5) k (List.mem_finRange k)
  rw [hcon] at h6
  exact Bool.noConfusion h6

/-- Component-free form of `gp11_triangle_free`: no three vertices of
`G(11, 2)` form a triangle. -/
theorem gp11_no_triangle (x y z : V 11) : ¬ Triangle (gp 11 2) x y z := by
  obtain ⟨a, i⟩ := x
  obtain ⟨b, j⟩ := y
  obtain ⟨c, k⟩ := z
  exact gp11_triangle_free a b c i j k

/-- Exhaustive enumeration: the unrestricted count of triangles of `G(11, 2)`
is `0`. -/
theorem gp11_triangle_count : triangleCount 11 2 = 0 := by
  decide

/-- For contrast, `G(6, 2)` has exactly two triangles (`6 ∣ 6`); this is the
only `n ≥ 4` for which `G(n, 2)` contains a triangle. -/
theorem gp6_triangle_count : triangleCount 6 2 = 2 := by
  decide

/-- `G(12, 2)` has no triangle (as `12 ∤ 6`). -/
theorem gp12_triangle_count : triangleCount 12 2 = 0 := by
  decide

/-! ## Cycles and pancyclicity -/

/-- `ClosedFrom G first xs`: the list `xs` is a walk that starts at `first`,
each consecutive pair is adjacent, and the last vertex is adjacent back to
`first`. -/
def ClosedFrom {n : Nat} (G : V n → V n → Bool) (first : V n) : List (V n) → Prop
  | [] => True
  | [x] => G x first = true
  | x :: y :: t => G x y = true ∧ ClosedFrom G first (y :: t)

/-- `ClosedCycle G p`: `p` is a closed walk of length at least three, i.e. it
has `x :: y :: t` shape with consecutive adjacency and last-to-first
adjacency. -/
def ClosedCycle {n : Nat} (G : V n → V n → Bool) : List (V n) → Prop
  | [] => False
  | [_] => False
  | x :: y :: t => G x y = true ∧ ClosedFrom G x (y :: t)

/-- `IsCycle G p`: `p` is a simple closed cycle — the vertices are pairwise
distinct, there are at least three of them, and consecutive (cyclically)
vertices are adjacent. -/
def IsCycle {n : Nat} (G : V n → V n → Bool) (p : List (V n)) : Prop :=
  p.Pairwise (· ≠ ·) ∧ 3 ≤ p.length ∧ ClosedCycle G p

/-- `HasCycleOfLength G L`: `G` contains a simple cycle with exactly `L`
vertices, presented as a list of `L` pairwise distinct vertices whose cyclic
consecutive pairs are adjacent. -/
def HasCycleOfLength {n : Nat} (G : V n → V n → Bool) (L : Nat) : Prop :=
  ∃ p : List (V n), p.length = L ∧ IsCycle G p

/-- `G` is pancyclic when it contains a cycle of every length
`3, 4, …, |V| = 2n`. -/
def Pancyclic {n : Nat} (G : V n → V n → Bool) : Prop :=
  ∀ L : Nat, 3 ≤ L → L ≤ 2 * n → HasCycleOfLength G L

/-- A list of length three is a three-element list. -/
theorem list_length_three {α : Type} {l : List α} (h : l.length = 3) :
    ∃ x y z : α, l = [x, y, z] := by
  cases l with
  | nil => simp at h
  | cons x t =>
    cases t with
    | nil => simp at h
    | cons y t2 =>
      cases t2 with
      | nil => simp at h
      | cons z t3 =>
        cases t3 with
        | nil => exact ⟨x, y, z, rfl⟩
        | cons w t4 => simp at h

/-- Pancyclicity of `G(11, 2)` would produce a cycle of length `3`. -/
theorem pancyclic_gp11_gives_3cycle (h : Pancyclic (gp 11 2)) :
    HasCycleOfLength (gp 11 2) 3 :=
  h 3 (by decide) (by decide)

/-- A cycle of length `3` in `G(11, 2)` is exactly a triangle. -/
theorem has3cycle_gp11_gives_triangle
    (h : HasCycleOfLength (gp 11 2) 3) :
    ∃ x y z : V 11, Triangle (gp 11 2) x y z := by
  obtain ⟨p, hlen, _hnod, _hle, hcyc⟩ := h
  obtain ⟨x, y, z, hp⟩ := list_length_three hlen
  have hcon : gp 11 2 x y = true ∧ gp 11 2 y z = true ∧ gp 11 2 z x = true := by
    rw [hp] at hcyc
    simpa [ClosedCycle, ClosedFrom] using hcyc
  exact ⟨x, y, z, by simp [Triangle, isTriangle, hcon.1, hcon.2.1, hcon.2.2]⟩

/-- `G(11, 2)` has no cycle of length `3`. -/
theorem gp11_no_3cycle : ¬ HasCycleOfLength (gp 11 2) 3 := by
  intro h
  obtain ⟨x, y, z, htri⟩ := has3cycle_gp11_gives_triangle h
  exact gp11_no_triangle x y z htri

/-- Main conclusion: the generalized Petersen graph `G(11, 2)` is NOT
pancyclic.  This directly refutes conjecture `00000001682`, whose parenthetical
claim is that `G(n, 2)` is pancyclic for all `n ≥ 11`. -/
theorem gp11_not_pancyclic : ¬ Pancyclic (gp 11 2) := by
  intro h
  exact gp11_no_3cycle (pancyclic_gp11_gives_3cycle h)

/-- The refutation, packaged: `G(11, 2)` is triangle-free and not
pancyclic. -/
theorem conjecture_00000001682_false :
    (∀ x y z : V 11, ¬ Triangle (gp 11 2) x y z) ∧
      ¬ Pancyclic (gp 11 2) :=
  ⟨gp11_no_triangle, gp11_not_pancyclic⟩

end Tlmc1682
