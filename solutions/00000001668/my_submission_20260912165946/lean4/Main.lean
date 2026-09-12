/-
  Disproof of conjecture 00000001668.

      "The complete classification table: chi_c(G(n,k)) = 3 when n = 0 (mod 3)
       and k = 1 (mod 3), and 4 otherwise (consistent with computations for
       n <= 30); the table is closed for all n and k."

  Both branches of the table are refuted, each by an explicit finite
  certificate:

  * `(n,k) = (6,1)` lies in the first branch, which predicts 3, yet `G(6,1)`
    admits a `(2,1)`-colouring, so `chi_c(G(6,1)) <= 2 < 3`.
  * `(n,k) = (5,1)` lies in the complement, which predicts 4, yet `G(5,1)`
    admits a `(5,2)`-colouring, so `chi_c(G(5,1)) <= 5/2 < 4`.

  Each certificate is a finite object verified edge by edge by `decide`.  No
  property of the graphs beyond these two colourings is used.

  Core Lean 4 only -- no Mathlib dependency.

  SCOPE.  This file formalises the refutation of the conjecture.  It does NOT
  formalise the paper's stronger structural claim that `chi_c(G(n,k)) <= 3` for
  *every* admissible `(n,k)`; that claim rests on Brooks' theorem, which is a
  research theorem and is neither formalised here nor assumed.  See
  `lean4/README.md` for the boundary.
-/

namespace Tlmc1668

/-! ## The circular distance on `Z_p` -/

/-- The ordinary absolute difference `|a - b|` of two naturals. -/
def absDiff (a b : Nat) : Nat := if a ≤ b then b - a else a - b

/-- The circular distance `|a - b|_p` on the residues mod `p`, in the form
`min(d, p - d)` with `d = |a - b|`.

This agrees with the paper's `min(d mod p, p - (d mod p))` for `d = a - b`:
both representatives lie in `[0, p)`, and taking the absolute value before
reducing is immaterial because `min` is applied afterwards. -/
def circDist (p : Nat) (a b : Fin p) : Nat :=
  min (absDiff a.val b.val) (p - absDiff a.val b.val)

/-- Unfolding lemma for `circDist`. -/
theorem circDist_def (p : Nat) (a b : Fin p) :
    circDist p a b = min (absDiff a.val b.val) (p - absDiff a.val b.val) := rfl

/-- The absolute difference of two naturals below `p` is below `p`. -/
theorem absDiff_lt_of_lt {a b p : Nat} (ha : a < p) (hb : b < p) : absDiff a b < p := by
  unfold absDiff
  split <;> omega

/-- Distinct naturals have positive absolute difference. -/
theorem absDiff_pos_of_ne {a b : Nat} (h : a ≠ b) : 0 < absDiff a b := by
  unfold absDiff
  split <;> omega

/-- The absolute difference from a natural to itself is zero. -/
theorem absDiff_self (a : Nat) : absDiff a a = 0 := by
  unfold absDiff
  split <;> omega

/-- The circular distance is strictly less than `p`. -/
theorem circDist_lt (p : Nat) (a b : Fin p) : circDist p a b < p := by
  rw [circDist_def]
  have h := absDiff_lt_of_lt a.isLt b.isLt
  omega

/-- Two distinct residues are at positive circular distance.  This is what makes
a proper colouring a `(p,1)`-colouring. -/
theorem circDist_pos (p : Nat) (a b : Fin p) (h : a ≠ b) : 1 ≤ circDist p a b := by
  rw [circDist_def]
  have hne : a.val ≠ b.val := fun hv => h (Fin.ext hv)
  have hd := absDiff_pos_of_ne hne
  have hp := absDiff_lt_of_lt a.isLt b.isLt
  omega

/-- The circular distance from a residue to itself is zero. -/
theorem circDist_self (p : Nat) (a : Fin p) : circDist p a a = 0 := by
  rw [circDist_def, absDiff_self]
  omega

/-! ## Graphs and `(p,q)`-colourings -/

/-- A finite graph on the vertex type `Fin m`, given by an edge list.  Each edge
is recorded once as an ordered pair; the colouring constraint below is
symmetric in the two endpoints, so the orientation does not matter. -/
structure Graph (m : Nat) where
  edges : List (Fin m × Fin m)

/-- `c` is a `(p,q)`-colouring of `G` (Definition 2.2): on every edge, the
circular distance between the two colours lies in `[q, p - q]`.

Written with `List.all` so that the condition is decidable by computation on a
concrete edge list.  `isPQ_iff` below recovers the `∀ e ∈ G.edges` form. -/
def isPQ {m : Nat} (G : Graph m) (p q : Nat) (c : Fin m → Fin p) : Bool :=
  G.edges.all fun e => decide (q ≤ circDist p (c e.1) (c e.2) ∧ circDist p (c e.1) (c e.2) ≤ p - q)

/-- The propositional form of `isPQ`: every edge satisfies the constraint.  This
is the statement that appears in the paper. -/
theorem isPQ_iff {m : Nat} (G : Graph m) (p q : Nat) (c : Fin m → Fin p) :
    isPQ G p q c = true ↔
      ∀ e, e ∈ G.edges → q ≤ circDist p (c e.1) (c e.2) ∧ circDist p (c e.1) (c e.2) ≤ p - q := by
  rw [isPQ, List.all_eq_true]
  exact ⟨fun h e he => of_decide_eq_true (h e he), fun h e he => decide_eq_true (h e he)⟩

/-- A proper `k`-colouring is a `(k,1)`-colouring.  This is the inequality
`chi_c <= chi` in the case `q = 1`: distinct residues are at circular distance
between `1` and `k - 1`. -/
theorem proper_is_pq {m k : Nat} (G : Graph m) (c : Fin m → Fin k)
    (h : ∀ e, e ∈ G.edges → c e.1 ≠ c e.2) : isPQ G k 1 c = true := by
  rw [isPQ_iff]
  intro e he
  exact ⟨circDist_pos k (c e.1) (c e.2) (h e he),
         by have := circDist_lt k (c e.1) (c e.2); omega⟩

/-! ## The generalized Petersen graph `G(n,k)` -/

/-- `u i` is vertex `i` of `G(n,k)`, an element of `Fin (2*n)`. -/
def u (n : Nat) (i : Fin n) : Fin (2 * n) := ⟨i.val, by omega⟩

/-- `v i` is vertex `n + i` of `G(n,k)`, an element of `Fin (2*n)`. -/
def v (n : Nat) (i : Fin n) : Fin (2 * n) := ⟨n + i.val, by omega⟩

/-- The generalized Petersen graph `G(n,k)` (Definition 2.1): the outer cycle
`u i -- u (i+1)`, the inner star polygon `v i -- v (i+k)`, and the spokes
`u i -- v i`, with all indices reduced mod `n`.  Requires `0 < n`. -/
def gp (n k : Nat) (hn : 0 < n) : Graph (2 * n) where
  edges :=
    (List.finRange n).map (fun i => (u n i, u n ⟨(i.val + 1) % n, Nat.mod_lt _ hn⟩))
    ++ (List.finRange n).map (fun i => (v n i, v n ⟨(i.val + k) % n, Nat.mod_lt _ hn⟩))
    ++ (List.finRange n).map (fun i => (u n i, v n i))

/-- `G(5,1)`, the pentagonal prism `C_5 x K_2`. -/
def G51 : Graph 10 := gp 5 1 (by decide)

/-- `G(6,1)`, the hexagonal prism `C_6 x K_2`. -/
def G61 : Graph 12 := gp 6 1 (by decide)

/-! ## The two certificates -/

/-- The `(5,2)`-colouring of `G(5,1)` exhibited in the paper: outer
`u_0..u_4 = 0,2,4,1,3` and inner `v_0..v_4 = 2,4,1,3,0`.  Since `u i = i` and
`v i = 5 + i`, the vertices `0..9` receive `0,2,4,1,3,2,4,1,3,0`. -/
def c51 : Fin 10 → Fin 5 := fun i =>
  match i.val with
  | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 1 | 4 => 3
  | 5 => 2 | 6 => 4 | 7 => 1 | 8 => 3 | 9 => 0
  | _ => 0

/-- The `(2,1)`-colouring of `G(6,1)` exhibited in the paper: outer
`u_0..u_5 = 0,1,0,1,0,1` and inner `v_0..v_5 = 1,0,1,0,1,0`. -/
def c61 : Fin 12 → Fin 2 := fun i =>
  match i.val with
  | 0 => 0 | 1 => 1 | 2 => 0 | 3 => 1 | 4 => 0 | 5 => 1
  | 6 => 1 | 7 => 0 | 8 => 1 | 9 => 0 | 10 => 1 | 11 => 0
  | _ => 0

/-- **`G(5,1)` has a `(5,2)`-colouring.**  All 15 edges are checked by `decide`;
there is no violating edge. -/
theorem gp51_has_5_2_colouring : isPQ G51 5 2 c51 = true := by decide

/-- **`G(6,1)` has a `(2,1)`-colouring.**  All 18 edges are checked by `decide`;
there is no violating edge. -/
theorem gp61_has_2_1_colouring : isPQ G61 2 1 c61 = true := by decide

/-- `c61` is a *proper* 2-colouring of `G(6,1)`: adjacent vertices get different
colours.  Derived from `gp61_has_2_1_colouring` through `isPQ_iff`, which shows
that the `(p,q)`-condition with `p = 2`, `q = 1` really does say "proper". -/
theorem gp61_proper (e : Fin 12 × Fin 12) (he : e ∈ G61.edges) : c61 e.1 ≠ c61 e.2 := by
  intro hc
  have h := ((isPQ_iff G61 2 1 c61).mp gp61_has_2_1_colouring) e he
  have h1 := h.1
  rw [hc, circDist_self] at h1
  omega

/-- **`G(6,1)` is bipartite**: it admits a proper 2-colouring, namely `c61`.
The propositional form is used because `∀ e : Fin m × Fin m` is not decidable in
core Lean (there is no `Fintype` instance for product types). -/
theorem gp61_bipartite : ∃ c : Fin 12 → Fin 2, ∀ e, e ∈ G61.edges → c e.1 ≠ c e.2 :=
  ⟨c61, gp61_proper⟩

/-- Cross-check: feeding the proper colouring into the general lemma
`proper_is_pq` recovers `gp61_has_2_1_colouring`. -/
theorem gp61_has_2_1_colouring' : isPQ G61 2 1 c61 = true :=
  proper_is_pq G61 c61 gp61_proper

/-! ## The refutation -/

/-- `p/q < a/b`, by cross-multiplication.  Every denominator occurring here is
positive, so this is the usual order on the corresponding rationals. -/
abbrev RatioLt (p q a b : Nat) : Prop := p * b < a * q

/-- `G` admits a circular colouring whose ratio is strictly below `a/b`.

Since `chi_c(G)` is the *infimum* of the ratios realised by circular colourings,
exhibiting a realised ratio below `a/b` shows that `chi_c(G) < a/b`, and hence
that `chi_c(G) != a/b`.  This is the only property of the infimum the refutation
uses, so `chi_c` itself is not formalised: the constructive form is stated
instead. -/
def HasColouringBelow {m : Nat} (G : Graph m) (a b : Nat) : Prop :=
  ∃ p q : Nat, ∃ c : Fin m → Fin p, isPQ G p q c = true ∧ RatioLt p q a b

/-- The conjecture's branch set `S_3 = {(n,k) : n = 0 (mod 3), k = 1 (mod 3)}`. -/
abbrev inS3 (n k : Nat) : Prop := n % 3 = 0 ∧ k % 3 = 1

/-- `chi_c(G(6,1)) < 3`, witnessed by the `(2,1)`-colouring: `2/1 < 3/1`. -/
theorem gp61_below_3 : HasColouringBelow G61 3 1 :=
  ⟨2, 1, c61, gp61_has_2_1_colouring, by decide⟩

/-- `chi_c(G(5,1)) < 4`, witnessed by the `(5,2)`-colouring: `5/2 < 4/1`. -/
theorem gp51_below_4 : HasColouringBelow G51 4 1 :=
  ⟨5, 2, c51, gp51_has_5_2_colouring, by decide⟩

/-- **The first branch is refuted.**  `(6,1)` lies in `S_3`, so the conjecture
predicts `chi_c(G(6,1)) = 3`; but `chi_c(G(6,1)) < 3`. -/
theorem branch_S3_refuted : inS3 6 1 ∧ HasColouringBelow G61 3 1 :=
  ⟨by decide, gp61_below_3⟩

/-- **The second branch is refuted.**  `(5,1)` lies in the complement of `S_3`,
so the conjecture predicts `chi_c(G(5,1)) = 4`; but `chi_c(G(5,1)) < 4`. -/
theorem branch_otherwise_refuted : ¬ inS3 5 1 ∧ HasColouringBelow G51 4 1 :=
  ⟨by decide, gp51_below_4⟩

/-- **Conjecture 00000001668 is false.**

The conjecture asserts a two-valued classification table.  Each branch of the
table is contradicted by an explicit pair `(n,k)` together with an explicit
circular colouring of `G(n,k)`:

* `(6,1)` satisfies `6 = 0` and `1 = 1` (mod 3), so the table requires
  `chi_c(G(6,1)) = 3`; but `G(6,1)` has a `(2,1)`-colouring, so
  `chi_c(G(6,1)) <= 2 < 3`.
* `(5,1)` does not satisfy `5 = 0` (mod 3), so the table requires
  `chi_c(G(5,1)) = 4`; but `G(5,1)` has a `(5,2)`-colouring, so
  `chi_c(G(5,1)) <= 5/2 < 4`.

Both certificates are finite and are verified edge by edge by `decide`, so this
is a complete disproof of the conjecture.  It is *not* the paper's stronger
structural statement that 4 is unattainable for every admissible pair, which
would require Brooks' theorem; see `lean4/README.md`. -/
theorem conjecture_00000001668_false :
    (inS3 6 1 ∧ HasColouringBelow G61 3 1) ∧
    (¬ inS3 5 1 ∧ HasColouringBelow G51 4 1) :=
  ⟨branch_S3_refuted, branch_otherwise_refuted⟩

end Tlmc1668
