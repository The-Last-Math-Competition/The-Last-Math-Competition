import Std

/-!
# TLMC 00000004091: chromatic number does not determine configuration Betti numbers

The algebraic model is rational cellular homology of a finite simple graph.
`HasFirstBetti G d` supplies an actual basis of its incidence-cycle space,
with existence and uniqueness of coefficients. No Betti values are stipulated.
For one particle the unordered configuration space is the graph itself.
The topological cellular/singular comparison is explained in the accompanying
paper; the kernel verification below uses no imported topological theorem.
-/
namespace TLMC4091

structure Graph where
  vertices : Nat
  edges : Nat
  source : Fin edges → Fin vertices
  target : Fin edges → Fin vertices
  noLoops : ∀ e, source e ≠ target e
  simple : ∀ e f,
    (source e = source f ∧ target e = target f) ∨
    (source e = target f ∧ target e = source f) → e = f

abbrev Chain (G : Graph) := Fin G.edges → Rat

def incoming (G : Graph) (z : Chain G) (v : Fin G.vertices) : Rat :=
  ((List.finRange G.edges).map fun e => if G.target e = v then z e else 0).sum

def outgoing (G : Graph) (z : Chain G) (v : Fin G.vertices) : Rat :=
  ((List.finRange G.edges).map fun e => if G.source e = v then z e else 0).sum

/-- The incidence boundary is incoming minus outgoing at every vertex. -/
def boundary (G : Graph) (z : Chain G) (v : Fin G.vertices) : Rat :=
  incoming G z v - outgoing G z v

/-- A rational cellular 1-cycle is a chain with zero incidence boundary. -/
def IsCycle (G : Graph) (z : Chain G) : Prop :=
  ∀ v, boundary G z v = 0

/-- Linear combination of d proposed cycle-basis vectors. -/
def linearCombination {G : Graph} {d : Nat}
    (basis : Fin d → Chain G) (a : Fin d → Rat) : Chain G :=
  fun e => ((List.finRange d).map fun i => a i * basis i e).sum

/-- A genuine dimension certificate: a basis, spanning, and unique coefficients.
For a graph there are no 2-cells, so H₁ = ker ∂₁ / im ∂₂ = ker ∂₁. -/
def HasFirstBetti (G : Graph) (d : Nat) : Prop :=
  ∃ basis : Fin d → Chain G,
    (∀ i, IsCycle G (basis i)) ∧
    ∀ z, IsCycle G z → ∃ a : Fin d → Rat,
      linearCombination basis a = z ∧
      ∀ b, linearCombination basis b = z → b = a

/-- An actual legal coloring of the underlying undirected graph. -/
structure Coloring (G : Graph) (k : Nat) where
  color : Fin G.vertices → Fin k
  proper : ∀ e, color (G.source e) ≠ color (G.target e)

/-- Legal coloring plus minimality, rather than an assigned chromatic label. -/
def HasChromaticNumber (G : Graph) (k : Nat) : Prop :=
  Nonempty (Coloring G k) ∧ ∀ j, j < k → ¬ Nonempty (Coloring G j)

abbrev segment : Graph where
  vertices := 2
  edges := 1
  source := fun _ => 0
  target := fun _ => 1
  noLoops := by decide
  simple := by decide

abbrev square : Graph where
  vertices := 4
  edges := 4
  source := fun e => e
  target := fun e => ⟨(e.val + 1) % 4, Nat.mod_lt _ (by decide)⟩
  noLoops := by decide
  simple := by decide

@[simp] private theorem finRange_zero : List.finRange 0 = [] := rfl
@[simp] private theorem finRange_one : List.finRange 1 = [0] := rfl
@[simp] private theorem finRange_four : List.finRange 4 = [0, 1, 2, 3] := rfl

@[simp] private theorem fin_four_last_val : (3 : Fin 4).val = 3 := rfl

private theorem fin_one (i : Fin 1) : i = 0 := by omega
private theorem fin_two (i : Fin 2) : i = 0 ∨ i = 1 := by omega
private theorem fin_four (i : Fin 4) : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega

private theorem rat_sub_eq_zero_iff (a b : Rat) : a - b = 0 ↔ a = b := by
  constructor
  · intro h
    have hh := congrArg (fun x : Rat => x + b) h
    simpa [Rat.sub_eq_add_neg, Rat.add_assoc, Rat.neg_add_cancel,
      Rat.add_zero, Rat.zero_add] using hh
  · intro h; subst b; exact Rat.sub_self

/-- The segment incidence matrix has trivial kernel. -/
theorem segment_cycle_iff (z : Chain segment) :
    IsCycle segment z ↔ z = fun _ => 0 := by
  constructor
  · intro h
    have hv := h 1
    have hz : z 0 = 0 := by
      simpa [boundary, incoming, outgoing, segment, Rat.add_zero, Rat.zero_add, Rat.sub_eq_add_neg] using hv
    funext e
    have he : e = 0 := fin_one e
    simpa [he] using hz
  · intro h; subst z
    intro v
    rcases fin_two v with rfl | rfl <;>
      simp [boundary, incoming, outgoing, segment, Rat.add_zero, Rat.sub_self]

/-- The coherently oriented square has precisely the constant edge chains. -/
theorem square_cycle_iff (z : Chain square) :
    IsCycle square z ↔ ∀ e, z e = z 0 := by
  constructor
  · intro h
    have h1 := h 1
    have h2 := h 2
    have h3 := h 3
    have z01 : z 0 = z 1 := by
      apply (rat_sub_eq_zero_iff _ _).mp
      simpa [boundary, incoming, outgoing, square, Rat.add_zero, Rat.zero_add] using h1
    have z12 : z 1 = z 2 := by
      apply (rat_sub_eq_zero_iff _ _).mp
      simpa [boundary, incoming, outgoing, square, Rat.add_zero, Rat.zero_add] using h2
    have z23 : z 2 = z 3 := by
      apply (rat_sub_eq_zero_iff _ _).mp
      simpa [boundary, incoming, outgoing, square, Rat.add_zero, Rat.zero_add] using h3
    intro e
    rcases fin_four e with rfl | rfl | rfl | rfl
    · rfl
    · exact z01.symm
    · exact (z01.trans z12).symm
    · exact (z01.trans (z12.trans z23)).symm
  · intro h v
    rcases fin_four v with rfl | rfl | rfl | rfl <;>
      simp [boundary, incoming, outgoing, square, Rat.add_zero, Rat.zero_add, h, Rat.sub_self]

/-- A zero-element basis for the actual segment cycle space. -/
theorem segment_firstBetti : HasFirstBetti segment 0 := by
  refine ⟨fun i => Fin.elim0 i, ?_, ?_⟩
  · intro i; exact Fin.elim0 i
  · intro z hz
    have hz0 := segment_cycle_iff z |>.mp hz
    refine ⟨fun i => Fin.elim0 i, ?_, ?_⟩
    · subst z; rfl
    · intro b _; funext i; exact Fin.elim0 i

/-- The all-one edge chain is a one-element basis, with coefficient z(0). -/
theorem square_firstBetti : HasFirstBetti square 1 := by
  refine ⟨fun _ _ => 1, ?_, ?_⟩
  · intro i; apply (square_cycle_iff _).mpr; intro e; rfl
  · intro z hz
    have hc := (square_cycle_iff z).mp hz
    refine ⟨fun _ => z 0, ?_, ?_⟩
    · funext e
      simp [linearCombination, Rat.add_zero, hc]
    · intro b hb
      funext i
      have he := congrFun hb 0
      have hi := fin_one i
      simpa [linearCombination, Rat.add_zero, hi] using he

private def segmentTwoColoring : Coloring segment 2 where
  color := fun v => v
  proper := by decide

private def squareTwoColoring : Coloring square 2 where
  color := fun v => ⟨v.val % 2, Nat.mod_lt _ (by decide)⟩
  proper := by decide

/-- Any graph with an edge is not colorable with fewer than two colors. -/
theorem no_fewer_than_two (G : Graph) (e : Fin G.edges) (j : Nat) (hj : j < 2) :
    ¬ Nonempty (Coloring G j) := by
  rintro ⟨c⟩
  have hs := (c.color (G.source e)).isLt
  have ht := (c.color (G.target e)).isLt
  have hv : c.color (G.source e) = c.color (G.target e) := by
    apply Fin.ext
    omega
  exact c.proper e hv

theorem segment_chromatic : HasChromaticNumber segment 2 := by
  exact ⟨⟨segmentTwoColoring⟩, fun j hj => no_fewer_than_two segment 0 j hj⟩

theorem square_chromatic : HasChromaticNumber square 2 := by
  exact ⟨⟨squareTwoColoring⟩, fun j hj => no_fewer_than_two square 0 j hj⟩

/-- Necessary n=1 consequence of the conjecture, weakened from a polynomial
of degree exactly one to an arbitrary function of chromatic number. -/
def ChromaticDeterminesFirstBetti : Prop :=
  ∃ f : Nat → Nat, ∀ (G : Graph) (k d : Nat),
    HasChromaticNumber G k → HasFirstBetti G d → f k = d

/-- The two certified graphs defeat every function, hence every polynomial. -/
theorem conjecture_00000004091_false : ¬ ChromaticDeterminesFirstBetti := by
  rintro ⟨f, hf⟩
  have h0 := hf segment 2 0 segment_chromatic segment_firstBetti
  have h1 := hf square 2 1 square_chromatic square_firstBetti
  omega

#print axioms conjecture_00000004091_false
#print axioms segment_firstBetti
#print axioms square_firstBetti
end TLMC4091
