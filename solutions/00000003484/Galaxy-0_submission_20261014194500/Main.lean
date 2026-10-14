import Std
set_option maxRecDepth 10000
set_option maxHeartbeats 5000000

namespace C3484

/-- The vertices a,b,c,x,y,z, in this order. -/
abbrev V := Fin 6

/-- The ordinary 3-sun: a central triangle and three independent ears. -/
def adj (i j : V) : Bool := i != j && ((i.val < 3 && j.val < 3) ||
  ((i == 3 && (j == 0 || j == 1)) || (j == 3 && (i == 0 || i == 1))) ||
  ((i == 4 && (j == 1 || j == 2)) || (j == 4 && (i == 1 || i == 2))) ||
  ((i == 5 && (j == 0 || j == 2)) || (j == 5 && (i == 0 || i == 2))))

theorem adj_irrefl : ∀ v, adj v v = false := by decide
theorem adj_symm : ∀ v w, adj v w = adj w v := by decide

/-- Edges of the ordinary n-cycle in its cyclic index order. -/
def CycleEdge (n : Nat) (i j : Fin n) : Prop :=
  i.val + 1 = j.val ∨ j.val + 1 = i.val ∨
    (i.val = 0 ∧ j.val + 1 = n) ∨ (j.val = 0 ∧ i.val + 1 = n)

/-- A simple cycle has distinct vertices and all successive cycle edges. -/
def SimpleCycle {W : Type} (E : W → W → Prop) (n : Nat) (f : Fin n → W) : Prop :=
  3 ≤ n ∧ Function.Injective f ∧ ∀ i j, CycleEdge n i j → E (f i) (f j)

/-- An induced cycle has precisely the cyclic edges. -/
def InducedCycle {W : Type} (E : W → W → Prop) (n : Nat) (f : Fin n → W) : Prop :=
  3 ≤ n ∧ Function.Injective f ∧ ∀ i j, E (f i) (f j) ↔ CycleEdge n i j

/-- Chordality means absence of induced cycles of length at least four. -/
def Chordal {W : Type} (E : W → W → Prop) : Prop :=
  ∀ n f, InducedCycle E n f → n ≤ 3

theorem cycle_neighbors {n : Nat} (hn : 3 ≤ n) (i : Fin n) :
    ∃ j k : Fin n, CycleEdge n i j ∧ CycleEdge n i k ∧ j ≠ k ∧
      (4 ≤ n → ¬ CycleEdge n j k) := by
  by_cases h0 : i.val = 0
  · refine ⟨⟨n - 1, by omega⟩, ⟨1, by omega⟩, ?_, ?_, ?_, ?_⟩
    · simp [CycleEdge] <;> omega
    · simp [CycleEdge] <;> omega
    · intro h; have := congrArg Fin.val h; simp only at this; omega
    · intro hn4; simp [CycleEdge] <;> omega
  · by_cases hlast : i.val + 1 = n
    · refine ⟨⟨i.val - 1, by omega⟩, ⟨0, by omega⟩, ?_, ?_, ?_, ?_⟩
      · simp [CycleEdge] <;> omega
      · simp [CycleEdge] <;> omega
      · intro h; have := congrArg Fin.val h; simp only at this; omega
      · intro hn4; simp [CycleEdge] <;> omega
    · refine ⟨⟨i.val - 1, by omega⟩, ⟨i.val + 1, by omega⟩, ?_, ?_, ?_, ?_⟩
      · simp [CycleEdge] <;> omega
      · simp [CycleEdge] <;> omega
      · intro h; have := congrArg Fin.val h; simp only at this; omega
      · intro hn4; simp [CycleEdge] <;> omega

/-- Each outer vertex is simplicial; this is a finite, kernel-checked fact. -/
theorem outer_simplicial : ∀ x a b : V,
    3 ≤ x.val → adj x a = true → adj x b = true → a ≠ b → adj a b = true := by
  decide

/-- Direct proof of the induced-cycle definition, without a PEO equivalence. -/
theorem threeSun_chordal : Chordal (fun v w => adj v w = true) := by
  intro n f ⟨hn, hinj, hedge⟩
  by_cases hlarge : n ≤ 3
  · exact hlarge
  exfalso
  have hn4 : 4 ≤ n := by omega
  have core : ∀ i, (f i).val < 3 := by
    intro i
    by_cases houter : (f i).val < 3
    · exact houter
    exfalso
    obtain ⟨j, k, hj, hk, hjk, hchord⟩ := cycle_neighbors hn i
    have hfjk : f j ≠ f k := fun h => hjk (hinj h)
    have hadj := outer_simplicial (f i) (f j) (f k) (by omega)
      ((hedge i j).mpr hj) ((hedge i k).mpr hk) hfjk
    exact hchord hn4 ((hedge j k).mp hadj)
  let i0 : Fin n := ⟨0, by omega⟩
  let i1 : Fin n := ⟨1, by omega⟩
  let i2 : Fin n := ⟨2, by omega⟩
  let i3 : Fin n := ⟨3, by omega⟩
  have h0 := core i0
  have h1 := core i1
  have h2 := core i2
  have h3 := core i3
  have ne01 : (f i0).val ≠ (f i1).val := by
    intro h; have := congrArg Fin.val (hinj (Fin.ext h)); simp [i0, i1] at this
  have ne02 : (f i0).val ≠ (f i2).val := by
    intro h; have := congrArg Fin.val (hinj (Fin.ext h)); simp [i0, i2] at this
  have ne03 : (f i0).val ≠ (f i3).val := by
    intro h; have := congrArg Fin.val (hinj (Fin.ext h)); simp [i0, i3] at this
  have ne12 : (f i1).val ≠ (f i2).val := by
    intro h; have := congrArg Fin.val (hinj (Fin.ext h)); simp [i1, i2] at this
  have ne13 : (f i1).val ≠ (f i3).val := by
    intro h; have := congrArg Fin.val (hinj (Fin.ext h)); simp [i1, i3] at this
  have ne23 : (f i2).val ≠ (f i3).val := by
    intro h; have := congrArg Fin.val (hinj (Fin.ext h)); simp [i2, i3] at this
  omega


/-- A clique is any set of mutually adjacent distinct vertices. -/
def Clique (S : V → Prop) : Prop :=
  ∀ v w, S v → S w → v ≠ w → adj v w = true

/-- Inclusion-maximality among all subsets, not just the displayed candidates. -/
def MaximalClique (S : V → Prop) : Prop :=
  Clique S ∧ ∀ T : V → Prop, Clique T → (∀ v, S v → T v) → ∀ v, T v → S v

/-- C={a,b,c}, X={a,b,x}, Y={b,c,y}, Z={a,c,z}. -/
def bag (b : Fin 4) (v : V) : Bool :=
  match b.val with
  | 0 => v == 0 || v == 1 || v == 2
  | 1 => v == 0 || v == 1 || v == 3
  | 2 => v == 1 || v == 2 || v == 4
  | _ => v == 0 || v == 2 || v == 5

def bagSet (b : Fin 4) : V → Prop := fun v => bag b v = true

theorem bags_are_cliques : ∀ b, Clique (bagSet b) := by
  unfold Clique bagSet
  decide

/-- Any vertex outside a listed bag misses some vertex inside it. -/
theorem outside_obstruction : ∀ b v, bag b v = false →
    ∃ w, bag b w = true ∧ w ≠ v ∧ adj w v = false := by
  decide

theorem bags_are_maximal (b : Fin 4) : MaximalClique (bagSet b) := by
  refine ⟨bags_are_cliques b, ?_⟩
  intro T hT hsub v hv
  change bag b v = true
  cases hmem : bag b v with
  | true => rfl
  | false =>
    obtain ⟨w, hw, hne, hmiss⟩ := outside_obstruction b v hmem
    have hhit := hT w v (hsub w hw) hv hne
    simp [hmiss] at hhit

/-- The three outer neighborhoods force their respective bags. -/
theorem outer_neighbor_bags :
    (∀ v, v = 3 ∨ adj 3 v = true → bag 1 v = true) ∧
    (∀ v, v = 4 ∨ adj 4 v = true → bag 2 v = true) ∧
    (∀ v, v = 5 ∨ adj 5 v = true → bag 3 v = true) ∧
    (∀ v, v ≠ 3 → v ≠ 4 → v ≠ 5 → bag 0 v = true) := by
  decide

/-- Every clique is contained in one of the four bags. -/
theorem clique_contained_in_bag (S : V → Prop) (hS : Clique S) :
    ∃ b, ∀ v, S v → bagSet b v := by
  by_cases hx : S 3
  · refine ⟨1, ?_⟩
    intro v hv
    apply outer_neighbor_bags.1 v
    by_cases heq : v = 3
    · exact Or.inl heq
    · exact Or.inr (hS 3 v hx hv (fun h => heq h.symm))
  · by_cases hy : S 4
    · refine ⟨2, ?_⟩
      intro v hv
      apply outer_neighbor_bags.2.1 v
      by_cases heq : v = 4
      · exact Or.inl heq
      · exact Or.inr (hS 4 v hy hv (fun h => heq h.symm))
    · by_cases hz : S 5
      · refine ⟨3, ?_⟩
        intro v hv
        apply outer_neighbor_bags.2.2.1 v
        by_cases heq : v = 5
        · exact Or.inl heq
        · exact Or.inr (hS 5 v hz hv (fun h => heq h.symm))
      · refine ⟨0, ?_⟩
        intro v hv
        apply outer_neighbor_bags.2.2.2 v
        · intro h; subst v; exact hx hv
        · intro h; subst v; exact hy hv
        · intro h; subst v; exact hz hv

/-- No two different indices name the same clique. -/
theorem bags_distinct : ∀ b c : Fin 4,
    (∀ v, bag b v = bag c v) → b = c := by decide

theorem maximal_cliques_complete (S : V → Prop) :
    MaximalClique S ↔ ∃ b : Fin 4, S = bagSet b := by
  constructor
  · intro hS
    obtain ⟨b, hsub⟩ := clique_contained_in_bag S hS.1
    refine ⟨b, funext fun v => propext ⟨hsub v, hS.2 _ (bags_are_cliques b) hsub v⟩⟩
  · rintro ⟨b, rfl⟩
    exact bags_are_maximal b

theorem bagSet_injective : Function.Injective bagSet := by
  intro b c h
  apply bags_distinct b c
  intro v
  have hv : (bag b v = true) = (bag c v = true) := congrArg (fun f => f v) h
  cases hb : bag b v <;> cases hc : bag c v <;> simp_all

/-- A finite list of distinct sets, proved to enumerate all maximal cliques. -/
def maximalCliqueList : List (V → Prop) := List.ofFn bagSet

theorem maximalCliqueList_length : maximalCliqueList.length = 4 := by rfl

theorem maximalCliqueList_nodup : maximalCliqueList.Nodup := by
  change (([0, 1, 2, 3] : List (Fin 4)).map bagSet).Pairwise (· ≠ ·)
  exact List.Pairwise.map (R := (· ≠ ·)) bagSet (fun _ _ hne heq => hne (bagSet_injective heq)) (by decide)

theorem mem_maximalCliqueList (S : V → Prop) :
    S ∈ maximalCliqueList ↔ MaximalClique S := by
  rw [maximal_cliques_complete]
  simp only [maximalCliqueList, List.mem_ofFn]
  constructor <;> rintro ⟨b, hb⟩ <;> exact ⟨b, hb.symm⟩


/-- A finite walk using only vertices satisfying `allowed`. -/
inductive PathWithin {W : Type} (E : W → W → Prop) (allowed : W → Prop) : W → W → Prop
  | refl (v) : allowed v → PathWithin E allowed v v
  | step {v w u} : allowed v → E v w → PathWithin E allowed w u → PathWithin E allowed v u

def Connected {W : Type} (E : W → W → Prop) : Prop :=
  ∀ v w, PathWithin E (fun _ => True) v w

def Acyclic {W : Type} (E : W → W → Prop) : Prop :=
  ∀ n f, ¬ SimpleCycle E n f

/-- The counterexample graph itself is connected (in fact its diameter is two). -/
theorem threeSun_connected : Connected (fun v w => adj v w = true) := by
  have hpaths : ∀ v w : V, v = w ∨ adj v w = true ∨
      ∃ z, adj v z = true ∧ adj z w = true := by decide
  intro v w
  rcases hpaths v w with heq | hedge | ⟨z, hvz, hzw⟩
  · subst w; exact PathWithin.refl _ trivial
  · exact PathWithin.step trivial hedge (PathWithin.refl _ trivial)
  · exact PathWithin.step trivial hvz (PathWithin.step trivial hzw (PathWithin.refl _ trivial))

/-- The star on the four maximal-clique nodes, centered at C. -/
def starEdge (i j : Fin 4) : Prop := (i = 0 ∧ j ≠ 0) ∨ (j = 0 ∧ i ≠ 0)

theorem star_irrefl : ∀ i, ¬ starEdge i i := by unfold starEdge; decide
theorem star_symm : ∀ i j, starEdge i j → starEdge j i := by unfold starEdge; decide

theorem star_connected : Connected starEdge := by
  intro i j
  by_cases hij : i = j
  · subst j; exact PathWithin.refl _ trivial
  by_cases hi : i = 0
  · subst i
    exact PathWithin.step trivial (Or.inl ⟨rfl, fun h => hij h.symm⟩)
      (PathWithin.refl _ trivial)
  by_cases hj : j = 0
  · subst j
    exact PathWithin.step trivial (Or.inr ⟨rfl, hi⟩) (PathWithin.refl _ trivial)
  exact PathWithin.step trivial (Or.inr ⟨rfl, hi⟩)
    (PathWithin.step trivial (Or.inl ⟨rfl, hj⟩) (PathWithin.refl _ trivial))

theorem star_leaf_neighbor (i j : Fin 4) (hi : i ≠ 0) (h : starEdge i j) : j = 0 := by
  rcases h with ⟨h0, _⟩ | ⟨h0, _⟩
  · exact False.elim (hi h0)
  · exact h0

/-- A direct proof of the absence of simple cycles of every length. -/
theorem star_acyclic : Acyclic starEdge := by
  intro n f ⟨hn, hinj, hedge⟩
  have hzero : ∀ i, f i = 0 := by
    intro i
    by_cases hi : f i = 0
    · exact hi
    obtain ⟨j, k, hj, hk, hjk, _⟩ := cycle_neighbors hn i
    have hj0 := star_leaf_neighbor (f i) (f j) hi (hedge i j hj)
    have hk0 := star_leaf_neighbor (f i) (f k) hi (hedge i k hk)
    exact False.elim (hjk (hinj (hj0.trans hk0.symm)))
  let i0 : Fin n := ⟨0, by omega⟩
  let i1 : Fin n := ⟨1, by omega⟩
  have heq := hinj ((hzero i0).trans (hzero i1).symm)
  have := congrArg Fin.val heq
  simp [i0, i1] at this

theorem shared_vertex_in_center : ∀ v i j, i ≠ j →
    bag i v = true → bag j v = true → bag 0 v = true := by decide

/-- For each graph vertex, the bags containing it form a connected subtree. -/
theorem star_running_intersection : ∀ v i j,
    bagSet i v → bagSet j v → PathWithin starEdge (fun b => bagSet b v) i j := by
  intro v i j hiMem hjMem
  by_cases hij : i = j
  · subst j; exact PathWithin.refl _ hiMem
  have hcenter := shared_vertex_in_center v i j hij hiMem hjMem
  by_cases hi : i = 0
  · subst i
    exact PathWithin.step hiMem (Or.inl ⟨rfl, fun h => hij h.symm⟩)
      (PathWithin.refl _ hjMem)
  by_cases hj : j = 0
  · subst j
    exact PathWithin.step hiMem (Or.inr ⟨rfl, hi⟩) (PathWithin.refl _ hjMem)
  exact PathWithin.step hiMem (Or.inr ⟨rfl, hi⟩)
    (PathWithin.step hcenter (Or.inl ⟨rfl, hj⟩) (PathWithin.refl _ hjMem))

/-- Conventional clique tree: a tree with one node for each maximal clique,
    and connected bags for each graph vertex. -/
structure CliqueTree (B : Type) where
  edge : B → B → Prop
  irreflexive : ∀ b, ¬ edge b b
  symmetric : ∀ b c, edge b c → edge c b
  connected : Connected edge
  acyclic : Acyclic edge
  bags : B → V → Prop
  maximal : ∀ b, MaximalClique (bags b)
  complete : ∀ S, MaximalClique S → ∃ b, S = bags b
  distinct : Function.Injective bags
  running : ∀ v b c, bags b v → bags c v → PathWithin edge (fun d => bags d v) b c

def threeSunCliqueTree : CliqueTree (Fin 4) where
  edge := starEdge
  irreflexive := star_irrefl
  symmetric := star_symm
  connected := star_connected
  acyclic := star_acyclic
  bags := bagSet
  maximal := bags_are_maximal
  complete := fun S h => (maximal_cliques_complete S).mp h
  distinct := bagSet_injective
  running := star_running_intersection

/-- Enumeration of all tree nodes. The maximal-clique list is independently
    certified complete and without repetitions above. -/
def treeNodeList : List (Fin 4) := List.ofFn id

theorem treeNodeList_length : treeNodeList.length = 4 := by rfl
theorem treeNodeList_nodup : treeNodeList.Nodup := by decide
theorem treeNodeList_complete (b : Fin 4) : b ∈ treeNodeList := by
  exact List.mem_ofFn.mpr ⟨b, rfl⟩

universe u

/-- Only transitivity and totality are required; every linear order qualifies. -/
structure Line (A : Type u) where
  le : A → A → Prop
  trans : ∀ {a b c}, le a b → le b c → le a c
  total : ∀ a b, le a b ∨ le b a

def EndpointRepresentation {A : Type u} (L : Line A) (l r : V → A) : Prop :=
  (∀ i, L.le (l i) (r i)) ∧
  (∀ i j, i ≠ j → (adj i j = true ↔ (L.le (l i) (r j) ∧ L.le (l j) (r i))))
theorem not_interval_endpoints {A : Type u} (L : Line A) (l r : V → A) :
    ¬ EndpointRepresentation L l r := by
  intro ⟨hr, h⟩
  have h01 := h 0 1 (by decide)
  have h02 := h 0 2 (by decide)
  have h03 := h 0 3 (by decide)
  have h04 := h 0 4 (by decide)
  have h05 := h 0 5 (by decide)
  have h12 := h 1 2 (by decide)
  have h13 := h 1 3 (by decide)
  have h14 := h 1 4 (by decide)
  have h15 := h 1 5 (by decide)
  have h23 := h 2 3 (by decide)
  have h24 := h 2 4 (by decide)
  have h25 := h 2 5 (by decide)
  have h34 := h 3 4 (by decide)
  have h35 := h 3 5 (by decide)
  have h45 := h 4 5 (by decide)
  simp [adj, Fin.isValue] at h01 h02 h03 h04 h05 h12 h13 h14 h15 h23 h24 h25 h34 h35 h45
  have ht : ∀ a b c, L.le a b → L.le b c → L.le a c := fun _ _ _ => L.trans
  have hl := L.total
  grind

/-- Two closed intervals intersect in an actual point. -/
def Intersects {A : Type u} (L : Line A) (l r : V → A) (i j : V) : Prop :=
  ∃ p : A, L.le (l i) p ∧ L.le p (r i) ∧ L.le (l j) p ∧ L.le p (r j)

/-- An interval representation uses nonempty closed intervals and actual
    intersections, rather than assuming the endpoint-overlap criterion. -/
def IntervalRepresentation {A : Type u} (L : Line A) (l r : V → A) : Prop :=
  (∀ i, L.le (l i) (r i)) ∧
  (∀ i j, i ≠ j → (adj i j = true ↔ Intersects L l r i j))

theorem le_refl {A : Type u} (L : Line A) (a : A) : L.le a a := by
  rcases L.total a a with h | h <;> exact h

theorem intersects_iff_endpoints {A : Type u} (L : Line A) (l r : V → A)
    (hnonempty : ∀ i, L.le (l i) (r i)) (i j : V) :
    Intersects L l r i j ↔ (L.le (l i) (r j) ∧ L.le (l j) (r i)) := by
  constructor
  · rintro ⟨p, hip, hpi, hjp, hpj⟩
    exact ⟨L.trans hip hpj, L.trans hjp hpi⟩
  · rintro ⟨hij, hji⟩
    rcases L.total (l i) (l j) with h | h
    · exact ⟨l j, h, hji, le_refl L _, hnonempty j⟩
    · exact ⟨l i, le_refl L _, hnonempty i, h, hij⟩

theorem interval_iff_endpoints {A : Type u} (L : Line A) (l r : V → A) :
    IntervalRepresentation L l r ↔ EndpointRepresentation L l r := by
  constructor
  · rintro ⟨hn, he⟩
    exact ⟨hn, fun i j hij => (he i j hij).trans (intersects_iff_endpoints L l r hn i j)⟩
  · rintro ⟨hn, he⟩
    exact ⟨hn, fun i j hij => (he i j hij).trans (intersects_iff_endpoints L l r hn i j).symm⟩

theorem not_interval {A : Type u} (L : Line A) (l r : V → A) :
    ¬ IntervalRepresentation L l r := by
  intro h
  exact not_interval_endpoints L l r ((interval_iff_endpoints L l r).mp h)

/-- Existential interval representability on any line, in particular the real
    line. Proving its negation is stronger than restricting the endpoints to R. -/
def IsInterval : Prop :=
  ∃ (A : Type) (L : Line A) (l r : V → A), IntervalRepresentation L l r

theorem threeSun_not_interval : ¬ IsInterval := by
  rintro ⟨A, L, l, r, h⟩
  exact not_interval L l r h

def bagCount : Nat := treeNodeList.length
def maximalCliqueCount : Nat := maximalCliqueList.length

theorem bagCount_eq : bagCount = 4 := rfl
theorem maximalCliqueCount_eq : maximalCliqueCount = 4 := rfl

/-- The two specified clauses alone are incompatible on this chordal graph.
    No meaning is assigned to the undefined Helly covering genus. -/
theorem no_natural_genus : ¬ ∃ h : Nat,
    bagCount = maximalCliqueCount - h ∧ (h = 0 ↔ IsInterval) := by
  rintro ⟨h, hformula, hzero⟩
  have hz : h = 0 := by
    rw [bagCount_eq, maximalCliqueCount_eq] at hformula
    omega
  exact threeSun_not_interval (hzero.mp hz)

/-- The same contradiction also holds with ordinary signed subtraction. -/
theorem no_integer_genus : ¬ ∃ h : Int,
    (bagCount : Int) = (maximalCliqueCount : Int) - h ∧ (h = 0 ↔ IsInterval) := by
  rintro ⟨h, hformula, hzero⟩
  have hz : h = 0 := by
    rw [bagCount_eq, maximalCliqueCount_eq] at hformula
    omega
  exact threeSun_not_interval (hzero.mp hz)

/-- All hypotheses and both independent counts are certified together. -/
theorem full_counterexample :
    Chordal (fun v w => adj v w = true) ∧
    Connected (fun v w => adj v w = true) ∧
    (∃ T : CliqueTree (Fin 4), T.bags = bagSet ∧ T.edge = starEdge) ∧
    treeNodeList.Nodup ∧ (∀ b, b ∈ treeNodeList) ∧
    maximalCliqueList.Nodup ∧ (∀ S, S ∈ maximalCliqueList ↔ MaximalClique S) ∧
    bagCount = 4 ∧ maximalCliqueCount = 4 ∧ ¬ IsInterval ∧
    (¬ ∃ h : Nat, bagCount = maximalCliqueCount - h ∧ (h = 0 ↔ IsInterval)) ∧
    (¬ ∃ h : Int, (bagCount : Int) = (maximalCliqueCount : Int) - h ∧
      (h = 0 ↔ IsInterval)) := by
  exact ⟨threeSun_chordal, threeSun_connected, ⟨threeSunCliqueTree, rfl, rfl⟩,
    treeNodeList_nodup, treeNodeList_complete,
    maximalCliqueList_nodup, mem_maximalCliqueList,
    bagCount_eq, maximalCliqueCount_eq, threeSun_not_interval,
    no_natural_genus, no_integer_genus⟩

end C3484

#print axioms C3484.threeSun_chordal
#print axioms C3484.maximal_cliques_complete
#print axioms C3484.star_acyclic
#print axioms C3484.star_running_intersection
#print axioms C3484.threeSunCliqueTree
#print axioms C3484.threeSun_not_interval
#print axioms C3484.no_natural_genus
#print axioms C3484.no_integer_genus
#print axioms C3484.full_counterexample
