/-
  Refutation of conjecture 00000000471.

  K_n^{(3)} is the complete 3-uniform hypergraph on n vertices: its edge set
  consists of all C(n,3) triples.  A hypertree is a minimally connected
  subhypergraph of that edge set, and t(K_n^{(3)}) counts them.  The conjecture
  asserts the closed form

      t(K_n^{(3)}) = n^{C(n-1,2) - 1} * prod_{i=1}^{n-1} (i^2 - i + 1)

  and claims it covers all known values for n <= 6.

  We give two independent refutations.

  (1) A TRIVIAL COUNTING BOUND.  A hypertree is a subhypergraph, i.e. a subset
      of the C(n,3) edges, so t(K_n^{(3)}) <= 2^{C(n,3)}.  At n = 3 the formula
      gives 3 while there are only 2^{C(3,3)} = 2 subhypergraphs in total.  The
      same failure occurs at n = 4, 5 and 6; at n = 6 the formula exceeds the
      total number of subhypergraphs by a factor of more than 55,000.  This
      argument uses nothing whatsoever about connectedness or minimality, so it
      is immune to any disagreement about how those two words are read.

  (2) EXACT ENUMERATION.  At n = 3 the edge set has exactly one member, so the
      only connected subhypergraph is that single edge, and it is minimal:
      t(K_3^{(3)}) = 1 against the formula's 3.  Exhaustive search gives 6 at
      n = 4 (against 336) and 25 at n = 5 (against 853125).

  Both are formalised below.  (1) is the load-bearing one; (2) is offered as
  confirmation and because it pins down the actual values.
-/

namespace Tlmc471

/-! ## 1. The hypergraph

Vertices are natural numbers; a vertex of K_n^{(3)} is a number below n.  A
hyperedge is represented by the list of its vertices. -/

/-- All triples `(a,b,c)` of vertices below `n`, in the order used to enumerate
the edge set. -/
def triples (n : Nat) : List (Nat × Nat × Nat) :=
  (List.range n).flatMap fun a =>
  (List.range n).flatMap fun b =>
  (List.range n).map fun c => (a, b, c)

/-- The edge set of K_n^{(3)}: the strictly increasing triples `a < b < c`,
each listed once.  So a 3-subset is stored exactly once rather than six times. -/
def edges (n : Nat) : List (List Nat) :=
  ((triples n).filter fun p => p.1 < p.2.1 && p.2.1 < p.2.2).map
    fun p => [p.1, p.2.1, p.2.2]

/-- The powerset: all sublists, i.e. all subhypergraphs of the edge set. -/
def sublists {α : Type} : List α → List (List α)
  | [] => [[]]
  | x :: xs =>
      let rest := sublists xs
      rest ++ rest.map fun ys => x :: ys

/-- The powerset of an `m`-element set has `2^m` elements. -/
theorem sublists_length {α : Type} (l : List α) :
    (sublists l).length = 2 ^ l.length := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
      simp [sublists, ih, Nat.pow_succ]
      omega

/-! ## 2. Connectedness and minimality -/

/-- Add to `acc` every vertex of the edge `e` that is not already there. -/
def addAll (acc : List Nat) (e : List Nat) : List Nat :=
  e.foldl (fun a v => if a.contains v then a else v :: a) acc

/-- Does the edge `e` meet the vertex set `acc`? -/
def touches (acc : List Nat) (e : List Nat) : Bool :=
  e.any fun v => acc.contains v

/-- One round of closure: every edge meeting `acc` contributes all of its
vertices. -/
def step (es : List (List Nat)) (acc : List Nat) : List Nat :=
  es.foldl (fun a e => if touches a e then addAll a e else a) acc

/-- The vertex set reachable from vertex `0` after `k` rounds.  Each round adds
at least one new vertex unless a fixed point has been reached, so `n` rounds
suffice on `n` vertices. -/
def closureFrom (es : List (List Nat)) : Nat → List Nat
  | 0 => [0]
  | k + 1 => step es (closureFrom es k)

/-- A subhypergraph is connected when its edges cover every vertex and the
graph obtained by replacing each edge with a triangle on its vertices is
connected.  Both conditions amount to: the closure from `0` is everything. -/
def connected (n : Nat) (es : List (List Nat)) : Bool :=
  (closureFrom es n).length == n

/-- Drop the entry at index `i`. -/
def eraseAt {α : Type} : List α → Nat → List α
  | [], _ => []
  | _ :: xs, 0 => xs
  | x :: xs, i + 1 => x :: eraseAt xs i

/-- Minimally connected: connected, and deleting any one edge disconnects. -/
def minimalConnected (n : Nat) (es : List (List Nat)) : Bool :=
  connected n es &&
  (List.range es.length).all (fun i => !(connected n (eraseAt es i)))

/-- The hypertrees of K_n^{(3)}.  This is a filter of the powerset, which is
what makes the counting bound in section 4 true by construction. -/
def hypertrees (n : Nat) : List (List (List Nat)) :=
  (sublists (edges n)).filter (minimalConnected n)

/-- Filtering never lengthens a list. -/
theorem filter_length_le {α : Type} (p : α → Bool) (l : List α) :
    (l.filter p).length ≤ l.length := by
  induction l with
  | nil => exact Nat.le_refl _
  | cons x xs ih =>
      by_cases h : p x
      · simp [List.filter, h]
        exact ih
      · simp [List.filter, h]
        exact Nat.le_trans ih (Nat.le_succ _)

/-! ## 3. The conjectured formula -/

/-- The polynomial `f(i) = i^2 - i + 1`. -/
def f (i : Nat) : Nat := i * i - i + 1

/-- The binomial coefficient `C(m,2) = m(m-1)/2`. -/
def binom2 (m : Nat) : Nat := m * (m - 1) / 2

/-- The product of `f(1), ..., f(k)`. -/
def prodF : Nat → Nat
  | 0 => 1
  | k + 1 => prodF k * f (k + 1)

/-- The conjectured closed form for `t(K_n^{(3)})`. -/
def formula (n : Nat) : Nat := n ^ (binom2 (n - 1) - 1) * prodF (n - 1)

/- The recursion limit is raised because the kernel walks the candidate lists
in order to evaluate the enumeration theorems below. -/
set_option maxRecDepth 100000

/-! ## 4. Refutation (1): the counting bound

A hypertree is a subhypergraph, so there are at most `2^{C(n,3)}` of them. -/

/-- Every hypertree is a subhypergraph, hence the count is bounded by the
number of subhypergraphs. -/
theorem hypertrees_le_subhypergraphs (n : Nat) :
    (hypertrees n).length ≤ (sublists (edges n)).length := by
  unfold hypertrees
  exact filter_length_le (minimalConnected n) (sublists (edges n))

/-- K_3^{(3)} has one edge. -/
theorem edges3_length : (edges 3).length = 1 := rfl

/-- K_4^{(3)} has four edges. -/
theorem edges4_length : (edges 4).length = 4 := rfl

/-- K_5^{(3)} has ten edges. -/
theorem edges5_length : (edges 5).length = 10 := rfl

/-- K_6^{(3)} has twenty edges. -/
theorem edges6_length : (edges 6).length = 20 := rfl

/-- So K_3^{(3)} has exactly two subhypergraphs. -/
theorem subhypergraphs3 : (sublists (edges 3)).length = 2 := rfl

/-- The formula at n = 3 is 3. -/
theorem formula3 : formula 3 = 3 := rfl

/-- The formula at n = 6 is 57,775,431,168. -/
theorem formula6 : formula 6 = 57775431168 := rfl

/-- **Refutation (1) at n = 3.** The formula claims more hypertrees than there
are subhypergraphs, which is impossible regardless of how "connected" and
"minimal" are read. -/
theorem refutation_bound_3 : formula 3 > (hypertrees 3).length := by
  have hle := hypertrees_le_subhypergraphs 3
  have hsub : (sublists (edges 3)).length = 2 := subhypergraphs3
  have hf : formula 3 = 3 := formula3
  omega

/-- **Refutation (1) at n = 6.** Here the formula overshoots the total number
of subhypergraphs by a factor of more than 55,000. -/
theorem refutation_bound_6 : formula 6 > (sublists (edges 6)).length := by
  rw [sublists_length, edges6_length, formula6]
  decide

/-! ## 5. Refutation (2): exact enumeration -/

/-- K_3^{(3)} has exactly one hypertree: its single edge. -/
theorem hypertrees3_length : (hypertrees 3).length = 1 := rfl

/-- That hypertree is the whole edge set. -/
theorem hypertrees3_eq : hypertrees 3 = [[[0, 1, 2]]] := rfl

/-- K_4^{(3)} has exactly six hypertrees. -/
theorem hypertrees4_length : (hypertrees 4).length = 6 := rfl

/-- The formula at n = 4 is 336. -/
theorem formula4 : formula 4 = 336 := rfl

/-- The formula at n = 5 is 853125. -/
theorem formula5 : formula 5 = 853125 := rfl

/-- **Refutation (2) at n = 3:** 3 is not 1. -/
theorem refutation_exact_3 : formula 3 ≠ (hypertrees 3).length := by
  rw [formula3, hypertrees3_length]
  decide

/-- **Refutation (2) at n = 4:** 336 is not 6. -/
theorem refutation_exact_4 : formula 4 ≠ (hypertrees 4).length := by
  rw [formula4, hypertrees4_length]
  decide

/- The n = 5 case enumerates 2^10 = 1024 subhypergraphs and runs a closure
computation on each, which needs more than the default heartbeat budget. -/
set_option maxHeartbeats 0

/-- K_5^{(3)} has exactly twenty-five hypertrees. -/
theorem hypertrees5_length : (hypertrees 5).length = 25 := rfl

/-- **Refutation (2) at n = 5:** 853125 is not 25. -/
theorem refutation_exact_5 : formula 5 ≠ (hypertrees 5).length := by
  rw [formula5, hypertrees5_length]
  decide

/-! ## 6. The two refutations agree, and the bound is the sharper one -/

/-- The enumeration confirms what the bound already forces: at n = 3 the true
count is 1, well inside the bound of 2, while the formula sits outside it. -/
theorem summary_3 :
    (hypertrees 3).length = 1 ∧ (sublists (edges 3)).length = 2 ∧
    formula 3 = 3 ∧ (hypertrees 3).length ≤ (sublists (edges 3)).length := by
  exact ⟨hypertrees3_length, subhypergraphs3, formula3,
         hypertrees_le_subhypergraphs 3⟩

end Tlmc471
