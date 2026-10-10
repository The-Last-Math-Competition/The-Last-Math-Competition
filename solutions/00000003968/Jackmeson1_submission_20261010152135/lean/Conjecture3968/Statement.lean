import Mathlib

/-! Formal statement for Conjecture3968: definitions only, ending in `Claim`. Split verbatim from the marked block of `Basic.lean`. -/

-- STATEMENT BEGIN
namespace C3968
open SimpleGraph

/-- "caterpillar tree": a tree having a path (the spine, an induced path subgraph isomorphic to
`pathGraph k`) such that every vertex lies on it or is adjacent to it (equivalently, deleting all
leaves leaves a path). -/
def IsCaterpillar {V : Type*} (G : SimpleGraph V) : Prop :=
  ∃ (k : ℕ) (S : Set V), Nonempty (G.induce S ≃g pathGraph k) ∧
    ∀ w, w ∈ S ∨ ∃ x ∈ S, G.Adj w x

/-- "A graceful labeling ... is a bijective labeling whose edge differences are exactly 1 through
n-1": `f : V ≃ {0,..,n-1}` and, for each `d ∈ [1, n-1]`, exactly one edge `{u, v}` of `G` has labels
differing by `d` (the smaller label `u` determines the edge, as `v = u + d`). -/
def IsGraceful {V : Type*} {n : ℕ} (G : SimpleGraph V) (f : V ≃ Fin n) : Prop :=
  ∀ d, 1 ≤ d → d ≤ n - 1 →
    ∃! u : Fin n, ∃ v : Fin n, G.Adj (f.symm u) (f.symm v) ∧ (v : ℕ) = u + d

/-- "n-vertex caterpillar trees" (vertex set `Fin n`). -/
def CatTree (n : ℕ) : Type := {G : SimpleGraph (Fin n) // G.IsTree ∧ IsCaterpillar G}

/-- Caterpillar trees are identified up to graph isomorphism. -/
instance isoSetoid (n : ℕ) : Setoid (CatTree n) where
  r G H := Nonempty (G.1 ≃g H.1)
  iseqv := ⟨fun _ => ⟨Iso.refl⟩, fun ⟨e⟩ => ⟨e.symm⟩, fun ⟨e⟩ ⟨e'⟩ => ⟨e.trans e'⟩⟩

/-- Convention A: "number of graceful labelings of n-vertex caterpillar trees" = sum over isomorphism
classes of caterpillars (one representative each) of the number of graceful bijections to `{0..n-1}`. -/
noncomputable def classCount (n : ℕ) : ℕ :=
  Nat.card (Σ c : Quotient (isoSetoid n), {f : Fin n ≃ Fin n // IsGraceful (Quotient.out c).1 f})

/-- Convention B: pairs (caterpillar tree on the vertex set `{0..n-1}`, graceful bijection). -/
noncomputable def pairCount (n : ℕ) : ℕ :=
  Nat.card {p : CatTree n × (Fin n ≃ Fin n) // IsGraceful p.1.1 p.2}

/-- Convention C: labelings counted up to automorphism, i.e. graceful caterpillar edge sets on the
label set `{0..n-1}` (the vertex IS its label). -/
noncomputable def edgeSetCount (n : ℕ) : ℕ :=
  Nat.card {G : CatTree n // IsGraceful G.1 (Equiv.refl (Fin n))}

/-- Convention D: as C, but a labeling and its complement `x ↦ n-1-x` are identified (the class of
an edge set `G` is the set `{G, G.comap Fin.rev}`); counts such classes. -/
noncomputable def complementCount (n : ℕ) : ℕ :=
  Nat.card {S : Set (SimpleGraph (Fin n)) //
    ∃ G : CatTree n, IsGraceful G.1 (Equiv.refl (Fin n)) ∧
      S = {G.1, G.1.comap (Fin.revPerm : Equiv.Perm (Fin n))}}

/-- A power series is a rational function: `Q * A = P` for polynomials with `Q ≠ 0`. -/
def Rational (a : ℕ → ℕ) : Prop :=
  ∃ P Q : Polynomial ℚ, Q ≠ 0 ∧
    (Q : PowerSeries ℚ) * PowerSeries.mk (fun n => (a n : ℚ)) = (P : PowerSeries ℚ)

/-- "The generating function of the number of graceful labelings ... is a rational function"
(the denominator clause about the partition function is not formalized; refuting rationality
refutes the conjunction). The coefficient of `z^n` is the count for `n` vertices. -/
def Conjecture (a : ℕ → ℕ) : Prop := Rational a

/-- What this package proves: under each of the four counting conventions the ordinary generating
function is not rational. -/
def Claim : Prop :=
  ¬ Conjecture classCount ∧ ¬ Conjecture pairCount ∧ ¬ Conjecture edgeSetCount ∧
    ¬ Conjecture complementCount

end C3968
-- STATEMENT END
