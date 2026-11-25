import Conjecture00000000505.Ring
import Conjecture00000000505.Module
import Conjecture00000000505.Poly
import Conjecture00000000505.DimensionDepth

namespace Conjecture00000000505

open Classical

/-- Finite simple graph on `n` vertices `Fin n`. -/
structure SimpleGraph (n : Nat) where
  adj : Fin n → Fin n → Prop
  symm : ∀ {u v : Fin n}, adj u v → adj v u
  loopless : ∀ u : Fin n, ¬ adj u u

/-- Predicate asserting that `G` has at least one edge (`E(G) ≠ ∅`). -/
def SimpleGraph.HasEdge {n : Nat} (G : SimpleGraph n) : Prop :=
  ∃ u v : Fin n, G.adj u v

/-- Ordered pairs `(u, v)` with `u < v` representing the undirected edges of `G`. -/
noncomputable def SimpleGraph.edgePairs {n : Nat} (G : SimpleGraph n) : List (Fin n × Fin n) :=
  ((finRangeList n).flatMap (fun u => (finRangeList n).map (fun v => (u, v)))).filter
    (fun p => decide (p.1.val < p.2.val ∧ G.adj p.1 p.2))

/-- Quadratic monomial generators `{ X_u X_v : {u, v} ∈ E(G) }` of the edge ideal `I(G)`. -/
noncomputable def edgeGenerators (K : Type u) [CAlgRing K] {n : Nat} (G : SimpleGraph n) :
    List (MPoly n K) :=
  G.edgePairs.map (fun p => MPoly.var (K := K) p.1 * MPoly.var (K := K) p.2)

/-- The edge ideal `I(G) = (X_u X_v : {u, v} ∈ E(G)) ⊆ K[X_0, ..., X_{n-1}]`. -/
noncomputable def edgeIdeal (K : Type u) [CAlgRing K] {n : Nat} (G : SimpleGraph n) :
    Ideal (MPoly n K) :=
  Ideal.span (edgeGenerators K G)

theorem mem_edgeIdeal_of_adj {K : Type u} [CAlgRing K] {n : Nat} (G : SimpleGraph n)
    {u v : Fin n} (h : G.adj u v) :
    MPoly.var (K := K) u * MPoly.var (K := K) v ∈ edgeIdeal K G := by
  have hne : u ≠ v := fun heq => by subst heq; exact G.loopless u h
  by_cases hlt : u.val < v.val
  · apply Ideal.mem_span_of_mem
    unfold edgeGenerators
    rw [List.mem_map]
    refine ⟨(u, v), ?_, rfl⟩
    unfold SimpleGraph.edgePairs
    rw [List.mem_filter]
    refine ⟨?_, decide_eq_true ⟨hlt, h⟩⟩
    rw [List.mem_flatMap]
    exact ⟨u, mem_finRangeList u, List.mem_map_of_mem (mem_finRangeList v)⟩
  · have hvlt : v.val < u.val := by
      have hval_ne : u.val ≠ v.val := fun hv => hne (Fin.ext hv)
      omega
    rw [r_mul_comm]
    apply Ideal.mem_span_of_mem
    unfold edgeGenerators
    rw [List.mem_map]
    refine ⟨(v, u), ?_, rfl⟩
    unfold SimpleGraph.edgePairs
    rw [List.mem_filter]
    refine ⟨?_, decide_eq_true ⟨hvlt, G.symm h⟩⟩
    rw [List.mem_flatMap]
    exact ⟨v, mem_finRangeList v, List.mem_map_of_mem (mem_finRangeList u)⟩

/-- `G` is a Cohen–Macaulay graph over `K` iff `K[X_0, ..., X_{n-1}] / I(G)` is Cohen–Macaulay. -/
def IsCohenMacaulayGraph (K : Type u) [CAlgField K] {n : Nat} (G : SimpleGraph n) : Prop :=
  IsCohenMacaulayQuot n K (edgeIdeal K G)

/-- Conjecture 00000000505 under Convention 1 (standard quotient projective dimension
`pd = pd_R(R / I(G))`), restricted to graphs with at least one edge (`E(G) ≠ ∅`). -/
def Conjecture505_QuotientPD_NonEmpty (K : Type u) [CAlgField K] : Prop :=
  ∀ (n : Nat) (G : SimpleGraph n) (ara pd : Nat),
    G.HasEdge →
    IsArithmeticalRank (MPoly n K) (edgeIdeal K G) ara →
    IsProjDim (MPoly n K) (QuotientMod (MPoly n K) (edgeIdeal K G)) pd →
    ara ≤ pd + 1 ∧ (IsCohenMacaulayGraph K G → ara = pd + 1)

/-- Conjecture 00000000505 under Convention 1 (`pd = pd_R(R / I(G))`) for all finite graphs. -/
def Conjecture505_QuotientPD (K : Type u) [CAlgField K] : Prop :=
  ∀ (n : Nat) (G : SimpleGraph n) (ara pd : Nat),
    IsArithmeticalRank (MPoly n K) (edgeIdeal K G) ara →
    IsProjDim (MPoly n K) (QuotientMod (MPoly n K) (edgeIdeal K G)) pd →
    ara ≤ pd + 1 ∧ (IsCohenMacaulayGraph K G → ara = pd + 1)

/-- Conjecture 00000000505 under Convention 2 (ideal-module projective dimension
`pd = pd_R(I(G))`) for finite simple graphs on `n ≥ 1` vertices. -/
def Conjecture505_IdealPD (K : Type u) [CAlgField K] : Prop :=
  ∀ (n : Nat) (G : SimpleGraph n) (ara pd : Nat),
    1 ≤ n →
    IsArithmeticalRank (MPoly n K) (edgeIdeal K G) ara →
    IsProjDim (MPoly n K) (IdealMod (MPoly n K) (edgeIdeal K G)) pd →
    ara ≤ pd + 1 ∧ (IsCohenMacaulayGraph K G → ara = pd + 1)

/-! ### Section 1: Disproof of Convention 2 (`pd = pd_R(I(G))`) via `G = K̄_1` (`n = 1`) -/

def edgeless1 : SimpleGraph 1 where
  adj _ _ := False
  symm h := h
  loopless _ h := h

theorem edgeless1_edgeIdeal_eq (K : Type u) [CAlgRing K] :
    edgeIdeal K edgeless1 = Ideal.span [] := by
  have hpairs : edgeless1.edgePairs = [] := by
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro p hp
    unfold SimpleGraph.edgePairs at hp
    rw [List.mem_filter] at hp
    have hdec := of_decide_eq_true hp.2
    exact hdec.2
  unfold edgeIdeal edgeGenerators
  rw [hpairs]
  rfl

theorem edgeless1_ara (K : Type u) [CAlgField K] :
    IsArithmeticalRank (MPoly 1 K) (edgeIdeal K edgeless1) 0 := by
  rw [edgeless1_edgeIdeal_eq]
  refine ⟨⟨[], rfl, fun _ => Iff.rfl⟩, ?_⟩
  intro s hs
  omega

theorem edgeless1_ideal_pd (K : Type u) [CAlgField K] :
    IsProjDim (MPoly 1 K) (IdealMod (MPoly 1 K) (edgeIdeal K edgeless1)) 0 := by
  rw [edgeless1_edgeIdeal_eq]
  let R := MPoly 1 K
  refine ⟨?_, fun e he => by omega⟩
  change IsProjective R (IdealMod R (Ideal.span []))
  refine ⟨0,
    ⟨fun _ => fun i => Fin.elim0 i,
      fun _ _ => funext (fun i => Fin.elim0 i),
      fun _ _ => funext (fun i => Fin.elim0 i)⟩,
    ⟨fun _ => ⟨0, rfl⟩,
      fun _ _ => Subtype.ext (r_add_zero 0).symm,
      fun r _ => Subtype.ext (r_mul_zero r).symm⟩,
    ?_⟩
  intro x
  apply Subtype.ext
  exact x.property.symm

theorem poly_zero_ideal_isPrime (K : Type u) [CAlgField K] :
    Ideal.IsPrime (Ideal.span ([] : List (Poly K))) := by
  have hdom := Poly.isDomain (CAlgField.isDomain K)
  refine ⟨hdom.one_ne_zero, fun a b hab => ?_⟩
  exact hdom.mul_eq_zero hab

theorem poly_X_ideal_isPrime (K : Type u) [CAlgField K] :
    Ideal.IsPrime (Ideal.span ([Poly.X] : List (Poly K))) := by
  have hdom := CAlgField.isDomain K
  refine ⟨fun h1 => ?_, fun a b hab => ?_⟩
  · rw [Poly.mem_span_X_iff, Poly.eval_one] at h1
    exact hdom.one_ne_zero h1
  · rw [Poly.mem_span_X_iff, Poly.eval_mul] at hab
    cases hdom.mul_eq_zero hab with
    | inl ha => exact Or.inl ((Poly.mem_span_X_iff a).mpr ha)
    | inr hb => exact Or.inr ((Poly.mem_span_X_iff b).mpr hb)

theorem mpoly1_maxIdeal_iff (K : Type u) [CAlgRing K] (f : MPoly 1 K) :
    f ∈ MPoly.maxIdeal 1 K ↔ f ∈ Ideal.span ([Poly.X] : List (Poly K)) := by
  have hvars : MPoly.varsList 1 K = [(Poly.X : Poly K)] := rfl
  unfold MPoly.maxIdeal
  rw [hvars]

theorem edgeless1_cm (K : Type u) [CAlgField K] :
    IsCohenMacaulayGraph K edgeless1 := by
  unfold IsCohenMacaulayGraph IsCohenMacaulayQuot
  rw [edgeless1_edgeIdeal_eq]
  have hdomK := CAlgField.isDomain K
  have hdomP := Poly.isDomain hdomK
  have hX_ne : (Poly.X : Poly K) ≠ 0 := by
    intro h
    have h1 : (Poly.X : Poly K).val 1 = (0 : Poly K).val 1 := congrArg (fun p => p.val 1) h
    exact hdomK.one_ne_zero h1
  refine ⟨hdomP.one_ne_zero, 1, ?_, ?_⟩
  · -- Krull dimension = 1
    constructor
    · let chain : Fin 2 → Ideal (Poly K)
        | ⟨0, _⟩ => Ideal.span []
        | ⟨1, _⟩ => Ideal.span [Poly.X]
      refine ⟨chain, fun x hx => hx, ?_, ?_⟩
      · intro i
        match i with
        | ⟨0, _⟩ => exact poly_zero_ideal_isPrime K
        | ⟨1, _⟩ => exact poly_X_ideal_isPrime K
      · intro i
        match i with
        | ⟨0, _⟩ =>
          refine ⟨fun x hx => ?_, Poly.X, Ideal.mem_span_head Poly.X [], hX_ne⟩
          change x = 0 at hx
          rw [hx]
          exact (Ideal.span [Poly.X]).zero_mem
    · intro e he ⟨chain, _, hprimes, hstrict⟩
      have h01 : Ideal.StrictSubset (chain ⟨0, by omega⟩) (chain ⟨1, by omega⟩) :=
        hstrict ⟨0, by omega⟩
      have h12 : Ideal.StrictSubset (chain ⟨1, by omega⟩) (chain ⟨2, by omega⟩) :=
        hstrict ⟨1, by omega⟩
      exact Poly.no_prime_chain_len_two (hprimes ⟨1, by omega⟩) (hprimes ⟨2, by omega⟩) h01 h12
  · -- Depth = 1
    constructor
    · refine ⟨[(Poly.X : Poly K)], rfl, ?_, ?_⟩
      · intro r hr
        cases hr with
        | head => exact (mpoly1_maxIdeal_iff K Poly.X).mpr (Ideal.mem_span_head Poly.X [])
        | tail _ h => cases h
      · refine ⟨fun f hf => ?_, ?_⟩
        · change Poly.X * f = 0 at hf
          cases hdomP.mul_eq_zero hf with
          | inl hX0 => exact False.elim (hX_ne hX0)
          | inr hf0 => exact hf0
        · rintro ⟨a, b, ha, hb, h1⟩
          change a = 0 at ha
          rw [ha, r_zero_add] at h1
          have hbX : (1 : Poly K) ∈ Ideal.span [Poly.X] := by rw [h1]; exact hb
          rw [Poly.mem_span_X_iff, Poly.eval_one] at hbX
          exact hdomK.one_ne_zero hbX
    · intro e he ⟨seq, hlen, hmem, hreg⟩
      match seq with
      | [] => simp at hlen; omega
      | [_] => simp at hlen; omega
      | r1 :: r2 :: tail =>
        rcases hreg with ⟨hreg1, hreg2, _⟩
        have hr1m : r1 ∈ Ideal.span ([Poly.X] : List (Poly K)) :=
          (mpoly1_maxIdeal_iff K r1).mp (hmem r1 (List.Mem.head _))
        have hr2m : r2 ∈ Ideal.span ([Poly.X] : List (Poly K)) :=
          (mpoly1_maxIdeal_iff K r2).mp (hmem r2 (List.Mem.tail _ (List.Mem.head _)))
        have hr1_eq : r1 = Poly.X * Poly.shift r1 := by
          have hd := Poly.eq_C_add_X_mul_shift r1
          have h0 : r1.val 0 = 0 := by
            rw [← Poly.eval_zero_eq_const]
            exact (Poly.mem_span_X_iff r1).mp hr1m
          rw [h0] at hd
          have hc0 : (Poly.C (0 : K)) = 0 := by
            apply Poly.ext; intro d
            change (if d = 0 then (0 : K) else 0) = 0
            by_cases hd0 : d = 0 <;> simp [hd0]
          rw [hc0, r_zero_add] at hd
          exact hd
        have hr2_eq : r2 = Poly.X * Poly.shift r2 := by
          have hd := Poly.eq_C_add_X_mul_shift r2
          have h0 : r2.val 0 = 0 := by
            rw [← Poly.eval_zero_eq_const]
            exact (Poly.mem_span_X_iff r2).mp hr2m
          rw [h0] at hd
          have hc0 : (Poly.C (0 : K)) = 0 := by
            apply Poly.ext; intro d
            change (if d = 0 then (0 : K) else 0) = 0
            by_cases hd0 : d = 0 <;> simp [hd0]
          rw [hc0, r_zero_add] at hd
          exact hd
        let u : Poly K := Poly.shift r1
        let v : Poly K := Poly.shift r2
        have hr1_u : r1 = Poly.X * u := hr1_eq
        have hr2_v : r2 = Poly.X * v := hr2_eq
        have hu_ne : u ≠ 0 := by
          intro hu0
          have hr10 : r1 = 0 := by
            rw [hr1_u, hu0, r_mul_zero]
          have h10 : (1 : Poly K) ∈ Ideal.span [] := hreg1 1 (by
            change r1 * 1 = 0
            rw [hr10, r_zero_mul])
          exact hdomP.one_ne_zero h10
        have hann : r2 * u ∈ Ideal.sum (Ideal.span []) (Ideal.span [r1]) := by
          refine ⟨0, v * r1, rfl, ⟨v, 0, rfl, by rw [r_add_zero]⟩, ?_⟩
          rw [r_zero_add, hr2_v, hr1_u]
          change (Poly.X * v) * u = v * (Poly.X * u)
          rw [r_mul_comm Poly.X v, r_mul_assoc]
        have hu_mem : u ∈ Ideal.sum (Ideal.span []) (Ideal.span [r1]) := hreg2 u hann
        rcases hu_mem with ⟨a, b, ha, ⟨q, z, hz, hb⟩, hueq⟩
        change a = 0 at ha
        change z = 0 at hz
        rw [ha, r_zero_add, hb, hz, r_add_zero, hr1_u] at hueq
        have hcancel : u * (q * Poly.X) = u * 1 := by
          calc
            u * (q * Poly.X) = q * (Poly.X * u) := by
              rw [r_mul_comm u (q * Poly.X), r_mul_assoc]
            _ = u := hueq.symm
            _ = u * 1 := (r_mul_one u).symm
        have hqX : q * Poly.X = 1 := IsDomain.mul_left_cancel hdomP hu_ne hcancel
        have hev := congrArg (fun p => Poly.eval p 0) hqX
        dsimp only at hev
        rw [Poly.eval_mul, Poly.eval_X, r_mul_zero, Poly.eval_one] at hev
        exact hdomK.one_ne_zero hev.symm

/-- Disproof of Conjecture 00000000505 under Convention 2 (`pd = pd_R(I(G))`) over every field `K`. -/
theorem disproof_conjecture505_idealPD (K : Type u) [CAlgField K] :
    ¬ Conjecture505_IdealPD K := by
  intro hconj
  have h := hconj 1 edgeless1 0 0 (Nat.le_refl 1) (edgeless1_ara K) (edgeless1_ideal_pd K)
  have heq : 0 = 0 + 1 := h.2 (edgeless1_cm K)
  omega

/-! ### Section 2: Disproof of Convention 1 (`pd = pd_R(R / I(G))`) via `G = K_2` (`n = 2`) -/

/-- The complete graph `K_2` on `2` vertices with a single undirected edge `{0, 1}`. -/
def K2Graph : SimpleGraph 2 where
  adj u v := u ≠ v
  symm h := Ne.symm h
  loopless _ h := h rfl

theorem K2Graph_adj_01 : K2Graph.adj ⟨0, by omega⟩ ⟨1, by omega⟩ :=
  fun h => Nat.noConfusion (congrArg Fin.val h)

theorem K2Graph_hasEdge : K2Graph.HasEdge :=
  ⟨⟨0, by omega⟩, ⟨1, by omega⟩, K2Graph_adj_01⟩

abbrev X0_2 (K : Type u) [CAlgRing K] : MPoly 2 K :=
  MPoly.var (n := 2) (K := K) ⟨0, by omega⟩

abbrev X1_2 (K : Type u) [CAlgRing K] : MPoly 2 K :=
  MPoly.var (n := 2) (K := K) ⟨1, by omega⟩

abbrev m01 (K : Type u) [CAlgRing K] : MPoly 2 K :=
  X0_2 K * X1_2 K

theorem X0_2_eq (K : Type u) [CAlgRing K] :
    X0_2 K = Poly.C (Poly.X : Poly K) := rfl

theorem X1_2_eq (K : Type u) [CAlgRing K] :
    X1_2 K = (Poly.X : Poly (Poly K)) := rfl

theorem K2_edgeIdeal_eq (K : Type u) [CAlgRing K] :
    edgeIdeal K K2Graph = Ideal.span [m01 K] := by
  have hpairs : K2Graph.edgePairs = [(⟨0, by omega⟩, ⟨1, by omega⟩)] := by
    let pred : Fin 2 × Fin 2 → Bool :=
      fun p => decide (p.1.val < p.2.val ∧ K2Graph.adj p.1 p.2)
    have h00 : ¬ (pred (⟨0, by omega⟩, ⟨0, by omega⟩) = true) := by
      intro ht
      have hc : (0 : Nat) < 0 ∧ _ := of_decide_eq_true ht
      omega
    have h01 : pred (⟨0, by omega⟩, ⟨1, by omega⟩) = true :=
      decide_eq_true ⟨(by omega : (0 : Nat) < 1), K2Graph_adj_01⟩
    have h10 : ¬ (pred (⟨1, by omega⟩, ⟨0, by omega⟩) = true) := by
      intro ht
      have hc : (1 : Nat) < 0 ∧ _ := of_decide_eq_true ht
      omega
    have h11 : ¬ (pred (⟨1, by omega⟩, ⟨1, by omega⟩) = true) := by
      intro ht
      have hc : (1 : Nat) < 1 ∧ _ := of_decide_eq_true ht
      omega
    change List.filter pred
      [(⟨0, by omega⟩, ⟨0, by omega⟩), (⟨0, by omega⟩, ⟨1, by omega⟩),
       (⟨1, by omega⟩, ⟨0, by omega⟩), (⟨1, by omega⟩, ⟨1, by omega⟩)] = _
    rw [List.filter_cons_of_neg h00, List.filter_cons_of_pos h01,
        List.filter_cons_of_neg h10, List.filter_cons_of_neg h11, List.filter_nil]
  unfold edgeIdeal edgeGenerators
  rw [hpairs]
  rfl

/-- Specialization `evY0 : K[X_0, X_1] → K[X_0]` setting `X_1 ↦ 0`. -/
noncomputable def evY0 {K : Type u} [CAlgRing K] (f : MPoly 2 K) : Poly K :=
  Poly.eval (R := Poly K) f 0

/-- Specialization `evX0 : K[X_0, X_1] → K[X_1] ≅ Poly K` setting `X_0 ↦ 0`. -/
def evX0 {K : Type u} [CAlgRing K] (f : MPoly 2 K) : Poly K :=
  ⟨fun d => (f.val d).val 0, by
    rcases f.property with ⟨Bf, hf⟩
    refine ⟨Bf, fun d hd => ?_⟩
    dsimp only
    rw [hf d hd]
    rfl⟩

/-- Section `secY0 : Poly K → MPoly 2 K` (`g ↦ g(X_0)`). -/
def secY0 {K : Type u} [CAlgRing K] (g : Poly K) : MPoly 2 K :=
  Poly.C g

/-- Section `secX0 : Poly K → MPoly 2 K` (`g ↦ g(X_1)`). -/
def secX0 {K : Type u} [CAlgRing K] (g : Poly K) : MPoly 2 K :=
  ⟨fun d => Poly.C (g.val d), by
    rcases g.property with ⟨Bg, hg⟩
    refine ⟨Bg, fun d hd => ?_⟩
    dsimp only
    rw [hg d hd]
    apply Poly.ext; intro i
    change (if i = 0 then (0 : K) else 0) = 0
    by_cases hi : i = 0 <;> simp [hi]⟩

section TwoVarLemmas
variable {K : Type u} [CAlgRing K]

theorem evY0_zero : evY0 (0 : MPoly 2 K) = 0 := Poly.eval_zero 0
theorem evY0_one : evY0 (1 : MPoly 2 K) = 1 := Poly.eval_one 0
theorem evY0_add (f g : MPoly 2 K) : evY0 (f + g) = evY0 f + evY0 g := Poly.eval_add f g 0
theorem evY0_sub (f g : MPoly 2 K) : evY0 (f - g) = evY0 f - evY0 g := Poly.eval_sub f g 0
theorem evY0_mul (f g : MPoly 2 K) : evY0 (f * g) = evY0 f * evY0 g := Poly.eval_mul f g 0
theorem evY0_eq_val0 (f : MPoly 2 K) : evY0 f = f.val 0 := Poly.eval_zero_eq_const f

theorem evY0_rpow (f : MPoly 2 K) : ∀ m : Nat, evY0 (rpow f m) = rpow (evY0 f) m
  | 0 => evY0_one
  | m + 1 => by rw [rpow_succ, rpow_succ, evY0_mul, evY0_rpow f m]

theorem evX0_zero : evX0 (0 : MPoly 2 K) = 0 := Poly.ext (fun _ => rfl)

theorem evX0_one : evX0 (1 : MPoly 2 K) = 1 := by
  apply Poly.ext; intro d
  change ((if d = 0 then (1 : Poly K) else 0).val 0) = (if d = 0 then (1 : K) else 0)
  by_cases hd : d = 0
  · subst hd; rfl
  · simp [hd]; rfl

theorem evX0_add (f g : MPoly 2 K) : evX0 (f + g) = evX0 f + evX0 g :=
  Poly.ext (fun _ => rfl)

theorem evX0_neg (f : MPoly 2 K) : evX0 (-f) = -(evX0 f) :=
  Poly.ext (fun _ => rfl)

theorem evX0_sub (f g : MPoly 2 K) : evX0 (f - g) = evX0 f - evX0 g :=
  Poly.ext (fun _ => rfl)

theorem finSum_val0 : ∀ (n : Nat) (F : Nat → Poly K),
    (finSum n F).val 0 = finSum n (fun i => (F i).val 0)
  | 0, _ => rfl
  | n + 1, F => by
    change (finSum n F + F n).val 0 = finSum n (fun i => (F i).val 0) + (F n).val 0
    change (finSum n F).val 0 + (F n).val 0 = _
    rw [finSum_val0 n F]

theorem poly_mul_val0 (a b : Poly K) : (a * b).val 0 = a.val 0 * b.val 0 := by
  change (finSum 1 (fun i => a.val i * b.val (0 - i))) = a.val 0 * b.val 0
  change (0 : K) + a.val 0 * b.val 0 = a.val 0 * b.val 0
  exact r_zero_add _

theorem evX0_mul (f g : MPoly 2 K) : evX0 (f * g) = evX0 f * evX0 g := by
  apply Poly.ext; intro d
  change (finSum (d + 1) (fun i => f.val i * g.val (d - i))).val 0 =
    finSum (d + 1) (fun i => (f.val i).val 0 * (g.val (d - i)).val 0)
  rw [finSum_val0]
  exact finSum_congr (d + 1) (fun i _ => poly_mul_val0 (f.val i) (g.val (d - i)))

theorem evX0_rpow (f : MPoly 2 K) : ∀ m : Nat, evX0 (rpow f m) = rpow (evX0 f) m
  | 0 => evX0_one
  | m + 1 => by rw [rpow_succ, rpow_succ, evX0_mul, evX0_rpow f m]

theorem evY0_X0 : evY0 (X0_2 K) = Poly.X := by
  rw [X0_2_eq]; exact Poly.eval_C Poly.X 0

theorem evY0_X1 : evY0 (X1_2 K) = 0 := by
  rw [X1_2_eq]; exact Poly.eval_X 0

theorem evX0_X0 : evX0 (X0_2 K) = 0 := by
  apply Poly.ext; intro d
  change ((if d = 0 then (Poly.X : Poly K) else 0).val 0) = 0
  by_cases hd : d = 0
  · subst hd; rfl
  · simp [hd]; rfl

theorem evX0_X1 : evX0 (X1_2 K) = Poly.X := by
  apply Poly.ext; intro d
  change ((if d = 1 then (1 : Poly K) else 0).val 0) = (if d = 1 then (1 : K) else 0)
  by_cases hd : d = 1
  · subst hd; rfl
  · simp [hd]; rfl

theorem evY0_secY0 (g : Poly K) : evY0 (secY0 g) = g := Poly.eval_C g 0

theorem evX0_secY0 (g : Poly K) : evX0 (secY0 g) = Poly.C (g.val 0) := by
  apply Poly.ext; intro d
  change ((if d = 0 then g else 0).val 0) = (if d = 0 then g.val 0 else 0)
  by_cases hd : d = 0
  · subst hd; rfl
  · simp [hd]; rfl

theorem evX0_secX0 (g : Poly K) : evX0 (secX0 g) = g :=
  Poly.ext (fun _ => rfl)

theorem secY0_one : secY0 (1 : Poly K) = 1 := by
  apply Poly.ext; intro d
  change (if d = 0 then (1 : Poly K) else 0) = (if d = 0 then (1 : Poly K) else 0)
  rfl

theorem secY0_mul (a b : Poly K) : secY0 (a * b) = secY0 a * secY0 b := Poly.C_mul a b

theorem secX0_one : secX0 (1 : Poly K) = 1 := by
  apply Poly.ext; intro d
  apply Poly.ext; intro i
  change (if i = 0 then (if d = 0 then (1 : K) else 0) else 0) =
    ((if d = 0 then (1 : Poly K) else 0).val i)
  by_cases hd : d = 0
  · subst hd
    rw [if_pos rfl, if_pos rfl]
    rfl
  · rw [if_neg hd, if_neg hd]
    by_cases hi : i = 0
    · rw [if_pos hi]; rfl
    · rw [if_neg hi]; rfl

theorem finSum_polyC : ∀ (n : Nat) (F : Nat → K),
    finSum n (fun k => Poly.C (F k)) = Poly.C (finSum n F)
  | 0, _ => by
    apply Poly.ext; intro i
    change (0 : K) = if i = 0 then 0 else 0
    by_cases hi : i = 0 <;> simp [hi]
  | n + 1, F => by
    change finSum n (fun k => Poly.C (F k)) + Poly.C (F n) = Poly.C (finSum n F + F n)
    rw [finSum_polyC n F, Poly.C_add]

theorem secX0_mul (a b : Poly K) : secX0 (a * b) = secX0 a * secX0 b := by
  apply Poly.ext; intro d
  change Poly.C (finSum (d + 1) (fun k => a.val k * b.val (d - k))) =
    finSum (d + 1) (fun k => Poly.C (a.val k) * Poly.C (b.val (d - k)))
  rw [← finSum_polyC]
  exact finSum_congr (d + 1) (fun k _ => Poly.C_mul (a.val k) (b.val (d - k)))

theorem sub_secY0_evY0_mem_X1 (h : MPoly 2 K) :
    h - secY0 (evY0 h) ∈ Ideal.span [X1_2 K] := by
  rw [X1_2_eq, Poly.mem_span_X_iff, Poly.eval_sub]
  change evY0 h - evY0 (secY0 (evY0 h)) = 0
  rw [evY0_secY0, r_sub_self]

theorem sub_secX0_evX0_mem_X0 (h : MPoly 2 K) :
    h - secX0 (evX0 h) ∈ Ideal.span [X0_2 K] := by
  let q : MPoly 2 K := ⟨fun d => Poly.shift (h.val d), by
    rcases h.property with ⟨Bh, hh⟩
    refine ⟨Bh, fun d hd => ?_⟩
    dsimp only
    rw [hh d hd]
    exact Poly.ext (fun _ => rfl)⟩
  refine ⟨q, 0, rfl, ?_⟩
  rw [r_add_zero, r_mul_comm]
  apply Poly.ext; intro d
  change h.val d - Poly.C ((h.val d).val 0) =
    (Poly.mul (Poly.mono 0 (Poly.X : Poly K)) q).val d
  rw [Poly.mono_mul_coeff]
  have h0 : 0 ≤ d := Nat.zero_le d
  have hsub : d - 0 = d := by omega
  simp [h0, hsub]
  have hd_eq := Poly.eq_C_add_X_mul_shift (h.val d)
  change h.val d + (-(Poly.C ((h.val d).val 0))) = Poly.X * Poly.shift (h.val d)
  calc
    h.val d + (-(Poly.C ((h.val d).val 0)))
      = (Poly.C ((h.val d).val 0) + Poly.X * Poly.shift (h.val d)) +
          (-(Poly.C ((h.val d).val 0))) := by conv => lhs; arg 1; rw [hd_eq]
    _ = Poly.X * Poly.shift (h.val d) +
          (Poly.C ((h.val d).val 0) + (-(Poly.C ((h.val d).val 0)))) := by
          rw [r_add_comm (Poly.C _) (Poly.X * _), r_add_assoc]
    _ = Poly.X * Poly.shift (h.val d) := by rw [r_add_right_neg, r_add_zero]

/-- Exact characterization `h ∈ (X_0 X_1) ↔ evY0 h = 0 ∧ evX0 h = 0`. -/
theorem mem_span_m01_iff (h : MPoly 2 K) :
    h ∈ Ideal.span [m01 K] ↔ evY0 h = 0 ∧ evX0 h = 0 := by
  constructor
  · rintro ⟨q, z, hz, hq⟩
    change z = 0 at hz
    rw [hz, r_add_zero] at hq
    rw [hq, evY0_mul, evX0_mul, evY0_mul, evX0_mul, evY0_X1, evX0_X0,
        r_mul_zero, r_zero_mul, r_mul_zero, r_mul_zero]
    exact ⟨rfl, rfl⟩
  · rintro ⟨hy0, hx0⟩
    let q : MPoly 2 K := ⟨fun d => Poly.shift (h.val (d + 1)), by
      rcases h.property with ⟨Bh, hh⟩
      refine ⟨Bh, fun d hd => ?_⟩
      dsimp only
      rw [hh (d + 1) (by omega)]
      exact Poly.ext (fun _ => rfl)⟩
    refine ⟨q, 0, rfl, ?_⟩
    rw [r_add_zero, r_mul_comm]
    have hm01 : m01 K = Poly.mono 1 (Poly.X : Poly K) := by
      apply Poly.ext; intro d
      change (Poly.mul (Poly.mono 0 (Poly.X : Poly K)) (Poly.mono 1 1)).val d =
        (if d = 1 then (Poly.X : Poly K) else 0)
      rw [Poly.mono_mul_coeff]
      have h0 : 0 ≤ d := Nat.zero_le d
      have hsub : d - 0 = d := by omega
      simp [h0, hsub]
      change Poly.X * (if d = 1 then (1 : Poly K) else 0) = if d = 1 then Poly.X else 0
      by_cases hd1 : d = 1
      · simp [hd1, r_mul_one]
      · simp [hd1, r_mul_zero]
    rw [hm01]
    apply Poly.ext; intro d
    rw [Poly.mono_mul_coeff']
    cases d with
    | zero =>
      have h0 : h.val 0 = 0 := by rw [← evY0_eq_val0]; exact hy0
      exact h0
    | succ k =>
      have h1 : 1 ≤ k + 1 := by omega
      have hsub : k + 1 - 1 = k := by omega
      simp [h1, hsub]
      have hdecomp := Poly.eq_C_add_X_mul_shift (h.val (k + 1))
      have hc0_val : (h.val (k + 1)).val 0 = 0 :=
        congrArg (fun p => p.val (k + 1)) hx0
      rw [hc0_val] at hdecomp
      have hc0 : (Poly.C (0 : K)) = 0 := by
        apply Poly.ext; intro i
        change (if i = 0 then (0 : K) else 0) = 0
        by_cases hi : i = 0 <;> simp [hi]
      rw [hc0, r_zero_add] at hdecomp
      exact hdecomp

end TwoVarLemmas

section K2Proofs
variable (K : Type u) [CAlgField K]

theorem m01_ne_zero : m01 K ≠ 0 := by
  have hdomK := CAlgField.isDomain K
  have hdom1 := Poly.isDomain hdomK
  have hdom2 := Poly.isDomain hdom1
  intro h0
  cases hdom2.mul_eq_zero h0 with
  | inl hx0 =>
    have hev := congrArg (fun p => (evY0 p).val 1) hx0
    dsimp only at hev
    rw [evY0_X0, evY0_zero] at hev
    exact hdomK.one_ne_zero hev
  | inr hx1 =>
    have hev := congrArg (fun p => (evX0 p).val 1) hx1
    dsimp only at hev
    rw [evX0_X1, evX0_zero] at hev
    exact hdomK.one_ne_zero hev

theorem K2_ara : IsArithmeticalRank (MPoly 2 K) (edgeIdeal K K2Graph) 1 := by
  rw [K2_edgeIdeal_eq]
  refine ⟨⟨[m01 K], rfl, fun _ => Iff.rfl⟩, ?_⟩
  intro s hs ⟨gs, hlen, hrad⟩
  have hs0 : s = 0 := by omega
  rw [hs0] at hlen
  have hnil : gs = [] := List.eq_nil_of_length_eq_zero hlen
  rw [hnil] at hrad
  have hm_in : Ideal.inRadical (Ideal.span [m01 K]) (m01 K) :=
    ⟨1, Nat.le_refl 1, by rw [rpow_one]; exact Ideal.mem_span_head (m01 K) []⟩
  rcases (hrad (m01 K)).mpr hm_in with ⟨m, _, hpow0⟩
  change rpow (m01 K) m = 0 at hpow0
  have hdom2 := MPoly.isDomain 2 (CAlgField.isDomain K)
  exact IsDomain.rpow_ne_zero hdom2 (m01_ne_zero K) m hpow0

theorem K2_quotient_pd :
    IsProjDim (MPoly 2 K) (QuotientMod (MPoly 2 K) (edgeIdeal K K2Graph)) 1 := by
  let R2 := MPoly 2 K
  let I := edgeIdeal K K2Graph
  have hI : I = Ideal.span [m01 K] := K2_edgeIdeal_eq K
  have hdomK := CAlgField.isDomain K
  have hdom2 := MPoly.isDomain 2 hdomK
  refine ⟨?_, ?_⟩
  · -- Resolution of length 1: `0 → R2^1 → R2^1 → R2 / I → 0`
    let eps : LinearMap R2 (FreeMod R2 1) (QuotientMod R2 I) := {
      toFun := fun v => QuotientMod.mk I (v ⟨0, by omega⟩)
      map_add := fun _ _ => rfl
      map_smul := fun _ _ => rfl
    }
    refine ⟨FreeMod R2 1, inferInstance, FreeMod.isProjective R2 1, eps, ?_, ?_⟩
    · intro y
      refine Quot.inductionOn y (fun a => ⟨fun _ => a, rfl⟩)
    · -- Show `KerMod eps` is projective (isomorphic to `FreeMod R2 1` via multiplication by `m01 K`)
      change IsProjective R2 (KerMod eps)
      have hker_iff : ∀ x : FreeMod R2 1,
          eps.toFun x = CAlgModule.zero (R := R2) ↔ ∃ q : R2, x ⟨0, by omega⟩ = q * m01 K := by
        intro x
        change QuotientMod.mk I (x ⟨0, by omega⟩) = QuotientMod.mk I 0 ↔ _
        rw [QuotientMod.eq_iff, hI]
        constructor
        · rintro ⟨q, z, hz, hx⟩
          change z = 0 at hz
          rw [hz, r_add_zero] at hx
          have hsub0 : x ⟨0, by omega⟩ - 0 = x ⟨0, by omega⟩ := by
            change x ⟨0, by omega⟩ + (-(0 : R2)) = x ⟨0, by omega⟩
            rw [r_neg_zero, r_add_zero]
          rw [hsub0] at hx
          exact ⟨q, hx⟩
        · rintro ⟨q, hxq⟩
          refine ⟨q, 0, rfl, ?_⟩
          rw [r_add_zero]
          change x ⟨0, by omega⟩ + (-(0 : R2)) = q * m01 K
          rw [r_neg_zero, r_add_zero]
          exact hxq
      let f_quot (z : KerMod eps) : R2 :=
        Classical.choose ((hker_iff z.val).mp z.property)
      have hf_quot (z : KerMod eps) : z.val ⟨0, by omega⟩ = f_quot z * m01 K :=
        Classical.choose_spec ((hker_iff z.val).mp z.property)
      let inc : LinearMap R2 (KerMod eps) (FreeMod R2 1) := {
        toFun := fun x _ => f_quot x
        map_add := fun x y => funext (fun _ => by
          change f_quot (CAlgModule.add (R := R2) x y) = f_quot x + f_quot y
          have hx : x.val ⟨0, by omega⟩ = f_quot x * m01 K := hf_quot x
          have hy : y.val ⟨0, by omega⟩ = f_quot y * m01 K := hf_quot y
          have hxy : x.val ⟨0, by omega⟩ + y.val ⟨0, by omega⟩ =
              f_quot (CAlgModule.add (R := R2) x y) * m01 K :=
            hf_quot (CAlgModule.add (R := R2) x y)
          apply IsDomain.mul_left_cancel hdom2 (m01_ne_zero K)
          calc
            m01 K * f_quot (CAlgModule.add (R := R2) x y)
              = f_quot (CAlgModule.add (R := R2) x y) * m01 K := r_mul_comm _ _
            _ = x.val ⟨0, by omega⟩ + y.val ⟨0, by omega⟩ := hxy.symm
            _ = f_quot x * m01 K + f_quot y * m01 K := by rw [hx, hy]
            _ = m01 K * f_quot x + m01 K * f_quot y := by
                rw [r_mul_comm (f_quot x) (m01 K), r_mul_comm (f_quot y) (m01 K)]
            _ = m01 K * (f_quot x + f_quot y) := (r_left_distrib _ _ _).symm)
        map_smul := fun r x => funext (fun _ => by
          change f_quot (CAlgModule.smul r x) = r * f_quot x
          have hx : x.val ⟨0, by omega⟩ = f_quot x * m01 K := hf_quot x
          have hrx : r * x.val ⟨0, by omega⟩ = f_quot (CAlgModule.smul r x) * m01 K :=
            hf_quot (CAlgModule.smul r x)
          apply IsDomain.mul_left_cancel hdom2 (m01_ne_zero K)
          calc
            m01 K * f_quot (CAlgModule.smul r x)
              = f_quot (CAlgModule.smul r x) * m01 K := r_mul_comm _ _
            _ = r * x.val ⟨0, by omega⟩ := hrx.symm
            _ = r * (f_quot x * m01 K) := by rw [hx]
            _ = (r * f_quot x) * m01 K := (r_mul_assoc _ _ _).symm
            _ = m01 K * (r * f_quot x) := r_mul_comm _ _)
      }
      let proj : LinearMap R2 (FreeMod R2 1) (KerMod eps) := {
        toFun := fun w => ⟨fun _ => w ⟨0, by omega⟩ * m01 K,
          (hker_iff _).mpr ⟨w ⟨0, by omega⟩, rfl⟩⟩
        map_add := fun v w => Subtype.ext (funext (fun _ => r_right_distrib _ _ _))
        map_smul := fun r w => Subtype.ext (funext (fun _ => r_mul_assoc _ _ _))
      }
      refine ⟨1, inc, proj, fun x => ?_⟩
      apply Subtype.ext
      funext i
      have hi0 : i = ⟨0, by omega⟩ := Fin.ext (by omega)
      subst hi0
      exact (hf_quot x).symm
  · -- Not projective (`e = 0`): `X0_2 * mk(X1_2) = 0` gives nonzero torsion!
    intro e he hp0
    have he0 : e = 0 := by omega
    subst he0
    change IsProjective R2 (QuotientMod R2 I) at hp0
    have hx0_ne : X0_2 K ≠ 0 := by
      intro h0
      have hev := congrArg (fun p => (evY0 p).val 1) h0
      dsimp only at hev
      rw [evY0_X0, evY0_zero] at hev
      exact hdomK.one_ne_zero hev
    have hsmul : CAlgModule.smul (X0_2 K) (QuotientMod.mk I (X1_2 K)) =
        CAlgModule.zero (R := R2) := by
      change QuotientMod.mk I (m01 K) = QuotientMod.mk I 0
      rw [QuotientMod.eq_iff, hI]
      refine ⟨1, 0, rfl, ?_⟩
      rw [r_one_mul, r_add_zero]
      change m01 K + (-(0 : R2)) = m01 K
      rw [r_neg_zero, r_add_zero]
    have hmk0 := IsProjective.torsion_free hdom2 hp0 hx0_ne hsmul
    change QuotientMod.mk I (X1_2 K) = QuotientMod.mk I 0 at hmk0
    rw [QuotientMod.eq_iff, hI] at hmk0
    have hx1_in : X1_2 K ∈ Ideal.span [m01 K] := by
      have hsub0 : X1_2 K - 0 = X1_2 K := by
        change X1_2 K + (-(0 : R2)) = X1_2 K
        rw [r_neg_zero, r_add_zero]
      rw [← hsub0]; exact hmk0
    rcases (mem_span_m01_iff (X1_2 K)).mp hx1_in with ⟨_, hx1_ev⟩
    rw [evX0_X1] at hx1_ev
    have h10 := congrArg (fun p => p.val 1) hx1_ev
    exact hdomK.one_ne_zero h10

theorem K2_cm : IsCohenMacaulayGraph K K2Graph := by
  unfold IsCohenMacaulayGraph IsCohenMacaulayQuot
  rw [K2_edgeIdeal_eq]
  have hdomK := CAlgField.isDomain K
  have hdom1 := Poly.isDomain hdomK
  have hX_ne : (Poly.X : Poly K) ≠ 0 := by
    intro h0
    exact hdomK.one_ne_zero (congrArg (fun p => p.val 1) h0)
  have h1_not_in : (1 : MPoly 2 K) ∉ Ideal.span [m01 K] := by
    intro h1
    rcases (mem_span_m01_iff (1 : MPoly 2 K)).mp h1 with ⟨hy, _⟩
    rw [evY0_one] at hy
    exact hdom1.one_ne_zero hy
  refine ⟨h1_not_in, 1, ?_, ?_⟩
  · -- Krull dimension of `K[X_0, X_1] / (X_0 X_1)` is `1`
    constructor
    · -- Prime chain `(X_1) ⊂ (X_0, X_1)` of length `1`
      let pY : Ideal (MPoly 2 K) := {
        carrier := fun f => evY0 f = 0
        zero_mem := evY0_zero
        add_mem := fun {a b} ha hb => by rw [evY0_add, ha, hb, r_add_zero]
        mul_mem_left := fun r {a} ha => by rw [evY0_mul, ha, r_mul_zero]
      }
      let pOrig : Ideal (MPoly 2 K) := {
        carrier := fun f => MPoly.evalOrigin f = 0
        zero_mem := MPoly.evalOrigin_zero
        add_mem := fun {a b} ha hb => by rw [MPoly.evalOrigin_add, ha, hb, r_add_zero]
        mul_mem_left := fun r {a} ha => by rw [MPoly.evalOrigin_mul, ha, r_mul_zero]
      }
      let chain : Fin 2 → Ideal (MPoly 2 K)
        | ⟨0, _⟩ => pY
        | ⟨1, _⟩ => pOrig
      refine ⟨chain, ?_, ?_, ?_⟩
      · intro x hx
        exact ((mem_span_m01_iff x).mp hx).1
      · intro i
        match i with
        | ⟨0, _⟩ =>
          refine ⟨fun h1 => ?_, fun a b hab => ?_⟩
          · change evY0 1 = 0 at h1; rw [evY0_one] at h1; exact hdom1.one_ne_zero h1
          · change evY0 (a * b) = 0 at hab; rw [evY0_mul] at hab; exact hdom1.mul_eq_zero hab
        | ⟨1, _⟩ =>
          refine ⟨fun h1 => ?_, fun a b hab => ?_⟩
          · change MPoly.evalOrigin 1 = 0 at h1
            rw [MPoly.evalOrigin_one] at h1
            exact hdomK.one_ne_zero h1
          · change MPoly.evalOrigin (a * b) = 0 at hab
            rw [MPoly.evalOrigin_mul] at hab
            exact hdomK.mul_eq_zero hab
      · intro i
        match i with
        | ⟨0, _⟩ =>
          refine ⟨fun x hx => ?_, X0_2 K, MPoly.evalOrigin_var _, ?_⟩
          · change evY0 x = 0 at hx
            change Poly.eval (evY0 x) 0 = 0
            rw [hx, Poly.eval_zero]
          · intro hx0
            change evY0 (X0_2 K) = 0 at hx0
            rw [evY0_X0] at hx0
            exact hX_ne hx0
    · -- No prime chain `p0 ⊂ p1 ⊂ p2` of length `e ≥ 2` containing `(X_0 X_1)`
      intro e he ⟨chain, hI0, hprimes, hstrict⟩
      let p0 := chain ⟨0, by omega⟩
      let p1 := chain ⟨1, by omega⟩
      let p2 := chain ⟨2, by omega⟩
      have hp0 : Ideal.IsPrime p0 := hprimes ⟨0, by omega⟩
      have hp1 : Ideal.IsPrime p1 := hprimes ⟨1, by omega⟩
      have hp2 : Ideal.IsPrime p2 := hprimes ⟨2, by omega⟩
      have h01 : Ideal.StrictSubset p0 p1 := hstrict ⟨0, by omega⟩
      have h12 : Ideal.StrictSubset p1 p2 := hstrict ⟨1, by omega⟩
      have hm_in_p0 : X0_2 K * X1_2 K ∈ p0 :=
        hI0 (m01 K) (Ideal.mem_span_head (m01 K) [])
      cases hp0.2 (X0_2 K) (X1_2 K) hm_in_p0 with
      | inr hx1_p0 =>
        -- Pull back `p0 ⊂ p1 ⊂ p2` along `secY0 : Poly K → MPoly 2 K`
        let pull (P : Ideal (MPoly 2 K)) : Ideal (Poly K) := {
          carrier := fun g => secY0 g ∈ P
          zero_mem := by
            have hz : secY0 (0 : Poly K) = 0 := by
              apply Poly.ext; intro d
              change (if d = 0 then (0 : Poly K) else 0) = 0
              by_cases hd : d = 0 <;> simp [hd]
            rw [hz]; exact P.zero_mem
          add_mem := fun {a b} ha hb => by
            change Poly.C (a + b) ∈ P
            rw [Poly.C_add]
            exact P.add_mem ha hb
          mul_mem_left := fun r {a} ha => by
            change secY0 (r * a) ∈ P
            rw [secY0_mul]
            exact P.mul_mem_left (secY0 r) ha
        }
        have hpull_prime : ∀ {P : Ideal (MPoly 2 K)}, Ideal.IsPrime P → Ideal.IsPrime (pull P) := by
          intro P hP
          refine ⟨fun h1 => hP.1 (by rw [← secY0_one]; exact h1), fun a b hab => ?_⟩
          change secY0 (a * b) ∈ P at hab
          rw [secY0_mul] at hab
          exact hP.2 (secY0 a) (secY0 b) hab
        have hx1_sub : ∀ {P : Ideal (MPoly 2 K)}, X1_2 K ∈ P →
            ∀ h : MPoly 2 K, h - secY0 (evY0 h) ∈ P := by
          intro P hx1P h
          rcases sub_secY0_evY0_mem_X1 h with ⟨q, z, hz, hdiff⟩
          change z = 0 at hz
          rw [hdiff, hz, r_add_zero]
          exact P.mul_mem_left q hx1P
        have hx1_p1 : X1_2 K ∈ p1 := h01.1 (X1_2 K) hx1_p0
        have hpull01 : Ideal.StrictSubset (pull p0) (pull p1) := by
          rcases h01 with ⟨hsub, y, hy1, hy0⟩
          refine ⟨fun g hg => hsub (secY0 g) hg, evY0 y, ?_, ?_⟩
          · have hdiff := hx1_sub hx1_p1 y
            have heq : secY0 (evY0 y) = y - (y - secY0 (evY0 y)) := by
              change secY0 (evY0 y) = y + (-(y + (-(secY0 (evY0 y)))))
              rw [r_neg_add, r_neg_neg, ← r_add_assoc, r_add_right_neg, r_zero_add]
            change secY0 (evY0 y) ∈ p1
            rw [heq]
            exact p1.sub_mem hy1 hdiff
          · intro hiny0
            apply hy0
            have hdiff := hx1_sub hx1_p0 y
            have heq : y = (y - secY0 (evY0 y)) + secY0 (evY0 y) := by
              change y = (y + (-(secY0 (evY0 y)))) + secY0 (evY0 y)
              rw [r_add_assoc, r_add_left_neg, r_add_zero]
            rw [heq]
            exact p0.add_mem hdiff hiny0
        have hx1_p2 : X1_2 K ∈ p2 := h12.1 (X1_2 K) hx1_p1
        have hpull12 : Ideal.StrictSubset (pull p1) (pull p2) := by
          rcases h12 with ⟨hsub, y, hy2, hy1⟩
          refine ⟨fun g hg => hsub (secY0 g) hg, evY0 y, ?_, ?_⟩
          · have hdiff := hx1_sub hx1_p2 y
            have heq : secY0 (evY0 y) = y - (y - secY0 (evY0 y)) := by
              change secY0 (evY0 y) = y + (-(y + (-(secY0 (evY0 y)))))
              rw [r_neg_add, r_neg_neg, ← r_add_assoc, r_add_right_neg, r_zero_add]
            change secY0 (evY0 y) ∈ p2
            rw [heq]
            exact p2.sub_mem hy2 hdiff
          · intro hiny1
            apply hy1
            have hdiff := hx1_sub hx1_p1 y
            have heq : y = (y - secY0 (evY0 y)) + secY0 (evY0 y) := by
              change y = (y + (-(secY0 (evY0 y)))) + secY0 (evY0 y)
              rw [r_add_assoc, r_add_left_neg, r_add_zero]
            rw [heq]
            exact p1.add_mem hdiff hiny1
        exact Poly.no_prime_chain_len_two (hpull_prime hp1) (hpull_prime hp2) hpull01 hpull12
      | inl hx0_p0 =>
        -- Symmetrically pull back `p0 ⊂ p1 ⊂ p2` along `secX0 : Poly K → MPoly 2 K`
        let pull (P : Ideal (MPoly 2 K)) : Ideal (Poly K) := {
          carrier := fun g => secX0 g ∈ P
          zero_mem := by
            have hz : secX0 (0 : Poly K) = 0 := by
              apply Poly.ext; intro d; apply Poly.ext; intro i
              change (if i = 0 then (0 : K) else 0) = 0
              by_cases hi : i = 0 <;> simp [hi]
            rw [hz]; exact P.zero_mem
          add_mem := fun {a b} ha hb => by
            have hadd : secX0 (a + b) = secX0 a + secX0 b := by
              apply Poly.ext; intro d
              exact Poly.C_add (a.val d) (b.val d)
            change secX0 (a + b) ∈ P
            rw [hadd]
            exact P.add_mem ha hb
          mul_mem_left := fun r {a} ha => by
            change secX0 (r * a) ∈ P
            rw [secX0_mul]
            exact P.mul_mem_left (secX0 r) ha
        }
        have hpull_prime : ∀ {P : Ideal (MPoly 2 K)}, Ideal.IsPrime P → Ideal.IsPrime (pull P) := by
          intro P hP
          refine ⟨fun h1 => hP.1 (by rw [← secX0_one]; exact h1), fun a b hab => ?_⟩
          change secX0 (a * b) ∈ P at hab
          rw [secX0_mul] at hab
          exact hP.2 (secX0 a) (secX0 b) hab
        have hx0_sub : ∀ {P : Ideal (MPoly 2 K)}, X0_2 K ∈ P →
            ∀ h : MPoly 2 K, h - secX0 (evX0 h) ∈ P := by
          intro P hx0P h
          rcases sub_secX0_evX0_mem_X0 h with ⟨q, z, hz, hdiff⟩
          change z = 0 at hz
          rw [hdiff, hz, r_add_zero]
          exact P.mul_mem_left q hx0P
        have hx0_p1 : X0_2 K ∈ p1 := h01.1 (X0_2 K) hx0_p0
        have hpull01 : Ideal.StrictSubset (pull p0) (pull p1) := by
          rcases h01 with ⟨hsub, y, hy1, hy0⟩
          refine ⟨fun g hg => hsub (secX0 g) hg, evX0 y, ?_, ?_⟩
          · have hdiff := hx0_sub hx0_p1 y
            have heq : secX0 (evX0 y) = y - (y - secX0 (evX0 y)) := by
              change secX0 (evX0 y) = y + (-(y + (-(secX0 (evX0 y)))))
              rw [r_neg_add, r_neg_neg, ← r_add_assoc, r_add_right_neg, r_zero_add]
            change secX0 (evX0 y) ∈ p1
            rw [heq]
            exact p1.sub_mem hy1 hdiff
          · intro hiny0
            apply hy0
            have hdiff := hx0_sub hx0_p0 y
            have heq : y = (y - secX0 (evX0 y)) + secX0 (evX0 y) := by
              change y = (y + (-(secX0 (evX0 y)))) + secX0 (evX0 y)
              rw [r_add_assoc, r_add_left_neg, r_add_zero]
            rw [heq]
            exact p0.add_mem hdiff hiny0
        have hx0_p2 : X0_2 K ∈ p2 := h12.1 (X0_2 K) hx0_p1
        have hpull12 : Ideal.StrictSubset (pull p1) (pull p2) := by
          rcases h12 with ⟨hsub, y, hy2, hy1⟩
          refine ⟨fun g hg => hsub (secX0 g) hg, evX0 y, ?_, ?_⟩
          · have hdiff := hx0_sub hx0_p2 y
            have heq : secX0 (evX0 y) = y - (y - secX0 (evX0 y)) := by
              change secX0 (evX0 y) = y + (-(y + (-(secX0 (evX0 y)))))
              rw [r_neg_add, r_neg_neg, ← r_add_assoc, r_add_right_neg, r_zero_add]
            change secX0 (evX0 y) ∈ p2
            rw [heq]
            exact p2.sub_mem hy2 hdiff
          · intro hiny1
            apply hy1
            have hdiff := hx0_sub hx0_p1 y
            have heq : y = (y - secX0 (evX0 y)) + secX0 (evX0 y) := by
              change y = (y + (-(secX0 (evX0 y)))) + secX0 (evX0 y)
              rw [r_add_assoc, r_add_left_neg, r_add_zero]
            rw [heq]
            exact p1.add_mem hdiff hiny1
        exact Poly.no_prime_chain_len_two (hpull_prime hp1) (hpull_prime hp2) hpull01 hpull12
  · -- Depth of `K[X_0, X_1] / (X_0 X_1)` is `1`
    constructor
    · -- Regular sequence `[X_1 - X_0]` of length `1`
      let theta := X1_2 K - X0_2 K
      refine ⟨[theta], rfl, ?_, ?_⟩
      · intro r hr
        cases hr with
        | head =>
          exact (MPoly.maxIdeal 2 K).sub_mem
            (MPoly.var_mem_maxIdeal ⟨1, by omega⟩)
            (MPoly.var_mem_maxIdeal ⟨0, by omega⟩)
        | tail _ h => cases h
      · refine ⟨fun f hf => ?_, ?_⟩
        · rcases (mem_span_m01_iff (theta * f)).mp hf with ⟨hy, hx⟩
          rw [evY0_mul, evY0_sub, evY0_X1, evY0_X0] at hy
          rw [evX0_mul, evX0_sub, evX0_X1, evX0_X0] at hx
          have hnegX : (0 : Poly K) - Poly.X ≠ 0 := by
            intro hz
            have hval := congrArg (fun p => p.val 1) hz
            change (0 : K) + (-(1 : K)) = 0 at hval
            rw [r_zero_add] at hval
            have h10 : (1 : K) = 0 := by
              rw [← r_neg_neg (1 : K), hval, r_neg_zero]
            exact hdomK.one_ne_zero h10
          have hposX : Poly.X - (0 : Poly K) ≠ 0 := by
            intro hz
            have hval := congrArg (fun p => p.val 1) hz
            change (1 : K) + (-(0 : K)) = 0 at hval
            rw [r_neg_zero, r_add_zero] at hval
            exact hdomK.one_ne_zero hval
          have hfy : evY0 f = 0 := by
            cases hdom1.mul_eq_zero hy with
            | inl h1 => exact False.elim (hnegX h1)
            | inr h2 => exact h2
          have hfx : evX0 f = 0 := by
            cases hdom1.mul_eq_zero hx with
            | inl h1 => exact False.elim (hposX h1)
            | inr h2 => exact h2
          exact (mem_span_m01_iff f).mpr ⟨hfy, hfx⟩
        · rintro ⟨a, b, ha, ⟨q, z, hz, hb⟩, h1⟩
          change z = 0 at hz
          rw [hb, hz, r_add_zero] at h1
          have horig := congrArg MPoly.evalOrigin h1
          have ha0 : MPoly.evalOrigin a = 0 := by
            rcases ha with ⟨qa, za, hza, haeq⟩
            change za = 0 at hza
            rw [haeq, hza, r_add_zero, MPoly.evalOrigin_mul, MPoly.evalOrigin_mul,
                MPoly.evalOrigin_var, r_zero_mul, r_mul_zero]
          have htheta0 : MPoly.evalOrigin theta = 0 := by
            change MPoly.evalOrigin (X1_2 K + (-X0_2 K)) = 0
            have hneg0 : MPoly.evalOrigin (-X0_2 K) = 0 := by
              apply r_add_left_cancel (a := MPoly.evalOrigin (X0_2 K))
              rw [← MPoly.evalOrigin_add, r_add_right_neg, MPoly.evalOrigin_zero,
                  MPoly.evalOrigin_var, r_add_zero]
            rw [MPoly.evalOrigin_add, MPoly.evalOrigin_var, hneg0, r_add_zero]
          rw [MPoly.evalOrigin_one, MPoly.evalOrigin_add, ha0, MPoly.evalOrigin_mul,
              htheta0, r_mul_zero, r_add_zero] at horig
          exact hdomK.one_ne_zero horig
    · -- No regular sequence `r1 :: r2 :: tail` of length `e ≥ 2` in `𝔪`
      intro e he ⟨seq, hlen, hmem, hreg⟩
      match seq with
      | [] => simp at hlen; omega
      | [_] => simp at hlen; omega
      | r1 :: r2 :: tail =>
        rcases hreg with ⟨hreg1, hreg2, _⟩
        have hr1_orig : MPoly.evalOrigin r1 = 0 :=
          MPoly.evalOrigin_eq_zero_of_mem_maxIdeal (hmem r1 (List.Mem.head _))
        have hr2_orig : MPoly.evalOrigin r2 = 0 :=
          MPoly.evalOrigin_eq_zero_of_mem_maxIdeal
            (hmem r2 (List.Mem.tail _ (List.Mem.head _)))
        let p := evY0 r1
        let q := evX0 r1
        have hp0 : p.val 0 = 0 := by
          rw [← Poly.eval_zero_eq_const]
          exact hr1_orig
        have hr2_y0 : (evY0 r2).val 0 = 0 := by
          rw [← Poly.eval_zero_eq_const]
          exact hr2_orig
        have hp_ne : p ≠ 0 := by
          intro hpz
          have hprod : r1 * X0_2 K ∈ Ideal.span [m01 K] := by
            rw [mem_span_m01_iff, evY0_mul, evX0_mul, evX0_X0, r_mul_zero]
            change p * evY0 (X0_2 K) = 0 ∧ 0 = 0
            rw [hpz, r_zero_mul]
            exact ⟨rfl, rfl⟩
          rcases (mem_span_m01_iff (X0_2 K)).mp (hreg1 (X0_2 K) hprod) with ⟨hx0y, _⟩
          rw [evY0_X0] at hx0y
          exact hX_ne hx0y
        have hq_ne : q ≠ 0 := by
          intro hqz
          have hprod : r1 * X1_2 K ∈ Ideal.span [m01 K] := by
            rw [mem_span_m01_iff, evY0_mul, evX0_mul, evY0_X1, r_mul_zero]
            change 0 = 0 ∧ q * evX0 (X1_2 K) = 0
            rw [hqz, r_zero_mul]
            exact ⟨rfl, rfl⟩
          rcases (mem_span_m01_iff (X1_2 K)).mp (hreg1 (X1_2 K) hprod) with ⟨_, hx1x⟩
          rw [evX0_X1] at hx1x
          exact hX_ne hx1x
        let z := secY0 p
        have hz_evY : evY0 z = p := evY0_secY0 p
        have hz_evX : evX0 z = 0 := by
          rw [evX0_secY0, hp0]
          apply Poly.ext; intro d
          change (if d = 0 then (0 : K) else 0) = 0
          by_cases hd : d = 0 <;> simp [hd]
        -- Show `r2 * z ∈ (X_0 X_1) + (r1)`
        let diff := r2 * z - secY0 (evY0 r2) * r1
        have hdiff_in : diff ∈ Ideal.span [m01 K] := by
          rw [mem_span_m01_iff]
          constructor
          · change evY0 (r2 * z - secY0 (evY0 r2) * r1) = 0
            rw [evY0_sub, evY0_mul, evY0_mul, hz_evY, evY0_secY0]
            exact r_sub_self (evY0 r2 * p)
          · change evX0 (r2 * z - secY0 (evY0 r2) * r1) = 0
            rw [evX0_sub, evX0_mul, evX0_mul, hz_evX, r_mul_zero, evX0_secY0, hr2_y0]
            have hc0 : (Poly.C (0 : K)) = 0 := by
              apply Poly.ext; intro d
              change (if d = 0 then (0 : K) else 0) = 0
              by_cases hd : d = 0 <;> simp [hd]
            rw [hc0, r_zero_mul, r_sub_self]
        have hr2z_mem : r2 * z ∈ Ideal.sum (Ideal.span [m01 K]) (Ideal.span [r1]) := by
          refine ⟨diff, secY0 (evY0 r2) * r1, hdiff_in,
            ⟨secY0 (evY0 r2), 0, rfl, by rw [r_add_zero]⟩, ?_⟩
          change r2 * z = (r2 * z + (-(secY0 (evY0 r2) * r1))) + secY0 (evY0 r2) * r1
          rw [r_add_assoc, r_add_left_neg, r_add_zero]
        -- By regularity of `r2`, `z ∈ (X_0 X_1) + (r1)`, yielding `1 = 0` in `K`!
        rcases hreg2 z hr2z_mem with ⟨a, b, ha, ⟨u, w, hw, hb⟩, hzeq⟩
        change w = 0 at hw
        rw [hb, hw, r_add_zero] at hzeq
        rcases (mem_span_m01_iff a).mp ha with ⟨hay, hax⟩
        have hevy : p = evY0 u * p := by
          have h := congrArg evY0 hzeq
          rw [hz_evY, evY0_add, hay, r_zero_add, evY0_mul] at h
          exact h
        have huY1 : evY0 u = 1 := by
          apply IsDomain.mul_left_cancel hdom1 hp_ne
          rw [r_mul_comm p (evY0 u), ← hevy, r_mul_one]
        have hevx : (0 : Poly K) = evX0 u * q := by
          have h := congrArg evX0 hzeq
          rw [hz_evX, evX0_add, hax, r_zero_add, evX0_mul] at h
          exact h
        have huX0 : evX0 u = 0 := by
          cases hdom1.mul_eq_zero hevx.symm with
          | inl h1 => exact h1
          | inr h2 => exact False.elim (hq_ne h2)
        have h_u00_1 : (u.val 0).val 0 = 1 := by
          rw [← evY0_eq_val0, huY1]
          rfl
        have h_u00_0 : (u.val 0).val 0 = 0 :=
          congrArg (fun g => g.val 0) huX0
        rw [h_u00_0] at h_u00_1
        exact hdomK.one_ne_zero h_u00_1.symm

/-- Disproof of Conjecture 00000000505 under Convention 1 (`pd = pd_R(R / I(G))`),
even restricted to non-empty graphs (`E(G) ≠ ∅`), over every field `K`. -/
theorem disproof_conjecture505_quotientPD_nonEmpty (K : Type u) [CAlgField K] :
    ¬ Conjecture505_QuotientPD_NonEmpty K := by
  intro hconj
  have h := hconj 2 K2Graph 1 1 K2Graph_hasEdge (K2_ara K) (K2_quotient_pd K)
  have heq : 1 = 1 + 1 := h.2 (K2_cm K)
  omega

/-- Disproof of Conjecture 00000000505 under Convention 1 (`pd = pd_R(R / I(G))`)
for general graphs over every field `K`. -/
theorem disproof_conjecture505_quotientPD (K : Type u) [CAlgField K] :
    ¬ Conjecture505_QuotientPD K := by
  intro hconj
  apply disproof_conjecture505_quotientPD_nonEmpty K
  intro n G ara pd _ hara hpd
  exact hconj n G ara pd hara hpd

end K2Proofs

/-! ### Section 3: Explicit Field Witnesses (`𝔽_2` and `𝔽_3`) Confirming Non-Vacuity -/

/-- Explicit field `𝔽_2` on `Bool` (`false = 0`, `true = 1`), demonstrating `CAlgField` non-vacuity. -/
instance instF2Field : CAlgField Bool where
  zero := false
  one := true
  add := bne
  mul := and
  neg := id
  add_assoc a b c := by cases a <;> cases b <;> cases c <;> rfl
  add_comm a b := by cases a <;> cases b <;> rfl
  zero_add a := by cases a <;> rfl
  add_left_neg a := by cases a <;> rfl
  mul_assoc a b c := by cases a <;> cases b <;> cases c <;> rfl
  mul_comm a b := by cases a <;> cases b <;> rfl
  one_mul a := by cases a <;> rfl
  left_distrib a b c := by cases a <;> cases b <;> cases c <;> rfl
  one_ne_zero := by decide
  inv := id
  mul_inv_cancel a ha := by cases a; exact False.elim (ha rfl); rfl

theorem disproof_over_F2 :
    ¬ Conjecture505_QuotientPD_NonEmpty Bool ∧ ¬ Conjecture505_IdealPD Bool :=
  ⟨disproof_conjecture505_quotientPD_nonEmpty Bool, disproof_conjecture505_idealPD Bool⟩

end Conjecture00000000505
