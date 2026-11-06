import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic

noncomputable section
open Filter Function
open scoped Topology

namespace TLMC2195

/-- The usual perfection condition, ranging over every finite induced graph.
An embedding of Fin n selects exactly an induced n-vertex graph. -/
def Perfect {V : Type} (G : SimpleGraph V) : Prop :=
  ∀ (n : ℕ) (e : Fin n ↪ V),
    (G.comap e).chromaticNumber = ((G.comap e).cliqueNum : ℕ∞)

theorem Perfect.hereditary {V W : Type} {G : SimpleGraph V}
    (h : Perfect G) (e : W ↪ V) : Perfect (G.comap e) := by
  intro n f
  simpa only [Embedding.coe_trans,SimpleGraph.comap_comap] using h n (f.trans e)

theorem Perfect.iso {V W : Type} {G : SimpleGraph V} {H : SimpleGraph W}
    (h : Perfect G) (e : G ≃g H) : Perfect H := by
  have he : H = G.comap e.symm := by
    ext a b
    exact e.symm.map_rel_iff.symm
  rw [he]
  exact h.hereditary e.symm.toEquiv.toEmbedding

theorem clique_chromatic_eq_of_two_colorable {V : Type} [Finite V]
    {G : SimpleGraph V} (hc : G.Colorable 2) :
    G.chromaticNumber = (G.cliqueNum : ℕ∞) := by
  classical
  apply le_antisymm _ G.cliqueNum_le_chromaticNumber
  by_cases hb : G = ⊥
  · subst G
    cases isEmpty_or_nonempty V with
    | inl hv =>
      have := hv
      simp only [SimpleGraph.chromaticNumber_eq_zero_of_isEmpty]
      exact bot_le
    | inr hv =>
      have := hv
      rw [SimpleGraph.chromaticNumber_bot]
      have hcl : (⊥ : SimpleGraph V).IsClique ({Classical.arbitrary V} : Finset V) := by simp
      exact_mod_cast hcl.card_le_cliqueNum
  · obtain ⟨a,b,hab⟩ := SimpleGraph.ne_bot_iff_exists_adj.mp hb
    have hcl : G.IsClique ({a,b} : Finset V) := by
      simpa [SimpleGraph.isClique_iff, hab.ne] using hab
    have htwo : 2 ≤ G.cliqueNum := by
      simpa [hab.ne] using hcl.card_le_cliqueNum
    exact hc.chromaticNumber_le.trans (by exact_mod_cast htwo)

theorem perfect_of_two_colorable {V : Type} {G : SimpleGraph V}
    (hc : G.Colorable 2) : Perfect G := by
  intro n e
  apply clique_chromatic_eq_of_two_colorable
  exact hc.of_hom ⟨e, fun h => h⟩

theorem perfect_bot (V : Type) : Perfect (⊥ : SimpleGraph V) := by
  apply perfect_of_two_colorable
  refine ⟨SimpleGraph.Coloring.mk (fun _ => 0) ?_⟩
  simp

/-- Ordinary single-vertex graph substitution. The left summand consists of
the surviving base vertices; every inserted vertex is joined to each old
neighbour of v. -/
def substitute {V W : Type} (G : SimpleGraph V) (v : V) (H : SimpleGraph W) :
    SimpleGraph ({x : V // x ≠ v} ⊕ W) where
  Adj a b := match a,b with
    | .inl x,.inl y => G.Adj x.1 y.1
    | .inr x,.inr y => H.Adj x y
    | .inl x,.inr _ => G.Adj x.1 v
    | .inr _,.inl y => G.Adj v y.1
  symm.symm := by
    rintro (x|x) (y|y) h
    · exact h.symm
    · exact h.symm
    · exact h.symm
    · exact h.symm
  loopless.irrefl := by
    rintro (x|x)
    · exact G.loopless.irrefl x.1
    · exact H.loopless.irrefl x

instance singletonSurvivorIsEmpty : IsEmpty {x : Fin 1 // x ≠ 0} :=
  ⟨fun x => x.2 (Subsingleton.elim _ _)⟩

def singletonSubstitutionIso {W : Type} (H : SimpleGraph W) :
    substitute (⊥ : SimpleGraph (Fin 1)) 0 H ≃g H where
  toEquiv :=
    { toFun := Sum.elim (fun x => isEmptyElim x) id
      invFun := Sum.inr
      left_inv := by rintro (x|x); exact isEmptyElim x; rfl
      right_inv := fun _ => rfl }
  map_rel_iff' := by
    rintro (x|x) (y|y)
    · exact isEmptyElim x
    · exact isEmptyElim x
    · exact isEmptyElim y
    · rfl

/-- The entire substitution product of two copies of the full perfect-graph
property, including arbitrary actual graph isomorphisms to labelled Fin n. -/
def InProduct {n : ℕ} (K : SimpleGraph (Fin n)) : Prop :=
  ∃ (m k : ℕ) (G : SimpleGraph (Fin m)) (v : Fin m) (H : SimpleGraph (Fin k)),
    Perfect G ∧ Perfect H ∧ Nonempty (substitute G v H ≃g K)

theorem inProduct_of_perfect {n : ℕ} {H : SimpleGraph (Fin n)} (h : Perfect H) :
    InProduct H :=
  ⟨1,n,⊥,0,H,perfect_bot _,h,⟨singletonSubstitutionIso H⟩⟩

theorem inProduct_iso {n : ℕ} {G H : SimpleGraph (Fin n)}
    (h : InProduct G) (e : G ≃g H) : InProduct H := by
  obtain ⟨m,k,A,v,B,hA,hB,⟨f⟩⟩ := h
  exact ⟨m,k,A,v,B,hA,hB,⟨f.trans e⟩⟩

/-- True labelled speed, the cardinality of all graphs in the product. -/
def speed (n : ℕ) : ℕ := Nat.card {G : SimpleGraph (Fin n) // InProduct G}

theorem speed_pos (n : ℕ) : 0 < speed n := by
  have : Nonempty {G : SimpleGraph (Fin n) // InProduct G} :=
    ⟨⟨⊥,inProduct_of_perfect (perfect_bot _)⟩⟩
  exact Nat.card_pos

/-- Every binary matrix gives its actual fixed-bipartition simple graph. -/
def bipGraph {m : ℕ} (A : Fin m → Fin m → Bool) : SimpleGraph (Fin m ⊕ Fin m) where
  Adj a b := match a,b with
    | .inl _,.inl _ => False
    | .inr _,.inr _ => False
    | .inl i,.inr j => A i j = true
    | .inr j,.inl i => A i j = true
  symm.symm := by rintro (i|i) (j|j) h <;> exact h
  loopless.irrefl := by rintro (i|i) <;> exact not_false

def bipColoring {m : ℕ} (A : Fin m → Fin m → Bool) : (bipGraph A).Coloring (Fin 2) :=
  SimpleGraph.Coloring.mk (Sum.elim (fun _ => 0) (fun _ => 1)) <| by
    rintro (i|i) (j|j) h <;> simp_all [bipGraph]

theorem bip_perfect {m : ℕ} (A : Fin m → Fin m → Bool) : Perfect (bipGraph A) :=
  perfect_of_two_colorable ⟨bipColoring A⟩

def labelledBip {m : ℕ} (A : Fin m → Fin m → Bool) : SimpleGraph (Fin (m+m)) :=
  (bipGraph A).comap finSumFinEquiv.symm

theorem labelledBip_perfect {m : ℕ} (A : Fin m → Fin m → Bool) :
    Perfect (labelledBip A) :=
  (bip_perfect A).hereditary finSumFinEquiv.symm.toEmbedding

theorem labelledBip_injective (m : ℕ) : Injective (@labelledBip m) := by
  intro A B h
  funext i j
  have h' := congrArg (fun G : SimpleGraph (Fin (m+m)) =>
    G.Adj (finSumFinEquiv (Sum.inl i)) (finSumFinEquiv (Sum.inr j))) h
  change (bipGraph A).Adj
    (finSumFinEquiv.symm (finSumFinEquiv (Sum.inl i)))
    (finSumFinEquiv.symm (finSumFinEquiv (Sum.inr j))) =
    (bipGraph B).Adj
    (finSumFinEquiv.symm (finSumFinEquiv (Sum.inl i)))
    (finSumFinEquiv.symm (finSumFinEquiv (Sum.inr j))) at h'
  simp only [Equiv.symm_apply_apply] at h'
  change (A i j = true) = (B i j = true) at h'
  cases ha : A i j <;> cases hb : B i j <;> simp_all

def matrixIntoProduct (m : ℕ) (A : Fin m → Fin m → Bool) :
    {G : SimpleGraph (Fin (m+m)) // InProduct G} :=
  ⟨labelledBip A,inProduct_of_perfect (labelledBip_perfect A)⟩

theorem matrixIntoProduct_injective (m : ℕ) : Injective (matrixIntoProduct m) := by
  intro A B h
  exact labelledBip_injective m (congrArg Subtype.val h)

theorem actual_speed_lower (m : ℕ) : 2^(m*m) ≤ speed (m+m) := by
  have h := Nat.card_le_card_of_injective _ (matrixIntoProduct_injective m)
  simpa [speed,Nat.card_eq_fintype_card,Fintype.card_fun,←pow_mul] using h

theorem chromatic_iso {V W : Type} {G : SimpleGraph V} {H : SimpleGraph W}
    (e : G ≃g H) : G.chromaticNumber = H.chromaticNumber :=
  le_antisymm (SimpleGraph.chromaticNumber_mono_of_hom e.toHom)
    (SimpleGraph.chromaticNumber_mono_of_hom e.symm.toHom)

theorem cliqueNum_le_iso {V W : Type} [Finite V] [Finite W]
    {G : SimpleGraph V} {H : SimpleGraph W} (e : G ≃g H) : G.cliqueNum ≤ H.cliqueNum := by
  classical
  obtain ⟨s,hs⟩ := G.exists_isNClique_cliqueNum
  have hcl : H.IsClique (s.map e.toEquiv.toEmbedding) := by
    intro a ha b hb hab
    obtain ⟨a',ha',rfl⟩ := Finset.mem_map.mp ha
    obtain ⟨b',hb',rfl⟩ := Finset.mem_map.mp hb
    exact e.map_rel_iff.mpr (hs.isClique ha' hb' (fun h => hab (congrArg e h)))
  simpa [hs.card_eq] using hcl.card_le_cliqueNum

theorem cliqueNum_iso {V W : Type} [Finite V] [Finite W]
    {G : SimpleGraph V} {H : SimpleGraph W} (e : G ≃g H) : G.cliqueNum = H.cliqueNum :=
  le_antisymm (cliqueNum_le_iso e) (cliqueNum_le_iso e.symm)

/-- The finite-embedding definition implies the usual native condition on
every induced vertex subset, not only a selected family of subgraphs. -/
theorem perfect_all_induced {V : Type} [Finite V] {G : SimpleGraph V}
    (h : Perfect G) (s : Set V) :
    (G.induce s).chromaticNumber = ((G.induce s).cliqueNum : ℕ∞) := by
  classical
  let _ : Fintype s := Fintype.ofFinite s
  let f : Fin (Fintype.card s) ≃ s := (Fintype.equivFin s).symm
  let e : Fin (Fintype.card s) ↪ V := f.toEmbedding.trans (Embedding.subtype _)
  let iso : G.comap e ≃g G.induce s :=
    { __ := f
      map_rel_iff' := by intros; rfl }
  rw [← chromatic_iso iso,← cliqueNum_iso iso]
  exact h _ e

theorem log_actual_speed_lower (m : ℕ) :
    (m : ℝ)*(m : ℝ)*Real.log 2 ≤ Real.log (speed (m+m)) := by
  have h : (2 : ℝ)^(m*m) ≤ (speed (m+m) : ℝ) := by exact_mod_cast actual_speed_lower m
  have hl := Real.log_le_log (by positivity : (0 : ℝ) < 2^(m*m)) h
  simpa [Real.log_pow,Nat.cast_mul,mul_assoc,mul_comm,mul_left_comm] using hl

theorem even_tendsto : Tendsto (fun m : ℕ => m+m) atTop atTop := by
  apply tendsto_atTop.2
  intro b
  filter_upwards [eventually_ge_atTop b] with m hm
  omega

theorem log_even_ratio_tendsto_zero :
    Tendsto (fun m : ℕ => Real.log ((m : ℝ)+m) / ((m : ℝ)+m)) atTop (𝓝 0) := by
  have hnat : Tendsto (fun m : ℕ => (m : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have heven := hnat.atTop_add_atTop hnat
  simpa [Function.comp_def] using (Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero).comp heven

/-- The genuine speed has no eventual exponential C*n*log(n) upper bound,
for any finite real C. This is a quantified asymptotic conclusion. -/
theorem no_eventual_log_bound (C : ℝ) :
    ¬ ∀ᶠ n : ℕ in atTop, Real.log (speed n) ≤ C*(n : ℝ)*Real.log n := by
  intro h
  have hzero : Tendsto (fun m : ℕ =>
      (4*C)*(Real.log ((m : ℝ)+m) / ((m : ℝ)+m))) atTop (𝓝 0) := by
    simpa using tendsto_const_nhds.mul log_even_ratio_tendsto_zero
  have hle : ∀ᶠ m : ℕ in atTop,
      Real.log 2 ≤ (4*C)*(Real.log ((m : ℝ)+m) / ((m : ℝ)+m)) := by
    filter_upwards [even_tendsto.eventually h,eventually_ge_atTop 1] with m hm hm1
    have hm0 : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
    have hlo := log_actual_speed_lower m
    have hhi : Real.log (speed (m+m)) ≤ C*((m : ℝ)+m)*Real.log ((m : ℝ)+m) := by
      simpa only [Nat.cast_add] using hm
    have hcancel : (m : ℝ)*Real.log 2 ≤ 2*C*Real.log ((m : ℝ)+m) := by
      apply (mul_le_mul_iff_right₀ hm0).mp
      nlinarith
    rw [← mul_div_assoc,le_div_iff₀ (by positivity : (0 : ℝ) < (m : ℝ)+m)]
    nlinarith
  have hbad : Real.log 2 ≤ 0 := ge_of_tendsto hzero hle
  have hpos : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num : (1 : ℝ) < 2)
  linarith

/-- Exact conventional meaning of the printed exp((1/2+o(1))*n*log n)
formula for this actual product, with the error tending to zero. -/
def PrintedSpeedFormula : Prop :=
  ∃ error : ℕ → ℝ, Tendsto error atTop (𝓝 0) ∧
    ∀ᶠ n : ℕ in atTop,
      (speed n : ℝ) = Real.exp (((1 : ℝ)/2+error n)*(n : ℝ)*Real.log n)

theorem not_printed_speed_formula : ¬ PrintedSpeedFormula := by
  rintro ⟨error,herror,hformula⟩
  apply no_eventual_log_bound 1
  have heps : ∀ᶠ n : ℕ in atTop, error n < (1 : ℝ)/2 :=
    herror.eventually (gt_mem_nhds (by norm_num))
  filter_upwards [hformula,heps,eventually_ge_atTop 1] with n hn he hn1
  rw [hn,Real.log_exp]
  have hlog : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by exact_mod_cast hn1)
  have hnonneg : 0 ≤ (n : ℝ)*Real.log n := mul_nonneg (Nat.cast_nonneg _) hlog
  calc
    (1/2+error n)*(n : ℝ)*Real.log n = (1/2+error n)*((n : ℝ)*Real.log n) := by ring
    _ ≤ 1*((n : ℝ)*Real.log n) := mul_le_mul_of_nonneg_right (by linarith) hnonneg
    _ = 1*(n : ℝ)*Real.log n := by ring

end TLMC2195
