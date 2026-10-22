import Mathlib.LinearAlgebra.Projectivization.Collinear
import Mathlib.LinearAlgebra.Projectivization.Cardinality
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Max
import Mathlib.Order.Filter.ENNReal
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/- Complete arcs in the actual projective plane; a uniform secant-count lower bound. -/
namespace TLMC1002

open scoped LinearAlgebra.Projectivization NNReal ENNReal
open Filter

abbrev Point (K : Type*) [Field K] := Projectivization K (Fin 3 → K)

variable (K : Type*) [Field K] [Fintype K]
set_option linter.unusedSectionVars false

noncomputable instance pointFintype : Fintype (Point K) := Fintype.ofFinite _

noncomputable def pointsOn (L : Submodule K (Fin 3 → K)) : Finset (Point K) := by
  classical
  exact Finset.univ.filter fun p => p ∈ L.projectivization

def IsArc (S : Finset (Point K)) : Prop := by
  classical
  exact ∀ L : Submodule K (Fin 3 → K), Module.finrank K L = 2 →
    (S ∩ pointsOn K L).card ≤ 2

def IsCompleteArc (S : Finset (Point K)) : Prop := by
  classical
  exact IsArc K S ∧ ∀ p ∉ S, ¬ IsArc K (insert p S)

theorem empty_isArc : IsArc K ∅ := by
  classical
  intro L hL
  simp

theorem plane_card : Fintype.card (Point K) =
    Fintype.card K ^ 2 + Fintype.card K + 1 := by
  have h := Projectivization.card_of_finrank K (V := Fin 3 → K)
    (n := 3) (by simp)
  simpa [Nat.card_eq_fintype_card, Finset.sum_range_succ, Nat.add_comm,
    Nat.add_left_comm, Nat.add_assoc] using h

theorem rep_mem_of_on (L : Submodule K (Fin 3 → K)) (p : Point K)
    (hp : p ∈ L.projectivization) : p.rep ∈ L := by
  apply (Submodule.mk_mem_projectivization_iff L p.rep_nonzero).mp
  rw [p.mk_rep]
  exact hp

noncomputable def restrictPoint (L : Submodule K (Fin 3 → K))
    (p : {p : Point K // p ∈ L.projectivization}) : Projectivization K L :=
  Projectivization.mk K ⟨p.val.rep, rep_mem_of_on K L p.val p.property⟩ (by
    intro h
    have hz : p.val.rep = 0 := congrArg Subtype.val h
    exact p.val.rep_nonzero hz)

theorem map_restrictPoint (L : Submodule K (Fin 3 → K))
    (p : {p : Point K // p ∈ L.projectivization}) :
    Projectivization.map L.subtype (by intro a b h; exact Subtype.ext h) (restrictPoint K L p) = p.val := by
  simp only [restrictPoint]
  exact p.val.mk_rep

theorem restrictPoint_injective (L : Submodule K (Fin 3 → K)) :
    Function.Injective (restrictPoint K L) := by
  intro p q hpq
  apply Subtype.ext
  have h := congrArg (Projectivization.map L.subtype (by intro a b h; exact Subtype.ext h)) hpq
  simpa only [map_restrictPoint] using h

theorem line_card_le (L : Submodule K (Fin 3 → K)) (hL : Module.finrank K L = 2) :
    (pointsOn K L).card ≤ Fintype.card K + 1 := by
  classical
  have hi := Nat.card_le_card_of_injective (restrictPoint K L) (restrictPoint_injective K L)
  have hc := Projectivization.card_of_finrank K (V := L) (n := 2) hL
  have he : (pointsOn K L).card = Nat.card {p : Point K // p ∈ L.projectivization} := by
    simp [pointsOn, Nat.card_eq_fintype_card, Fintype.card_subtype]
  rw [he]
  refine hi.trans_eq ?_
  simpa [Nat.card_eq_fintype_card, Finset.sum_range_succ, Nat.add_comm] using hc

theorem exists_complete_arc : ∃ S : Finset (Point K), IsCompleteArc K S := by
  classical
  let candidates := (Finset.univ : Finset (Point K)).powerset.filter (IsArc K)
  have he : candidates.Nonempty := ⟨∅, by simp [candidates, empty_isArc]⟩
  obtain ⟨S, hS, hmax⟩ := candidates.exists_max_image Finset.card he
  have hArc : IsArc K S := (Finset.mem_filter.mp hS).2
  refine ⟨S, hArc, ?_⟩
  intro p hp hins
  have hmem : insert p S ∈ candidates := by simp [candidates, hins]
  have hle := hmax (insert p S) hmem
  rw [Finset.card_insert_of_notMem hp] at hle
  omega

theorem exists_min_complete_arc :
    ∃ S : Finset (Point K), IsCompleteArc K S ∧
      ∀ T : Finset (Point K), IsCompleteArc K T → S.card ≤ T.card := by
  classical
  obtain ⟨S, hS⟩ := exists_complete_arc K
  let candidates := (Finset.univ : Finset (Point K)).powerset.filter (IsCompleteArc K)
  have he : candidates.Nonempty := ⟨S, by simp [candidates, hS]⟩
  obtain ⟨T, hT, hmin⟩ := candidates.exists_min_image Finset.card he
  refine ⟨T, (Finset.mem_filter.mp hT).2, ?_⟩
  intro U hU
  exact hmin U (by simp [candidates, hU])

noncomputable def minArc : Finset (Point K) := Classical.choose (exists_min_complete_arc K)

theorem minArc_complete : IsCompleteArc K (minArc K) :=
  (Classical.choose_spec (exists_min_complete_arc K)).1

theorem minArc_minimal (T : Finset (Point K)) (hT : IsCompleteArc K T) :
    (minArc K).card ≤ T.card :=
  (Classical.choose_spec (exists_min_complete_arc K)).2 T hT

noncomputable def minSize : ℕ := (minArc K).card

noncomputable def pairLine (p q : Point K) : Submodule K (Fin 3 → K) :=
  Submodule.span K {p.rep, q.rep}

theorem pairLine_finrank (p q : Point K) (hpq : p ≠ q) :
    Module.finrank K (pairLine K p q) = 2 := by
  have hi : LinearIndependent K ![p.rep, q.rep] := by
    apply (Projectivization.independent_mk_iff_LinearIndependent p.rep_nonzero q.rep_nonzero).mp
    simpa only [p.mk_rep, q.mk_rep] using
      ((Projectivization.independent_pair_iff_ne p q).mpr hpq)
  rw [pairLine, ← Matrix.range_cons_cons_empty _ _ ![]]
  simpa using finrank_span_eq_card hi

theorem left_mem_pairLine (p q : Point K) : p ∈ (pairLine K p q).projectivization := by
  rw [← p.mk_rep, Submodule.mk_mem_projectivization_iff]
  exact Submodule.subset_span (by simp)

theorem right_mem_pairLine (p q : Point K) : q ∈ (pairLine K p q).projectivization := by
  rw [← q.mk_rep, Submodule.mk_mem_projectivization_iff]
  exact Submodule.subset_span (by simp)

theorem outside_on_secant (S : Finset (Point K)) (hS : IsCompleteArc K S)
    (x : Point K) (hx : x ∉ S) :
    ∃ p ∈ S, ∃ q ∈ S, p ≠ q ∧ x ∈ (pairLine K p q).projectivization := by
  classical
  have hbad := hS.2 x hx
  change ¬ ∀ L : Submodule K (Fin 3 → K), Module.finrank K L = 2 →
    (insert x S ∩ pointsOn K L).card ≤ 2 at hbad
  push Not at hbad
  obtain ⟨L, hL, hc⟩ := hbad
  have hxL : x ∈ pointsOn K L := by
    by_contra hn
    have he : insert x S ∩ pointsOn K L = S ∩ pointsOn K L := by
      ext p
      simp only [Finset.mem_inter, Finset.mem_insert]
      aesop
    rw [he] at hc
    exact (not_lt_of_ge (hS.1 L hL)) hc
  have hxnot : x ∉ S ∩ pointsOn K L := by simp [hx]
  have he : insert x S ∩ pointsOn K L = insert x (S ∩ pointsOn K L) := by
    ext p
    simp only [Finset.mem_inter, Finset.mem_insert]
    aesop
  have htwo : (S ∩ pointsOn K L).card = 2 := by
    rw [he, Finset.card_insert_of_notMem hxnot] at hc
    have hu := hS.1 L hL
    omega
  obtain ⟨p, q, hpq, heq⟩ := Finset.card_eq_two.mp htwo
  have hp : p ∈ S ∩ pointsOn K L := by rw [heq]; simp
  have hq : q ∈ S ∩ pointsOn K L := by rw [heq]; simp
  have hpL : p ∈ L.projectivization := by simpa [pointsOn] using (Finset.mem_inter.mp hp).2
  have hqL : q ∈ L.projectivization := by simpa [pointsOn] using (Finset.mem_inter.mp hq).2
  have hline : L = pairLine K p q :=
    Projectivization.line_unique hpq L (pairLine K p q) hL (pairLine_finrank K p q hpq)
      hpL hqL (left_mem_pairLine K p q) (right_mem_pairLine K p q)
  refine ⟨p, (Finset.mem_inter.mp hp).1, q, (Finset.mem_inter.mp hq).1, hpq, ?_⟩
  rw [← hline]
  simpa [pointsOn] using hxL

noncomputable def secant (T : Finset (Point K)) : Submodule K (Fin 3 → K) :=
  Submodule.span K (Projectivization.rep '' (T : Set (Point K)))

theorem secant_pair [DecidableEq (Point K)] (p q : Point K) : secant K {p, q} = pairLine K p q := by
  classical
  simp only [secant, pairLine, Finset.coe_pair, Set.image_pair]

theorem secant_finrank (T : Finset (Point K)) (hT : T.card = 2) :
    Module.finrank K (secant K T) = 2 := by
  classical
  obtain ⟨p, q, hpq, rfl⟩ := Finset.card_eq_two.mp hT
  rw [secant_pair]
  exact pairLine_finrank K p q hpq

theorem cover_count (S : Finset (Point K)) (hS : IsCompleteArc K S) :
    Fintype.card K ^ 2 + Fintype.card K + 1 ≤
      S.card + S.card.choose 2 * (Fintype.card K + 1) := by
  classical
  let family := S.powersetCard 2
  let cover := S ∪ family.biUnion (fun T => pointsOn K (secant K T))
  have hall : (Finset.univ : Finset (Point K)) ⊆ cover := by
    intro x _
    by_cases hx : x ∈ S
    · exact Finset.mem_union_left _ hx
    · obtain ⟨p, hp, q, hq, hpq, hxline⟩ := outside_on_secant K S hS x hx
      apply Finset.mem_union_right
      apply Finset.mem_biUnion.mpr
      refine ⟨{p, q}, ?_, ?_⟩
      · apply Finset.mem_powersetCard.mpr
        constructor
        · intro y hy
          simp only [Finset.mem_insert, Finset.mem_singleton] at hy
          rcases hy with rfl | rfl
          · exact hp
          · exact hq
        · simp [hpq]
      · simpa [pointsOn, secant_pair] using hxline
  have hline (T : Finset (Point K)) (hT : T ∈ family) :
      (pointsOn K (secant K T)).card ≤ Fintype.card K + 1 :=
    line_card_le K (secant K T) (secant_finrank K T (Finset.mem_powersetCard.mp hT).2)
  calc
    Fintype.card K ^ 2 + Fintype.card K + 1 = (Finset.univ : Finset (Point K)).card := by
      simpa using (plane_card K).symm
    _ ≤ cover.card := Finset.card_le_card hall
    _ ≤ S.card + (family.biUnion (fun T => pointsOn K (secant K T))).card :=
      Finset.card_union_le _ _
    _ ≤ S.card + ∑ T ∈ family, (pointsOn K (secant K T)).card := by
      exact Nat.add_le_add_left (Finset.card_biUnion_le) _
    _ ≤ S.card + ∑ T ∈ family, (Fintype.card K + 1) := by
      exact Nat.add_le_add_left (Finset.sum_le_sum hline) _
    _ = S.card + S.card.choose 2 * (Fintype.card K + 1) := by
      simp [family]

theorem two_choose_real (n : ℕ) : 2 * (n.choose 2 : ℝ) = (n : ℝ)^2 - n := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    rw [Nat.choose_succ_succ, Nat.choose_one_right]
    push_cast
    nlinarith

theorem complete_arc_square_bound (S : Finset (Point K)) (hS : IsCompleteArc K S) :
    (2 : ℝ) * Fintype.card K < (S.card : ℝ)^2 := by
  have hq : (2 : ℝ) ≤ Fintype.card K := by
    have hq' : 1 < Nat.card K := Finite.one_lt_card
    have hq'' : 2 ≤ Nat.card K := by omega
    rw [Nat.card_eq_fintype_card] at hq''
    exact_mod_cast hq''
  have hc : (Fintype.card K : ℝ)^2 + Fintype.card K + 1 ≤
      S.card + (S.card.choose 2 : ℝ) * (Fintype.card K + 1) := by
    exact_mod_cast cover_count K S hS
  have ht := two_choose_real S.card
  have hk : (0 : ℝ) ≤ S.card := Nat.cast_nonneg _
  have hnonneg : 0 ≤ ((Fintype.card K : ℝ) - 1) * S.card :=
    mul_nonneg (by linarith) hk
  by_contra hn
  have hn' : (S.card : ℝ)^2 ≤ 2 * Fintype.card K := le_of_not_gt hn
  have hm := mul_le_mul_of_nonneg_left hn' (show 0 ≤ (Fintype.card K : ℝ) + 1 by linarith)
  nlinarith

noncomputable def sqrtTwo : ℝ≥0 := ⟨Real.sqrt 2, Real.sqrt_nonneg 2⟩

theorem sqrtTwo_gt_one : (1 : ℝ≥0) < sqrtTwo := by
  change (1 : ℝ) < Real.sqrt 2
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  have hp := Real.sqrt_nonneg (2 : ℝ)
  nlinarith

noncomputable def minRatio : ℝ≥0 :=
  ⟨(minSize K : ℝ) / Real.sqrt (Fintype.card K),
    div_nonneg (Nat.cast_nonneg _) (Real.sqrt_nonneg _)⟩

theorem minRatio_lower : sqrtTwo ≤ minRatio K := by
  change Real.sqrt 2 ≤ (minSize K : ℝ) / Real.sqrt (Fintype.card K)
  have hq : (0 : ℝ) < Fintype.card K := by
    exact_mod_cast Fintype.card_pos (α := K)
  have hs : 0 < Real.sqrt (Fintype.card K : ℝ) := Real.sqrt_pos.mpr hq
  apply (le_div_iff₀ hs).mpr
  have hk : (0 : ℝ) ≤ minSize K := Nat.cast_nonneg _
  have hprod : (Real.sqrt 2 * Real.sqrt (Fintype.card K : ℝ)) ^ 2 =
      2 * Fintype.card K := by
    rw [mul_pow, Real.sq_sqrt (by norm_num), Real.sq_sqrt hq.le]
  have hbound := complete_arc_square_bound K (minArc K) (minArc_complete K)
  change 2 * (Fintype.card K : ℝ) < (minSize K : ℝ)^2 at hbound
  have hp := mul_nonneg (Real.sqrt_nonneg (2 : ℝ))
    (Real.sqrt_nonneg (Fintype.card K : ℝ))
  nlinarith

theorem real_liminf_ne_one_of_lower (u : ℕ → ℝ≥0) (hu : ∀ n, sqrtTwo ≤ u n) :
    Filter.liminf (fun n => (u n : ℝ)) Filter.atTop ≠ 1 := by
  intro h
  rw [NNReal.toReal_liminf] at h
  have he : Filter.liminf u Filter.atTop = 1 := by exact_mod_cast h
  by_cases hc : Filter.atTop.IsCoboundedUnder (· ≥ ·) u
  · have hl : sqrtTwo ≤ Filter.liminf u Filter.atTop :=
      Filter.le_liminf_of_le hc (Filter.Eventually.of_forall hu)
    rw [he] at hl
    exact (not_le_of_gt sqrtTwo_gt_one) hl
  · have hz := NNReal.liminf_of_not_isCoboundedUnder hc
    rw [he] at hz
    exact one_ne_zero hz

theorem extended_liminf_lower (F : ℕ → Type*) [∀ n, Field (F n)] [∀ n, Fintype (F n)] :
    (sqrtTwo : ℝ≥0∞) ≤ Filter.liminf (fun n => (minRatio (F n) : ℝ≥0∞)) Filter.atTop := by
  apply Filter.le_liminf_of_le (by isBoundedDefault)
  exact Filter.Eventually.of_forall fun n => by exact_mod_cast minRatio_lower (F n)

/-- This holds for every finite-field sequence, hence for any enumeration of all
prime-power field sizes; the growing-cardinality hypothesis states the intended regime. -/
theorem growing_fields_real_liminf_ne_one (F : ℕ → Type*)
    [∀ n, Field (F n)] [∀ n, Fintype (F n)]
    (_hq : Filter.Tendsto (fun n => Fintype.card (F n)) Filter.atTop Filter.atTop) :
    Filter.liminf (fun n => ((minRatio (F n) : ℝ≥0) : ℝ)) Filter.atTop ≠ 1 :=
  real_liminf_ne_one_of_lower _ (fun n => minRatio_lower (F n))

end TLMC1002
