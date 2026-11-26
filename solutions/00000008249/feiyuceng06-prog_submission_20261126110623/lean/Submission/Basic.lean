import Mathlib.Analysis.Convex.Basic
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Tactic

namespace Conjecture8249

open Set

abbrev Utilities := ℝ × ℝ

/-- Individually rational feasible utilities for a two-player bargaining problem. -/
structure BargainingProblem where
  feasible : Set Utilities
  disagreement : Utilities
  compact : IsCompact feasible
  convex : Convex ℝ feasible
  individuallyRational : ∀ p ∈ feasible, disagreement ≤ p
  strictlyImproves : ∃ p ∈ feasible, disagreement.1 < p.1 ∧ disagreement.2 < p.2

def Pareto (B : BargainingProblem) (p : Utilities) : Prop :=
  p ∈ B.feasible ∧ ∀ q ∈ B.feasible, p ≤ q → q = p

def nashProduct (d p : Utilities) : ℝ :=
  (p.1 - d.1) * (p.2 - d.2)

def IsNash (B : BargainingProblem) (p : Utilities) : Prop :=
  p ∈ B.feasible ∧ IsMaxOn (nashProduct B.disagreement) B.feasible p

def IsIdeal (B : BargainingProblem) (u : Utilities) : Prop :=
  IsGreatest (Prod.fst '' B.feasible) u.1 ∧ IsGreatest (Prod.snd '' B.feasible) u.2

def mixture (weight : ℝ) (nash ks : Utilities) : Utilities :=
  weight • nash + (1 - weight) • ks

/-- The coordinatewise greatest feasible point on the line through disagreement and ideal. -/
def IsKalaiSmorodinsky (B : BargainingProblem) (p : Utilities) : Prop :=
  ∃ u, IsIdeal B u ∧ IsGreatest (B.feasible ∩ range (fun t => mixture t u B.disagreement)) p

def IsMixtureAtWeight (B : BargainingProblem) (w : ℝ) (p : Utilities) : Prop :=
  ∃ n k, IsNash B n ∧ IsKalaiSmorodinsky B k ∧ p = mixture w n k

def IsMixture (B : BargainingProblem) (p : Utilities) : Prop :=
  ∃ w ∈ Icc (0 : ℝ) 1, IsMixtureAtWeight B w p

/-- Independent positive affine changes of the two players' utility units. -/
structure UnitChange where
  scale : Utilities
  shift : Utilities
  fst_pos : 0 < scale.1
  snd_pos : 0 < scale.2

def UnitChange.apply (g : UnitChange) (p : Utilities) : Utilities :=
  (g.scale.1 * p.1 + g.shift.1, g.scale.2 * p.2 + g.shift.2)

private theorem UnitChange.continuous (g : UnitChange) : Continuous g.apply := by
  exact ((continuous_const.mul continuous_fst).add continuous_const).prodMk
    ((continuous_const.mul continuous_snd).add continuous_const)

private theorem UnitChange.fst_le_iff (g : UnitChange) (p q : Utilities) :
    (g.apply p).1 ≤ (g.apply q).1 ↔ p.1 ≤ q.1 := by
  change g.scale.1 * p.1 + g.shift.1 ≤ g.scale.1 * q.1 + g.shift.1 ↔ p.1 ≤ q.1
  rw [add_le_add_iff_right, mul_le_mul_iff_right₀ g.fst_pos]

private theorem UnitChange.snd_le_iff (g : UnitChange) (p q : Utilities) :
    (g.apply p).2 ≤ (g.apply q).2 ↔ p.2 ≤ q.2 := by
  change g.scale.2 * p.2 + g.shift.2 ≤ g.scale.2 * q.2 + g.shift.2 ↔ p.2 ≤ q.2
  rw [add_le_add_iff_right, mul_le_mul_iff_right₀ g.snd_pos]

def BargainingProblem.changeUnits (B : BargainingProblem) (g : UnitChange) :
    BargainingProblem where
  feasible := g.apply '' B.feasible
  disagreement := g.apply B.disagreement
  compact := B.compact.image g.continuous
  convex := by
    intro _ hp _ hq a b ha hb hab
    obtain ⟨p, hp, rfl⟩ := hp
    obtain ⟨q, hq, rfl⟩ := hq
    refine ⟨a • p + b • q, B.convex hp hq ha hb hab, ?_⟩
    apply Prod.ext
    · change g.scale.1 * (a * p.1 + b * q.1) + g.shift.1 =
        a * (g.scale.1 * p.1 + g.shift.1) + b * (g.scale.1 * q.1 + g.shift.1)
      linear_combination -g.shift.1 * hab
    · change g.scale.2 * (a * p.2 + b * q.2) + g.shift.2 =
        a * (g.scale.2 * p.2 + g.shift.2) + b * (g.scale.2 * q.2 + g.shift.2)
      linear_combination -g.shift.2 * hab
  individuallyRational := by
    rintro _ ⟨p, hp, rfl⟩
    obtain ⟨hfst, hsnd⟩ := B.individuallyRational p hp
    exact ⟨(g.fst_le_iff _ _).2 hfst, (g.snd_le_iff _ _).2 hsnd⟩
  strictlyImproves := by
    obtain ⟨p, hp, hfst, hsnd⟩ := B.strictlyImproves
    refine ⟨g.apply p, ⟨p, hp, rfl⟩, ?_, ?_⟩
    · exact add_lt_add_left (mul_lt_mul_of_pos_left hfst g.fst_pos) _
    · exact add_lt_add_left (mul_lt_mul_of_pos_left hsnd g.snd_pos) _

abbrev Rule := BargainingProblem → Utilities

def AffineCovariant (f : Rule) : Prop :=
  ∀ (B : BargainingProblem) (g : UnitChange), f (B.changeUnits g) = g.apply (f B)

def ScaleCovariant (f : Rule) : Prop :=
  ∀ (B : BargainingProblem) (g : UnitChange), g.shift = 0 →
    f (B.changeUnits g) = g.apply (f B)

def ParetoRule (f : Rule) : Prop :=
  ∀ B, Pareto B (f B)

def FixedWeightMixtureRule (f : Rule) : Prop :=
  ∃ w ∈ Icc (0 : ℝ) 1, ∀ B, IsMixtureAtWeight B w (f B)

/-- The conjectured two-axiom characterization of fixed-weight mixtures. -/
def MixtureCharacterization : Prop :=
  ∀ f : Rule, (ScaleCovariant f ∧ ParetoRule f) ↔ FixedWeightMixtureRule f

/-- First maximize player 1's utility, then maximize player 2's utility on that face. -/
def IsLexMax (B : BargainingProblem) (p : Utilities) : Prop :=
  p ∈ B.feasible ∧
    ∀ q ∈ B.feasible, q.1 ≤ p.1 ∧ (q.1 = p.1 → q.2 ≤ p.2)

theorem exists_lexMax (B : BargainingProblem) : ∃ p, IsLexMax B p := by
  obtain ⟨p₀, hp₀, _, _⟩ := B.strictlyImproves
  obtain ⟨p, hp, hmax⟩ := B.compact.exists_isMaxOn ⟨p₀, hp₀⟩ continuous_fst.continuousOn
  let face := B.feasible ∩ {q : Utilities | q.1 = p.1}
  have face_compact : IsCompact face :=
    B.compact.inter_right (isClosed_eq continuous_fst continuous_const)
  obtain ⟨r, hr, hsecond⟩ :=
    face_compact.exists_isMaxOn ⟨p, hp, rfl⟩ continuous_snd.continuousOn
  have hr_first : r.1 = p.1 := hr.2
  refine ⟨r, hr.1, fun q hq => ⟨?_, ?_⟩⟩
  · rw [hr_first]
    exact hmax hq
  · intro hq_first
    exact hsecond (show q ∈ face from ⟨hq, hq_first.trans hr_first⟩)

theorem lexMax_unique {B : BargainingProblem} {p q : Utilities}
    (hp : IsLexMax B p) (hq : IsLexMax B q) : p = q := by
  obtain ⟨hqp, hqp₂⟩ := hp.2 q hq.1
  obtain ⟨hpq, hpq₂⟩ := hq.2 p hp.1
  have hfst := le_antisymm hpq hqp
  exact Prod.ext hfst (le_antisymm (hpq₂ hfst) (hqp₂ hfst.symm))

theorem IsLexMax.pareto {B : BargainingProblem} {p : Utilities} (hp : IsLexMax B p) :
    Pareto B p := by
  refine ⟨hp.1, fun q hq hdom => ?_⟩
  have hfst := le_antisymm (hp.2 q hq).1 hdom.1
  exact Prod.ext hfst (le_antisymm ((hp.2 q hq).2 hfst) hdom.2)

theorem IsLexMax.changeUnits {B : BargainingProblem} {p : Utilities}
    (hp : IsLexMax B p) (g : UnitChange) : IsLexMax (B.changeUnits g) (g.apply p) := by
  refine ⟨⟨p, hp.1, rfl⟩, ?_⟩
  rintro _ ⟨q, hq, rfl⟩
  obtain ⟨hfst, hsnd⟩ := hp.2 q hq
  refine ⟨(g.fst_le_iff _ _).2 hfst, fun heq => (g.snd_le_iff _ _).2 (hsnd ?_)⟩
  exact le_antisymm hfst ((g.fst_le_iff _ _).1 heq.ge)

noncomputable def lexRule (B : BargainingProblem) : Utilities :=
  (exists_lexMax B).choose

theorem lexRule_isLexMax (B : BargainingProblem) : IsLexMax B (lexRule B) :=
  (exists_lexMax B).choose_spec

theorem lexRule_affineCovariant : AffineCovariant lexRule :=
  fun B g => lexMax_unique (lexRule_isLexMax (B.changeUnits g))
    ((lexRule_isLexMax B).changeUnits g)

theorem lexRule_scaleCovariant : ScaleCovariant lexRule :=
  fun B g _ => lexRule_affineCovariant B g

theorem lexRule_pareto : ParetoRule lexRule :=
  fun B => (lexRule_isLexMax B).pareto

/-- The feasible polygon used in both counterexamples. -/
def polygon : Set Utilities :=
  {p | 0 ≤ p.1 ∧ 0 ≤ p.2 ∧ p.1 ≤ 32 ∧ p.1 + 2 * p.2 ≤ 64 ∧
    2 * p.1 + 3 * p.2 ≤ 108}

theorem mem_polygon (p : Utilities) :
    p ∈ polygon ↔ 0 ≤ p.1 ∧ 0 ≤ p.2 ∧ p.1 ≤ 32 ∧ p.1 + 2 * p.2 ≤ 64 ∧
      2 * p.1 + 3 * p.2 ≤ 108 :=
  Iff.rfl

private theorem polygon_compact : IsCompact polygon := by
  have hclosed : IsClosed polygon := by
    exact (isClosed_le continuous_const continuous_fst).inter <|
      (isClosed_le continuous_const continuous_snd).inter <|
      (isClosed_le continuous_fst continuous_const).inter <|
      (isClosed_le (continuous_fst.add (continuous_const.mul continuous_snd))
        continuous_const).inter <|
      isClosed_le ((continuous_const.mul continuous_fst).add
        (continuous_const.mul continuous_snd)) continuous_const
  refine IsCompact.of_isClosed_subset (isCompact_Icc (α := Utilities)
    (a := (0, 0)) (b := (32, 32))) hclosed ?_
  intro p hp
  obtain ⟨hx, hy, hxmax, h₁, _⟩ := (mem_polygon p).1 hp
  exact ⟨⟨hx, hy⟩, ⟨hxmax, by linarith⟩⟩

private theorem polygon_convex : Convex ℝ polygon := by
  intro p hp q hq a b ha hb hab
  obtain ⟨px, py, pxmax, p₁, p₂⟩ := (mem_polygon p).1 hp
  obtain ⟨qx, qy, qxmax, q₁, q₂⟩ := (mem_polygon q).1 hq
  refine (mem_polygon _).2 ⟨?_, ?_, ?_, ?_, ?_⟩
  · change 0 ≤ a * p.1 + b * q.1
    exact add_nonneg (mul_nonneg ha px) (mul_nonneg hb qx)
  · change 0 ≤ a * p.2 + b * q.2
    exact add_nonneg (mul_nonneg ha py) (mul_nonneg hb qy)
  · change a * p.1 + b * q.1 ≤ 32
    nlinarith [mul_le_mul_of_nonneg_left pxmax ha, mul_le_mul_of_nonneg_left qxmax hb]
  · change a * p.1 + b * q.1 + 2 * (a * p.2 + b * q.2) ≤ 64
    nlinarith [mul_le_mul_of_nonneg_left p₁ ha, mul_le_mul_of_nonneg_left q₁ hb]
  · change 2 * (a * p.1 + b * q.1) + 3 * (a * p.2 + b * q.2) ≤ 108
    nlinarith [mul_le_mul_of_nonneg_left p₂ ha, mul_le_mul_of_nonneg_left q₂ hb]

def counterexample : BargainingProblem where
  feasible := polygon
  disagreement := (0, 0)
  compact := polygon_compact
  convex := polygon_convex
  individuallyRational := fun p hp => ⟨((mem_polygon p).1 hp).1, ((mem_polygon p).1 hp).2.1⟩
  strictlyImproves := by
    refine ⟨(1, 1), (mem_polygon _).2 ?_, ?_, ?_⟩ <;> norm_num

theorem disagreement_mem : counterexample.disagreement ∈ counterexample.feasible := by
  exact (mem_polygon (0, 0)).2 (by norm_num)

theorem polygon_comprehensive {p q : Utilities} (hp : p ∈ polygon)
    (hq0 : (0, 0) ≤ q) (hqp : q ≤ p) : q ∈ polygon := by
  obtain ⟨_, _, hpmax, hp₁, hp₂⟩ := (mem_polygon p).1 hp
  exact (mem_polygon q).2 ⟨hq0.1, hq0.2, hqp.1.trans hpmax,
    by linarith [hqp.1, hqp.2], by linarith [hqp.1, hqp.2]⟩

theorem counterexample_ideal : IsIdeal counterexample (32, 32) := by
  constructor
  · refine ⟨⟨(32, 0), (mem_polygon _).2 (by norm_num), rfl⟩, ?_⟩
    rintro _ ⟨p, hp, rfl⟩
    exact ((mem_polygon p).1 hp).2.2.1
  · refine ⟨⟨(0, 32), (mem_polygon _).2 (by norm_num), rfl⟩, ?_⟩
    rintro _ ⟨p, hp, rfl⟩
    obtain ⟨hx, _, _, h₁, _⟩ := (mem_polygon p).1 hp
    change p.2 ≤ 32
    linarith

def nashPoint : Utilities := (27, 18)
noncomputable def ksPoint : Utilities := (64 / 3, 64 / 3)
noncomputable def lexPoint : Utilities := (32, 44 / 3)

theorem counterexample_nash : IsNash counterexample nashPoint := by
  refine ⟨(mem_polygon _).2 (by norm_num [nashPoint]), ?_⟩
  intro p hp
  obtain ⟨hx, _, _, _, h₂⟩ := (mem_polygon p).1 hp
  change (p.1 - 0) * (p.2 - 0) ≤ (27 - 0) * (18 - 0)
  nlinarith [mul_le_mul_of_nonneg_left h₂ hx, sq_nonneg (p.1 - 27)]

theorem counterexample_nash_unique {p : Utilities} (hp : IsNash counterexample p) :
    p = nashPoint := by
  obtain ⟨hx, _, _, _, h₂⟩ := (mem_polygon p).1 hp.1
  have hprod := hp.2 counterexample_nash.1
  change (27 - 0) * (18 - 0) ≤ (p.1 - 0) * (p.2 - 0) at hprod
  have hsq : (p.1 - 27) ^ 2 ≤ 0 := by
    nlinarith [mul_le_mul_of_nonneg_left h₂ hx]
  have hfst : p.1 = 27 := by nlinarith [sq_nonneg (p.1 - 27)]
  apply Prod.ext hfst
  change p.2 = 18
  rw [hfst] at hprod h₂
  apply le_antisymm <;> linarith

private theorem ks_isGreatest_on_ideal_line :
    IsGreatest (counterexample.feasible ∩ range
      (fun t => mixture t (32, 32) counterexample.disagreement)) ksPoint := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · exact (mem_polygon _).2 (by norm_num [ksPoint])
  · refine ⟨2 / 3, ?_⟩
    apply Prod.ext <;>
      change (2 / 3 : ℝ) * 32 + (1 - 2 / 3) * 0 = 64 / 3 <;> norm_num
  · rintro p ⟨hp, t, rfl⟩
    have h := ((mem_polygon _).1 hp).2.2.2.1
    change t * 32 + (1 - t) * 0 + 2 * (t * 32 + (1 - t) * 0) ≤ 64 at h
    exact ⟨show t * 32 + (1 - t) * 0 ≤ 64 / 3 by linarith,
      show t * 32 + (1 - t) * 0 ≤ 64 / 3 by linarith⟩

theorem counterexample_ks : IsKalaiSmorodinsky counterexample ksPoint :=
  ⟨(32, 32), counterexample_ideal, ks_isGreatest_on_ideal_line⟩

theorem counterexample_ks_unique {p : Utilities}
    (hp : IsKalaiSmorodinsky counterexample p) : p = ksPoint := by
  obtain ⟨u, hu, hp⟩ := hp
  have hu_eq : u = (32, 32) :=
    Prod.ext (hu.1.unique counterexample_ideal.1) (hu.2.unique counterexample_ideal.2)
  subst u
  exact hp.unique ks_isGreatest_on_ideal_line

theorem counterexample_lex : IsLexMax counterexample lexPoint := by
  refine ⟨(mem_polygon _).2 (by norm_num [lexPoint]), fun p hp => ⟨?_, ?_⟩⟩
  · exact ((mem_polygon p).1 hp).2.2.1
  · intro hp_first
    have h := ((mem_polygon p).1 hp).2.2.2.2
    change p.1 = 32 at hp_first
    change p.2 ≤ 44 / 3
    linarith

theorem counterexample_lex_not_mixture :
    ¬ IsMixture counterexample (lexRule counterexample) := by
  rintro ⟨w, hw, n, k, hn, hk, heq⟩
  rw [lexMax_unique (lexRule_isLexMax counterexample) counterexample_lex,
    counterexample_nash_unique hn, counterexample_ks_unique hk] at heq
  have h := congrArg Prod.fst heq
  change (32 : ℝ) = w * 27 + (1 - w) * (64 / 3) at h
  linarith [hw.2]

theorem axioms_do_not_force_pointwise_mixtures :
    ¬ ∀ f : Rule, (ScaleCovariant f ∧ ParetoRule f) → ∀ B, IsMixture B (f B) := by
  intro h
  exact counterexample_lex_not_mixture
    (h lexRule ⟨lexRule_scaleCovariant, lexRule_pareto⟩ counterexample)

theorem disprove_conjecture_00000008249 : ¬ MixtureCharacterization := by
  intro h
  obtain ⟨w, hw, hmix⟩ := (h lexRule).1 ⟨lexRule_scaleCovariant, lexRule_pareto⟩
  exact counterexample_lex_not_mixture ⟨w, hw, hmix counterexample⟩

theorem counterexample_nash_pareto : Pareto counterexample nashPoint := by
  refine ⟨counterexample_nash.1, fun p hp hdom => ?_⟩
  have h := ((mem_polygon p).1 hp).2.2.2.2
  have hx : 27 ≤ p.1 := hdom.1
  have hy : 18 ≤ p.2 := hdom.2
  exact Prod.ext (show p.1 = 27 by linarith) (show p.2 = 18 by linarith)

theorem counterexample_ks_pareto : Pareto counterexample ksPoint := by
  refine ⟨ks_isGreatest_on_ideal_line.1.1, fun p hp hdom => ?_⟩
  have h := ((mem_polygon p).1 hp).2.2.2.1
  have hx : 64 / 3 ≤ p.1 := hdom.1
  have hy : 64 / 3 ≤ p.2 := hdom.2
  exact Prod.ext (show p.1 = 64 / 3 by linarith) (show p.2 = 64 / 3 by linarith)

theorem counterexample_mixture_feasible (w : ℝ) (hw : w ∈ Icc (0 : ℝ) 1) :
    mixture w nashPoint ksPoint ∈ counterexample.feasible :=
  counterexample.convex counterexample_nash.1 ks_isGreatest_on_ideal_line.1.1
    hw.1 (sub_nonneg.mpr hw.2) (by ring)

theorem interior_mixture_strictly_dominated {w : ℝ} (hw₀ : 0 < w) (hw₁ : w < 1) :
    ∃ q ∈ counterexample.feasible,
      (mixture w nashPoint ksPoint).1 < q.1 ∧
      (mixture w nashPoint ksPoint).2 < q.2 := by
  let e := min w (1 - w) / 6
  have he : 0 < e := div_pos (lt_min hw₀ (sub_pos.mpr hw₁)) (by norm_num)
  have he_n : e ≤ w / 6 := div_le_div_of_nonneg_right (min_le_left _ _) (by norm_num)
  have he_k : e ≤ (1 - w) / 6 :=
    div_le_div_of_nonneg_right (min_le_right _ _) (by norm_num)
  let x := w * 27 + (1 - w) * (64 / 3)
  let y := w * 18 + (1 - w) * (64 / 3)
  refine ⟨(x + e, y + e), (mem_polygon _).2 ?_, ?_, ?_⟩
  · change 0 ≤ x + e ∧ 0 ≤ y + e ∧ x + e ≤ 32 ∧
      (x + e) + 2 * (y + e) ≤ 64 ∧ 2 * (x + e) + 3 * (y + e) ≤ 108
    dsimp [x, y]
    exact ⟨by linarith, by linarith, by linarith, by linarith, by linarith⟩
  · change x < x + e
    linarith
  · change y < y + e
    linarith

theorem interior_mixture_not_pareto {w : ℝ} (hw₀ : 0 < w) (hw₁ : w < 1) :
    ¬ Pareto counterexample (mixture w nashPoint ksPoint) := by
  intro h
  obtain ⟨q, hq, hx, hy⟩ := interior_mixture_strictly_dominated hw₀ hw₁
  have heq := h.2 q hq ⟨hx.le, hy.le⟩
  exact hx.ne (congrArg Prod.fst heq).symm

theorem interior_weight_rule_not_pareto {f : Rule} {w : ℝ} (hw₀ : 0 < w) (hw₁ : w < 1)
    (hmix : ∀ B, IsMixtureAtWeight B w (f B)) : ¬ ParetoRule f := by
  intro hf
  obtain ⟨n, k, hn, hk, heq⟩ := hmix counterexample
  rw [counterexample_nash_unique hn, counterexample_ks_unique hk] at heq
  exact interior_mixture_not_pareto hw₀ hw₁ (heq ▸ hf counterexample)

end Conjecture8249
