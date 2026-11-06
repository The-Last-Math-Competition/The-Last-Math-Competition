import Mathlib

/-!
# Minimal Kakeya sets in `AG(2,q)`, `q` odd  (conjecture 00000001064)

A *Kakeya set* in the affine plane `F × F` over a finite field `F` is a set containing a full
affine line in every direction: for every slope `m` a line `y = m x + b`, and a vertical line
`x = c`.  We prove the theorem of Blokhuis–Mazzocca: for `q = |F|` odd the minimum size of a
Kakeya set is `q(q+1)/2 + (q-1)/2`.

Outline (see `PROOF.md`):
* `card_ge_easy`: Faber's incidence formula gives `|K| ≥ q(q+1)/2` for every `q`.
* `jamison`: a blocking set of `AG(2,q)` has at least `2q-1` points (polynomial method).
* parity: points of odd multiplicity, together with one extra point, form a blocking set; the
  product lemma `not_allTwo_pair` excludes two "all-2" lines; this yields the refinement
  `card_ge_odd`.
* `card_extremalSet`: the dual conic plus a vertical line attains the bound.
-/

open Finset

namespace Kakeya

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-! ### Lines -/

/-- The affine line `y = m x + b` (slope `m`, intercept `b`). -/
def lineS (m b : F) : Finset (F × F) := univ.image fun x => (x, m * x + b)

/-- The vertical affine line `x = c`. -/
def lineV (c : F) : Finset (F × F) := univ.image fun y => (c, y)

lemma mem_lineS {m b : F} {p : F × F} : p ∈ lineS m b ↔ p.2 = m * p.1 + b := by
  constructor
  · intro h
    simp only [lineS, mem_image, mem_univ, true_and] at h
    obtain ⟨x, rfl⟩ := h
    rfl
  · intro h
    simp only [lineS, mem_image, mem_univ, true_and]
    exact ⟨p.1, Prod.ext rfl h.symm⟩

omit [Field F] in
lemma mem_lineV {c : F} {p : F × F} : p ∈ lineV c ↔ p.1 = c := by
  constructor
  · intro h
    simp only [lineV, mem_image, mem_univ, true_and] at h
    obtain ⟨y, rfl⟩ := h
    rfl
  · intro h
    simp only [lineV, mem_image, mem_univ, true_and]
    exact ⟨p.2, Prod.ext h.symm rfl⟩

lemma card_lineS (m b : F) : (lineS m b).card = Fintype.card F := by
  rw [lineS, card_image_of_injective _ (fun x y h => (Prod.mk.inj h).1), card_univ]

omit [Field F] in
lemma card_lineV (c : F) : (lineV c).card = Fintype.card F := by
  rw [lineV, card_image_of_injective _ (fun x y h => (Prod.mk.inj h).2), card_univ]

/-- A Kakeya set: it contains a line `y = m x + b` for every slope `m`, and a vertical line. -/
def IsKakeya (K : Finset (F × F)) : Prop :=
  (∀ m : F, ∃ b : F, ∀ x : F, (x, m * x + b) ∈ K) ∧ ∃ c : F, ∀ y : F, (c, y) ∈ K

/-- The affine line with direction `d` and parameter `s`: `y = m x + s` if `d = some m`, and
`x = s` if `d = none` (the vertical direction). -/
def dirLine : Option F → F → Finset (F × F)
  | none, s => lineV s
  | some m, s => lineS m s

lemma card_dirLine (d : Option F) (s : F) : (dirLine d s).card = Fintype.card F := by
  cases d with
  | none => exact card_lineV s
  | some m => exact card_lineS m s

lemma card_inter_lineS_lineV (m b c : F) : (lineS m b ∩ lineV c).card = 1 := by
  rw [card_eq_one]
  refine ⟨(c, m * c + b), ?_⟩
  ext p
  simp only [mem_inter, mem_lineV, mem_lineS, mem_singleton]
  constructor
  · rintro ⟨h2, h1⟩
    exact Prod.ext h1 (by rw [h2, h1])
  · rintro rfl
    exact ⟨rfl, rfl⟩

lemma card_inter_lineS_lineS {m m' : F} (b b' : F) (hmm : m ≠ m') :
    (lineS m b ∩ lineS m' b').card = 1 := by
  rw [card_eq_one]
  have hsub : m - m' ≠ 0 := sub_ne_zero.mpr hmm
  refine ⟨((b' - b) / (m - m'), m * ((b' - b) / (m - m')) + b), ?_⟩
  ext p
  simp only [mem_inter, mem_lineS, mem_singleton]
  constructor
  · rintro ⟨h1, h2⟩
    have hx : p.1 = (b' - b) / (m - m') := by
      rw [eq_div_iff hsub]
      linear_combination h2 - h1
    exact Prod.ext hx (by rw [h1, hx])
  · rintro rfl
    refine ⟨rfl, ?_⟩
    simp only
    field_simp
    ring

/-- Two lines with different directions meet in exactly one point. -/
lemma card_inter_dirLine {d d' : Option F} (s s' : F) (h : d ≠ d') :
    (dirLine d s ∩ dirLine d' s').card = 1 := by
  cases d with
  | none =>
    cases d' with
    | none => exact absurd rfl h
    | some m => rw [dirLine, dirLine, inter_comm]; exact card_inter_lineS_lineV m s' s
  | some m =>
    cases d' with
    | none => exact card_inter_lineS_lineV m s s'
    | some m' => exact card_inter_lineS_lineS s s' (fun e => h (by rw [e]))

/-- Two distinct parallel lines are disjoint. -/
lemma disjoint_dirLine {d : Option F} {s s' : F} (h : s ≠ s') :
    Disjoint (dirLine d s) (dirLine d s') := by
  rw [disjoint_left]
  intro p hp hp'
  cases d with
  | none => rw [dirLine, mem_lineV] at hp hp'; exact h (hp.symm.trans hp')
  | some m => rw [dirLine, mem_lineS] at hp hp'; exact h (by linear_combination hp' - hp)

/-! ### Line systems

A *line system* is a choice of one line in each of the `q+1` directions, encoded by a function
`t : Option F → F` giving the parameter of the line in each direction. -/

/-- The line of direction `d` in the system `t`. -/
def sysLine (t : Option F → F) (d : Option F) : Finset (F × F) := dirLine d (t d)

lemma mem_sysLine_some {t : Option F → F} {m : F} {p : F × F} :
    p ∈ sysLine t (some m) ↔ p.2 = m * p.1 + t (some m) := mem_lineS

lemma mem_sysLine_none {t : Option F → F} {p : F × F} :
    p ∈ sysLine t none ↔ p.1 = t none := mem_lineV

lemma card_sysLine (t : Option F → F) (d : Option F) : (sysLine t d).card = Fintype.card F :=
  card_dirLine d (t d)

lemma card_inter_sysLine (t : Option F → F) {d d' : Option F} (h : d ≠ d') :
    (sysLine t d ∩ sysLine t d').card = 1 :=
  card_inter_dirLine (t d) (t d') h

lemma card_inter_dirLine_sysLine (t : Option F → F) {d d' : Option F} (s : F) (h : d ≠ d') :
    (dirLine d s ∩ sysLine t d').card = 1 :=
  card_inter_dirLine s (t d') h

/-- The multiplicity of a point: the number of lines of the system through it. -/
def mult (t : Option F → F) (A : F × F) : ℕ :=
  (univ.filter fun d : Option F => A ∈ sysLine t d).card

/-- The union of the lines of the system, as the set of points of positive multiplicity. -/
def cover (t : Option F → F) : Finset (F × F) :=
  univ.filter fun A => 1 ≤ mult t A

lemma mem_cover {t : Option F → F} {A : F × F} :
    A ∈ cover t ↔ ∃ d, A ∈ sysLine t d := by
  simp only [cover, mem_filter, mem_univ, true_and, mult, Nat.one_le_iff_ne_zero,
    ← Nat.pos_iff_ne_zero, card_pos, filter_nonempty_iff]

lemma mult_eq_sum (t : Option F → F) (A : F × F) :
    mult t A = ∑ d : Option F, if A ∈ sysLine t d then 1 else 0 := by
  rw [mult, card_filter]

omit [Field F] in
lemma sum_ite_mem (s : Finset (F × F)) :
    (∑ A : F × F, if A ∈ s then (1 : ℕ) else 0) = s.card := by
  rw [sum_boole, Nat.cast_id, filter_univ_mem]

/-- (C1) `∑_A mult A = (q+1) q`. -/
lemma sum_mult (t : Option F → F) :
    ∑ A : F × F, mult t A = (Fintype.card F + 1) * Fintype.card F := by
  simp_rw [mult_eq_sum]
  rw [sum_comm]
  simp_rw [sum_ite_mem, card_sysLine]
  rw [sum_const, card_univ, Fintype.card_option, smul_eq_mul]

omit [Field F] [DecidableEq F] in
lemma offDiag_filter (p : Option F → Prop) [DecidablePred p] :
    (univ.filter p).offDiag = univ.offDiag.filter fun x => p x.1 ∧ p x.2 := by
  ext x
  simp only [mem_offDiag, mem_filter, mem_univ, true_and]
  tauto

lemma mult_mul_pred (t : Option F → F) (A : F × F) :
    mult t A * (mult t A - 1) =
      ∑ x ∈ (univ : Finset (Option F)).offDiag,
        if A ∈ sysLine t x.1 ∧ A ∈ sysLine t x.2 then 1 else 0 := by
  rw [sum_boole, Nat.cast_id, ← offDiag_filter (fun d => A ∈ sysLine t d), offDiag_card, mult]
  exact Nat.mul_sub_one _ _

/-- (C2) `∑_A mult A (mult A - 1) = (q+1) q`. -/
lemma sum_mult_mul_pred (t : Option F → F) :
    ∑ A : F × F, mult t A * (mult t A - 1) = (Fintype.card F + 1) * Fintype.card F := by
  simp_rw [mult_mul_pred]
  rw [sum_comm]
  have : ∀ x ∈ (univ : Finset (Option F)).offDiag,
      (∑ A : F × F, if A ∈ sysLine t x.1 ∧ A ∈ sysLine t x.2 then 1 else 0) = 1 := by
    intro x hx
    rw [mem_offDiag] at hx
    have := sum_ite_mem (sysLine t x.1 ∩ sysLine t x.2)
    simp only [mem_inter] at this
    rw [this, card_inter_sysLine t hx.2.2]
  rw [sum_congr rfl this, sum_const, smul_eq_mul, mul_one, offDiag_card, card_univ,
    Fintype.card_option]
  have hq : 1 ≤ Fintype.card F := Fintype.card_pos
  generalize Fintype.card F = q at hq ⊢
  rcases Nat.exists_eq_add_of_le hq with ⟨k, rfl⟩
  ring_nf
  omega

/-! ### Faber's formula and the easy bound -/

/-- Pointwise identity behind Faber's formula. -/
lemma faber_pointwise (n : ℕ) :
    (2 : ℤ) * (if 1 ≤ n then 1 else 0) =
      2 * n - n * (n - 1) + (if 1 ≤ n then ((n : ℤ) - 1) * ((n : ℤ) - 2) else 0) := by
  split_ifs with h
  · ring
  · have : n = 0 := by omega
    subst this; simp

lemma cast_mult_mul_pred (n : ℕ) : ((n * (n - 1) : ℕ) : ℤ) = (n : ℤ) * ((n : ℤ) - 1) := by
  rcases Nat.eq_zero_or_pos n with h | h
  · subst h; simp
  · push_cast [Nat.cast_sub h]; ring

/-- The excess `2σ = ∑_{mult A ≥ 1} (mult A - 1)(mult A - 2)`. -/
def excess (t : Option F → F) : ℤ :=
  ∑ A : F × F, if 1 ≤ mult t A then ((mult t A : ℤ) - 1) * ((mult t A : ℤ) - 2) else 0

lemma excess_nonneg (t : Option F → F) : 0 ≤ excess t := by
  apply sum_nonneg
  intro A _
  split_ifs with h
  · rcases Nat.lt_or_ge (mult t A) 2 with h2 | h2
    · have : mult t A = 1 := by omega
      rw [this]; norm_num
    · have : (2 : ℤ) ≤ mult t A := by exact_mod_cast h2
      nlinarith
  · exact le_rfl

/-- Faber's formula: `2 |⋃ 𝓛| = q(q+1) + 2σ`. -/
lemma two_mul_card_cover (t : Option F → F) :
    2 * ((cover t).card : ℤ) = (Fintype.card F : ℤ) * (Fintype.card F + 1) + excess t := by
  have h1 : ((cover t).card : ℤ) = ∑ A : F × F, if 1 ≤ mult t A then (1 : ℤ) else 0 := by
    rw [sum_boole, cover]
  rw [h1, mul_sum, excess]
  have h2 : ∀ A : F × F, (2 : ℤ) * (if 1 ≤ mult t A then 1 else 0) =
      2 * (mult t A : ℤ) - ((mult t A * (mult t A - 1) : ℕ) : ℤ) +
        (if 1 ≤ mult t A then ((mult t A : ℤ) - 1) * ((mult t A : ℤ) - 2) else 0) := by
    intro A
    rw [cast_mult_mul_pred]
    exact faber_pointwise _
  rw [sum_congr rfl fun A _ => h2 A, sum_add_distrib, sum_sub_distrib, ← mul_sum]
  have h3' : (∑ A : F × F, (mult t A : ℤ)) = (Fintype.card F + 1) * Fintype.card F := by
    exact_mod_cast sum_mult t
  have h4' : (∑ A : F × F, ((mult t A * (mult t A - 1) : ℕ) : ℤ)) =
      (Fintype.card F + 1) * Fintype.card F := by
    exact_mod_cast sum_mult_mul_pred t
  rw [h3', h4']
  ring

/-- From a Kakeya set one extracts a line system whose union lies inside it. -/
lemma cover_subset {K : Finset (F × F)} (hK : IsKakeya K) :
    ∃ t : Option F → F, cover t ⊆ K := by
  obtain ⟨hS, c, hc⟩ := hK
  choose b hb using hS
  refine ⟨fun d => d.elim c b, fun A hA => ?_⟩
  obtain ⟨d, hd⟩ := mem_cover.mp hA
  cases d with
  | none =>
    rw [mem_sysLine_none] at hd
    change A.1 = c at hd
    have := hc A.2
    rw [← hd] at this
    exact this
  | some m =>
    rw [mem_sysLine_some] at hd
    change A.2 = m * A.1 + b m at hd
    have := hb m A.1
    rw [← hd] at this
    exact this

/-- **Easy lower bound** (Faber): every Kakeya set has at least `q(q+1)/2` points. -/
theorem card_ge_easy {K : Finset (F × F)} (hK : IsKakeya K) :
    Fintype.card F * (Fintype.card F + 1) / 2 ≤ K.card := by
  obtain ⟨t, hsub⟩ := cover_subset hK
  have h := two_mul_card_cover t
  have h0 := excess_nonneg t
  have h2 : Fintype.card F * (Fintype.card F + 1) ≤ 2 * (cover t).card := by
    have : (Fintype.card F : ℤ) * (Fintype.card F + 1) ≤ 2 * ((cover t).card : ℤ) := by linarith
    exact_mod_cast this
  exact (Nat.div_le_of_le_mul h2).trans (card_le_card hsub)

/-! ### Jamison's theorem: a blocking set of `AG(2,q)` has at least `2q - 1` points

Proof by the polynomial method (Brouwer–Schrijver, dualised): after translating `(0,0) ∈ B`, the
polynomial `f = ∏_{(a,b) ∈ B∖{0}} (1 - a X₀ + b X₁)` vanishes on `F² ∖ {0}` and `f(0) = 1`, so
`∑_v f(v) = 1`; but if `deg f < 2(q-1)` every monomial has an exponent `< q-1` in one variable and
`∑_{x ∈ F} x^e = 0` for `e < q - 1`, forcing `∑_v f(v) = 0`. -/

/-- A blocking set: a set of points meeting every affine line. -/
def IsBlocking (B : Finset (F × F)) : Prop :=
  (∀ m b : F, ∃ p ∈ B, p.2 = m * p.1 + b) ∧ ∀ c : F, ∃ p ∈ B, p.1 = c

omit [Fintype F] in
lemma isBlocking_translate {B : Finset (F × F)} (hB : IsBlocking B) (v : F × F) :
    IsBlocking (B.image fun p => (p.1 - v.1, p.2 - v.2)) := by
  obtain ⟨h1, h2⟩ := hB
  constructor
  · intro m b
    obtain ⟨p, hp, hpe⟩ := h1 m (b + v.2 - m * v.1)
    exact ⟨(p.1 - v.1, p.2 - v.2), mem_image_of_mem _ hp, by simp only; linear_combination hpe⟩
  · intro c
    obtain ⟨p, hp, hpe⟩ := h2 (c + v.1)
    exact ⟨(p.1 - v.1, p.2 - v.2), mem_image_of_mem _ hp, by simp only; linear_combination hpe⟩

open MvPolynomial in
/-- The polynomial `∏_{(a,b) ∈ B} (1 - a X₀ + b X₁)`. -/
noncomputable def blockPoly (B : Finset (F × F)) : MvPolynomial (Fin 2) F :=
  ∏ p ∈ B, (1 - C p.1 * X 0 + C p.2 * X 1)

omit [Fintype F] [DecidableEq F] in
open MvPolynomial in
lemma totalDegree_blockPoly (B : Finset (F × F)) : (blockPoly B).totalDegree ≤ B.card := by
  refine (totalDegree_finsetProd _ _).trans ?_
  rw [card_eq_sum_ones]
  apply sum_le_sum
  intro p _
  refine (totalDegree_add _ _).trans (max_le ((totalDegree_sub _ _).trans (max_le ?_ ?_)) ?_)
  · rw [totalDegree_one]; exact zero_le_one
  · exact (totalDegree_mul _ _).trans (by simp [totalDegree_C, totalDegree_X])
  · exact (totalDegree_mul _ _).trans (by simp [totalDegree_C, totalDegree_X])

omit [Fintype F] [DecidableEq F] in
open MvPolynomial in
lemma eval_blockPoly (B : Finset (F × F)) (v : Fin 2 → F) :
    eval v (blockPoly B) = ∏ p ∈ B, (1 - p.1 * v 0 + p.2 * v 1) := by
  rw [blockPoly, map_prod]
  simp only [map_add, map_sub, map_one, map_mul, eval_C, eval_X]

omit [Fintype F] [DecidableEq F] in
lemma eval_blockPoly_zero (B : Finset (F × F)) : MvPolynomial.eval 0 (blockPoly B) = 1 := by
  rw [eval_blockPoly]
  exact prod_eq_one fun p _ => by simp

omit [Fintype F] in
lemma eval_blockPoly_eq_zero {B : Finset (F × F)} (hB : IsBlocking B) (v : Fin 2 → F)
    (hv : v ≠ 0) : MvPolynomial.eval v (blockPoly (B.erase (0, 0))) = 0 := by
  rw [eval_blockPoly]
  by_cases h1 : v 1 = 0
  · have h0 : v 0 ≠ 0 := by
      intro h0; apply hv; ext i; fin_cases i <;> simp [h0, h1]
    obtain ⟨p, hp, hpe⟩ := hB.2 (v 0)⁻¹
    refine prod_eq_zero (i := p) (mem_erase.mpr ⟨?_, hp⟩) ?_
    · rintro rfl
      exact h0 (inv_eq_zero.mp hpe.symm)
    · rw [hpe, h1, inv_mul_cancel₀ h0]; ring
  · obtain ⟨p, hp, hpe⟩ := hB.1 (v 0 / v 1) (-(1 / v 1))
    refine prod_eq_zero (i := p) (mem_erase.mpr ⟨?_, hp⟩) ?_
    · rintro rfl
      simp only [mul_zero, zero_add] at hpe
      have := neg_eq_zero.mp hpe.symm
      rw [one_div, inv_eq_zero] at this
      exact h1 this
    · rw [hpe]
      field_simp
      ring

omit [DecidableEq F] in
open MvPolynomial in
/-- If `deg f < 2(q-1)` then `∑_{v ∈ F²} f(v) = 0`. -/
lemma sum_eval_eq_zero (f : MvPolynomial (Fin 2) F)
    (hf : f.totalDegree < 2 * (Fintype.card F - 1)) :
    ∑ v : Fin 2 → F, eval v f = 0 := by
  simp_rw [eval_eq']
  rw [sum_comm]
  apply sum_eq_zero
  intro d hd
  rw [← mul_sum]
  have hsum : (∑ v : Fin 2 → F, ∏ i, v i ^ d i) = ∏ i : Fin 2, ∑ x : F, x ^ d i := by
    rw [prod_univ_sum, Fintype.piFinset_univ]
  rw [hsum, Fin.prod_univ_two]
  have hdeg : d 0 + d 1 ≤ f.totalDegree := by
    have := le_totalDegree hd
    rwa [Finsupp.sum_fintype _ _ (fun _ => rfl), Fin.sum_univ_two] at this
  rcases Nat.lt_or_ge (d 0) (Fintype.card F - 1) with h0 | h0
  · rw [FiniteField.sum_pow_lt_card_sub_one F _ h0, zero_mul, mul_zero]
  · have h1 : d 1 < Fintype.card F - 1 := by omega
    rw [FiniteField.sum_pow_lt_card_sub_one F _ h1, mul_zero, mul_zero]

/-- **Jamison's theorem**: a blocking set of `AG(2,q)` has at least `2q - 1` points. -/
theorem jamison {B : Finset (F × F)} (hB : IsBlocking B) : 2 * Fintype.card F - 1 ≤ B.card := by
  obtain ⟨p₀, hp₀, -⟩ := hB.2 0
  set B' := B.image fun p => (p.1 - p₀.1, p.2 - p₀.2) with hB'
  have hB'B : B'.card = B.card := card_image_of_injective _ (fun p q h => by
    simp only [Prod.mk.injEq] at h
    exact Prod.ext (sub_left_injective h.1) (sub_left_injective h.2))
  have hbl := isBlocking_translate hB p₀
  have h0 : (0, 0) ∈ B' := mem_image.mpr ⟨p₀, hp₀, by simp⟩
  have hcard : (B'.erase (0, 0)).card = B.card - 1 := by rw [card_erase_of_mem h0, hB'B]
  have hdeg := totalDegree_blockPoly (B'.erase (0, 0))
  by_contra hlt
  push Not at hlt
  have hq : 1 < Fintype.card F := Fintype.one_lt_card
  have hlt' : (blockPoly (B'.erase (0, 0))).totalDegree < 2 * (Fintype.card F - 1) := by omega
  have h1 := sum_eval_eq_zero _ hlt'
  rw [Fintype.sum_eq_single 0 (fun v hv => eval_blockPoly_eq_zero hbl v hv),
    eval_blockPoly_zero] at h1
  exact one_ne_zero h1

/-! ### Parity and all-2 lines -/

lemma sum_mult_line (t : Option F → F) (L : Finset (F × F)) :
    ∑ A ∈ L, mult t A = ∑ d : Option F, (L ∩ sysLine t d).card := by
  simp_rw [mult_eq_sum]
  rw [sum_comm]
  refine sum_congr rfl fun d _ => ?_
  rw [sum_boole, Nat.cast_id, filter_mem_eq_inter]

/-- A line not belonging to the system carries exactly `q` incidences with the system. -/
lemma sum_mult_line_not_sys (t : Option F → F) (d₀ : Option F) {s : F} (hs : s ≠ t d₀) :
    ∑ A ∈ dirLine d₀ s, mult t A = Fintype.card F := by
  rw [sum_mult_line, ← add_sum_erase _ _ (mem_univ d₀)]
  have h0 : (dirLine d₀ s ∩ sysLine t d₀).card = 0 := by
    rw [card_eq_zero, ← disjoint_iff_inter_eq_empty]; exact disjoint_dirLine hs
  rw [h0, zero_add,
    sum_congr rfl fun d hd => card_inter_dirLine_sysLine t s (ne_of_mem_erase hd).symm,
    sum_const, smul_eq_mul, mul_one, card_erase_of_mem (mem_univ _), card_univ,
    Fintype.card_option]
  simp

/-- A line of the system carries exactly `2q` incidences with the system. -/
lemma sum_mult_sysLine (t : Option F → F) (d₀ : Option F) :
    ∑ A ∈ sysLine t d₀, mult t A = 2 * Fintype.card F := by
  rw [sum_mult_line, ← add_sum_erase _ _ (mem_univ d₀), inter_self, card_sysLine,
    sum_congr rfl fun d hd => card_inter_sysLine t (ne_of_mem_erase hd).symm,
    sum_const, smul_eq_mul, mul_one, card_erase_of_mem (mem_univ _), card_univ,
    Fintype.card_option]
  omega

lemma exists_odd_mult_of_sum_odd (t : Option F → F) {L : Finset (F × F)}
    (h : Odd (∑ A ∈ L, mult t A)) : ∃ A ∈ L, Odd (mult t A) := by
  by_contra hcon
  push Not at hcon
  exact (Nat.not_even_iff_odd.mpr h)
    (even_sum _ fun A hA => Nat.not_odd_iff_even.mp (hcon A hA))

/-- For `q` odd, every affine line not in the system contains a point of odd multiplicity. -/
lemma exists_odd_not_sys (hq : Odd (Fintype.card F)) (t : Option F → F) (d₀ : Option F) {s : F}
    (hs : s ≠ t d₀) : ∃ A ∈ dirLine d₀ s, Odd (mult t A) :=
  exists_odd_mult_of_sum_odd t (by rw [sum_mult_line_not_sys t d₀ hs]; exact hq)

/-- An *all-2* line of the system: every point of it has multiplicity exactly `2`. -/
def AllTwo (t : Option F → F) (d : Option F) : Prop := ∀ A ∈ sysLine t d, mult t A = 2

/-- A line of the system either contains a point of odd multiplicity or is all-2. -/
lemma exists_odd_or_allTwo (t : Option F → F) (d₀ : Option F) :
    (∃ A ∈ sysLine t d₀, Odd (mult t A)) ∨ AllTwo t d₀ := by
  by_cases h : ∃ A ∈ sysLine t d₀, Odd (mult t A)
  · exact Or.inl h
  · right
    push Not at h
    have hge : ∀ A ∈ sysLine t d₀, 2 ≤ mult t A := by
      intro A hA
      have h1 : 1 ≤ mult t A := card_pos.mpr ⟨d₀, mem_filter.mpr ⟨mem_univ _, hA⟩⟩
      obtain ⟨k, hk⟩ := Nat.not_odd_iff_even.mp (h A hA)
      omega
    have hsum : ∑ A ∈ sysLine t d₀, 2 = ∑ A ∈ sysLine t d₀, mult t A := by
      rw [sum_mult_sysLine, sum_const, smul_eq_mul, card_sysLine, mul_comm]
    intro A hA
    exact ((sum_eq_sum_iff_of_le hge).mp hsum A hA).symm

/-- A point on three lines of the system has multiplicity at least `3`. -/
lemma three_le_mult (t : Option F → F) {A : F × F} {d₁ d₂ d₃ : Option F} (h12 : d₁ ≠ d₂)
    (h13 : d₁ ≠ d₃) (h23 : d₂ ≠ d₃) (h1 : A ∈ sysLine t d₁) (h2 : A ∈ sysLine t d₂)
    (h3 : A ∈ sysLine t d₃) : 3 ≤ mult t A :=
  two_lt_card_iff.mpr ⟨d₁, d₂, d₃, mem_filter.mpr ⟨mem_univ _, h1⟩,
    mem_filter.mpr ⟨mem_univ _, h2⟩, mem_filter.mpr ⟨mem_univ _, h3⟩, h12, h13, h23⟩

/-- No point of an all-2 line lies on two further lines of the system. -/
lemma allTwo_not_three (t : Option F → F) {A : F × F} {d₁ d₂ d₃ : Option F} (h12 : d₁ ≠ d₂)
    (h13 : d₁ ≠ d₃) (h23 : d₂ ≠ d₃) (h1 : A ∈ sysLine t d₁) (h2 : A ∈ sysLine t d₂)
    (h3 : A ∈ sysLine t d₃) (hall : AllTwo t d₁) : False := by
  have := three_le_mult t h12 h13 h23 h1 h2 h3
  rw [hall A h1] at this
  omega

/-- Auxiliary for the product argument.  If `L_{ma}` is all-2 and `P = (xs, ys)` is its
intersection with `L_{mb}`, then `m ↦ (t ma - t m)/(m - ma)` (the abscissa of `L_m ∩ L_{ma}`)
is injective on `F ∖ {ma, mb}` with image `F ∖ {t none, xs}`. -/
lemma allTwo_image (t : Option F → F) {ma mb : F} (hne : ma ≠ mb) (ha : AllTwo t (some ma))
    {xs ys : F} (hPa : ys = ma * xs + t (some ma)) (hPb : ys = mb * xs + t (some mb)) :
    Set.InjOn (fun m => (t (some ma) - t (some m)) / (m - ma))
        (((univ.erase ma).erase mb : Finset F) : Set F) ∧
      (((univ.erase ma).erase mb).image fun m => (t (some ma) - t (some m)) / (m - ma)) =
        (univ.erase (t none)).erase xs := by
  have hPa' : (xs, ys) ∈ sysLine t (some ma) := mem_sysLine_some.mpr hPa
  have hPb' : (xs, ys) ∈ sysLine t (some mb) := mem_sysLine_some.mpr hPb
  have hxs : xs ≠ t none := fun h =>
    allTwo_not_three t (d₁ := some ma) (d₂ := some mb) (d₃ := none) (by simpa using hne)
      (by simp) (by simp) hPa' hPb' (mem_sysLine_none.mpr h) ha
  -- the point `L_m ∩ L_{ma}`
  set u : F → F := fun m => (t (some ma) - t (some m)) / (m - ma) with hu
  have hmemA : ∀ m, (u m, ma * u m + t (some ma)) ∈ sysLine t (some ma) :=
    fun m => mem_sysLine_some.mpr rfl
  have hmemM : ∀ m, m ≠ ma → (u m, ma * u m + t (some ma)) ∈ sysLine t (some m) := by
    intro m hm
    rw [mem_sysLine_some]
    simp only [hu]
    have : m - ma ≠ 0 := sub_ne_zero.mpr hm
    field_simp
    ring
  have hmem : ∀ m ∈ (univ.erase ma).erase mb, m ≠ ma ∧ m ≠ mb := fun m hm =>
    ⟨(mem_erase.mp (mem_erase.mp hm).2).1, (mem_erase.mp hm).1⟩
  have hinj : Set.InjOn u (((univ.erase ma).erase mb : Finset F) : Set F) := by
    intro m hm m' hm' heq
    by_contra hmm
    have hm1 := (hmem m (by exact_mod_cast hm)).1
    have hm2 := (hmem m' (by exact_mod_cast hm')).1
    have h2 := hmemM m hm1
    have h3 := hmemM m' hm2
    rw [← heq] at h3
    exact allTwo_not_three t (d₁ := some ma) (d₂ := some m) (d₃ := some m')
      (by simpa using hm1.symm) (by simpa using hm2.symm) (by simpa using hmm) (hmemA m) h2 h3 ha
  refine ⟨hinj, ?_⟩
  have hsub : (((univ.erase ma).erase mb).image u) ⊆ (univ.erase (t none)).erase xs := by
    intro w hw
    obtain ⟨m, hm, rfl⟩ := mem_image.mp hw
    obtain ⟨hm1, hm2⟩ := hmem m hm
    rw [mem_erase, mem_erase]
    refine ⟨?_, ?_, mem_univ _⟩
    · intro h
      -- `P_m = (xs, ys)` lies on `L_{ma}, L_m, L_{mb}`
      have hP : (u m, ma * u m + t (some ma)) = (xs, ys) := by rw [h, hPa]
      have h2 := hmemM m hm1
      rw [hP] at h2
      exact allTwo_not_three t (d₁ := some ma) (d₂ := some m) (d₃ := some mb)
        (by simpa using hm1.symm) (by simpa using hne) (by simpa using hm2) hPa' h2 hPb' ha
    · intro h
      have h2 := hmemM m hm1
      have h3 : (u m, ma * u m + t (some ma)) ∈ sysLine t none := mem_sysLine_none.mpr h
      exact allTwo_not_three t (d₁ := some ma) (d₂ := some m) (d₃ := none)
        (by simpa using hm1.symm) (by simp) (by simp) (hmemA m) h2 h3 ha
  refine eq_of_subset_of_card_le hsub ?_
  rw [card_image_of_injOn hinj, card_erase_of_mem (mem_erase.mpr ⟨hxs, mem_univ _⟩),
    card_erase_of_mem (mem_univ _), card_erase_of_mem (mem_erase.mpr ⟨hne.symm, mem_univ _⟩),
    card_erase_of_mem (mem_univ _)]

/-- `(m₁ - m₀) ∏_{m ∉ {m₀,m₁}} (m - m₀) = ∏_{w ≠ 0} w`. -/
lemma prod_sub_erase {m₀ m₁ : F} (hne : m₀ ≠ m₁) :
    (m₁ - m₀) * ∏ m ∈ (univ.erase m₀).erase m₁, (m - m₀) = ∏ w ∈ univ.erase (0 : F), w := by
  have hinj : Function.Injective fun m : F => m - m₀ := sub_left_injective
  have himg : ((univ.erase m₀).erase m₁).image (fun m => m - m₀) =
      (univ.erase 0).erase (m₁ - m₀) := by
    rw [image_erase hinj, image_erase hinj,
      image_univ_of_surjective (fun w => ⟨w + m₀, by simp⟩), sub_self]
  have this : ∏ x ∈ ((univ.erase m₀).erase m₁).image (fun m => m - m₀), x =
      ∏ m ∈ (univ.erase m₀).erase m₁, (m - m₀) := prod_image hinj.injOn
  rw [himg] at this
  rw [← this]
  exact mul_prod_erase (univ.erase (0 : F)) (fun w => w)
    (mem_erase.mpr ⟨sub_ne_zero.mpr hne.symm, mem_univ _⟩)

/-- **Key product lemma** (the case of Bichara–Korchmáros we need): for `q` odd, two distinct
non-vertical lines of the system cannot both be all-2. -/
lemma not_allTwo_pair (hF : ringChar F ≠ 2) (t : Option F → F) {m₀ m₁ : F} (hne : m₀ ≠ m₁)
    (h₀ : AllTwo t (some m₀)) (h₁ : AllTwo t (some m₁)) : False := by
  have hsub : m₀ - m₁ ≠ 0 := sub_ne_zero.mpr hne
  obtain ⟨xs, hxs⟩ : ∃ xs : F, xs = (t (some m₁) - t (some m₀)) / (m₀ - m₁) := ⟨_, rfl⟩
  obtain ⟨ys, hys⟩ : ∃ ys : F, ys = m₀ * xs + t (some m₀) := ⟨_, rfl⟩
  have hys' : ys = m₁ * xs + t (some m₁) := by
    rw [hys, hxs]; field_simp; ring
  obtain ⟨hinj₀, himg₀⟩ := allTwo_image t hne h₀ hys hys'
  obtain ⟨hinj₁, himg₁⟩ := allTwo_image t hne.symm h₁ hys' hys
  rw [erase_right_comm] at hinj₁ himg₁
  set S : Finset F := (univ.erase m₀).erase m₁ with hS
  have hmem : ∀ m ∈ S, m ≠ m₀ ∧ m ≠ m₁ := fun m hm =>
    ⟨(mem_erase.mp (mem_erase.mp hm).2).1, (mem_erase.mp hm).1⟩
  -- the two products over `F ∖ {t none, xs}` agree
  have hprod : (∏ m ∈ S, ((t (some m₀) - t (some m)) / (m - m₀) - xs)) =
      ∏ m ∈ S, ((t (some m₁) - t (some m)) / (m - m₁) - xs) := by
    have e₀ : ∏ w ∈ S.image (fun m => (t (some m₀) - t (some m)) / (m - m₀)), (w - xs) =
        ∏ m ∈ S, ((t (some m₀) - t (some m)) / (m - m₀) - xs) := prod_image hinj₀
    have e₁ : ∏ w ∈ S.image (fun m => (t (some m₁) - t (some m)) / (m - m₁)), (w - xs) =
        ∏ m ∈ S, ((t (some m₁) - t (some m)) / (m - m₁) - xs) := prod_image hinj₁
    rw [himg₀] at e₀
    rw [himg₁] at e₁
    rw [← e₀, ← e₁]
  -- rewrite both sides as `(ys - γ m)/(m - mᵢ)`
  have hγ₀ : ∀ m ∈ S, (t (some m₀) - t (some m)) / (m - m₀) - xs =
      (ys - (m * xs + t (some m))) / (m - m₀) := by
    intro m hm
    have : m - m₀ ≠ 0 := sub_ne_zero.mpr (hmem m hm).1
    rw [hys]; field_simp; ring
  have hγ₁ : ∀ m ∈ S, (t (some m₁) - t (some m)) / (m - m₁) - xs =
      (ys - (m * xs + t (some m))) / (m - m₁) := by
    intro m hm
    have : m - m₁ ≠ 0 := sub_ne_zero.mpr (hmem m hm).2
    rw [hys']; field_simp; ring
  rw [prod_congr rfl hγ₀, prod_congr rfl hγ₁, prod_div_distrib, prod_div_distrib] at hprod
  -- the numerators are nonzero
  have hN : (∏ m ∈ S, (ys - (m * xs + t (some m)))) ≠ 0 := by
    rw [prod_ne_zero_iff]
    intro m hm h
    obtain ⟨hm1, hm2⟩ := hmem m hm
    have h3 : (xs, ys) ∈ sysLine t (some m) := mem_sysLine_some.mpr (sub_eq_zero.mp h)
    exact allTwo_not_three t (d₁ := some m₀) (d₂ := some m₁) (d₃ := some m) (by simpa using hne)
      (by simpa using hm1.symm) (by simpa using hm2.symm) (mem_sysLine_some.mpr hys)
      (mem_sysLine_some.mpr hys') h3 h₀
  have hD₀ : (∏ m ∈ S, (m - m₀)) ≠ 0 :=
    prod_ne_zero_iff.mpr fun m hm => sub_ne_zero.mpr (hmem m hm).1
  have hD₁ : (∏ m ∈ S, (m - m₁)) ≠ 0 :=
    prod_ne_zero_iff.mpr fun m hm => sub_ne_zero.mpr (hmem m hm).2
  have hD : (∏ m ∈ S, (m - m₁)) = ∏ m ∈ S, (m - m₀) := by
    rw [div_eq_div_iff hD₀ hD₁] at hprod
    exact mul_left_cancel₀ hN hprod
  -- Wilson-free conclusion: both products are `W/(m₁ - m₀)` and `W/(m₀ - m₁)`
  have hW₀ := prod_sub_erase hne
  have hW₁ := prod_sub_erase hne.symm
  rw [erase_right_comm] at hW₁
  rw [← hS] at hW₀ hW₁
  rw [hD] at hW₁
  have h2 : (2 * (m₁ - m₀)) * ∏ m ∈ S, (m - m₀) = 0 := by linear_combination hW₀ - hW₁
  rcases mul_eq_zero.mp h2 with h | h
  · rcases mul_eq_zero.mp h with h | h
    · exact Ring.two_ne_zero hF h
    · exact hne (sub_eq_zero.mp h).symm
  · exact hD₀ h

/-! ### The refined bound for odd `q` -/

/-- Pointwise inequality: `[n odd] ≤ 2·[n ≥ 1](n-1)(n-2) - n(n-2)`. -/
lemma odd_pointwise (n : ℕ) :
    (if Odd n then (1 : ℤ) else 0) ≤
      2 * (if 1 ≤ n then ((n : ℤ) - 1) * ((n : ℤ) - 2) else 0) - (n : ℤ) * ((n : ℤ) - 2) := by
  rcases Nat.lt_or_ge n 4 with h | h
  · interval_cases n <;> simp [Nat.odd_iff]
  · have h' : (4 : ℤ) ≤ n := by exact_mod_cast h
    rw [if_pos (show 1 ≤ n by omega)]
    split_ifs <;> nlinarith

/-- The number of points of odd multiplicity is at most `4σ = 2 · excess`. -/
lemma card_odd_le (t : Option F → F) :
    ((univ.filter fun A => Odd (mult t A)).card : ℤ) ≤ 2 * excess t := by
  have h1 : ((univ.filter fun A => Odd (mult t A)).card : ℤ) =
      ∑ A : F × F, if Odd (mult t A) then (1 : ℤ) else 0 := by
    rw [sum_boole]
  have h2 : ∑ A : F × F, (mult t A : ℤ) * ((mult t A : ℤ) - 2) = 0 := by
    have e : ∀ A : F × F, (mult t A : ℤ) * ((mult t A : ℤ) - 2) =
        ((mult t A * (mult t A - 1) : ℕ) : ℤ) - (mult t A : ℤ) := by
      intro A; rw [cast_mult_mul_pred]; ring
    rw [sum_congr rfl fun A _ => e A, sum_sub_distrib]
    have h3 : (∑ A : F × F, ((mult t A * (mult t A - 1) : ℕ) : ℤ)) =
        (Fintype.card F + 1) * Fintype.card F := by exact_mod_cast sum_mult_mul_pred t
    have h4 : (∑ A : F × F, (mult t A : ℤ)) = (Fintype.card F + 1) * Fintype.card F := by
      exact_mod_cast sum_mult t
    rw [h3, h4, sub_self]
  rw [h1]
  calc (∑ A : F × F, if Odd (mult t A) then (1 : ℤ) else 0)
      ≤ ∑ A : F × F, (2 * (if 1 ≤ mult t A then ((mult t A : ℤ) - 1) * ((mult t A : ℤ) - 2)
          else 0) - (mult t A : ℤ) * ((mult t A : ℤ) - 2)) :=
        sum_le_sum fun A _ => odd_pointwise _
    _ = 2 * excess t := by
        rw [sum_sub_distrib, ← mul_sum, h2, sub_zero, excess]

/-- A point on the vertical line of the system lying on every all-2 non-vertical line. -/
lemma exists_blocking_point (hF : ringChar F ≠ 2) (t : Option F → F) :
    ∃ E : F × F, E ∈ sysLine t none ∧ ∀ m, AllTwo t (some m) → E ∈ sysLine t (some m) := by
  by_cases h : ∃ m₀, AllTwo t (some m₀)
  · obtain ⟨m₀, hm₀⟩ := h
    refine ⟨(t none, m₀ * t none + t (some m₀)), mem_sysLine_none.mpr rfl, fun m hm => ?_⟩
    by_cases hmm : m = m₀
    · subst hmm; exact mem_sysLine_some.mpr rfl
    · exact (not_allTwo_pair hF t hmm hm hm₀).elim
  · push Not at h
    exact ⟨(t none, 0), mem_sysLine_none.mpr rfl, fun m hm => (h m hm).elim⟩

/-- The odd-multiplicity points together with `E` form a blocking set. -/
lemma isBlocking_odd (hq : Odd (Fintype.card F)) (t : Option F → F) {E : F × F}
    (hE : E ∈ sysLine t none) (hE' : ∀ m, AllTwo t (some m) → E ∈ sysLine t (some m)) :
    IsBlocking ((univ.filter fun A => Odd (mult t A)) ∪ {E}) := by
  constructor
  · intro m b₀
    by_cases hb : b₀ = t (some m)
    · rcases exists_odd_or_allTwo t (some m) with ⟨A, hA, hodd⟩ | hall
      · exact ⟨A, mem_union_left _ (mem_filter.mpr ⟨mem_univ _, hodd⟩),
          by rw [hb]; exact mem_sysLine_some.mp hA⟩
      · exact ⟨E, mem_union_right _ (mem_singleton_self _),
          by rw [hb]; exact mem_sysLine_some.mp (hE' m hall)⟩
    · obtain ⟨A, hA, hodd⟩ := exists_odd_not_sys hq t (some m) hb
      exact ⟨A, mem_union_left _ (mem_filter.mpr ⟨mem_univ _, hodd⟩), mem_lineS.mp hA⟩
  · intro c₀
    by_cases hc : c₀ = t none
    · exact ⟨E, mem_union_right _ (mem_singleton_self _), by rw [hc]; exact mem_sysLine_none.mp hE⟩
    · obtain ⟨A, hA, hodd⟩ := exists_odd_not_sys hq t none hc
      exact ⟨A, mem_union_left _ (mem_filter.mpr ⟨mem_univ _, hodd⟩), mem_lineV.mp hA⟩

/-- For `q` odd, the excess satisfies `2σ ≥ q - 1`. -/
theorem excess_ge (hq : Odd (Fintype.card F)) (t : Option F → F) :
    (Fintype.card F : ℤ) - 1 ≤ excess t := by
  have hF : ringChar F ≠ 2 := fun h =>
    (Nat.not_even_iff_odd.mpr hq) (Nat.even_iff.mpr (FiniteField.even_card_of_char_two h))
  obtain ⟨E, hE, hE'⟩ := exists_blocking_point hF t
  have hj := jamison (isBlocking_odd hq t hE hE')
  have hle := card_union_le (univ.filter fun A => Odd (mult t A)) {E}
  rw [card_singleton] at hle
  have hodd := card_odd_le t
  have h'' : 2 * Fintype.card F ≤ (univ.filter fun A => Odd (mult t A)).card + 2 := by omega
  have h3 : (2 * Fintype.card F : ℤ) ≤ ((univ.filter fun A => Odd (mult t A)).card : ℤ) + 2 := by
    exact_mod_cast h''
  linarith

/-- **Refined lower bound** (Blokhuis–Mazzocca): for `q` odd every Kakeya set has at least
`q(q+1)/2 + (q-1)/2` points. -/
theorem card_ge_odd (hq : Odd (Fintype.card F)) {K : Finset (F × F)} (hK : IsKakeya K) :
    Fintype.card F * (Fintype.card F + 1) / 2 + (Fintype.card F - 1) / 2 ≤ K.card := by
  obtain ⟨t, hsub⟩ := cover_subset hK
  have h := two_mul_card_cover t
  have h0 := excess_ge hq t
  obtain ⟨k, hk⟩ := hq
  rw [hk] at h h0 ⊢
  have e2 : (2 * k + 1) * (2 * k + 1 + 1) / 2 = (2 * k + 1) * (k + 1) := by
    rw [show (2 * k + 1) * (2 * k + 1 + 1) = ((2 * k + 1) * (k + 1)) * 2 by ring]
    exact Nat.mul_div_cancel _ two_pos
  have e3 : (2 * k + 1 - 1) / 2 = k := by omega
  rw [e2, e3]
  have : (2 * k + 1) * (k + 1) + k ≤ (cover t).card := by
    have h5 : (2 : ℤ) * (((2 * k + 1) * (k + 1) + k : ℕ) : ℤ) ≤ 2 * ((cover t).card : ℤ) := by
      rw [h]; push_cast at h0 ⊢; nlinarith
    have := (mul_le_mul_iff_right₀ (by norm_num : (0:ℤ) < 2)).mp h5
    exact_mod_cast this
  exact this.trans (card_le_card hsub)

/-! ### The construction: dual conic plus one vertical line -/

/-- Points `(x,y)` with `x² - y` a square: the union of the tangent lines `y = m x - m²/4`
of the parabola `y = x²` (the affine part of a dual conic). -/
def parabolaSet (F : Type*) [Field F] [Fintype F] [DecidableEq F] : Finset (F × F) :=
  univ.filter fun p => IsSquare (p.1 ^ 2 - p.2)

/-- The extremal Kakeya set: `parabolaSet ∪ {x = 0}`. -/
def extremalSet (F : Type*) [Field F] [Fintype F] [DecidableEq F] : Finset (F × F) :=
  parabolaSet F ∪ lineV 0

omit [DecidableEq F] in
lemma ringChar_ne_two_of_odd (hq : Odd (Fintype.card F)) : ringChar F ≠ 2 := fun h =>
  (Nat.not_even_iff_odd.mpr hq) (Nat.even_iff.mpr (FiniteField.even_card_of_char_two h))

theorem isKakeya_extremalSet (hq : Odd (Fintype.card F)) : IsKakeya (extremalSet F) := by
  have h2 : (2 : F) ≠ 0 := Ring.two_ne_zero (ringChar_ne_two_of_odd hq)
  refine ⟨fun m => ⟨-(m ^ 2 / 4), fun x => ?_⟩, 0, fun y => ?_⟩
  · apply mem_union_left
    simp only [parabolaSet, mem_filter, mem_univ, true_and]
    refine ⟨x - m / 2, ?_⟩
    have h4 : (4 : F) ≠ 0 := by
      have : (4 : F) = 2 * 2 := by norm_num
      rw [this]; exact mul_ne_zero h2 h2
    field_simp
    ring
  · exact mem_union_right _ (mem_lineV.mpr rfl)

/-- Number of squares (including `0`) in a finite field of odd characteristic: `(q+1)/2`. -/
lemma two_mul_card_squares (hF : ringChar F ≠ 2) :
    2 * (univ.filter fun a : F => IsSquare a).card = Fintype.card F + 1 := by
  set S := univ.filter fun a : F => IsSquare a with hS
  set N := univ.filter fun a : F => ¬ IsSquare a with hN
  have hSN : S.card + N.card = Fintype.card F := by
    rw [hS, hN, card_filter_add_card_filter_not, card_univ]
  have hsum := quadraticChar_sum_zero hF
  rw [← sum_filter_add_sum_filter_not univ fun a : F => IsSquare a] at hsum
  have h0 : (0 : F) ∈ S := by rw [hS, mem_filter]; exact ⟨mem_univ _, ⟨0, by simp⟩⟩
  have hSsum : (∑ a ∈ S, quadraticChar F a) = (S.card : ℤ) - 1 := by
    rw [← sum_erase S (MulChar.map_zero _)]
    rw [sum_congr rfl fun a ha => (quadraticChar_one_iff_isSquare (ne_of_mem_erase ha)).mpr
      (mem_filter.mp (mem_of_mem_erase ha)).2]
    have : 1 ≤ S.card := card_pos.mpr ⟨0, h0⟩
    rw [sum_const, card_erase_of_mem h0, nsmul_eq_mul, mul_one, Nat.cast_sub this, Nat.cast_one]
  have hNsum : (∑ a ∈ N, quadraticChar F a) = -(N.card : ℤ) := by
    rw [sum_congr rfl fun a ha => quadraticChar_neg_one_iff_not_isSquare.mpr
      (mem_filter.mp ha).2]
    rw [sum_const, nsmul_eq_mul, mul_neg_one]
  rw [hSsum, hNsum] at hsum
  have : (2 : ℤ) * S.card = Fintype.card F + 1 := by
    have := congrArg (Nat.cast (R := ℤ)) hSN
    push_cast at this
    linarith
  exact_mod_cast this

lemma card_squares (hF : ringChar F ≠ 2) :
    (univ.filter fun a : F => IsSquare a).card = (Fintype.card F + 1) / 2 := by
  have := two_mul_card_squares hF
  omega

/-- For fixed `x`, the number of `y` with `x² - y` a square equals the number of squares. -/
lemma card_fiber (x : F) :
    (univ.filter fun y : F => IsSquare (x ^ 2 - y)).card =
      (univ.filter fun a : F => IsSquare a).card := by
  refine card_bij' (fun y _ => x ^ 2 - y) (fun a _ => x ^ 2 - a) ?_ ?_ ?_ ?_
  · intro y hy
    simp only [mem_filter, mem_univ, true_and] at hy ⊢
    exact hy
  · intro a ha
    simp only [mem_filter, mem_univ, true_and] at ha ⊢
    simpa using ha
  · intro y _; ring
  · intro a _; ring

lemma card_parabolaSet :
    (parabolaSet F).card = Fintype.card F * (univ.filter fun a : F => IsSquare a).card := by
  have : parabolaSet F =
      ((univ : Finset F) ×ˢ (univ.filter fun a : F => IsSquare a)).image
        fun xs => (xs.1, xs.1 ^ 2 - xs.2) := by
    ext p
    rw [parabolaSet, mem_filter, mem_image]
    constructor
    · rintro ⟨-, h⟩
      exact ⟨(p.1, p.1 ^ 2 - p.2), by simp [mem_product, h], by simp⟩
    · rintro ⟨⟨x, s⟩, hxs, rfl⟩
      rw [mem_product, mem_filter] at hxs
      exact ⟨mem_univ _, by simpa using hxs.2.2⟩
  rw [this, card_image_of_injective, card_product, card_univ]
  rintro ⟨x, s⟩ ⟨x', s'⟩ h
  simp only [Prod.mk.injEq] at h
  obtain ⟨rfl, h2⟩ := h
  simp only [Prod.mk.injEq, true_and]
  linear_combination -h2

lemma card_parabolaSet_inter_lineV (c : F) :
    (parabolaSet F ∩ lineV c).card = (univ.filter fun a : F => IsSquare a).card := by
  rw [← card_fiber c]
  have : parabolaSet F ∩ lineV c =
      (univ.filter fun y : F => IsSquare (c ^ 2 - y)).image fun y => (c, y) := by
    ext p
    simp only [parabolaSet, mem_inter, mem_filter, mem_univ, true_and, mem_lineV, mem_image]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨p.2, by rw [← h2]; exact h1, by rw [← h2]⟩
    · rintro ⟨y, hy, rfl⟩
      exact ⟨hy, rfl⟩
  rw [this, card_image_of_injective _ fun y y' h => (Prod.mk.inj h).2]

/-- **The construction attains the bound.** -/
theorem card_extremalSet (hq : Odd (Fintype.card F)) :
    (extremalSet F).card =
      Fintype.card F * (Fintype.card F + 1) / 2 + (Fintype.card F - 1) / 2 := by
  have hF := ringChar_ne_two_of_odd hq
  have h := card_union_add_card_inter (parabolaSet F) (lineV 0)
  rw [card_parabolaSet, card_parabolaSet_inter_lineV, card_lineV, card_squares hF] at h
  rw [extremalSet]
  obtain ⟨k, hk⟩ := hq
  rw [hk] at h ⊢
  have e1 : (2 * k + 1 + 1) / 2 = k + 1 := by omega
  have e2 : (2 * k + 1) * (2 * k + 1 + 1) / 2 = (2 * k + 1) * (k + 1) := by
    rw [show (2 * k + 1) * (2 * k + 1 + 1) = ((2 * k + 1) * (k + 1)) * 2 by ring]
    exact Nat.mul_div_cancel _ two_pos
  have e3 : (2 * k + 1 - 1) / 2 = k := by omega
  rw [e1] at h
  rw [e2, e3]
  have : (parabolaSet F ∪ lineV 0).card + (k + 1) = (2 * k + 1) * (k + 1) + (2 * k + 1) := h
  nlinarith

/-! ### Main theorem -/

/-- **Blokhuis–Mazzocca.** For `q = |F|` odd, every Kakeya set in `F²` has at least
`q(q+1)/2 + (q-1)/2` points, and this bound is attained. -/
theorem kakeya_min (hq : Odd (Fintype.card F)) :
    (∀ K : Finset (F × F), IsKakeya K →
        Fintype.card F * (Fintype.card F + 1) / 2 + (Fintype.card F - 1) / 2 ≤ K.card) ∧
      ∃ K : Finset (F × F), IsKakeya K ∧
        K.card = Fintype.card F * (Fintype.card F + 1) / 2 + (Fintype.card F - 1) / 2 :=
  ⟨fun _ hK => card_ge_odd hq hK, extremalSet F, isKakeya_extremalSet hq, card_extremalSet hq⟩

/-- The minimum size of a Kakeya set, as an infimum, equals `q(q+1)/2 + (q-1)/2` for `q` odd. -/
theorem kakeya_sInf (hq : Odd (Fintype.card F)) :
    sInf {n : ℕ | ∃ K : Finset (F × F), IsKakeya K ∧ K.card = n} =
      Fintype.card F * (Fintype.card F + 1) / 2 + (Fintype.card F - 1) / 2 := by
  apply le_antisymm
  · exact Nat.sInf_le ⟨extremalSet F, isKakeya_extremalSet hq, card_extremalSet hq⟩
  · refine le_csInf ⟨_, extremalSet F, isKakeya_extremalSet hq, card_extremalSet hq⟩ ?_
    rintro n ⟨K, hK, rfl⟩
    exact card_ge_odd hq hK

end Kakeya

#print axioms Kakeya.card_ge_easy
#print axioms Kakeya.jamison
#print axioms Kakeya.not_allTwo_pair
#print axioms Kakeya.card_ge_odd
#print axioms Kakeya.isKakeya_extremalSet
#print axioms Kakeya.card_extremalSet
#print axioms Kakeya.kakeya_min
#print axioms Kakeya.kakeya_sInf
