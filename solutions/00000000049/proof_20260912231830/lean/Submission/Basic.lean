import Mathlib

/-!
# Conjecture 00000000049

Conjecture 00000000049 asserts, of point sets in the plane all of whose
pairwise distances are prime, that the maximal size is `4` and that a set of
size `4` exists. Both are true, and both are proved here. The plane is modeled
as `ℂ` with its usual metric, which is the Euclidean plane as a metric space.

## The proof of part (a)

Four points of the plane satisfy the Gram relation `gram = 0` in their six
squared distances (`gram_dist`): the Gram matrix of the three difference
vectors is singular. If the six distances are primes, each squared distance is
`4` or is `1` modulo `8`, and a check of the `64` patterns (`pattern_mod8`)
leaves only three shapes for the set of pairs at distance `2`: a perfect
matching, a triangle, or all six pairs. All six pairs gives `gram = 128 ≠ 0`;
a triangle gives `gram ≡ 16` modulo `32` (`tri_mod32`). So **exactly two of the
six distances are `2`** (`two_of_six`).

Five points would have five four-point subsets, each containing exactly two
pairs at distance `2`, while each pair lies in three of those subsets: `3e = 10`
for the number `e` of pairs at distance `2`, which has no solution (`no_five`).

## Contents

* `ConjectureHolds` — the conjecture, both parts; `conjecture_holds` — its proof.
* `witness`, `conjecture_part_b` — part (b): the four collinear points
  `0, 2, 5, 7`, whose six pairwise distances are `2, 5, 7, 3, 5, 2`.
* `gram`, `gram_dist`, `gram_int` — the Gram relation of four coplanar points.
* `pattern_mod8`, `tri_mod32` — the two finite residue checks.
* `two_of_six`, `two_of_four` — exactly two of the six distances equal `2`.
* `no_five`, `card_le_four` — part (a).
* `gaps_of_four_collinear` — the arithmetic behind the appendix of the paper:
  a collinear prime-distance quadruple has gaps `2, 3, 2`.
-/

namespace Submission00000000049

open Complex

/-- A family of points in the plane, pairwise distinct, all of whose pairwise
distances are prime. -/
def IsPrimeDistanceSet {n : ℕ} (P : Fin n → ℂ) : Prop :=
  Function.Injective P ∧
    ∀ i j : Fin n, i ≠ j → ∃ p : ℕ, p.Prime ∧ dist (P i) (P j) = (p : ℝ)

/-- Conjecture 00000000049: the maximal size is `4`, and size `4` occurs. -/
def ConjectureHolds : Prop :=
  (∀ (n : ℕ) (P : Fin n → ℂ), IsPrimeDistanceSet P → n ≤ 4) ∧
    (∃ P : Fin 4 → ℂ, IsPrimeDistanceSet P)

/-! ## Part (b): a configuration of size four -/

/-- The abscissae of the witness: four collinear points. -/
def xs : Fin 4 → ℝ := ![0, 2, 5, 7]

/-- The witness, as points of the plane. -/
def witness : Fin 4 → ℂ := fun i => (xs i : ℂ)

/-- The pairwise distances, tabulated (the diagonal is `0`). -/
def dTable : Fin 4 → Fin 4 → ℕ :=
  ![![0, 2, 5, 7], ![2, 0, 3, 5], ![5, 3, 0, 2], ![7, 5, 2, 0]]

theorem dist_witness (i j : Fin 4) : dist (witness i) (witness j) = |xs i - xs j| := by
  have h : ((xs i : ℂ) - (xs j : ℂ)) = ((xs i - xs j : ℝ) : ℂ) := by push_cast; ring
  rw [witness, witness, Complex.dist_eq, h, Complex.norm_real, Real.norm_eq_abs]

theorem abs_xs_eq (i j : Fin 4) : |xs i - xs j| = (dTable i j : ℝ) := by
  fin_cases i <;> fin_cases j <;> norm_num [xs, dTable]

theorem dTable_prime (i j : Fin 4) (hij : i ≠ j) : (dTable i j).Prime := by
  revert hij; fin_cases i <;> fin_cases j <;> decide

theorem witness_injective : Function.Injective witness := by
  intro i j hij
  by_contra hne
  have h0 : dist (witness i) (witness j) = 0 := by rw [hij, dist_self]
  rw [dist_witness, abs_xs_eq] at h0
  have hp := dTable_prime i j hne
  have : dTable i j = 0 := by exact_mod_cast h0
  exact hp.ne_zero this

theorem conjecture_part_b : ∃ P : Fin 4 → ℂ, IsPrimeDistanceSet P := by
  refine ⟨witness, witness_injective, fun i j hij => ⟨dTable i j, dTable_prime i j hij, ?_⟩⟩
  rw [dist_witness, abs_xs_eq]


/-! ## The Gram form -/

/-- The Gram form of four points of the plane, written in the six squared
distances: `s₁ = |P₀P₁|²`, `s₂ = |P₀P₂|²`, `s₃ = |P₀P₃|²`, `t₁₂ = |P₁P₂|²`,
`t₁₃ = |P₁P₃|²`, `t₂₃ = |P₂P₃|²`. It is `det(2G)/2` for the Gram matrix `G` of
the three difference vectors, so it vanishes in the plane. -/
def gram {R : Type*} [CommRing R] (s₁ s₂ s₃ t₁₂ t₁₃ t₂₃ : R) : R :=
  4*s₁*s₂*s₃ + (s₁+s₂-t₁₂)*(s₁+s₃-t₁₃)*(s₂+s₃-t₂₃)
    - s₁*(s₂+s₃-t₂₃)^2 - s₂*(s₁+s₃-t₁₃)^2 - s₃*(s₁+s₂-t₁₂)^2

theorem gram_eq_zero (v₁ v₂ v₃ : ℂ) :
    gram (normSq v₁) (normSq v₂) (normSq v₃)
      (normSq (v₁ - v₂)) (normSq (v₁ - v₃)) (normSq (v₂ - v₃)) = 0 := by
  simp only [gram, Complex.normSq_apply, Complex.sub_re, Complex.sub_im]
  ring

theorem normSq_sub_eq (X Y : ℂ) : normSq (X - Y) = dist X Y ^ 2 := by
  rw [dist_eq_norm, Complex.normSq_eq_norm_sq]

/-- The Gram relation for four points of the plane, in their distances. -/
theorem gram_dist (A B C D : ℂ) :
    gram (dist A B ^ 2) (dist A C ^ 2) (dist A D ^ 2)
      (dist B C ^ 2) (dist B D ^ 2) (dist C D ^ 2) = 0 := by
  have h := gram_eq_zero (B - A) (C - A) (D - A)
  have e₁ : B - A - (C - A) = B - C := by ring
  have e₂ : B - A - (D - A) = B - D := by ring
  have e₃ : C - A - (D - A) = C - D := by ring
  rw [e₁, e₂, e₃] at h
  simpa [normSq_sub_eq, dist_comm A B, dist_comm A C, dist_comm A D] using h

/-- The Gram relation with integer squared distances. -/
theorem gram_int {A B C D : ℂ} {a b c d e f : ℕ}
    (hab : dist A B = a) (hac : dist A C = b) (had : dist A D = c)
    (hbc : dist B C = d) (hbd : dist B D = e) (hcd : dist C D = f) :
    gram (a ^ 2 : ℤ) (b ^ 2) (c ^ 2) (d ^ 2) (e ^ 2) (f ^ 2) = 0 := by
  have h := gram_dist A B C D
  rw [hab, hac, had, hbc, hbd, hcd] at h
  have hR : ((gram (a ^ 2 : ℤ) (b ^ 2) (c ^ 2) (d ^ 2) (e ^ 2) (f ^ 2) : ℤ) : ℝ) = 0 := by
    push_cast [gram] at h ⊢
    linarith [h]
  exact_mod_cast hR

/-! ## The residue computations -/

/-- A squared distance modulo `8`: `4` if the distance is `2`, else `1`. -/
def v8 (x : Bool) : ZMod 8 := cond x 4 1

/-- Modulo `8`, the Gram relation forces the pairs at distance `2` to form a
perfect matching, a triangle, or all six pairs. The arguments are the pairs
`AB, AC, AD, BC, BD, CD`. -/
theorem pattern_mod8 : ∀ a b c d e f : Bool,
    gram (v8 a) (v8 b) (v8 c) (v8 d) (v8 e) (v8 f) = 0 →
      (a && f && !b && !c && !d && !e) ||
      (b && e && !a && !c && !d && !f) ||
      (c && d && !a && !b && !e && !f) ||
      (d && e && f && !a && !b && !c) ||
      (b && c && f && !a && !d && !e) ||
      (a && c && e && !b && !d && !f) ||
      (a && b && d && !c && !e && !f) ||
      (a && b && c && d && e && f) := by decide

/-- The squares of odd numbers modulo `32`. -/
def sq32 : Fin 4 → ZMod 32 := ![1, 9, 17, 25]

/-- Modulo `32`, the Gram relation fails for each of the four triangles: three
points at mutual distance `2`, and a fourth at odd distances from them. -/
theorem tri_mod32 : ∀ i j k : Fin 4,
    gram (sq32 i) (sq32 j) (sq32 k) 4 4 4 ≠ 0 ∧
    gram (sq32 i) 4 4 (sq32 j) (sq32 k) 4 ≠ 0 ∧
    gram 4 (sq32 i) 4 (sq32 j) 4 (sq32 k) ≠ 0 ∧
    gram 4 4 (sq32 i) 4 (sq32 j) (sq32 k) ≠ 0 := by decide

theorem odd_sq_mod8 : ∀ x : ZMod 8, x.val % 2 = 1 → x ^ 2 = 1 := by decide

theorem odd_sq_mod32 : ∀ x : ZMod 32, x.val % 2 = 1 → ∃ i : Fin 4, x ^ 2 = sq32 i := by decide

/-- An odd prime has `p² ≡ 1` modulo `8`. -/
theorem sq_mod8_of_odd_prime {p : ℕ} (hp : p.Prime) (h2 : p ≠ 2) :
    ((p : ZMod 8)) ^ 2 = 1 := by
  refine odd_sq_mod8 _ ?_
  rw [ZMod.val_natCast]
  have := hp.eq_two_or_odd
  omega

/-- An odd prime has `p²` among `1, 9, 17, 25` modulo `32`. -/
theorem sq_mod32_of_odd_prime {p : ℕ} (hp : p.Prime) (h2 : p ≠ 2) :
    ∃ i : Fin 4, ((p : ZMod 32)) ^ 2 = sq32 i := by
  refine odd_sq_mod32 _ ?_
  rw [ZMod.val_natCast]
  have := hp.eq_two_or_odd
  omega

/-- The three odd distances of a triangle configuration, as residues mod `32`. -/
theorem odd_triple {x y z : ℕ} (hx : x.Prime) (hy : y.Prime) (hz : z.Prime)
    (hx2 : x ≠ 2) (hy2 : y ≠ 2) (hz2 : z ≠ 2) :
    ∃ i j k : Fin 4, ((x : ZMod 32)) ^ 2 = sq32 i ∧ ((y : ZMod 32)) ^ 2 = sq32 j ∧
      ((z : ZMod 32)) ^ 2 = sq32 k := by
  obtain ⟨i, hi⟩ := sq_mod32_of_odd_prime hx hx2
  obtain ⟨j, hj⟩ := sq_mod32_of_odd_prime hy hy2
  obtain ⟨k, hk⟩ := sq_mod32_of_odd_prime hz hz2
  exact ⟨i, j, k, hi, hj, hk⟩

/-! ## Exactly two of the six distances are `2` -/

/-- The arithmetic heart of part (a): six primes that are the pairwise distances
of four points of the plane — so that they satisfy the Gram relation — contain
exactly two `2`s. -/
theorem two_of_six {a b c d e f : ℕ}
    (ha : a.Prime) (hb : b.Prime) (hc : c.Prime)
    (hd : d.Prime) (he : e.Prime) (hf : f.Prime)
    (h : gram (a ^ 2 : ℤ) (b ^ 2) (c ^ 2) (d ^ 2) (e ^ 2) (f ^ 2) = 0) :
    (if a = 2 then 1 else 0) + (if b = 2 then 1 else 0) + (if c = 2 then 1 else 0)
      + (if d = 2 then 1 else 0) + (if e = 2 then 1 else 0)
      + (if f = 2 then 1 else 0) = 2 := by
  have cast8 : ∀ {n : ℕ}, n.Prime → ((n : ZMod 8)) ^ 2 = v8 (decide (n = 2)) := by
    intro n hn
    by_cases h2 : n = 2
    · subst h2; decide
    · rw [decide_eq_false_iff_not.mpr h2]
      exact sq_mod8_of_odd_prime hn h2
  have h8 : gram (v8 (decide (a = 2))) (v8 (decide (b = 2))) (v8 (decide (c = 2)))
      (v8 (decide (d = 2))) (v8 (decide (e = 2))) (v8 (decide (f = 2))) = 0 := by
    have h' := congrArg (fun t : ℤ => (t : ZMod 8)) h
    simp only [gram] at h' ⊢
    push_cast at h'
    rw [← cast8 ha, ← cast8 hb, ← cast8 hc, ← cast8 hd, ← cast8 he, ← cast8 hf]
    linear_combination h'
  have hpat := pattern_mod8 _ _ _ _ _ _ h8
  simp only [Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq,
    decide_eq_false_iff_not] at hpat
  rcases hpat with (((((((h' | h') | h') | h') | h') | h') | h') | h')
  -- three perfect matchings
  · obtain ⟨⟨⟨⟨⟨p1, p2⟩, p3⟩, p4⟩, p5⟩, p6⟩ := h'
    simp [p1, p2, p3, p4, p5, p6]
  · obtain ⟨⟨⟨⟨⟨p1, p2⟩, p3⟩, p4⟩, p5⟩, p6⟩ := h'
    simp [p1, p2, p3, p4, p5, p6]
  · obtain ⟨⟨⟨⟨⟨p1, p2⟩, p3⟩, p4⟩, p5⟩, p6⟩ := h'
    simp [p1, p2, p3, p4, p5, p6]
  -- four triangles, each impossible modulo 32
  · exfalso
    obtain ⟨⟨⟨⟨⟨p1, p2⟩, p3⟩, p4⟩, p5⟩, p6⟩ := h'
    subst p1; subst p2; subst p3
    obtain ⟨i, j, k, hi, hj, hk⟩ := odd_triple ha hb hc p4 p5 p6
    refine (tri_mod32 i j k).1 ?_
    have h' := congrArg (fun t : ℤ => (t : ZMod 32)) h
    simp only [gram] at h' ⊢
    push_cast at h'
    rw [← hi, ← hj, ← hk]
    linear_combination h'
  · exfalso
    obtain ⟨⟨⟨⟨⟨p1, p2⟩, p3⟩, p4⟩, p5⟩, p6⟩ := h'
    subst p1; subst p2; subst p3
    obtain ⟨i, j, k, hi, hj, hk⟩ := odd_triple ha hd he p4 p5 p6
    refine (tri_mod32 i j k).2.1 ?_
    have h' := congrArg (fun t : ℤ => (t : ZMod 32)) h
    simp only [gram] at h' ⊢
    push_cast at h'
    rw [← hi, ← hj, ← hk]
    linear_combination h'
  · exfalso
    obtain ⟨⟨⟨⟨⟨p1, p2⟩, p3⟩, p4⟩, p5⟩, p6⟩ := h'
    subst p1; subst p2; subst p3
    obtain ⟨i, j, k, hi, hj, hk⟩ := odd_triple hb hd hf p4 p5 p6
    refine (tri_mod32 i j k).2.2.1 ?_
    have h' := congrArg (fun t : ℤ => (t : ZMod 32)) h
    simp only [gram] at h' ⊢
    push_cast at h'
    rw [← hi, ← hj, ← hk]
    linear_combination h'
  · exfalso
    obtain ⟨⟨⟨⟨⟨p1, p2⟩, p3⟩, p4⟩, p5⟩, p6⟩ := h'
    subst p1; subst p2; subst p3
    obtain ⟨i, j, k, hi, hj, hk⟩ := odd_triple hc he hf p4 p5 p6
    refine (tri_mod32 i j k).2.2.2 ?_
    have h' := congrArg (fun t : ℤ => (t : ZMod 32)) h
    simp only [gram] at h' ⊢
    push_cast at h'
    rw [← hi, ← hj, ← hk]
    linear_combination h'
  -- all six distances equal to 2: the Gram form is 128, not 0
  · exfalso
    obtain ⟨⟨⟨⟨⟨p1, p2⟩, p3⟩, p4⟩, p5⟩, p6⟩ := h'
    subst p1; subst p2; subst p3; subst p4; subst p5; subst p6
    norm_num [gram] at h

/-! ## No five points -/

/-- Four points of the plane with prime pairwise distances: exactly two of the
six distances equal `2`. -/
theorem two_of_four {A B C D : ℂ} {a b c d e f : ℕ}
    (ha : a.Prime) (hb : b.Prime) (hc : c.Prime)
    (hd : d.Prime) (he : e.Prime) (hf : f.Prime)
    (hab : dist A B = a) (hac : dist A C = b) (had : dist A D = c)
    (hbc : dist B C = d) (hbd : dist B D = e) (hcd : dist C D = f) :
    (if a = 2 then 1 else 0) + (if b = 2 then 1 else 0) + (if c = 2 then 1 else 0)
      + (if d = 2 then 1 else 0) + (if e = 2 then 1 else 0)
      + (if f = 2 then 1 else 0) = 2 :=
  two_of_six ha hb hc hd he hf (gram_int hab hac had hbc hbd hcd)

/-- No five points of the plane have all ten pairwise distances prime.

Each of the five four-point subsets contains exactly two pairs at distance `2`,
and each pair lies in three of those subsets, so `3e = 5 * 2` for the number `e`
of pairs at distance `2` — impossible. -/
theorem no_five (P : Fin 5 → ℂ)
    (h : ∀ i j : Fin 5, i ≠ j → ∃ p : ℕ, p.Prime ∧ dist (P i) (P j) = p) : False := by
  obtain ⟨p01, hp01, hd01⟩ := h 0 1 (by decide)
  obtain ⟨p02, hp02, hd02⟩ := h 0 2 (by decide)
  obtain ⟨p03, hp03, hd03⟩ := h 0 3 (by decide)
  obtain ⟨p04, hp04, hd04⟩ := h 0 4 (by decide)
  obtain ⟨p12, hp12, hd12⟩ := h 1 2 (by decide)
  obtain ⟨p13, hp13, hd13⟩ := h 1 3 (by decide)
  obtain ⟨p14, hp14, hd14⟩ := h 1 4 (by decide)
  obtain ⟨p23, hp23, hd23⟩ := h 2 3 (by decide)
  obtain ⟨p24, hp24, hd24⟩ := h 2 4 (by decide)
  obtain ⟨p34, hp34, hd34⟩ := h 3 4 (by decide)
  have e0123 := two_of_four hp01 hp02 hp03 hp12 hp13 hp23 hd01 hd02 hd03 hd12 hd13 hd23
  have e0124 := two_of_four hp01 hp02 hp04 hp12 hp14 hp24 hd01 hd02 hd04 hd12 hd14 hd24
  have e0134 := two_of_four hp01 hp03 hp04 hp13 hp14 hp34 hd01 hd03 hd04 hd13 hd14 hd34
  have e0234 := two_of_four hp02 hp03 hp04 hp23 hp24 hp34 hd02 hd03 hd04 hd23 hd24 hd34
  have e1234 := two_of_four hp12 hp13 hp14 hp23 hp24 hp34 hd12 hd13 hd14 hd23 hd24 hd34
  omega

/-! ## Part (a): the bound -/

/-- **Part (a)**: a prime-distance set has at most four points. -/
theorem card_le_four {n : ℕ} (P : Fin n → ℂ) (hP : IsPrimeDistanceSet P) : n ≤ 4 := by
  by_contra hn
  have hn5 : 5 ≤ n := by omega
  refine no_five (fun i : Fin 5 => P ⟨i.val, by have := i.isLt; omega⟩) ?_
  intro i j hij
  refine hP.2 _ _ ?_
  simp only [ne_eq, Fin.mk.injEq]
  exact fun hv => hij (Fin.ext hv)

/-- **Conjecture 00000000049 holds.** -/
theorem conjecture_holds : ConjectureHolds :=
  ⟨fun _ P hP => card_le_four P hP, conjecture_part_b⟩

/-! ## The collinear quadruples, for the appendix of the paper

A prime-distance quadruple is in fact collinear (paper, Appendix A; the
geometric step is not formalized). Granting collinearity, its consecutive gaps
are forced, which is the arithmetic half of the uniqueness statement and is
proved here: of two adjacent gaps exactly one is `2`, and `q, q + 2, q + 4`
cannot all be prime unless `q = 3`. -/

/-- The sum of two odd primes is never prime: it is even and exceeds `2`. -/
theorem not_prime_add_of_ne_two {u v : ℕ} (hu : u.Prime) (hv : v.Prime)
    (hu2 : u ≠ 2) (hv2 : v ≠ 2) : ¬ (u + v).Prime := by
  obtain ⟨k, hk⟩ := hu.odd_of_ne_two hu2
  obtain ⟨l, hl⟩ := hv.odd_of_ne_two hv2
  have hu2' := hu.two_le
  have hv2' := hv.two_le
  intro h
  have hdvd : 2 ∣ u + v := ⟨k + l + 1, by omega⟩
  rcases h.eq_one_or_self_of_dvd 2 hdvd with h' | h' <;> omega

/-- Four points on a line with all six pairwise distances prime have
consecutive gaps `2, 3, 2` — so the quadruple is `{0, 2, 5, 7}` up to an
isometry of the line. -/
theorem gaps_of_four_collinear {g₁ g₂ g₃ : ℕ}
    (h₁ : g₁.Prime) (h₂ : g₂.Prime) (h₃ : g₃.Prime)
    (h₁₂ : (g₁ + g₂).Prime) (h₂₃ : (g₂ + g₃).Prime)
    (h₁₂₃ : (g₁ + g₂ + g₃).Prime) : g₁ = 2 ∧ g₂ = 3 ∧ g₃ = 2 := by
  -- adjacent gaps are never both odd, and never both `2`
  have adj : ∀ {u v : ℕ}, u.Prime → v.Prime → (u + v).Prime → (u = 2) ≠ (v = 2) := by
    intro u v hu hv huv
    by_cases hu2 : u = 2 <;> by_cases hv2 : v = 2
    · exact absurd huv (by rw [hu2, hv2]; decide)
    · simp [hu2, hv2]
    · simp [hu2, hv2]
    · exact absurd huv (not_prime_add_of_ne_two hu hv hu2 hv2)
  have a12 := adj h₁ h₂ h₁₂
  have a23 := adj h₂ h₃ h₂₃
  -- the middle gap cannot be the even one: the total span would be even
  have hmid : g₂ ≠ 2 := by
    intro hg2
    have hg1 : g₁ ≠ 2 := by simpa [hg2] using a12.symm
    have hg3 : g₃ ≠ 2 := by simpa [hg2] using a23
    obtain ⟨k, hk⟩ := h₁.odd_of_ne_two hg1
    obtain ⟨l, hl⟩ := h₃.odd_of_ne_two hg3
    have b1 := h₁.two_le
    have b3 := h₃.two_le
    have hdvd : 2 ∣ g₁ + g₂ + g₃ := ⟨k + l + 2, by omega⟩
    rcases h₁₂₃.eq_one_or_self_of_dvd 2 hdvd with h' | h' <;> omega
  have hg1 : g₁ = 2 := by by_contra h; simp [hmid, h] at a12
  have hg3 : g₃ = 2 := by by_contra h; simp [hmid, h] at a23
  -- `g₂`, `g₂ + 2`, `g₂ + 4` are all prime, so one of them is divisible by 3
  refine ⟨hg1, ?_, hg3⟩
  subst hg1; subst hg3
  by_contra hne
  have hodd := h₂.odd_of_ne_two hmid
  have h3le := h₂.two_le
  -- one of `g₂`, `g₂ + 2`, `g₂ + 4` is a multiple of `3` and larger than `3`
  have key : (3 ∣ g₂) ∨ (3 ∣ g₂ + 2) ∨ (3 ∣ 2 + g₂ + 2) := by omega
  have h24 : (g₂ + 2).Prime := by simpa [Nat.add_comm] using h₂₃
  have h244 : (2 + g₂ + 2).Prime := by simpa [Nat.add_comm, Nat.add_assoc] using h₁₂₃
  rcases key with hk | hk | hk
  · rcases (h₂.eq_one_or_self_of_dvd 3 hk) with h' | h' <;> omega
  · rcases (h24.eq_one_or_self_of_dvd 3 hk) with h' | h' <;> omega
  · rcases (h244.eq_one_or_self_of_dvd 3 hk) with h' | h' <;> omega

end Submission00000000049
