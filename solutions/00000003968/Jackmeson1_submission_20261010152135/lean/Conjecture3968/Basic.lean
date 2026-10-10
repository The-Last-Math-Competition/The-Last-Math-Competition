import Mathlib
import Conjecture3968.Statement

/-! # Conjecture 00000003968: rationality of the graceful-labeling count of caterpillars -/

-- (formal statement: see Statement.lean)

namespace C3968

/-- A rational generating function has at most exponential coefficient growth. -/
theorem rational_bound {a : ℕ → ℕ} (h : Rational a) :
    ∃ M R : ℚ, 0 < M ∧ 1 ≤ R ∧ ∀ n, (a n : ℚ) ≤ M * R ^ n := by
  obtain ⟨P, Q, hQ, hPQ⟩ := h
  obtain ⟨Q1, hQ1, hnd⟩ := Polynomial.exists_eq_pow_rootMultiplicity_mul_and_not_dvd Q hQ 0
  set k := Q.rootMultiplicity 0
  have hq0 : Q1.coeff 0 ≠ 0 := by
    intro h0; apply hnd; simpa [Polynomial.X_dvd_iff] using h0
  have hrec : ∀ n, P.natDegree < n + k →
      ∑ p ∈ Finset.HasAntidiagonal.antidiagonal n, Q1.coeff p.1 * (a p.2 : ℚ) = 0 := by
    intro n hn
    have h1 := congrArg (PowerSeries.coeff (n + k)) hPQ
    rw [hQ1] at h1
    simp only [sub_zero, map_zero, Polynomial.C_0, Polynomial.coe_mul, Polynomial.coe_pow,
      Polynomial.coe_X, mul_assoc] at h1
    rw [PowerSeries.coeff_X_pow_mul] at h1
    simp only [PowerSeries.coeff_mul, Polynomial.coeff_coe, PowerSeries.coeff_mk] at h1
    rw [h1, Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)]
  set c : ℚ := ∑ i ∈ Finset.range Q1.natDegree, |Q1.coeff (i + 1)| / |Q1.coeff 0| with hc
  have hg : ∀ m, ∑ i ∈ Finset.range m, |Q1.coeff (i + 1)| / |Q1.coeff 0| ≤ c := by
    intro m
    rcases le_total m Q1.natDegree with hm | hm
    · exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hm)
        (fun _ _ _ => by positivity)
    · rw [hc]; refine le_of_eq (Finset.sum_subset (Finset.range_mono hm) ?_).symm
      intro i _ hi
      rw [Finset.mem_range, not_lt] at hi
      rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)]; simp
  have hc0 : 0 ≤ c := Finset.sum_nonneg (fun _ _ => by positivity)
  set N := P.natDegree + 1
  set M : ℚ := 1 + ∑ j ∈ Finset.range (N + 1), (a j : ℚ) with hM
  have hM1 : 1 ≤ M := by
    rw [hM]
    have : 0 ≤ ∑ j ∈ Finset.range (N + 1), (a j : ℚ) :=
      Finset.sum_nonneg (fun _ _ => by positivity)
    linarith
  refine ⟨M, c + 1, by linarith, by linarith, ?_⟩
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases le_or_gt n N with hn | hn
    · have h1 : (a n : ℚ) ≤ ∑ j ∈ Finset.range (N + 1), (a j : ℚ) :=
        Finset.single_le_sum (f := fun j => (a j : ℚ)) (fun _ _ => by positivity)
          (Finset.mem_range.2 (by omega))
      have h2 : (1 : ℚ) ≤ (c + 1) ^ n := one_le_pow₀ (by linarith)
      nlinarith
    · obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
      have h1 := hrec (m + 1) (by omega)
      rw [Finset.Nat.sum_antidiagonal_succ] at h1
      simp only at h1
      have h2 : (a (m + 1) : ℚ) = -(∑ p ∈ Finset.HasAntidiagonal.antidiagonal m,
          Q1.coeff (p.1 + 1) / Q1.coeff 0 * (a p.2 : ℚ)) := by
        have : Q1.coeff 0 * (a (m + 1) : ℚ) + ∑ p ∈ Finset.HasAntidiagonal.antidiagonal m,
            Q1.coeff (p.1 + 1) * (a p.2 : ℚ) = 0 := h1
        have h4 : ∑ p ∈ Finset.HasAntidiagonal.antidiagonal m,
            Q1.coeff (p.1 + 1) / Q1.coeff 0 * (a p.2 : ℚ) =
            (∑ p ∈ Finset.HasAntidiagonal.antidiagonal m, Q1.coeff (p.1 + 1) * (a p.2 : ℚ))
              / Q1.coeff 0 := by
          rw [Finset.sum_div]; exact Finset.sum_congr rfl (fun _ _ => by ring)
        rw [h4]; field_simp; linarith
      have h3 : (a (m + 1) : ℚ) ≤ ∑ p ∈ Finset.HasAntidiagonal.antidiagonal m,
          |Q1.coeff (p.1 + 1)| / |Q1.coeff 0| * (M * (c + 1) ^ m) := by
        rw [h2]
        refine (neg_le_abs _).trans ?_
        refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun p hp => ?_)
        rw [abs_mul, abs_div, Nat.abs_cast]
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        have hp2 : p.2 ≤ m := by have := Finset.HasAntidiagonal.mem_antidiagonal.1 hp; omega
        refine (ih p.2 (by omega)).trans ?_
        exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (by linarith) hp2) (by linarith)
      refine h3.trans ?_
      rw [← Finset.sum_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
      have := hg (m + 1)
      simp only at *
      have hMp : 0 ≤ M * (c + 1) ^ m := by positivity
      calc _ ≤ c * (M * (c + 1) ^ m) := mul_le_mul_of_nonneg_right this hMp
        _ ≤ M * (c + 1) ^ (m + 1) := by rw [pow_succ]; nlinarith

/-- Superexponential growth along `n = 12 s` rules out a rational generating function. -/
theorem not_rational_of_fact {a : ℕ → ℕ} (h : ∀ s, 1 ≤ s → s.factorial ≤ a (12 * s)) :
    ¬ Rational a := by
  intro hr
  obtain ⟨M, R, hM, hR, hb⟩ := rational_bound hr
  have ht := FloorSemiring.tendsto_pow_div_factorial_atTop ((R : ℝ) ^ 12)
  have hMr : (0:ℝ) < M := by exact_mod_cast hM
  obtain ⟨s, hs1, hs2⟩ := ((ht.eventually (gt_mem_nhds (show (0:ℝ) < 1 / M by positivity))).and
    (Filter.eventually_ge_atTop 1)).exists
  have h1 : (s.factorial : ℝ) ≤ M * ((R:ℝ)^12)^s := by
    have h2 : (s.factorial : ℚ) ≤ a (12*s) := by exact_mod_cast h s hs2
    have h3 : (s.factorial : ℚ) ≤ M * (R^12)^s := by
      rw [← pow_mul]; exact h2.trans (hb (12 * s))
    exact_mod_cast h3
  have hf : (0:ℝ) < s.factorial := by positivity
  rw [div_lt_iff₀ hf] at hs1
  have e : (M:ℝ) * (1 / M * s.factorial) = s.factorial := by field_simp
  have := mul_lt_mul_of_pos_left hs1 hMr
  linarith


/-- A graph given by a parent map `pr` with decreasing rank `ρ` toward the root `0` is a tree. -/
theorem tree_of_par (n : ℕ) (hn : 0 < n) (pr ρ : ℕ → ℕ) (hb : ∀ v < n, pr v < n)
    (h0 : pr 0 = 0) (hρ : ∀ v, 0 < v → v < n → ρ (pr v) < ρ v) :
    (SimpleGraph.fromRel (fun u v : Fin n => pr u = (v : ℕ))).IsTree := by
  classical
  set G := SimpleGraph.fromRel (fun u v : Fin n => pr u = (v : ℕ)) with hG
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  rw [SimpleGraph.isTree_iff_connected_and_card]
  have hne : ∀ v : Fin n, (v : ℕ) ≠ 0 → (v : ℕ) ≠ pr v := by
    intro v hv e
    have := hρ v (by omega) v.2
    rw [← e] at this; omega
  refine ⟨?_, ?_⟩
  · refine SimpleGraph.Connected.mk (fun x y => ?_)
    have key : ∀ k, ∀ v : Fin n, ρ v = k → G.Reachable v ⟨0, hn⟩ := by
      intro k
      induction k using Nat.strong_induction_on with
      | _ k ih =>
        intro v hv
        by_cases h : (v : ℕ) = 0
        · have : v = ⟨0, hn⟩ := Fin.ext h
          subst this; rfl
        · have hlt := hρ v (by omega) v.2
          have hadj : G.Adj v ⟨pr v, hb v v.2⟩ := by
            rw [hG, SimpleGraph.fromRel_adj]
            exact ⟨fun e => hne v h (by simpa [Fin.ext_iff] using e), Or.inl rfl⟩
          exact hadj.reachable.trans (ih _ (by simp only at *; omega) _ rfl)
    exact (key _ x rfl).trans (key _ y rfl).symm
  · have hbij : Function.Bijective (fun v : {v : Fin n // (v : ℕ) ≠ 0} =>
        (⟨s(v.1, ⟨pr v.1, hb v.1 v.1.2⟩), by
          rw [hG, SimpleGraph.mem_edgeSet, SimpleGraph.fromRel_adj]
          exact ⟨fun e => hne v.1 v.2 (by simpa [Fin.ext_iff] using e), Or.inl rfl⟩⟩ : G.edgeSet)) := by
      constructor
      · rintro ⟨v, hv⟩ ⟨w, hw⟩ e
        have e' := congrArg Subtype.val e
        simp only [Sym2.eq_iff, Fin.ext_iff] at e'
        rcases e' with ⟨e1, _⟩ | ⟨e1, e2⟩
        · exact Subtype.ext (Fin.ext e1)
        · have a1 := hρ v (by omega) v.2
          have a2 := hρ w (by omega) w.2
          rw [e2] at a1; rw [← e1] at a2; omega
      · rintro ⟨e, he⟩
        induction e using Sym2.ind with
        | _ x y =>
          rw [hG, SimpleGraph.mem_edgeSet, SimpleGraph.fromRel_adj] at he
          obtain ⟨hxy, h | h⟩ := he
          · have hx : (x : ℕ) ≠ 0 := by
              intro e; rw [e, h0] at h; exact hxy (Fin.ext (by omega))
            have : (⟨pr x, hb x x.2⟩ : Fin n) = y := Fin.ext h
            exact ⟨⟨x, hx⟩, Subtype.ext (by show s(x, _) = s(x, y); rw [this])⟩
          · have hy : (y : ℕ) ≠ 0 := by
              intro e; rw [e, h0] at h; exact hxy (Fin.ext (by omega))
            refine ⟨⟨y, hy⟩, Subtype.ext ?_⟩
            have : (⟨pr y, hb y y.2⟩ : Fin n) = x := Fin.ext h
            show s(y, _) = s(x, y)
            rw [this, Sym2.eq_swap]
    have := Nat.card_eq_of_bijective _ hbij
    rw [← this]
    have h1 : Fintype.card {x : Fin n // (x : ℕ) = 0} = 1 := by
      rw [Fintype.card_eq_one_iff]
      exact ⟨⟨⟨0, hn⟩, rfl⟩, fun ⟨x, hx⟩ => Subtype.ext (Fin.ext hx)⟩
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Fintype.card_subtype_compl, h1]
    simp
    omega



/-! ## The family of graceful caterpillars on `12 s` vertices -/

/-- Parent map: spine zigzag `0, n-1, 1, n-2, ...` (`n = 12 s`), leaves `4s..7s-1` hang on `4s-1`,
leaves `7s..8s-1` hang on the high vertex `x + 3s + 1 + t (x - 7s)`. -/
def par (s : ℕ) (t : ℕ → ℕ) (v : ℕ) : ℕ :=
  if v < 4*s then (if v = 0 then 0 else 12*s - v)
  else if v < 7*s then 4*s - 1
  else if v < 8*s then v + 3*s + 1 + t (v - 7*s)
  else 12*s - 1 - v

def rk (s v : ℕ) : ℕ :=
  if v < 4*s then 2*v else if v < 8*s then 12*s + v else 2*(12*s-1-v)+1

def fam (s : ℕ) (t : ℕ → ℕ) : SimpleGraph (Fin (12*s)) :=
  SimpleGraph.fromRel (fun u v => par s t u = (v : ℕ))

theorem fam_tree {s : ℕ} {t : ℕ → ℕ} (hs : 1 ≤ s) (ht : ∀ q < s, t q < s) :
    (fam s t).IsTree :=
  tree_of_par (12*s) (by omega) (par s t) (rk s)
    (by intro v hv; have := ht (v-7*s); simp only [par]; split_ifs <;> omega)
    (by simp only [par]; split_ifs <;> omega)
    (by intro v h0 hv; have := ht (v-7*s); simp only [par, rk]; split_ifs <;> omega)

theorem fam_adj {s : ℕ} {t : ℕ → ℕ} {u v : Fin (12*s)} (h : (u : ℕ) < v) :
    (fam s t).Adj u v ↔
      (((u : ℕ) < 4*s ∧ 8*s ≤ v ∧ ((u : ℕ) + v = 12*s - 1 ∨ (u : ℕ) + v = 12*s)) ∨
      ((u : ℕ) = 4*s - 1 ∧ 4*s ≤ v ∧ (v : ℕ) < 7*s) ∨
      (7*s ≤ u ∧ (u : ℕ) < 8*s ∧ (v : ℕ) = u + 3*s + 1 + t (u - 7*s))) := by
  have := v.2
  simp only [fam, SimpleGraph.fromRel_adj, par, Fin.ext_iff, ne_eq]
  split_ifs <;> omega

theorem fam_cat {s : ℕ} {t : ℕ → ℕ} (hs : 1 ≤ s) (ht : ∀ q < s, t q < s) :
    IsCaterpillar (fam s t) := by
  refine ⟨8*s, {v | (v : ℕ) < 4*s ∨ 8*s ≤ v}, ⟨?_⟩, ?_⟩
  · exact
    { toFun := fun x => ⟨if (x.1 : ℕ) < 4*s then 2*x.1 else 2*(12*s-1-x.1)+1, by
        have h1 := x.2; have h2 := x.1.2
        simp only [Set.mem_ofPred_eq] at h1
        split_ifs <;> omega⟩
      invFun := fun r => ⟨⟨if (r : ℕ) % 2 = 0 then r/2 else 12*s - 1 - r/2, by
          have := r.2; split_ifs <;> omega⟩, by
          have := r.2; simp only [Set.mem_ofPred_eq]; split_ifs <;> omega⟩
      left_inv := fun x => by
        have h1 := x.2; have h2 := x.1.2
        simp only [Set.mem_ofPred_eq] at h1
        apply Subtype.ext; apply Fin.ext; simp only
        split_ifs <;> omega
      right_inv := fun r => by
        have := r.2
        apply Fin.ext; simp only
        split_ifs <;> omega
      map_rel_iff' := fun {a b} => by
        have h1 := a.2; have h2 := b.2; have h3 := a.1.2; have h4 := b.1.2
        simp only [Set.mem_ofPred_eq] at h1 h2
        simp only [Equiv.coe_fn_mk, SimpleGraph.pathGraph_adj, SimpleGraph.comap_adj,
          Function.Embedding.coe_subtype, Subtype.coe_prop]
        rcases lt_trichotomy (a.1 : ℕ) b.1 with h | h | h
        · rw [fam_adj h]
          split_ifs <;> omega
        · have : a.1 = b.1 := Fin.ext h
          simp only [fam, SimpleGraph.fromRel_adj, this]
          split_ifs <;> omega
        · rw [SimpleGraph.adj_comm, fam_adj h]
          split_ifs <;> omega }
  · intro w
    by_cases hw : (w : ℕ) < 4*s ∨ 8*s ≤ w
    · exact Or.inl hw
    · right
      have := ht (w - 7*s)
      have hp : par s t w < 12*s := by simp only [par]; split_ifs <;> omega
      refine ⟨⟨par s t w, hp⟩, ?_, ?_⟩
      · show par s t w < 4*s ∨ 8*s ≤ par s t w
        simp only [par]; split_ifs <;> omega
      · refine (SimpleGraph.fromRel_adj _ _ _).2 ⟨fun h => ?_, Or.inl rfl⟩
        have h' : (w : ℕ) = par s t w := congrArg Fin.val h
        revert h'; simp only [par]; split_ifs <;> omega

theorem fam_graceful {s : ℕ} {t : ℕ → ℕ} (hs : 1 ≤ s) (ht : ∀ q < s, t q < s)
    (hinj : ∀ q q', q < s → q' < s → t q = t q' → q = q')
    (hsurj : ∀ e < s, ∃ q < s, t q = e) :
    IsGraceful (fam s t) (Equiv.refl (Fin (12*s))) := by
  intro d hd1 hd2
  simp only [Equiv.refl_symm, Equiv.refl_apply]
  have hn : 12*s - 1 = 12*s - 1 := rfl
  by_cases c1 : d ≤ 3*s
  · refine ⟨⟨4*s-1, by omega⟩, ⟨⟨4*s-1+d, by omega⟩, ?_, rfl⟩, ?_⟩
    · rw [fam_adj (by simp <;> omega)]; simp <;> omega
    · rintro u ⟨v, hv, hvd⟩
      have huv : (u : ℕ) < v := by omega
      rw [fam_adj huv] at hv
      have := v.2
      apply Fin.ext; simp only
      have := ht (u - 7*s)
      rcases hv with hv | hv | hv <;> omega
  by_cases c2 : d ≤ 4*s
  · obtain ⟨q, hq, hqd⟩ := hsurj (d - 3*s - 1) (by omega)
    refine ⟨⟨7*s+q, by omega⟩, ⟨⟨7*s+q+d, by omega⟩, ?_, rfl⟩, ?_⟩
    · rw [fam_adj (by simp <;> omega)]; simp <;> omega
    · rintro u ⟨v, hv, hvd⟩
      have huv : (u : ℕ) < v := by omega
      rw [fam_adj huv] at hv
      have := v.2
      apply Fin.ext; simp only
      rcases hv with hv | hv | hv <;> try omega
      have := hinj (u - 7*s) q (by omega) hq (by omega)
      omega
  · refine ⟨⟨(12*s-d)/2, by omega⟩, ⟨⟨(12*s-d)/2+d, by omega⟩, ?_, rfl⟩, ?_⟩
    · rw [fam_adj (by simp <;> omega)]; simp <;> omega
    · rintro u ⟨v, hv, hvd⟩
      have huv : (u : ℕ) < v := by omega
      rw [fam_adj huv] at hv
      have := v.2
      apply Fin.ext; simp only
      have := ht (u - 7*s)
      rcases hv with hv | hv | hv <;> omega



/-! ## Counting: `s! ≤` each count at `n = 12 s` -/

/-- Extension of a permutation of `Fin s` to a function `ℕ → ℕ`. -/
def tt {s : ℕ} (τ : Equiv.Perm (Fin s)) (q : ℕ) : ℕ := if h : q < s then (τ ⟨q, h⟩ : ℕ) else 0

theorem tt_lt {s : ℕ} (τ : Equiv.Perm (Fin s)) : ∀ q < s, tt τ q < s := by
  intro q hq; simp only [tt, dif_pos hq]; exact (τ ⟨q, hq⟩).2

theorem tt_inj {s : ℕ} (τ : Equiv.Perm (Fin s)) :
    ∀ q q', q < s → q' < s → tt τ q = tt τ q' → q = q' := by
  intro q q' hq hq' h
  simp only [tt, dif_pos hq, dif_pos hq'] at h
  have := τ.injective (Fin.ext h)
  simpa using congrArg Fin.val this

theorem tt_surj {s : ℕ} (τ : Equiv.Perm (Fin s)) : ∀ e < s, ∃ q < s, tt τ q = e := by
  intro e he
  refine ⟨(τ.symm ⟨e, he⟩ : ℕ), (τ.symm ⟨e, he⟩).2, ?_⟩
  simp [tt]

/-- The caterpillar of the family attached to `τ`. -/
def catOf {s : ℕ} (hs : 1 ≤ s) (τ : Equiv.Perm (Fin s)) : CatTree (12 * s) :=
  ⟨fam s (tt τ), fam_tree hs (tt_lt τ), fam_cat hs (tt_lt τ)⟩

theorem fam_inj {s : ℕ} {t t' : ℕ → ℕ} (ht : ∀ q < s, t q < s) (ht' : ∀ q < s, t' q < s)
    (h : fam s t = fam s t') : ∀ q < s, t q = t' q := by
  intro q hq
  have h1 : (fam s t).Adj ⟨7*s+q, by have := ht q hq; omega⟩
      ⟨7*s+q+3*s+1+t q, by have := ht q hq; omega⟩ := by
    rw [fam_adj (by simp <;> omega)]
    simp only [Fin.val_mk]
    right; right
    refine ⟨by omega, by omega, ?_⟩
    have e : 7*s+q-7*s = q := by omega
    rw [e]
  rw [h, fam_adj (by simp <;> omega)] at h1
  have e : 7*s+q-7*s = q := by omega
  have := ht' q hq
  simp only [Fin.val_mk, e] at h1
  omega

theorem catOf_inj {s : ℕ} (hs : 1 ≤ s) : Function.Injective (fun τ => (catOf hs τ).1) := by
  intro τ τ' h
  have := fam_inj (tt_lt τ) (tt_lt τ') h
  ext q
  have h2 := this q.1 q.2
  simp only [tt, dif_pos q.2] at h2
  exact h2

theorem catOf_graceful {s : ℕ} (hs : 1 ≤ s) (τ : Equiv.Perm (Fin s)) :
    IsGraceful (catOf hs τ).1 (Equiv.refl (Fin (12 * s))) :=
  fam_graceful hs (tt_lt τ) (tt_inj τ) (tt_surj τ)

instance (n : ℕ) : Finite (CatTree n) := by unfold CatTree; infer_instance

theorem edgeSet_ge {s : ℕ} (hs : 1 ≤ s) : s.factorial ≤ edgeSetCount (12 * s) := by
  have := Nat.card_le_card_of_injective
    (fun τ : Equiv.Perm (Fin s) => (⟨catOf hs τ, catOf_graceful hs τ⟩ :
      {G : CatTree (12 * s) // IsGraceful G.1 (Equiv.refl (Fin (12 * s)))}))
    (fun τ τ' h => catOf_inj hs (congrArg (fun x => x.1.1) h))
  simpa [edgeSetCount, Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin] using this

theorem pair_ge {s : ℕ} (hs : 1 ≤ s) : s.factorial ≤ pairCount (12 * s) := by
  have := Nat.card_le_card_of_injective
    (fun τ : Equiv.Perm (Fin s) => (⟨(catOf hs τ, Equiv.refl (Fin (12 * s))), catOf_graceful hs τ⟩ :
      {p : CatTree (12 * s) × (Fin (12 * s) ≃ Fin (12 * s)) // IsGraceful p.1.1 p.2}))
    (fun τ τ' h => catOf_inj hs (congrArg (fun x => x.1.1.1) h))
  simpa [pairCount, Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin] using this

theorem class_ge {s : ℕ} (hs : 1 ≤ s) : s.factorial ≤ classCount (12 * s) := by
  have hex : ∀ τ : Equiv.Perm (Fin s), Nonempty ((Quotient.out (Quotient.mk (isoSetoid (12 * s))
      (catOf hs τ))).1 ≃g (catOf hs τ).1) := fun τ =>
    Quotient.exact (Quotient.out_eq (Quotient.mk (isoSetoid (12 * s)) (catOf hs τ)))
  have hkey : ∀ (τ : Equiv.Perm (Fin s)) (u v : Fin (12 * s)),
      (Quotient.out (Quotient.mk (isoSetoid (12 * s)) (catOf hs τ))).1.Adj
        ((hex τ).some.toEquiv.symm u) ((hex τ).some.toEquiv.symm v) ↔ (catOf hs τ).1.Adj u v := by
    intro τ u v
    have h := (hex τ).some.map_rel_iff (a := (hex τ).some.toEquiv.symm u)
      (b := (hex τ).some.toEquiv.symm v)
    have e1 : (hex τ).some ((hex τ).some.toEquiv.symm u) = u :=
      (hex τ).some.toEquiv.apply_symm_apply u
    have e2 : (hex τ).some ((hex τ).some.toEquiv.symm v) = v :=
      (hex τ).some.toEquiv.apply_symm_apply v
    rw [e1, e2] at h
    exact h.symm
  let Φ : Equiv.Perm (Fin s) → (Σ c : Quotient (isoSetoid (12 * s)),
      {f : Fin (12 * s) ≃ Fin (12 * s) // IsGraceful (Quotient.out c).1 f}) := fun τ =>
    ⟨Quotient.mk _ (catOf hs τ), (hex τ).some.toEquiv, by
      intro d h1 h2
      have := catOf_graceful hs τ d h1 h2
      simp only [Equiv.refl_symm, Equiv.refl_apply] at this
      simp only [hkey]
      exact this⟩
  let Ψ : (Σ c : Quotient (isoSetoid (12 * s)),
      {f : Fin (12 * s) ≃ Fin (12 * s) // IsGraceful (Quotient.out c).1 f}) →
      SimpleGraph (Fin (12 * s)) := fun p => (Quotient.out p.1).1.comap p.2.1.symm
  have hΨΦ : ∀ τ, Ψ (Φ τ) = (catOf hs τ).1 := by
    intro τ
    ext u v
    exact hkey τ u v
  have hinj : Function.Injective Φ := by
    refine Function.Injective.of_comp (f := Ψ) ?_
    intro τ τ' h
    exact catOf_inj hs (by simpa [Function.comp_def, hΨΦ] using h)
  have := Nat.card_le_card_of_injective Φ hinj
  simpa [classCount, Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin] using this

theorem complement_ge {s : ℕ} (hs : 1 ≤ s) : s.factorial ≤ complementCount (12 * s) := by
  have hne : ∀ τ τ' : Equiv.Perm (Fin s),
      (catOf hs τ).1 ≠ (catOf hs τ').1.comap (Fin.revPerm : Equiv.Perm (Fin (12 * s))) := by
    intro τ τ' h
    have h' : fam s (tt τ) = (fam s (tt τ')).comap (Fin.revPerm : Equiv.Perm (Fin (12 * s))) := h
    have hB : ¬ (fam s (tt τ)).Adj ⟨0, by omega⟩ ⟨12*s-2, by omega⟩ := by
      rw [fam_adj (by simp <;> omega)]; simp <;> omega
    apply hB
    have hA : (fam s (tt τ')).Adj ⟨1, by omega⟩ ⟨12*s-1, by omega⟩ := by
      rw [fam_adj (by simp <;> omega)]; simp <;> omega
    have e1 : (Fin.revPerm : Equiv.Perm (Fin (12 * s))) ⟨0, by omega⟩ = ⟨12*s-1, by omega⟩ :=
      Fin.ext (by simp)
    have e2 : (Fin.revPerm : Equiv.Perm (Fin (12 * s))) ⟨12*s-2, by omega⟩ = ⟨1, by omega⟩ :=
      Fin.ext (by simp; omega)
    rw [h', SimpleGraph.comap_adj, e1, e2]
    exact hA.symm
  have := Nat.card_le_card_of_injective
    (fun τ : Equiv.Perm (Fin s) => (⟨{(catOf hs τ).1,
        (catOf hs τ).1.comap (Fin.revPerm : Equiv.Perm (Fin (12 * s)))},
        ⟨catOf hs τ, catOf_graceful hs τ, rfl⟩⟩ :
      {S : Set (SimpleGraph (Fin (12 * s))) //
        ∃ G : CatTree (12 * s), IsGraceful G.1 (Equiv.refl (Fin (12 * s))) ∧
          S = {G.1, G.1.comap (Fin.revPerm : Equiv.Perm (Fin (12 * s)))}}))
    (fun τ τ' h => by
      have h2 : ({(catOf hs τ).1, (catOf hs τ).1.comap (Fin.revPerm : Equiv.Perm (Fin (12 * s)))} :
          Set (SimpleGraph (Fin (12 * s)))) = {(catOf hs τ').1,
          (catOf hs τ').1.comap (Fin.revPerm : Equiv.Perm (Fin (12 * s)))} := congrArg Subtype.val h
      have h3 : (catOf hs τ).1 ∈ ({(catOf hs τ').1, (catOf hs τ').1.comap
          (Fin.revPerm : Equiv.Perm (Fin (12 * s)))} : Set (SimpleGraph (Fin (12 * s)))) := by
        rw [← h2]; exact Or.inl rfl
      rcases h3 with h3 | h3
      · exact catOf_inj hs h3
      · exact absurd h3 (hne τ τ'))
  simpa [complementCount, Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin] using this

theorem main : Claim :=
  ⟨fun h => not_rational_of_fact (fun _ hs => class_ge hs) h,
   fun h => not_rational_of_fact (fun _ hs => pair_ge hs) h,
   fun h => not_rational_of_fact (fun _ hs => edgeSet_ge hs) h,
   fun h => not_rational_of_fact (fun _ hs => complement_ge hs) h⟩


end C3968
