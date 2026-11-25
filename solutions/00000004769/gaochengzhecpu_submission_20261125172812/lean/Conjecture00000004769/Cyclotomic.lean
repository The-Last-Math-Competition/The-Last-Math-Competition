/-
  Conjecture00000004769/Cyclotomic.lean
  First-principles construction and algebraic theory of cyclotomic polynomials `Phi_d(q)`
  in Core Lean 4.19.0:
    1. Constructive definition of `cyclotomic n` for all `n >= 1` over `Z[q]`.
    2. Complete proof of `q^n - 1 = prod_{d | n} Phi_d(q)` via integer Pseudo-Bezout
       identities (zero rationals, zero complex numbers, zero custom axioms).
    3. Self-reciprocality / palindromicity of `Phi_d(q)` for all `d >= 2` and all
       products of cyclotomic polynomials with `F(1) > 0`.
    4. Exact evaluation `Phi_d(1)` (0 at d=1, p at d=p^k, 1 otherwise) and the universal
       Prime-Divisor Degree & Cyclotomic-Order Lower Bounds.
-/

import Conjecture00000004769.Polynomial

namespace Conjecture00000004769

/-! ### 1. Elementary Number Theory & List Helpers -/

theorem int_ofNat_mul (a b : Nat) : Int.ofNat (a * b) = Int.ofNat a * Int.ofNat b :=
  Int.ofNat_mul a b

theorem int_ofNat_add (a b : Nat) : Int.ofNat (a + b) = Int.ofNat a + Int.ofNat b :=
  Int.ofNat_add a b

theorem nodup_append_of_disjoint {α : Type} {xs ys : List α}
    (hx : xs.Nodup) (hy : ys.Nodup) (hd : ∀ a ∈ xs, ∀ b ∈ ys, a ≠ b) :
    (xs ++ ys).Nodup := by
  induction xs with
  | nil => exact hy
  | cons x xs ih =>
    rw [List.cons_append]
    cases hx with
    | cons hnot hxs =>
      apply List.Pairwise.cons
      · intro z hz
        rw [List.mem_append] at hz
        rcases hz with hzx | hzy
        · exact fun heq => hnot z hzx (heq.symm ▸ rfl)
        · exact hd x (List.mem_cons.mpr (Or.inl rfl)) z hzy
      · exact ih hxs (fun a ha b hb => hd a (List.mem_cons.mpr (Or.inr ha)) b hb)

theorem nodup_map_of_inj {α β : Type} {f : α → β} {xs : List α}
    (hx : xs.Nodup) (hinj : ∀ a ∈ xs, ∀ b ∈ xs, f a = f b → a = b) :
    (xs.map f).Nodup := by
  induction xs with
  | nil => exact List.Pairwise.nil
  | cons x xs ih =>
    cases hx with
    | cons hnot hxs =>
      simp only [List.map]
      apply List.Pairwise.cons
      · intro y hy heq
        rw [List.mem_map] at hy
        rcases hy with ⟨z, hz, rfl⟩
        have hxz : x = z :=
          hinj x (List.mem_cons.mpr (Or.inl rfl)) z (List.mem_cons.mpr (Or.inr hz)) heq
        exact hnot z hz hxz
      · exact ih hxs (fun a ha b hb =>
          hinj a (List.mem_cons.mpr (Or.inr ha)) b (List.mem_cons.mpr (Or.inr hb)))

theorem nodup_filter_of_nodup {α : Type} (p : α → Bool) {xs : List α} (h : xs.Nodup) :
    (xs.filter p).Nodup := by
  induction xs with
  | nil => exact List.Pairwise.nil
  | cons x xs ih =>
    cases h with
    | cons hnot hxs =>
      dsimp only [List.filter]
      cases hp : p x
      · exact ih hxs
      · apply List.Pairwise.cons
        · intro y hy heq
          have hym : y ∈ xs := (List.mem_filter.mp hy).1
          exact hnot y hym heq
        · exact ih hxs

theorem filter_filter_eq {α : Type} (p q : α → Bool) (xs : List α) :
    (xs.filter q).filter p = xs.filter (fun x => p x && q x) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    cases hq : q x <;> cases hp : p x <;> simp [List.filter, hq, hp, ih]

def divisors (n : Nat) : List Nat :=
  ((List.range n).map (· + 1)).filter (fun d => n % d == 0)

def properDivisors (n : Nat) : List Nat :=
  ((List.range (n - 1)).map (· + 1)).filter (fun d => n % d == 0)

def divisorsGe2 (n : Nat) : List Nat :=
  (divisors n).filter (fun d => decide (2 ≤ d))

theorem mem_divisors_iff {n d : Nat} :
    d ∈ divisors n ↔ 1 ≤ d ∧ d ≤ n ∧ d ∣ n := by
  simp only [divisors, List.mem_filter, List.mem_map, List.mem_range, beq_iff_eq]
  constructor
  · rintro ⟨⟨i, hi, rfl⟩, hmod⟩
    exact ⟨by omega, by omega, Nat.dvd_of_mod_eq_zero hmod⟩
  · rintro ⟨hd1, hdn, hdvd⟩
    refine ⟨⟨d - 1, by omega, by omega⟩, Nat.mod_eq_zero_of_dvd hdvd⟩

theorem mem_properDivisors_iff {n d : Nat} :
    d ∈ properDivisors n ↔ 1 ≤ d ∧ d < n ∧ d ∣ n := by
  simp only [properDivisors, List.mem_filter, List.mem_map, List.mem_range, beq_iff_eq]
  constructor
  · rintro ⟨⟨i, hi, rfl⟩, hmod⟩
    exact ⟨by omega, by omega, Nat.dvd_of_mod_eq_zero hmod⟩
  · rintro ⟨hd1, hdn, hdvd⟩
    refine ⟨⟨d - 1, by omega, by omega⟩, Nat.mod_eq_zero_of_dvd hdvd⟩

theorem mem_divisorsGe2_iff {n d : Nat} :
    d ∈ divisorsGe2 n ↔ 2 ≤ d ∧ d ≤ n ∧ d ∣ n := by
  simp only [divisorsGe2, List.mem_filter, mem_divisors_iff, decide_eq_true_eq]
  constructor
  · rintro ⟨⟨_, hle, hdvd⟩, hd2⟩; exact ⟨hd2, hle, hdvd⟩
  · rintro ⟨hd2, hle, hdvd⟩; exact ⟨⟨by omega, hle, hdvd⟩, hd2⟩

theorem nodup_range_aux : ∀ (m : Nat), (List.range m).Nodup
  | 0 => List.Pairwise.nil
  | m + 1 => by
    rw [List.range_succ]
    apply nodup_append_of_disjoint (nodup_range_aux m)
      (List.Pairwise.cons (by simp) List.Pairwise.nil)
    intro a ha b hb
    simp only [List.mem_range] at ha
    simp only [List.mem_singleton] at hb
    omega

theorem nodup_map_add_one (m : Nat) : ((List.range m).map (· + 1)).Nodup := by
  apply nodup_map_of_inj (nodup_range_aux m)
  intro x _ y _ hxy; omega

theorem nodup_divisors (n : Nat) : (divisors n).Nodup :=
  nodup_filter_of_nodup _ (nodup_map_add_one n)

theorem nodup_properDivisors (n : Nat) : (properDivisors n).Nodup :=
  nodup_filter_of_nodup _ (nodup_map_add_one (n - 1))

theorem divisors_eq_proper_append (n : Nat) (hn : 1 ≤ n) :
    divisors n = properDivisors n ++ [n] := by
  unfold divisors properDivisors
  cases n with
  | zero => omega
  | succ m =>
    simp only [Nat.add_sub_cancel, List.range_succ, List.map_append, List.map,
               List.filter_append, List.filter, Nat.mod_self, beq_self_eq_true, cond_true]

theorem divisors_eq_one_cons_ge2 (n : Nat) (hn : 1 ≤ n) :
    divisors n = 1 :: divisorsGe2 n := by
  unfold divisorsGe2 divisors
  cases n with
  | zero => omega
  | succ m =>
    rw [List.range_succ_eq_map]
    have hd21 : decide (2 ≤ 1) = false := rfl
    simp only [List.map_cons, Nat.zero_add, List.filter, Nat.mod_one, beq_self_eq_true, hd21]
    congr 1
    have hmap : List.map (fun x => x + 1) (List.map Nat.succ (List.range m)) =
        List.map (fun x => x + 2) (List.range m) := by
      rw [List.map_map]
      apply List.map_congr_left
      intro x _; dsimp [Function.comp]
    rw [hmap]
    clear hmap
    induction (List.range m) with
    | nil => rfl
    | cons a as ih =>
      cases hmod : (m + 1) % (a + 2) == 0
      · dsimp only [List.map, List.filter]
        rw [hmod]
        exact ih
      · dsimp only [List.map, List.filter]
        rw [hmod]
        dsimp only [List.filter]
        have hge2 : decide (2 ≤ a + 2) = true := by simp
        rw [hge2]
        exact congrArg (List.cons (a + 2)) ih

theorem monicOfDeg_unique {p : Poly} {d1 d2 : Nat}
    (h1 : IsMonicOfDeg p d1) (h2 : IsMonicOfDeg p d2) : d1 = d2 := by
  by_cases hlt : d1 < d2
  · have hc0 := h1.2.2 d2 hlt
    rw [h2.2.1] at hc0; contradiction
  · by_cases hgt : d2 < d1
    · have hc0 := h2.2.2 d1 hgt
      rw [h1.2.1] at hc0; contradiction
    · omega

/-! ### 2. Polynomials `q^n - 1` and Geometric Sums `1 + q^d + ... + q^{(k-1)d}` -/

def qPowSubOne (n : Nat) : Poly :=
  sub (shift one n) one

def geomStep (d : Nat) : Nat → Poly
  | 0 => zero
  | k + 1 => add (geomStep d k) (shift one (d * k))

theorem trim_qPowSubOne (n : Nat) : trim (qPowSubOne n) = qPowSubOne n := trim_sub _ _

theorem trim_geomStep (d k : Nat) : trim (geomStep d k) = geomStep d k := by
  induction k with
  | zero => rfl
  | succ _ _ => exact trim_add _ _

theorem coeff_shift_one (n m : Nat) :
    coeff (shift one n) m = if m = n then 1 else 0 := by
  have h : shift one n = shift (constPoly 1) n := rfl
  rw [h, coeff_shift_const]

theorem eval_shift_one (s : Nat) (x : Int) : eval (shift one s) x = x ^ s := by
  rw [eval_eq_sumRange (shift one s) (s + 1) (fun k hk => by
    rw [coeff_shift_one]; exact if_neg (by omega : k ≠ s)) x]
  have hcongr : sumRange (s + 1) (fun k => coeff (shift one s) k * x ^ k) =
      sumRange (s + 1) (fun k => if k = s then x ^ s else 0) := by
    apply sumRange_congr
    intro k _
    rw [coeff_shift_one]
    split <;> simp [*]
  rw [hcongr, sumRange_single (Nat.lt_succ_self s)]

theorem eval_geomStep_one (d m : Nat) : eval (geomStep d m) 1 = Int.ofNat m := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [geomStep, eval_add, ih, eval_shift_one, int_one_pow, int_ofNat_add]
    rfl

theorem coeff_qPowSubOne {n : Nat} (hn : 1 ≤ n) (m : Nat) :
    coeff (qPowSubOne n) m = if m = n then 1 else if m = 0 then -1 else 0 := by
  rw [qPowSubOne, coeff_sub, coeff_shift_one, coeff_one]
  by_cases hmn : m = n
  · have hne0 : n ≠ 0 := by omega
    simp [hmn, hne0]
  · by_cases hm0 : m = 0
    · have h0n : 0 ≠ n := by omega
      simp [hm0, h0n]
    · simp [hmn, hm0]

theorem monic_qPowSubOne {n : Nat} (hn : 1 ≤ n) : IsMonicOfDeg (qPowSubOne n) n := by
  refine ⟨trim_qPowSubOne n, ?_, ?_⟩
  · rw [coeff_qPowSubOne hn, if_pos rfl]
  · intro k hk
    rw [coeff_qPowSubOne hn, if_neg (by omega : k ≠ n), if_neg (by omega : k ≠ 0)]

theorem monic_geomStep {d m : Nat} (hd : 1 ≤ d) (hm : 1 ≤ m) :
    IsMonicOfDeg (geomStep d m) (d * (m - 1)) := by
  induction m with
  | zero => omega
  | succ m ih =>
    cases m with
    | zero =>
      dsimp only [geomStep, Nat.mul_zero, Nat.sub_self]
      have h1 : add zero (shift one 0) = one := by
        apply poly_ext (trim_add _ _) trim_one
        intro k; rw [coeff_add, coeff_zero, coeff_shift_one, coeff_one]; omega
      rw [h1]
      exact ⟨trim_one, by simp [coeff_one], fun k hk => by rw [coeff_one, if_neg (by omega : k ≠ 0)]⟩
    | succ m' =>
      have ih' := ih (by omega)
      simp only [Nat.add_sub_cancel] at ih' ⊢
      refine ⟨trim_geomStep d (m' + 2), ?_, ?_⟩
      · rw [geomStep, coeff_add, coeff_shift_one, if_pos rfl]
        have hlt : d * m' < d * (m' + 1) := by rw [Nat.mul_succ]; omega
        rw [ih'.2.2 _ hlt, Int.zero_add]
      · intro k hk
        rw [geomStep, coeff_add, coeff_shift_one]
        have hlt : d * m' < k := by
          have : d * m' ≤ d * (m' + 1) := by rw [Nat.mul_succ]; omega
          omega
        rw [ih'.2.2 k hlt, if_neg (by omega : k ≠ d * (m' + 1)), Int.zero_add]

theorem mul_shift_one (p : Poly) (s : Nat) :
    mul p (shift one s) = shift p s := by
  rw [mul_comm]
  apply poly_ext (trim_mul _ _) (trim_shift p s)
  intro k
  have h1 : shift one s = shift (constPoly 1) s := rfl
  rw [h1, coeff_mul_shift_const, coeff_shift]
  by_cases hsk : s ≤ k
  · rw [if_pos hsk, if_neg (by omega : ¬(k < s)), Int.one_mul]
  · rw [if_neg hsk, if_pos (by omega : k < s)]

theorem shift_shift (p : Poly) (a b : Nat) :
    shift (shift p a) b = shift p (a + b) := by
  apply poly_ext (trim_shift _ _) (trim_shift _ _)
  intro k
  rw [coeff_shift, coeff_shift, coeff_shift]
  by_cases hkb : k < b
  · rw [if_pos hkb, if_pos (by omega : k < a + b)]
  · rw [if_neg hkb]
    by_cases hkab : k < a + b
    · rw [if_pos (by omega : k - b < a), if_pos hkab]
    · rw [if_neg (by omega : ¬(k - b < a)), if_neg hkab]
      have hsub : k - b - a = k - (a + b) := by omega
      rw [hsub]

theorem qPowSubOne_zero : qPowSubOne 0 = zero := by
  apply poly_ext (trim_qPowSubOne 0) trim_zero
  intro k
  rw [qPowSubOne, coeff_sub, coeff_shift_one, coeff_one, coeff_zero]
  by_cases hk0 : k = 0 <;> simp [hk0]

theorem mul_qPowSubOne_geomStep (d k : Nat) :
    mul (qPowSubOne d) (geomStep d k) = qPowSubOne (d * k) := by
  induction k with
  | zero =>
    simp only [geomStep, Nat.mul_zero, mul_zero_right, qPowSubOne_zero]
  | succ k ih =>
    simp only [geomStep, mul_add, ih]
    apply poly_ext (trim_add _ _) (trim_qPowSubOne _)
    intro m
    have hmul : mul (qPowSubOne d) (shift one (d * k)) =
        sub (shift one (d * (k + 1))) (shift one (d * k)) := by
      unfold qPowSubOne
      rw [mul_comm, mul_sub, mul_comm (shift one (d * k)) _,
          mul_shift_one, shift_shift,
          mul_one_right _ (trim_shift one (d * k))]
      have hd : d + d * k = d * (k + 1) := by rw [Nat.mul_succ, Nat.add_comm]
      rw [hd]
    rw [coeff_add, hmul, coeff_sub]
    unfold qPowSubOne
    rw [coeff_sub, coeff_sub]
    omega

theorem geomStep_pseudo_mod (d k : Nat) :
    ∃ s : Poly, add (geomStep d k) (mul s (qPowSubOne d)) = constPoly (Int.ofNat k) := by
  induction k with
  | zero =>
    refine ⟨zero, ?_⟩
    simp only [geomStep, zero_add_left _ (trim_mul _ _), mul_comm zero _, mul_zero_right]
    rfl
  | succ k ih =>
    rcases ih with ⟨s, hs⟩
    refine ⟨sub s (geomStep d k), ?_⟩
    have hpow : sub (shift one (d * k)) (mul (geomStep d k) (qPowSubOne d)) = one := by
      rw [mul_comm (geomStep d k) (qPowSubOne d), mul_qPowSubOne_geomStep]
      apply poly_ext (trim_sub _ _) trim_one
      intro m
      rw [coeff_sub]
      unfold qPowSubOne
      rw [coeff_sub]
      omega
    apply poly_ext (trim_add _ _) (trim_const _)
    intro m
    have hs_m := coeff_congr hs m
    have hp_m := coeff_congr hpow m
    have hsub_mul : mul (sub s (geomStep d k)) (qPowSubOne d) =
        sub (mul s (qPowSubOne d)) (mul (geomStep d k) (qPowSubOne d)) := by
      rw [mul_comm, mul_sub, mul_comm (qPowSubOne d) s, mul_comm (qPowSubOne d) _]
    simp only [geomStep, coeff_add, hsub_mul, coeff_sub] at hs_m hp_m ⊢
    rw [coeff_const] at hs_m ⊢
    rw [coeff_one] at hp_m
    by_cases hm0 : m = 0
    · rw [if_pos hm0] at hs_m hp_m ⊢
      rw [int_ofNat_add]
      have h1 : Int.ofNat 1 = (1 : Int) := rfl
      rw [h1]; omega
    · rw [if_neg hm0] at hs_m hp_m ⊢; omega

theorem qPowSubOne_add_split (a b : Nat) :
    qPowSubOne (a + b) = add (mul (shift one b) (qPowSubOne a)) (qPowSubOne b) := by
  apply poly_ext (trim_qPowSubOne _) (trim_add _ _)
  intro m
  have hmul : mul (shift one b) (qPowSubOne a) = sub (shift one (a + b)) (shift one b) := by
    unfold qPowSubOne
    rw [mul_sub, mul_comm (shift one b) (shift one a),
        mul_shift_one, shift_shift, mul_one_right _ (trim_shift one b)]
  rw [coeff_add, hmul, coeff_sub]
  unfold qPowSubOne
  rw [coeff_sub, coeff_sub]
  omega

/-- Polynomial Euclidean algorithm: `q^gcd(a,b) - 1` is a `Z[q]`-linear combination of `q^a - 1` and `q^b - 1`. -/
theorem qPowSubOne_bezout (a b : Nat) :
    ∃ u v : Poly, add (mul u (qPowSubOne a)) (mul v (qPowSubOne b)) = qPowSubOne (Nat.gcd a b) := by
  induction a using Nat.strongRecOn generalizing b with
  | ind a ih =>
    by_cases ha0 : a = 0
    · subst ha0
      rw [Nat.gcd_zero_left]
      refine ⟨zero, one, ?_⟩
      rw [mul_comm zero _, mul_zero_right, zero_add_left _ (trim_mul _ _),
          one_mul_left _ (trim_qPowSubOne b)]
    · have hapos : 0 < a := Nat.pos_of_ne_zero ha0
      have hmod_lt : b % a < a := Nat.mod_lt b hapos
      rcases ih (b % a) hmod_lt a with ⟨u', v', huv'⟩
      have hgcd : Nat.gcd a b = Nat.gcd (b % a) a := Nat.gcd_rec a b
      rw [hgcd]
      let q0 := b / a
      let r := b % a
      let K := mul (shift one r) (geomStep a q0)
      have hb_eq : b = a * q0 + r := (Nat.div_add_mod b a).symm
      have hstep : qPowSubOne b = add (mul K (qPowSubOne a)) (qPowSubOne r) := by
        dsimp only [K]
        conv => lhs; rw [hb_eq]
        rw [qPowSubOne_add_split (a * q0) r, ← mul_qPowSubOne_geomStep a q0,
            mul_comm (qPowSubOne a) (geomStep a q0), ← mul_assoc]
      have hr_eq : qPowSubOne r = sub (qPowSubOne b) (mul K (qPowSubOne a)) := by
        apply poly_ext (trim_qPowSubOne r) (trim_sub _ _)
        intro m
        have hm := coeff_congr hstep m
        rw [coeff_add] at hm
        rw [coeff_sub]; omega
      refine ⟨sub v' (mul u' K), u', ?_⟩
      apply poly_ext (trim_add _ _) (trim_qPowSubOne _)
      intro m
      have hm := coeff_congr huv' m
      have h1 : mul u' (qPowSubOne r) = sub (mul u' (qPowSubOne b)) (mul (mul u' K) (qPowSubOne a)) := by
        rw [hr_eq, mul_sub, ← mul_assoc u' K (qPowSubOne a)]
      have h2 : mul (sub v' (mul u' K)) (qPowSubOne a) =
          sub (mul v' (qPowSubOne a)) (mul (mul u' K) (qPowSubOne a)) := by
        rw [mul_comm, mul_sub, mul_comm (qPowSubOne a) v', mul_comm (qPowSubOne a) _]
      rw [h1] at hm
      rw [coeff_add, h2, coeff_sub]
      rw [coeff_add, coeff_sub] at hm
      omega

/-! ### 3. Pseudo-Coprimality & Pairwise Coprime Product Divisibility -/

def PseudoCoprime (f g : Poly) : Prop :=
  ∃ u v : Poly, ∃ m : Nat, 1 ≤ m ∧ add (mul u f) (mul v g) = constPoly (Int.ofNat m)

theorem pseudoCoprime_symm {f g : Poly} (h : PseudoCoprime f g) : PseudoCoprime g f := by
  rcases h with ⟨u, v, m, hm, heq⟩
  exact ⟨v, u, m, hm, by rw [add_comm, heq]⟩

theorem pseudoCoprime_of_factors {F G f g a b : Poly}
    (hFG : PseudoCoprime F G) (hF : F = mul a f) (hG : G = mul b g) :
    PseudoCoprime f g := by
  rcases hFG with ⟨u, v, m, hm, heq⟩
  refine ⟨mul u a, mul v b, m, hm, ?_⟩
  rw [mul_assoc, ← hF, mul_assoc, ← hG, heq]

theorem pseudoCoprime_mul_right {f g1 g2 : Poly}
    (h1 : PseudoCoprime f g1) (h2 : PseudoCoprime f g2) :
    PseudoCoprime f (mul g1 g2) := by
  rcases h1 with ⟨u1, v1, m1, hm1, heq1⟩
  rcases h2 with ⟨u2, v2, m2, hm2, heq2⟩
  refine ⟨add (mul u1 (constPoly (Int.ofNat m2))) (mul (mul v1 g1) u2),
          mul v1 v2, m1 * m2, Nat.mul_le_mul hm1 hm2, ?_⟩
  have hconst : mul (constPoly (Int.ofNat m1)) (constPoly (Int.ofNat m2)) =
      constPoly (Int.ofNat (m1 * m2)) := by
    apply poly_ext (trim_mul _ _) (trim_const _)
    intro k
    rw [coeff_mul, coeff_const]
    by_cases hk0 : k = 0
    · rw [hk0, if_pos rfl]
      dsimp only [sumRange]
      rw [Int.zero_add, Nat.sub_zero, coeff_const, coeff_const, if_pos rfl, if_pos rfl, int_ofNat_mul]
    · rw [if_neg hk0]
      rw [sumRange_congr (g := fun _ => 0)]
      · exact sumRange_zero _
      · intro i _
        by_cases hi0 : i = 0
        · rw [hi0, Nat.sub_zero, coeff_const, coeff_const, if_pos rfl, if_neg hk0, Int.mul_zero]
        · rw [coeff_const, if_neg hi0, Int.zero_mul]
  calc add (mul (add (mul u1 (constPoly (Int.ofNat m2))) (mul (mul v1 g1) u2)) f)
           (mul (mul v1 v2) (mul g1 g2))
    _ = add (add (mul (mul u1 (constPoly (Int.ofNat m2))) f) (mul (mul (mul v1 g1) u2) f))
            (mul (mul v1 v2) (mul g1 g2)) := by rw [add_mul]
    _ = add (mul (mul u1 f) (constPoly (Int.ofNat m2)))
            (add (mul (mul v1 g1) (mul u2 f)) (mul (mul v1 g1) (mul v2 g2))) := by
          have t1 : mul (mul u1 (constPoly (Int.ofNat m2))) f = mul (mul u1 f) (constPoly (Int.ofNat m2)) := by
            rw [mul_assoc, mul_comm (constPoly (Int.ofNat m2)) f, ← mul_assoc]
          have t2 : mul (mul (mul v1 g1) u2) f = mul (mul v1 g1) (mul u2 f) := mul_assoc _ _ _
          have t3 : mul (mul v1 v2) (mul g1 g2) = mul (mul v1 g1) (mul v2 g2) := by
            rw [mul_assoc v1 v2 (mul g1 g2), ← mul_assoc v2 g1 g2, mul_comm v2 g1,
                mul_assoc g1 v2 g2, ← mul_assoc]
          rw [t1, t2, t3, add_assoc]
    _ = add (mul (mul u1 f) (add (mul u2 f) (mul v2 g2)))
            (mul (mul v1 g1) (add (mul u2 f) (mul v2 g2))) := by rw [heq2, ← mul_add, heq2]
    _ = mul (add (mul u1 f) (mul v1 g1)) (add (mul u2 f) (mul v2 g2)) := (add_mul _ _ _).symm
    _ = mul (constPoly (Int.ofNat m1)) (constPoly (Int.ofNat m2)) := by rw [heq1, heq2]
    _ = constPoly (Int.ofNat (m1 * m2)) := hconst

theorem dvd_mul_of_pseudoCoprime {f g h : Poly} {df dg : Nat}
    (hf : IsMonicOfDeg f df) (hg : IsMonicOfDeg g dg) (hh : trim h = h)
    (hcop : PseudoCoprime f g)
    (hdvf : ∃ q1, trim q1 = q1 ∧ h = mul q1 f)
    (hdvg : ∃ q2, trim q2 = q2 ∧ h = mul q2 g) :
    ∃ q, trim q = q ∧ h = mul q (mul f g) := by
  rcases hcop with ⟨u, v, m, hm1, hbez⟩
  rcases hdvf with ⟨q1, _, hq1⟩
  rcases hdvg with ⟨q2, _, hq2⟩
  have hm0 : Int.ofNat m ≠ 0 := by
    intro hbad
    have : m = 0 := Int.ofNat.inj hbad
    omega
  have hscale : scale (Int.ofNat m) h = mul (add (mul u q2) (mul v q1)) (mul f g) := by
    have hcm : scale (Int.ofNat m) h = mul (constPoly (Int.ofNat m)) h := by
      have hsc : constPoly (Int.ofNat m) = scale (Int.ofNat m) one := by
        apply poly_ext (trim_const _) (trim_scale _ _)
        intro j; rw [coeff_const, coeff_scale, coeff_one]; split <;> simp
      rw [hsc, scale_mul_left, one_mul_left h hh]
    have p1 : mul (mul u f) h = mul (mul u q2) (mul f g) := by
      rw [hq2, mul_assoc u f (mul q2 g), ← mul_assoc f q2 g,
          mul_comm f q2, mul_assoc q2 f g, ← mul_assoc]
    have p2 : mul (mul v g) h = mul (mul v q1) (mul f g) := by
      rw [hq1, mul_assoc v g (mul q1 f), mul_comm q1 f, ← mul_assoc g f q1,
          mul_comm g f, mul_comm (mul f g) q1, ← mul_assoc v q1 (mul f g)]
    rw [hcm, ← hbez, add_mul, p1, p2, ← add_mul]
  have hfg : IsMonicOfDeg (mul f g) (df + dg) := mul_monicOfDeg hf hg
  have hdvd := dvd_of_scale_dvd hh hfg hm0 hscale
  exact ⟨monicDiv h (mul f g) (df + dg),
         (monicDiv_rem_spec h hfg).1,
         hdvd.2⟩

def sumNatList : List Nat → Nat
  | [] => 0
  | x :: xs => x + sumNatList xs

theorem pseudoCoprime_polyProd_list (d : Nat) (xs : List Nat) (F : Nat → Poly)
    (hcop : ∀ y ∈ xs, PseudoCoprime (F d) (F y)) :
    PseudoCoprime (F d) (polyProd xs F) := by
  induction xs with
  | nil =>
    refine ⟨zero, one, 1, Nat.le_refl 1, ?_⟩
    simp only [polyProd, mul_comm zero _, mul_zero_right, zero_add_left _ (trim_mul _ _),
               mul_one_right _ trim_one]
    rfl
  | cons x xs ih =>
    exact pseudoCoprime_mul_right
      (hcop x (List.mem_cons.mpr (Or.inl rfl)))
      (ih (fun y hy => hcop y (List.mem_cons.mpr (Or.inr hy))))

theorem polyProd_monic_and_dvd {ds : List Nat} (hnodup : ds.Nodup)
    (F : Nat → Poly) (degF : Nat → Nat) (h : Poly) (hh : trim h = h)
    (hmonic : ∀ d ∈ ds, IsMonicOfDeg (F d) (degF d))
    (hdvd : ∀ d ∈ ds, ∃ q, trim q = q ∧ h = mul q (F d))
    (hcop : ∀ d1 ∈ ds, ∀ d2 ∈ ds, d1 ≠ d2 → PseudoCoprime (F d1) (F d2)) :
    IsMonicOfDeg (polyProd ds F) (sumNatList (ds.map degF)) ∧
    (∃ q, trim q = q ∧ h = mul q (polyProd ds F)) := by
  induction ds with
  | nil =>
    simp only [polyProd, List.map, sumNatList]
    refine ⟨⟨trim_one, by simp [coeff_one], fun k hk => by rw [coeff_one, if_neg (by omega : k ≠ 0)]⟩,
            ⟨h, hh, (mul_one_right h hh).symm⟩⟩
  | cons d ds ih =>
    cases hnodup with
    | cons hd_not_mem hds_nodup =>
      have hih := ih hds_nodup
        (fun x hx => hmonic x (List.mem_cons.mpr (Or.inr hx)))
        (fun x hx => hdvd x (List.mem_cons.mpr (Or.inr hx)))
        (fun x hx y hy hne =>
          hcop x (List.mem_cons.mpr (Or.inr hx)) y (List.mem_cons.mpr (Or.inr hy)) hne)
      rcases hih with ⟨hprod_monic, hprod_dvd⟩
      have hd_monic := hmonic d (List.mem_cons.mpr (Or.inl rfl))
      have hd_dvd := hdvd d (List.mem_cons.mpr (Or.inl rfl))
      have hcop_prod : PseudoCoprime (F d) (polyProd ds F) :=
        pseudoCoprime_polyProd_list d ds F (fun y hy =>
          hcop d (List.mem_cons.mpr (Or.inl rfl)) y (List.mem_cons.mpr (Or.inr hy))
            (fun heq => hd_not_mem y hy heq))
      simp only [polyProd, List.map, sumNatList]
      exact ⟨mul_monicOfDeg hd_monic hprod_monic,
             dvd_mul_of_pseudoCoprime hd_monic hprod_monic hh hcop_prod hd_dvd hprod_dvd⟩

theorem polyProd_filter_split {α : Type} (xs : List α) (p : α → Bool) (F : α → Poly) :
    polyProd xs F = mul (polyProd (xs.filter p) F) (polyProd (xs.filter (fun x => !p x)) F) := by
  induction xs with
  | nil =>
    simp [polyProd, one_mul_left _ trim_one]
  | cons x xs ih =>
    simp only [List.filter, polyProd]
    cases hp : p x
    · simp only [Bool.not_false, cond_false, cond_true, polyProd]
      rw [ih, ← mul_assoc (F x), mul_comm (F x) (polyProd (List.filter p xs) F), mul_assoc]
    · simp only [Bool.not_true, cond_true, cond_false, polyProd]
      rw [ih, mul_assoc]

theorem filter_divisors_dvd {a b : Nat} (ha : 1 ≤ a) (hab : a ∣ b) (hb : 1 ≤ b) :
    (divisors b).filter (fun m => a % m == 0) = divisors a := by
  have hab_le : a ≤ b := Nat.le_of_dvd hb hab
  unfold divisors
  have hsplit : List.range b = List.range a ++ ((List.range (b - a)).map (fun x => a + x)) := by
    have : b = a + (b - a) := by omega
    conv => lhs; rw [this]
    exact List.range_add
  rw [hsplit, List.map_append, List.filter_append, List.filter_append, filter_filter_eq]
  have hleft : List.filter (fun m => (a % m == 0) && (b % m == 0))
        (List.map (· + 1) (List.range a)) =
      List.filter (fun d => a % d == 0) (List.map (· + 1) (List.range a)) := by
    apply List.filter_congr
    intro m _
    by_cases ham : a % m == 0
    · have hmdvd : m ∣ a := Nat.dvd_of_mod_eq_zero (beq_iff_eq.mp ham)
      have hmb : b % m == 0 := beq_iff_eq.mpr (Nat.mod_eq_zero_of_dvd (Nat.dvd_trans hmdvd hab))
      simp [ham, hmb]
    · simp [ham]
  have hright : List.filter (fun m => a % m == 0)
      (List.filter (fun d => b % d == 0)
        (List.map (· + 1) (List.map (fun x => a + x) (List.range (b - a))))) = [] := by
    rw [List.filter_eq_nil_iff]
    intro m hm
    have hm1 := (List.mem_filter.mp hm).1
    simp only [List.mem_map, List.mem_range] at hm1
    rcases hm1 with ⟨y, ⟨x, _, rfl⟩, rfl⟩
    rw [beq_iff_eq]
    intro hmod
    have hdvd : a + x + 1 ∣ a := Nat.dvd_of_mod_eq_zero hmod
    have hle : a + x + 1 ≤ a := Nat.le_of_dvd ha hdvd
    omega
  rw [hleft, hright, List.append_nil]

theorem mem_polyProd_dvd {α : Type} [DecidableEq α] {x : α} {xs : List α} (hx : x ∈ xs)
    (F : α → Poly) :
    ∃ q, trim q = q ∧ polyProd xs F = mul q (F x) := by
  induction xs with
  | nil => contradiction
  | cons y ys ih =>
    rcases List.mem_cons.mp hx with rfl | hmem
    · refine ⟨polyProd ys F, trim_polyProd ys F, ?_⟩
      simp [polyProd, mul_comm]
    · rcases ih hmem with ⟨q, _, heq⟩
      refine ⟨mul (F y) q, trim_mul _ _, ?_⟩
      simp only [polyProd, heq, mul_assoc]

/-! ### 4. Constructive Definition of `cyclotomic` & Master Factorization Theorem -/

def cycloDeg (n : Nat) : Nat :=
  if n = 0 then 0
  else
    have : ∀ d ∈ properDivisors n, d < n := fun d hd => (mem_properDivisors_iff.mp hd).2.1
    n - sumNatList ((properDivisors n).attach.map (fun ⟨d, _⟩ => cycloDeg d))
termination_by n
decreasing_by exact this d ‹_›

def cyclotomic (n : Nat) : Poly :=
  if n = 0 then one
  else
    have : ∀ d ∈ properDivisors n, d < n := fun d hd => (mem_properDivisors_iff.mp hd).2.1
    let properProd := polyProd (properDivisors n).attach (fun ⟨d, _⟩ => cyclotomic d)
    let degProper := sumNatList ((properDivisors n).attach.map (fun ⟨d, _⟩ => cycloDeg d))
    monicDiv (qPowSubOne n) properProd degProper
termination_by n
decreasing_by exact this d ‹_›

theorem polyProd_attach (xs : List α) (f : α → Poly) :
    polyProd xs.attach (fun ⟨x, _⟩ => f x) = polyProd xs f := by
  suffices h : ∀ (ys : List α) (hy : ∀ y ∈ ys, y ∈ xs),
      polyProd (ys.pmap Subtype.mk hy) (fun ⟨x, _⟩ => f x) = polyProd ys f from
    h xs (fun _ hx => hx)
  intro ys
  induction ys with
  | nil => intro _; rfl
  | cons y ys ih =>
    intro hy
    simp only [List.pmap, polyProd]
    rw [ih]

theorem map_attach_eq (xs : List α) (f : α → β) :
    xs.attach.map (fun ⟨x, _⟩ => f x) = xs.map f := by
  suffices h : ∀ (ys : List α) (hy : ∀ y ∈ ys, y ∈ xs),
      (ys.pmap Subtype.mk hy).map (fun ⟨x, _⟩ => f x) = ys.map f from
    h xs (fun _ hx => hx)
  intro ys
  induction ys with
  | nil => intro _; rfl
  | cons y ys ih =>
    intro hy
    simp only [List.pmap, List.map]
    rw [ih]

theorem cycloDeg_def {n : Nat} (hn : 1 ≤ n) :
    cycloDeg n = n - sumNatList ((properDivisors n).map cycloDeg) := by
  conv => lhs; unfold cycloDeg
  have hne : n ≠ 0 := by omega
  simp [hne, map_attach_eq]

theorem cyclotomic_def {n : Nat} (hn : 1 ≤ n) :
    cyclotomic n = monicDiv (qPowSubOne n)
      (polyProd (properDivisors n) cyclotomic)
      (sumNatList ((properDivisors n).map cycloDeg)) := by
  conv => lhs; unfold cyclotomic
  have hne : n ≠ 0 := by omega
  simp [hne, polyProd_attach, map_attach_eq]

theorem polyProd_singleton (d : Nat) (F : Nat → Poly) (hT : trim (F d) = F d) :
    polyProd [d] F = F d := by
  dsimp only [polyProd]
  exact mul_one_right (F d) hT

/-- Master strong-induction theorem: every `cyclotomic n` (`n >= 1`) is monic of degree `cycloDeg n`
    and satisfies `q^n - 1 = prod_{d | n} cyclotomic d` in `Z[q]`. -/
theorem cyclotomic_spec (n : Nat) (hn : 1 ≤ n) :
    IsMonicOfDeg (cyclotomic n) (cycloDeg n) ∧
    qPowSubOne n = polyProd (divisors n) cyclotomic := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    have hgeom_quot : ∀ a b, 1 ≤ a → a < b → b < n → a ∣ b →
        geomStep a (b / a) =
          polyProd ((divisors b).filter (fun m => !(a % m == 0))) cyclotomic := by
      intro a b ha hab hbn hdvd
      have hb1 : 1 ≤ b := by omega
      have hba : a * (b / a) = b := Nat.mul_div_cancel' hdvd
      have lhs_eq : mul (qPowSubOne a) (geomStep a (b / a)) = qPowSubOne b := by
        rw [mul_qPowSubOne_geomStep, hba]
      have rhs_eq : qPowSubOne b =
          mul (qPowSubOne a) (polyProd ((divisors b).filter (fun m => !(a % m == 0))) cyclotomic) := by
        rw [(ih b hbn hb1).2, polyProd_filter_split (divisors b) (fun m => a % m == 0) cyclotomic,
            filter_divisors_dvd ha hdvd hb1, ← (ih a (by omega) ha).2]
      rw [rhs_eq] at lhs_eq
      exact mul_monic_cancel_left (monic_qPowSubOne ha)
        (trim_geomStep _ _) (trim_polyProd _ _) lhs_eq

    have hcop_lt : ∀ d1 d2, 1 ≤ d1 → d1 < n → 1 ≤ d2 → d2 < n → d1 ≠ d2 →
        PseudoCoprime (cyclotomic d1) (cyclotomic d2) := by
      intro d1 d2 hd1_pos hd1_lt hd2_pos hd2_lt hne
      let g := Nat.gcd d1 d2
      have hg_dvd1 : g ∣ d1 := Nat.gcd_dvd_left d1 d2
      have hg_dvd2 : g ∣ d2 := Nat.gcd_dvd_right d1 d2
      have hg_pos : 1 ≤ g := by
        have h0 : g ≠ 0 := by
          intro hg0
          have : d1 = 0 := Nat.eq_zero_of_zero_dvd (hg0 ▸ hg_dvd1)
          omega
        omega
      have hg_le1 : g ≤ d1 := Nat.le_of_dvd hd1_pos hg_dvd1
      have hg_le2 : g ≤ d2 := Nat.le_of_dvd hd2_pos hg_dvd2
      by_cases hgd1 : g = d1
      · have hd1_dvd2 : d1 ∣ d2 := hgd1 ▸ hg_dvd2
        have hd1_lt_d2 : d1 < d2 := by omega
        let k := d2 / d1
        have hk_ge1 : 1 ≤ k := by
          have hk_mul : d1 * k = d2 := Nat.mul_div_cancel' hd1_dvd2
          by_cases hk0 : k = 0
          · have hmul0 : d1 * 0 = d2 := hk0 ▸ hk_mul
            simp at hmul0; omega
          · exact Nat.pos_of_ne_zero hk0
        rcases geomStep_pseudo_mod d1 k with ⟨s, hs⟩
        have hF1 : ∃ q1, trim q1 = q1 ∧ qPowSubOne d1 = mul q1 (cyclotomic d1) := by
          rw [(ih d1 hd1_lt hd1_pos).2]
          exact mem_polyProd_dvd (mem_divisors_iff.mpr ⟨hd1_pos, Nat.le_refl d1, Nat.dvd_refl d1⟩)
            cyclotomic
        have hF2 : ∃ q2, trim q2 = q2 ∧ geomStep d1 k = mul q2 (cyclotomic d2) := by
          rw [hgeom_quot d1 d2 hd1_pos hd1_lt_d2 hd2_lt hd1_dvd2]
          have hmem : d2 ∈ (divisors d2).filter (fun m => !(d1 % m == 0)) := by
            rw [List.mem_filter]
            refine ⟨mem_divisors_iff.mpr ⟨hd2_pos, Nat.le_refl d2, Nat.dvd_refl d2⟩, ?_⟩
            have hnot : ¬(d1 % d2 = 0) := by
              intro hmod
              have : d2 ≤ d1 := Nat.le_of_dvd hd1_pos (Nat.dvd_of_mod_eq_zero hmod)
              omega
            simp [hnot]
          exact mem_polyProd_dvd hmem cyclotomic
        rcases hF1 with ⟨q1, _, hq1⟩
        rcases hF2 with ⟨q2, _, hq2⟩
        apply pseudoCoprime_symm
        exact pseudoCoprime_of_factors ⟨one, s, k, hk_ge1, by
          rw [one_mul_left _ (trim_geomStep d1 k), hs]⟩ hq2 hq1
      · by_cases hgd2 : g = d2
        · have hd2_dvd1 : d2 ∣ d1 := hgd2 ▸ hg_dvd1
          have hd2_lt_d1 : d2 < d1 := by omega
          let k := d1 / d2
          have hk_ge1 : 1 ≤ k := by
            have hk_mul : d2 * k = d1 := Nat.mul_div_cancel' hd2_dvd1
            by_cases hk0 : k = 0
            · have hmul0 : d2 * 0 = d1 := hk0 ▸ hk_mul
              simp at hmul0; omega
            · exact Nat.pos_of_ne_zero hk0
          rcases geomStep_pseudo_mod d2 k with ⟨s, hs⟩
          have hF2 : ∃ q2, trim q2 = q2 ∧ qPowSubOne d2 = mul q2 (cyclotomic d2) := by
            rw [(ih d2 hd2_lt hd2_pos).2]
            exact mem_polyProd_dvd (mem_divisors_iff.mpr ⟨hd2_pos, Nat.le_refl d2, Nat.dvd_refl d2⟩)
              cyclotomic
          have hF1 : ∃ q1, trim q1 = q1 ∧ geomStep d2 k = mul q1 (cyclotomic d1) := by
            rw [hgeom_quot d2 d1 hd2_pos hd2_lt_d1 hd1_lt hd2_dvd1]
            have hmem : d1 ∈ (divisors d1).filter (fun m => !(d2 % m == 0)) := by
              rw [List.mem_filter]
              refine ⟨mem_divisors_iff.mpr ⟨hd1_pos, Nat.le_refl d1, Nat.dvd_refl d1⟩, ?_⟩
              have hnot : ¬(d2 % d1 = 0) := by
                intro hmod
                have : d1 ≤ d2 := Nat.le_of_dvd hd2_pos (Nat.dvd_of_mod_eq_zero hmod)
                omega
              simp [hnot]
            exact mem_polyProd_dvd hmem cyclotomic
          rcases hF1 with ⟨q1, _, hq1⟩
          rcases hF2 with ⟨q2, _, hq2⟩
          exact pseudoCoprime_of_factors ⟨one, s, k, hk_ge1, by
            rw [one_mul_left _ (trim_geomStep d2 k), hs]⟩ hq1 hq2
        · have hg_lt1 : g < d1 := by omega
          have hg_lt2 : g < d2 := by omega
          rcases qPowSubOne_bezout d1 d2 with ⟨U, V, hUV⟩
          have hd1_g : qPowSubOne d1 = mul (qPowSubOne g) (geomStep g (d1 / g)) := by
            rw [mul_qPowSubOne_geomStep, Nat.mul_div_cancel' hg_dvd1]
          have hd2_g : qPowSubOne d2 = mul (qPowSubOne g) (geomStep g (d2 / g)) := by
            rw [mul_qPowSubOne_geomStep, Nat.mul_div_cancel' hg_dvd2]
          have hfactor : mul (qPowSubOne g)
              (add (mul U (geomStep g (d1 / g))) (mul V (geomStep g (d2 / g)))) =
              mul (qPowSubOne g) one := by
            rw [mul_one_right _ (trim_qPowSubOne g), mul_add,
                ← mul_assoc (qPowSubOne g) U _, mul_comm (qPowSubOne g) U, mul_assoc U _ _, ← hd1_g,
                ← mul_assoc (qPowSubOne g) V _, mul_comm (qPowSubOne g) V, mul_assoc V _ _, ← hd2_g,
                hUV]
          have hunit : add (mul U (geomStep g (d1 / g))) (mul V (geomStep g (d2 / g))) = one :=
            mul_monic_cancel_left (monic_qPowSubOne hg_pos) (trim_add _ _) trim_one hfactor
          have hF1 : ∃ q1, trim q1 = q1 ∧ geomStep g (d1 / g) = mul q1 (cyclotomic d1) := by
            rw [hgeom_quot g d1 hg_pos hg_lt1 hd1_lt hg_dvd1]
            have hmem : d1 ∈ (divisors d1).filter (fun m => !(g % m == 0)) := by
              rw [List.mem_filter]
              refine ⟨mem_divisors_iff.mpr ⟨hd1_pos, Nat.le_refl d1, Nat.dvd_refl d1⟩, ?_⟩
              have hnot : ¬(g % d1 = 0) := by
                intro hmod
                have : d1 ≤ g := Nat.le_of_dvd hg_pos (Nat.dvd_of_mod_eq_zero hmod)
                omega
              simp [hnot]
            exact mem_polyProd_dvd hmem cyclotomic
          have hF2 : ∃ q2, trim q2 = q2 ∧ geomStep g (d2 / g) = mul q2 (cyclotomic d2) := by
            rw [hgeom_quot g d2 hg_pos hg_lt2 hd2_lt hg_dvd2]
            have hmem : d2 ∈ (divisors d2).filter (fun m => !(g % m == 0)) := by
              rw [List.mem_filter]
              refine ⟨mem_divisors_iff.mpr ⟨hd2_pos, Nat.le_refl d2, Nat.dvd_refl d2⟩, ?_⟩
              have hnot : ¬(g % d2 = 0) := by
                intro hmod
                have : d2 ≤ g := Nat.le_of_dvd hg_pos (Nat.dvd_of_mod_eq_zero hmod)
                omega
              simp [hnot]
            exact mem_polyProd_dvd hmem cyclotomic
          rcases hF1 with ⟨q1, _, hq1⟩
          rcases hF2 with ⟨q2, _, hq2⟩
          exact pseudoCoprime_of_factors ⟨U, V, 1, Nat.le_refl 1, hunit⟩ hq1 hq2

    have hdvd_each : ∀ d ∈ properDivisors n, ∃ q, trim q = q ∧ qPowSubOne n = mul q (cyclotomic d) := by
      intro d hd
      rcases mem_properDivisors_iff.mp hd with ⟨hd1, hdn, hdvd⟩
      have hn_eq : qPowSubOne n = mul (qPowSubOne d) (geomStep d (n / d)) := by
        rw [mul_qPowSubOne_geomStep, Nat.mul_div_cancel' hdvd]
      have hd_factor : ∃ q0, trim q0 = q0 ∧ qPowSubOne d = mul q0 (cyclotomic d) := by
        rw [(ih d hdn hd1).2]
        exact mem_polyProd_dvd (mem_divisors_iff.mpr ⟨hd1, Nat.le_refl d, Nat.dvd_refl d⟩) cyclotomic
      rcases hd_factor with ⟨q0, _, hq0⟩
      refine ⟨mul (geomStep d (n / d)) q0, trim_mul _ _, ?_⟩
      rw [hn_eq, hq0, mul_comm (mul q0 (cyclotomic d)) _, mul_assoc]

    have hprop := polyProd_monic_and_dvd (nodup_properDivisors n) cyclotomic cycloDeg
      (qPowSubOne n) (trim_qPowSubOne n)
      (fun d hd => by
        rcases mem_properDivisors_iff.mp hd with ⟨hd1, hdn, _⟩
        exact (ih d hdn hd1).1)
      hdvd_each
      (fun d1 hd1 d2 hd2 hne => by
        rcases mem_properDivisors_iff.mp hd1 with ⟨h1p, h1lt, _⟩
        rcases mem_properDivisors_iff.mp hd2 with ⟨h2p, h2lt, _⟩
        exact hcop_lt d1 d2 h1p h1lt h2p h2lt hne)

    rcases hprop with ⟨hP_monic, ⟨Q, hQ_trim, hQ_eq⟩⟩
    let P := polyProd (properDivisors n) cyclotomic
    let dp := sumNatList ((properDivisors n).map cycloDeg)
    have hQP_eq : qPowSubOne n = mul Q P := hQ_eq
    have hscale1 : scale 1 (qPowSubOne n) = mul Q P := by
      have hs1 : scale 1 (qPowSubOne n) = qPowSubOne n := by
        apply poly_ext (trim_scale _ _) (trim_qPowSubOne n)
        intro k; rw [coeff_scale, Int.one_mul]
      rw [hs1, hQP_eq]
    have hdvd1 := dvd_of_scale_dvd (trim_qPowSubOne n) hP_monic (by decide) hscale1
    have hQ_cyc : Q = cyclotomic n := by
      rw [cyclotomic_def hn]
      exact mul_monic_cancel_left hP_monic hQ_trim
        (monicDiv_rem_spec (qPowSubOne n) hP_monic).1
        (by rw [mul_comm P Q, ← hQP_eq, mul_comm P _, ← hdvd1.2])
    have hQ_ne0 : Q ≠ zero := by
      intro h0
      rw [h0, mul_comm zero P, mul_zero_right] at hQP_eq
      have h1 : coeff (qPowSubOne n) n = 1 := (monic_qPowSubOne hn).2.1
      rw [hQP_eq, coeff_zero] at h1
      contradiction
    rcases exists_top_deg hQ_trim hQ_ne0 with ⟨dq, hdq0, hdq_top⟩
    have htop_prod : coeff (mul Q P) (dq + dp) = coeff Q dq := by
      rw [coeff_mul_rect hdq_top hP_monic.2.2 (dq + dp)]
      have hlt1 : dq < dq + 1 := Nat.lt_succ_self dq
      have hlt2 : dp < dp + 1 := Nat.lt_succ_self dp
      have h1 : sumRange (dq + 1) (fun i =>
            sumRange (dp + 1) (fun j => if i + j = dq + dp then coeff Q i * coeff P j else 0)) =
          sumRange (dq + 1) (fun i => if i = dq then coeff Q dq * coeff P dp else 0) := by
        apply sumRange_congr
        intro i hi
        by_cases hid : i = dq
        · rw [hid, if_pos rfl]
          have h2 : sumRange (dp + 1) (fun j => if dq + j = dq + dp then coeff Q dq * coeff P j else 0) =
              sumRange (dp + 1) (fun j => if j = dp then coeff Q dq * coeff P dp else 0) := by
            apply sumRange_congr
            intro j _
            by_cases hjd : j = dp
            · rw [hjd, if_pos rfl, if_pos rfl]
            · rw [if_neg (by omega : dq + j ≠ dq + dp), if_neg hjd]
          rw [h2, sumRange_single hlt2]
        · rw [if_neg hid]
          rw [sumRange_congr (g := fun _ => 0)]
          · exact sumRange_zero _
          · intro j hj; exact if_neg (by omega : i + j ≠ dq + dp)
      rw [h1, sumRange_single hlt1, hP_monic.2.1, Int.mul_one]
    have hdq_dp_eq_n : dq + dp = n := by
      by_cases hgt : n < dq + dp
      · have h0 : coeff (qPowSubOne n) (dq + dp) = 0 := (monic_qPowSubOne hn).2.2 _ hgt
        rw [hQP_eq, htop_prod] at h0
        exact False.elim (hdq0 h0)
      · by_cases hlt : dq + dp < n
        · have h0 : coeff (mul Q P) n = 0 := by
            rw [coeff_mul_rect hdq_top hP_monic.2.2 n]
            rw [sumRange_congr (g := fun _ => 0)]
            · exact sumRange_zero _
            · intro i hi
              rw [sumRange_congr (g := fun _ => 0)]
              · exact sumRange_zero _
              · intro j hj; exact if_neg (by omega : i + j ≠ n)
          rw [← hQP_eq, (monic_qPowSubOne hn).2.1] at h0
          contradiction
        · omega
    have hQ_lc1 : coeff Q dq = 1 := by
      have h1 : coeff (qPowSubOne n) (dq + dp) = 1 := by
        rw [hdq_dp_eq_n]; exact (monic_qPowSubOne hn).2.1
      rw [hQP_eq, htop_prod] at h1
      exact h1
    have hdq_eq : dq = cycloDeg n := by
      rw [cycloDeg_def hn]
      change dq = n - dp
      omega
    have hQ_monic : IsMonicOfDeg (cyclotomic n) (cycloDeg n) := by
      rw [← hQ_cyc, ← hdq_eq]
      exact ⟨hQ_trim, hQ_lc1, hdq_top⟩
    refine ⟨hQ_monic, ?_⟩
    rw [divisors_eq_proper_append n hn, polyProd_append,
        polyProd_singleton n cyclotomic hQ_monic.1, ← hQ_cyc, mul_comm P Q, ← hQP_eq]

theorem cyclotomic_one_eq : cyclotomic 1 = qPowSubOne 1 := by
  have h := (cyclotomic_spec 1 (Nat.le_refl 1)).2
  have hdiv : divisors 1 = [1] := rfl
  rw [hdiv, polyProd_singleton 1 cyclotomic (cyclotomic_spec 1 (Nat.le_refl 1)).1.1] at h
  exact h.symm

theorem eval_cyclotomic_one_at_1 : eval (cyclotomic 1) 1 = 0 := by
  rw [cyclotomic_one_eq]; rfl

theorem geomStep_one_eq_polyProd_ge2 {n : Nat} (hn : 1 ≤ n) :
    geomStep 1 n = polyProd (divisorsGe2 n) cyclotomic := by
  have h1 : mul (qPowSubOne 1) (geomStep 1 n) = qPowSubOne n := by
    have := mul_qPowSubOne_geomStep 1 n
    simpa using this
  have h2 : qPowSubOne n = mul (qPowSubOne 1) (polyProd (divisorsGe2 n) cyclotomic) := by
    rw [(cyclotomic_spec n hn).2, divisors_eq_one_cons_ge2 n hn, polyProd, cyclotomic_one_eq]
  rw [h2] at h1
  exact mul_monic_cancel_left (monic_qPowSubOne (Nat.le_refl 1))
    (trim_geomStep 1 n) (trim_polyProd _ _) h1

/-! ### 5. Palindromicity of All Cyclotomic Polynomials `d >= 2` -/

theorem coeff_geomStep_one (n k : Nat) :
    coeff (geomStep 1 n) k = if k < n then 1 else 0 := by
  induction n with
  | zero => simp [geomStep, coeff_zero]
  | succ n ih =>
    simp only [geomStep, Nat.one_mul, coeff_add, ih, coeff_shift_one]
    by_cases hkn : k < n
    · rw [if_pos hkn, if_neg (by omega : k ≠ n), if_pos (by omega : k < n + 1)]; rfl
    · rw [if_neg hkn]
      by_cases hkeq : k = n
      · rw [hkeq, if_pos rfl, if_pos (Nat.lt_succ_self n)]; rfl
      · rw [if_neg hkeq, if_neg (by omega : ¬(k < n + 1))]; rfl

theorem palindromic_geomStep_one {n : Nat} (hn : 1 ≤ n) :
    IsPalindromicOfDeg (geomStep 1 n) (n - 1) := by
  refine ⟨⟨trim_geomStep 1 n, ?_, ?_⟩, ?_, ?_⟩
  · rw [coeff_geomStep_one, if_pos (by omega : n - 1 < n)]
  · intro k hk; rw [coeff_geomStep_one, if_neg (by omega : ¬(k < n))]
  · rw [coeff_geomStep_one, if_pos (by omega : 0 < n)]
  · intro k hk
    rw [coeff_geomStep_one, coeff_geomStep_one,
        if_pos (by omega : k < n), if_pos (by omega : n - 1 - k < n)]

theorem polyProd_palindromic (ds : List Nat) (F : Nat → Poly) (degF : Nat → Nat)
    (hpal : ∀ d ∈ ds, IsPalindromicOfDeg (F d) (degF d)) :
    IsPalindromicOfDeg (polyProd ds F) (sumNatList (ds.map degF)) := by
  induction ds with
  | nil =>
    simp only [polyProd, List.map, sumNatList]
    refine ⟨⟨trim_one, rfl, fun k hk => by rw [coeff_one, if_neg (by omega : k ≠ 0)]⟩,
            rfl, ?_⟩
    intro k hk
    have hk0 : k = 0 := by omega
    rw [hk0]
  | cons d ds ih =>
    simp only [polyProd, List.map, sumNatList]
    exact mul_palindromic (hpal d (List.mem_cons.mpr (Or.inl rfl)))
      (ih (fun x hx => hpal x (List.mem_cons.mpr (Or.inr hx))))

theorem divisorsGe2_eq_properGe2_append {n : Nat} (hn : 2 ≤ n) :
    divisorsGe2 n = ((properDivisors n).filter (fun d => decide (2 ≤ d))) ++ [n] := by
  unfold divisorsGe2
  rw [divisors_eq_proper_append n (by omega), List.filter_append]
  have hn2 : decide (2 ≤ n) = true := by simp [hn]
  simp [List.filter, hn2]

theorem cyclotomic_palindromic (d : Nat) (hd : 2 ≤ d) :
    IsPalindromicOfDeg (cyclotomic d) (cycloDeg d) := by
  induction d using Nat.strongRecOn with
  | ind d ih =>
    let propGe2 := (properDivisors d).filter (fun m => decide (2 ≤ m))
    have hP_pal : IsPalindromicOfDeg (polyProd propGe2 cyclotomic) (sumNatList (propGe2.map cycloDeg)) := by
      apply polyProd_palindromic
      intro m hm
      rw [List.mem_filter, decide_eq_true_eq] at hm
      have hlt : m < d := (mem_properDivisors_iff.mp hm.1).2.1
      exact ih m hlt hm.2
    have hd_monic := (cyclotomic_spec d (by omega)).1
    have hprod : geomStep 1 d = mul (polyProd propGe2 cyclotomic) (cyclotomic d) := by
      rw [geomStep_one_eq_polyProd_ge2 (by omega), divisorsGe2_eq_properGe2_append hd,
          polyProd_append, polyProd_singleton d cyclotomic hd_monic.1]
    have hdeg_sum : sumNatList (propGe2.map cycloDeg) + cycloDeg d = d - 1 := by
      have hm1 := mul_monicOfDeg hP_pal.1 hd_monic
      rw [← hprod] at hm1
      exact monicOfDeg_unique hm1 (palindromic_geomStep_one (by omega)).1
    have hgeom_pal : IsPalindromicOfDeg
        (mul (polyProd propGe2 cyclotomic) (cyclotomic d))
        (sumNatList (propGe2.map cycloDeg) + cycloDeg d) := by
      rw [← hprod, hdeg_sum]
      exact palindromic_geomStep_one (by omega)
    exact palindromic_right_of_mul hP_pal hd_monic hgeom_pal

/-! ### 6. Exact Evaluation `Phi_d(1)` & Prime-Divisor Degree / Order Bounds -/

def IsPrimeNat (p : Nat) : Prop :=
  2 ≤ p ∧ ∀ d, d ∣ p → d = 1 ∨ d = p

def IsPrimePowNat (n : Nat) : Prop :=
  ∃ p k : Nat, IsPrimeNat p ∧ 1 ≤ k ∧ n = p ^ k

theorem exists_prime_dvd {n : Nat} (hn : 2 ≤ n) : ∃ p, IsPrimeNat p ∧ p ∣ n := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    by_cases hprime : ∀ d, d ∣ n → d = 1 ∨ d = n
    · exact ⟨n, ⟨hn, hprime⟩, Nat.dvd_refl n⟩
    · have hex : ∃ d, 2 ≤ d ∧ d < n ∧ d ∣ n := by
        apply Classical.byContradiction
        intro hnone
        apply hprime
        intro d hdvd
        have hd_pos : 1 ≤ d := by
          by_cases hd0 : d = 0
          · subst hd0; have : n = 0 := Nat.eq_zero_of_zero_dvd hdvd; omega
          · omega
        have hd_le : d ≤ n := Nat.le_of_dvd (by omega) hdvd
        by_cases hd1 : d = 1
        · exact Or.inl hd1
        · by_cases hdn : d = n
          · exact Or.inr hdn
          · exfalso; exact hnone ⟨d, by omega, by omega, hdvd⟩
      rcases hex with ⟨d, hd2, hdn, hdvd⟩
      rcases ih d hdn hd2 with ⟨p, hp, hpd⟩
      exact ⟨p, hp, Nat.dvd_trans hpd hdvd⟩

theorem nat_bezout (u v : Nat) :
    ∃ s t : Int, s * (u : Int) + t * (v : Int) = ((Nat.gcd u v : Nat) : Int) := by
  induction u using Nat.strongRecOn generalizing v with
  | ind u ihu =>
    by_cases hu0 : u = 0
    · subst hu0; rw [Nat.gcd_zero_left]; exact ⟨0, 1, by simp⟩
    · rcases ihu (v % u) (Nat.mod_lt v (by omega)) u with ⟨s', t', hst'⟩
      rw [Nat.gcd_rec u v, ← hst']
      have hv_eq : ((v % u : Nat) : Int) = (v : Int) - (u : Int) * ((v / u : Nat) : Int) := by
        have hd : u * (v / u) + v % u = v := Nat.div_add_mod v u
        have hd_int : ((u * (v / u) + v % u : Nat) : Int) = (v : Int) := congrArg Nat.cast hd
        rw [Int.ofNat_add, Int.ofNat_mul] at hd_int
        omega
      refine ⟨t' - s' * ((v / u : Nat) : Int), s', ?_⟩
      rw [hv_eq, Int.sub_mul, Int.mul_sub]
      have hmul : s' * ((u : Int) * ((v / u : Nat) : Int)) =
          s' * ((v / u : Nat) : Int) * (u : Int) := by
        rw [← Int.mul_assoc, Int.mul_right_comm]
      omega

theorem coprime_dvd_of_dvd_mul {x y b : Nat} (hx : 1 ≤ x)
    (hgcd : Nat.gcd x y = 1) (hdvd : x ∣ y * b) : x ∣ b := by
  rcases nat_bezout x y with ⟨s, t, hst⟩
  rw [hgcd] at hst
  rcases hdvd with ⟨k, hk⟩
  have h2 : (y : Int) * (b : Int) = (x : Int) * (k : Int) := by
    have hc : ((y * b : Nat) : Int) = ((x * k : Nat) : Int) := congrArg Nat.cast hk
    rw [Int.ofNat_mul, Int.ofNat_mul] at hc
    exact hc
  let w := s * (b : Int) + t * (k : Int)
  have hb_int : (b : Int) = (x : Int) * w := by
    dsimp only [w]
    calc (b : Int) = 1 * (b : Int) := (Int.one_mul _).symm
      _ = (s * (x : Int) + t * (y : Int)) * (b : Int) := by rw [hst]; rfl
      _ = s * (x : Int) * (b : Int) + t * ((y : Int) * (b : Int)) := by
            rw [Int.add_mul, Int.mul_assoc t]
      _ = s * (x : Int) * (b : Int) + t * ((x : Int) * (k : Int)) := by rw [h2]
      _ = (x : Int) * s * (b : Int) + (x : Int) * t * (k : Int) := by
            rw [Int.mul_comm s (x : Int), ← Int.mul_assoc t (x : Int) (k : Int),
                Int.mul_comm t (x : Int)]
      _ = (x : Int) * (s * (b : Int) + t * (k : Int)) := by
            rw [Int.mul_assoc (x : Int) s, Int.mul_assoc (x : Int) t, ← Int.mul_add]
  have hw_nonneg : 0 ≤ w := by
    apply Classical.byContradiction
    intro hneg
    have hneg' : w < 0 := by omega
    have hx_pos : (0 : Int) < (x : Int) := by omega
    have hprod_neg : (x : Int) * w < 0 := Int.mul_neg_of_pos_of_neg hx_pos hneg'
    omega
  refine ⟨w.toNat, ?_⟩
  have hw_eq : (w.toNat : Int) = w := Int.toNat_of_nonneg hw_nonneg
  have hcast : ((b : Nat) : Int) = ((x * w.toNat : Nat) : Int) := by
    rw [Int.ofNat_mul, hw_eq]; exact hb_int
  exact Int.ofNat.inj hcast

theorem prime_dvd_mul {p a b : Nat} (hp : IsPrimeNat p) (hdvd : p ∣ a * b) :
    p ∣ a ∨ p ∣ b := by
  by_cases hpa : p ∣ a
  · exact Or.inl hpa
  · right
    have hgcd : Nat.gcd p a = 1 := by
      rcases hp.2 (Nat.gcd p a) (Nat.gcd_dvd_left p a) with h1 | hp_eq
      · exact h1
      · exfalso; exact hpa (hp_eq ▸ Nat.gcd_dvd_right p a)
    exact coprime_dvd_of_dvd_mul (by have := hp.1; omega) hgcd hdvd

theorem prime_dvd_pow {p a k : Nat} (hp : IsPrimeNat p) (hdvd : p ∣ a ^ k) : p ∣ a := by
  induction k with
  | zero =>
    simp only [Nat.pow_zero] at hdvd
    have : p ≤ 1 := Nat.le_of_dvd (Nat.le_refl 1) hdvd
    have := hp.1; omega
  | succ k ih =>
    rw [Nat.pow_succ] at hdvd
    rcases prime_dvd_mul hp hdvd with h1 | h2
    · exact ih h1
    · exact h2

theorem dvd_prime_pow {p k d : Nat} (hp : IsPrimeNat p) (hdvd : d ∣ p ^ k) :
    ∃ j, j ≤ k ∧ d = p ^ j := by
  induction k generalizing d with
  | zero =>
    simp only [Nat.pow_zero] at hdvd
    have hd1 : d = 1 := by
      have hd_pos : 1 ≤ d := by
        by_cases h0 : d = 0
        · subst h0; simp at hdvd
        · omega
      have hd_le : d ≤ 1 := Nat.le_of_dvd (Nat.le_refl 1) hdvd
      omega
    exact ⟨0, Nat.le_refl 0, hd1⟩
  | succ k ih =>
    by_cases hpd : p ∣ d
    · rcases hpd with ⟨d', rfl⟩
      rw [Nat.pow_succ, Nat.mul_comm (p ^ k) p] at hdvd
      have hp0 : 0 < p := by have := hp.1; omega
      have hd' : d' ∣ p ^ k := Nat.dvd_of_mul_dvd_mul_left hp0 hdvd
      rcases ih hd' with ⟨j, hjk, rfl⟩
      exact ⟨j + 1, by omega, by rw [Nat.pow_succ, Nat.mul_comm]⟩
    · have hdpk : d ∣ p ^ k := by
        by_cases hd1 : d ≤ 1
        · have hd_pos : 1 ≤ d := by
            by_cases h0 : d = 0
            · subst h0
              have : p ^ (k + 1) = 0 := Nat.eq_zero_of_zero_dvd hdvd
              have hp_pos : 0 < p ^ (k + 1) := Nat.pow_pos (by have := hp.1; omega)
              omega
            · omega
          have : d = 1 := by omega
          subst this; exact Nat.one_dvd _
        · exfalso
          rcases exists_prime_dvd (by omega : 2 ≤ d) with ⟨q, hq, hqd⟩
          have hqp : q ∣ p := prime_dvd_pow hq (Nat.dvd_trans hqd hdvd)
          rcases hp.2 q hqp with hq1 | hqp_eq
          · have := hq.1; omega
          · subst hqp_eq; exact hpd hqd
      rcases ih hdpk with ⟨j, hjk, rfl⟩
      exact ⟨j, by omega, rfl⟩

theorem properDivisors_prime_pow {p k : Nat} (hp : IsPrimeNat p) (hk : 1 ≤ k) :
    properDivisors (p ^ k) = divisors (p ^ (k - 1)) := by
  have hp2 := hp.1
  have hpk : p ^ k = p ^ (k - 1) * p := by
    cases k with
    | zero => omega
    | succ k' => simp [Nat.pow_succ]
  have hsub : p ^ (k - 1) ≤ p ^ k - 1 := by
    have hp1 : 1 ≤ p ^ (k - 1) := Nat.pow_pos (by omega)
    have : p ^ (k - 1) * 2 ≤ p ^ (k - 1) * p := Nat.mul_le_mul_left _ hp2
    omega
  unfold properDivisors divisors
  have hsplit : List.range (p ^ k - 1) =
      List.range (p ^ (k - 1)) ++ ((List.range (p ^ k - 1 - p ^ (k - 1))).map (fun x => p ^ (k - 1) + x)) := by
    have : p ^ k - 1 = p ^ (k - 1) + (p ^ k - 1 - p ^ (k - 1)) := by omega
    conv => lhs; rw [this]
    exact List.range_add
  rw [hsplit, List.map_append, List.filter_append]
  have hleft : List.filter (fun d => p ^ k % d == 0) (List.map (· + 1) (List.range (p ^ (k - 1)))) =
      List.filter (fun d => p ^ (k - 1) % d == 0) (List.map (· + 1) (List.range (p ^ (k - 1)))) := by
    apply List.filter_congr
    intro d hd
    simp only [List.mem_map, List.mem_range] at hd
    rcases hd with ⟨i, _, rfl⟩
    by_cases h1 : p ^ k % (i + 1) == 0
    · have hdvd : i + 1 ∣ p ^ k := Nat.dvd_of_mod_eq_zero (beq_iff_eq.mp h1)
      rcases dvd_prime_pow hp hdvd with ⟨j, _, hj_eq⟩
      have hj_lt : j ≤ k - 1 := by
        by_cases hjeq : j = k
        · subst hjeq; omega
        · omega
      have hdvd' : i + 1 ∣ p ^ (k - 1) := by
        rw [hj_eq]
        have : k - 1 = j + (k - 1 - j) := by omega
        rw [this, Nat.pow_add]
        exact ⟨p ^ (k - 1 - j), rfl⟩
      have h2 : p ^ (k - 1) % (i + 1) == 0 := beq_iff_eq.mpr (Nat.mod_eq_zero_of_dvd hdvd')
      simp [h1, h2]
    · have h2 : ¬(p ^ (k - 1) % (i + 1) == 0) := by
        intro hmod
        apply h1
        have hdvd' : i + 1 ∣ p ^ (k - 1) := Nat.dvd_of_mod_eq_zero (beq_iff_eq.mp hmod)
        have hdvd : i + 1 ∣ p ^ k := by rw [hpk]; exact Nat.dvd_mul_right_of_dvd hdvd' p
        exact beq_iff_eq.mpr (Nat.mod_eq_zero_of_dvd hdvd)
      simp [h1, h2]
  have hright : List.filter (fun d => p ^ k % d == 0)
      (List.map (· + 1) (List.map (fun x => p ^ (k - 1) + x) (List.range (p ^ k - 1 - p ^ (k - 1))))) = [] := by
    rw [List.filter_eq_nil_iff]
    intro d hd
    simp only [List.mem_map, List.mem_range] at hd
    rcases hd with ⟨y, ⟨x, _, rfl⟩, rfl⟩
    rw [beq_iff_eq]
    intro hmod
    have hdvd : p ^ (k - 1) + x + 1 ∣ p ^ k := Nat.dvd_of_mod_eq_zero hmod
    rcases dvd_prime_pow hp hdvd with ⟨j, hjk, hj_eq⟩
    by_cases hjeq : j = k
    · subst hjeq; omega
    · have hj_le : p ^ j ≤ p ^ (k - 1) := by
        have : k - 1 = j + (k - 1 - j) := by omega
        rw [this, Nat.pow_add]
        have hp_pos : 1 ≤ p ^ (k - 1 - j) := Nat.pow_pos (by omega)
        exact Nat.le_mul_of_pos_right _ hp_pos
      omega
  rw [hleft, hright, List.append_nil]

theorem cyclotomic_prime_pow {p k : Nat} (hp : IsPrimeNat p) (hk : 1 ≤ k) :
    cyclotomic (p ^ k) = geomStep (p ^ (k - 1)) p ∧
    cycloDeg (p ^ k) = (p - 1) * p ^ (k - 1) ∧
    eval (cyclotomic (p ^ k)) 1 = Int.ofNat p := by
  have hp2 := hp.1
  have hpk1_pos : 1 ≤ p ^ (k - 1) := Nat.pow_pos (by omega)
  have hpk_pos : 1 ≤ p ^ k := Nat.pow_pos (by omega)
  have hpk_eq : p ^ k = p ^ (k - 1) * p := by
    cases k with
    | zero => omega
    | succ k' => simp [Nat.pow_succ]
  have h1 : qPowSubOne (p ^ k) = mul (qPowSubOne (p ^ (k - 1))) (cyclotomic (p ^ k)) := by
    rw [(cyclotomic_spec (p ^ k) hpk_pos).2, divisors_eq_proper_append (p ^ k) hpk_pos,
        polyProd_append, properDivisors_prime_pow hp hk,
        ← (cyclotomic_spec (p ^ (k - 1)) hpk1_pos).2,
        polyProd_singleton (p ^ k) cyclotomic (cyclotomic_spec (p ^ k) hpk_pos).1.1]
  have h2 : qPowSubOne (p ^ k) = mul (qPowSubOne (p ^ (k - 1))) (geomStep (p ^ (k - 1)) p) := by
    conv => lhs; rw [hpk_eq]
    exact (mul_qPowSubOne_geomStep (p ^ (k - 1)) p).symm
  rw [h1] at h2
  have hcyc : cyclotomic (p ^ k) = geomStep (p ^ (k - 1)) p :=
    mul_monic_cancel_left (monic_qPowSubOne hpk1_pos)
      (cyclotomic_spec (p ^ k) hpk_pos).1.1 (trim_geomStep _ _) h2
  have hdeg : cycloDeg (p ^ k) = (p - 1) * p ^ (k - 1) := by
    have hm1 := (cyclotomic_spec (p ^ k) hpk_pos).1
    rw [hcyc] at hm1
    have hm2 := monic_geomStep hpk1_pos (by omega : 1 ≤ p)
    rw [monicOfDeg_unique hm1 hm2, Nat.mul_comm]
  refine ⟨hcyc, hdeg, ?_⟩
  rw [hcyc, eval_geomStep_one]

theorem eval_polyProd_pos_of_pos (xs : List Nat)
    (hall : ∀ m ∈ xs, 1 ≤ eval (cyclotomic m) 1) :
    1 ≤ eval (polyProd xs cyclotomic) 1 := by
  induction xs with
  | nil => simp [polyProd, eval_one_poly]
  | cons x xs ih =>
    simp only [polyProd, eval_mul]
    have hx1 : 1 ≤ eval (cyclotomic x) 1 := hall x (List.mem_cons.mpr (Or.inl rfl))
    have hxs1 : 1 ≤ eval (polyProd xs cyclotomic) 1 :=
      ih (fun y hy => hall y (List.mem_cons.mpr (Or.inr hy)))
    exact Int.le_trans (by decide : (1 : Int) ≤ 1 * 1)
      (Int.mul_le_mul hx1 hxs1 (by omega) (by omega))

/-- Every cyclotomic polynomial `d >= 2` takes a strictly positive integer value at `q = 1`. -/
theorem eval_cyclotomic_one_pos (d : Nat) (hd : 2 ≤ d) :
    1 ≤ eval (cyclotomic d) 1 := by
  induction d using Nat.strongRecOn with
  | ind d ih =>
    let propGe2 := (properDivisors d).filter (fun m => decide (2 ≤ m))
    have hd_monic := (cyclotomic_spec d (by omega)).1
    have hprod : geomStep 1 d = mul (polyProd propGe2 cyclotomic) (cyclotomic d) := by
      rw [geomStep_one_eq_polyProd_ge2 (by omega), divisorsGe2_eq_properGe2_append hd,
          polyProd_append, polyProd_singleton d cyclotomic hd_monic.1]
    have hev : (d : Int) = eval (polyProd propGe2 cyclotomic) 1 * eval (cyclotomic d) 1 := by
      have h0 : eval (geomStep 1 d) 1 = eval (mul (polyProd propGe2 cyclotomic) (cyclotomic d)) 1 :=
        hprod ▸ rfl
      rw [eval_geomStep_one, eval_mul] at h0
      exact h0
    have hP_pos : 1 ≤ eval (polyProd propGe2 cyclotomic) 1 :=
      eval_polyProd_pos_of_pos propGe2 (fun m hm => by
        rw [List.mem_filter, decide_eq_true_eq] at hm
        exact ih m (mem_properDivisors_iff.mp hm.1).2.1 hm.2)
    apply Classical.byContradiction
    intro hle0
    have hle0' : eval (cyclotomic d) 1 ≤ 0 := by omega
    have hprod_le0 : eval (polyProd propGe2 cyclotomic) 1 * eval (cyclotomic d) 1 ≤ 0 :=
      Int.mul_nonpos_of_nonneg_of_nonpos (by omega) hle0'
    omega

/-- Extract maximal power of a prime `p` dividing `n >= 1`: `n = p^k * m` with `¬(p | m)`. -/
theorem extract_prime_pow {p : Nat} (hp : IsPrimeNat p) :
    ∀ n : Nat, 1 ≤ n → ∃ k m : Nat, 1 ≤ m ∧ ¬(p ∣ m) ∧ n = p ^ k * m := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro hn1
    by_cases hpn : p ∣ n
    · rcases hpn with ⟨n', rfl⟩
      have hn'_pos : 1 ≤ n' := by
        by_cases h0 : n' = 0
        · subst h0; simp at hn1
        · omega
      have hn'_lt : n' < p * n' := by
        have hp2 := hp.1
        have : 1 * n' < p * n' := Nat.mul_lt_mul_of_pos_right (by omega) (by omega)
        simpa using this
      rcases ih n' hn'_lt hn'_pos with ⟨k, m, hm1, hnpm, hn'_eq⟩
      refine ⟨k + 1, m, hm1, hnpm, ?_⟩
      rw [hn'_eq, Nat.pow_succ, Nat.mul_comm (p ^ k) p, Nat.mul_assoc]
    · exact ⟨0, n, hn1, hpn, by simp⟩

/-- Subsequence product divisibility on `Nat` for `Nodup` lists. -/
theorem subseq_prod_dvd {xs ys : List Nat} (hnodup : xs.Nodup)
    (hsub : ∀ x ∈ xs, x ∈ ys) (val : Nat → Nat) :
    (xs.map val).foldr (· * ·) 1 ∣ (ys.map val).foldr (· * ·) 1 := by
  induction xs generalizing ys with
  | nil => exact Nat.one_dvd _
  | cons x xs ih =>
    cases hnodup with
    | cons hx_not_xs hxs_nodup =>
      have hx_mem : x ∈ ys := hsub x (List.mem_cons.mpr (Or.inl rfl))
      rcases List.append_of_mem hx_mem with ⟨pre, post, rfl⟩
      have hsub' : ∀ z ∈ xs, z ∈ pre ++ post := by
        intro z hz
        have hz_ne : z ≠ x := fun heq => hx_not_xs z hz heq.symm
        have hmem := hsub z (List.mem_cons.mpr (Or.inr hz))
        rw [List.mem_append] at hmem ⊢
        rcases hmem with hpre | hcons
        · exact Or.inl hpre
        · rcases List.mem_cons.mp hcons with rfl | hpost
          · exact False.elim (hz_ne rfl)
          · exact Or.inr hpost
      have hdvd_rest := ih hxs_nodup hsub'
      have hsplit_prod : ∀ (a b : List Nat),
          ((a ++ x :: b).map val).foldr (· * ·) 1 =
            val x * ((a ++ b).map val).foldr (· * ·) 1 := by
        intro a b
        induction a with
        | nil => simp [List.map, List.foldr]
        | cons u a iha =>
          simp only [List.cons_append, List.map, List.foldr, iha]
          rw [← Nat.mul_assoc, Nat.mul_comm (val u) (val x), Nat.mul_assoc]
      rw [hsplit_prod pre post]
      simp only [List.map, List.foldr]
      exact Nat.mul_dvd_mul_left (val x) hdvd_rest

theorem eval_polyProd_toNat_eq {ds : List Nat} (hd2 : ∀ d ∈ ds, 2 ≤ d) :
    (eval (polyProd ds cyclotomic) 1).toNat =
      (ds.map (fun d => (eval (cyclotomic d) 1).toNat)).foldr (· * ·) 1 ∧
    1 ≤ eval (polyProd ds cyclotomic) 1 := by
  induction ds with
  | nil =>
    simp [polyProd, eval_one_poly]
  | cons d ds ih =>
    have hd_pos := eval_cyclotomic_one_pos d (hd2 d (List.mem_cons.mpr (Or.inl rfl)))
    rcases ih (fun x hx => hd2 x (List.mem_cons.mpr (Or.inr hx))) with ⟨htN, hpos⟩
    simp only [polyProd, eval_mul, List.map, List.foldr]
    have hmul_pos : 1 ≤ eval (cyclotomic d) 1 * eval (polyProd ds cyclotomic) 1 :=
      Int.le_trans (by decide : (1 : Int) ≤ 1 * 1)
        (Int.mul_le_mul hd_pos hpos (by omega) (by omega))
    refine ⟨?_, hmul_pos⟩
    have h1 : ((eval (cyclotomic d) 1).toNat : Int) = eval (cyclotomic d) 1 :=
      Int.toNat_of_nonneg (by omega)
    have h2 : ((eval (polyProd ds cyclotomic) 1).toNat : Int) = eval (polyProd ds cyclotomic) 1 :=
      Int.toNat_of_nonneg (by omega)
    have h3 : (((eval (cyclotomic d) 1 * eval (polyProd ds cyclotomic) 1).toNat : Nat) : Int) =
        (((eval (cyclotomic d) 1).toNat * (eval (polyProd ds cyclotomic) 1).toNat : Nat) : Int) := by
      rw [Int.ofNat_mul, h1, h2, Int.toNat_of_nonneg (by omega)]
    rw [Int.ofNat.inj h3, htN]

/-- Exact value of `Phi_d(1)` for non-prime-powers `d >= 2`: always `1`. -/
theorem eval_cyclotomic_one_non_prime_pow {d : Nat} (hd : 2 ≤ d) (hnpp : ¬IsPrimePowNat d) :
    eval (cyclotomic d) 1 = 1 := by
  have hv_pos := eval_cyclotomic_one_pos d hd
  let v := (eval (cyclotomic d) 1).toNat
  have hv_eq : (v : Int) = eval (cyclotomic d) 1 := Int.toNat_of_nonneg (by omega)
  suffices hv1 : v = 1 by
    rw [← hv_eq, hv1]; rfl
  by_cases hv_le1 : v ≤ 1
  · omega
  · exfalso
    rcases exists_prime_dvd (by omega : 2 ≤ v) with ⟨p, hp, hpv⟩
    have hd_prod : d = ((divisorsGe2 d).map (fun m => (eval (cyclotomic m) 1).toNat)).foldr (· * ·) 1 := by
      have hev : (eval (geomStep 1 d) 1).toNat = (eval (polyProd (divisorsGe2 d) cyclotomic) 1).toNat :=
        (geomStep_one_eq_polyProd_ge2 (by omega : 1 ≤ d)) ▸ rfl
      have hgeom_d : (eval (geomStep 1 d) 1).toNat = d := by rw [eval_geomStep_one]; rfl
      have ht := (eval_polyProd_toNat_eq (ds := divisorsGe2 d)
        (fun m hm => (mem_divisorsGe2_iff.mp hm).1)).1
      exact hgeom_d.symm.trans (hev.trans ht)
    have hvd : v ∣ d := by
      have hsub := subseq_prod_dvd (xs := [d]) (ys := divisorsGe2 d)
        (List.Pairwise.cons (by simp) List.Pairwise.nil)
        (fun x hx => by
          simp only [List.mem_singleton] at hx; rw [hx]
          exact mem_divisorsGe2_iff.mpr ⟨hd, Nat.le_refl d, Nat.dvd_refl d⟩)
        (fun m => (eval (cyclotomic m) 1).toNat)
      simp only [List.map, List.foldr, Nat.mul_one, ← hd_prod] at hsub
      exact hsub
    have hpd : p ∣ d := Nat.dvd_trans hpv hvd
    rcases extract_prime_pow hp d (by omega) with ⟨k, m, hm1, hnpm, hd_eq⟩
    have hk1 : 1 ≤ k := by
      by_cases hk0 : k = 0
      · have hd_m : d = m := by rw [hk0, Nat.pow_zero, Nat.one_mul] at hd_eq; exact hd_eq
        rw [hd_m] at hpd; exact False.elim (hnpm hpd)
      · omega
    have hm2 : 2 ≤ m := by
      by_cases hm_eq1 : m = 1
      · have hd_pk : d = p ^ k := by rw [hm_eq1, Nat.mul_one] at hd_eq; exact hd_eq
        exact False.elim (hnpp ⟨p, k, hp, hk1, hd_pk⟩)
      · omega
    let pPows := (List.range k).map (fun i => p ^ (i + 1))
    let testList := pPows ++ [d]
    have hpow_strict : ∀ i j, i < j → p ^ i < p ^ j := by
      intro i j hij
      have hsplit : j = i + (j - i) := by omega
      rw [hsplit, Nat.pow_add]
      have hgt : 1 < p ^ (j - i) := by
        cases hdiff : j - i with
        | zero => omega
        | succ t =>
          rw [Nat.pow_succ]
          have htpos : 1 ≤ p ^ t := Nat.pow_pos (by have := hp.1; omega)
          have : 1 * 2 ≤ p ^ t * p := Nat.mul_le_mul htpos hp.1
          omega
      have hipos : 0 < p ^ i := Nat.pow_pos (by have := hp.1; omega)
      have := Nat.mul_lt_mul_of_pos_left hgt hipos
      simpa using this
    have htest_nodup : testList.Nodup := by
      apply nodup_append_of_disjoint
      · apply nodup_map_of_inj (nodup_range_aux k)
        intro i _ j _ hij
        by_cases hlt : i < j
        · have := hpow_strict (i + 1) (j + 1) (by omega); omega
        · by_cases hgt : j < i
          · have := hpow_strict (j + 1) (i + 1) (by omega); omega
          · omega
      · exact List.Pairwise.cons (by simp) List.Pairwise.nil
      · intro a ha b hb
        simp only [pPows, List.mem_map, List.mem_range] at ha
        simp only [List.mem_singleton] at hb
        rcases ha with ⟨i, hi, rfl⟩
        rw [hb]
        intro heq
        have hle_pk : p ^ (i + 1) ≤ p ^ k := by
          by_cases hik : i + 1 = k
          · rw [hik]; exact Nat.le_refl _
          · exact Nat.le_of_lt (hpow_strict (i + 1) k (by omega))
        have hlt_d : p ^ k < d := by
          rw [hd_eq]
          have hpk_pos : 0 < p ^ k := Nat.pow_pos (by have := hp.1; omega)
          have : p ^ k * 1 < p ^ k * m := Nat.mul_lt_mul_of_pos_left (by omega) hpk_pos
          simpa using this
        omega
    have htest_sub : ∀ x ∈ testList, x ∈ divisorsGe2 d := by
      intro x hx
      rw [List.mem_append] at hx
      rcases hx with hpows | hsing
      · simp only [pPows, List.mem_map, List.mem_range] at hpows
        rcases hpows with ⟨i, hi, rfl⟩
        rw [mem_divisorsGe2_iff]
        have hge2 : 2 ≤ p ^ (i + 1) := by
          rw [Nat.pow_succ]
          have : 1 * 2 ≤ p ^ i * p := Nat.mul_le_mul (Nat.pow_pos (by have := hp.1; omega)) hp.1
          omega
        have hdvd_pk : p ^ (i + 1) ∣ p ^ k := by
          have hsum_k : k = (i + 1) + (k - (i + 1)) := by omega
          refine ⟨p ^ (k - (i + 1)), ?_⟩
          conv => lhs; rw [hsum_k]
          exact Nat.pow_add p (i + 1) (k - (i + 1))
        have hdvd_d : p ^ (i + 1) ∣ d := by
          rw [hd_eq]; exact Nat.dvd_mul_right_of_dvd hdvd_pk m
        exact ⟨hge2, Nat.le_of_dvd (by omega) hdvd_d, hdvd_d⟩
      · simp only [List.mem_singleton] at hsing; rw [hsing]
        exact mem_divisorsGe2_iff.mpr ⟨hd, Nat.le_refl d, Nat.dvd_refl d⟩
    have hdvd_prod := subseq_prod_dvd htest_nodup htest_sub (fun t => (eval (cyclotomic t) 1).toNat)
    rw [← hd_prod] at hdvd_prod
    have hpPows_prod : ∀ j : Nat,
        (((List.range j).map (fun i => p ^ (i + 1))).map
          (fun t => (eval (cyclotomic t) 1).toNat)).foldr (· * ·) 1 = p ^ j := by
      intro j
      induction j with
      | zero => rfl
      | succ j ihj =>
        rw [List.range_succ, List.map_append, List.map_append, List.foldr_append]
        simp only [List.map, List.foldr, Nat.mul_one]
        have hval : (eval (cyclotomic (p ^ (j + 1))) 1).toNat = p := by
          rw [(cyclotomic_prime_pow hp (by omega : 1 ≤ j + 1)).2.2]; rfl
        rw [hval]
        have hfold_mul : ∀ (zs : List Nat) (b : Nat),
            zs.foldr (· * ·) b = zs.foldr (· * ·) 1 * b := by
          intro zs b
          induction zs with
          | nil => simp [List.foldr]
          | cons z zs ihz => simp [List.foldr, ihz, Nat.mul_assoc]
        rw [hfold_mul, ihj, Nat.pow_succ]
    have hfold_append : ((testList).map (fun t => (eval (cyclotomic t) 1).toNat)).foldr (· * ·) 1 =
        p ^ k * v := by
      simp only [testList, List.map_append, List.foldr_append, List.map, List.foldr, Nat.mul_one]
      have hfold_mul : ∀ (zs : List Nat) (b : Nat),
          zs.foldr (· * ·) b = zs.foldr (· * ·) 1 * b := by
        intro zs b
        induction zs with
        | nil => simp [List.foldr]
        | cons z zs ihz => simp [List.foldr, ihz, Nat.mul_assoc]
      rw [hfold_mul, hpPows_prod k]
    rw [hfold_append, hd_eq] at hdvd_prod
    have hvm : v ∣ m := Nat.dvd_of_mul_dvd_mul_left (Nat.pow_pos (by have := hp.1; omega)) hdvd_prod
    exact hnpm (Nat.dvd_trans hpv hvm)

/-! ### 7. Cyclotomic Products & Universal Obstruction Theorems -/

def IsCyclotomicProduct (P : Poly) : Prop :=
  ∃ ds : List Nat, (∀ d ∈ ds, 1 ≤ d) ∧ P = polyProd ds cyclotomic

theorem cyclotomicProd_indices_ge2 {ds : List Nat}
    (hd1 : ∀ d ∈ ds, 1 ≤ d)
    (hpos : 1 ≤ eval (polyProd ds cyclotomic) 1) :
    ∀ d ∈ ds, 2 ≤ d := by
  intro d hd
  have hd_ge1 := hd1 d hd
  by_cases hd_eq1 : d = 1
  · subst hd_eq1
    rcases mem_polyProd_dvd hd cyclotomic with ⟨q, _, hq⟩
    rw [hq, eval_mul, eval_cyclotomic_one_at_1, Int.mul_zero] at hpos
    omega
  · omega

theorem cyclotomicProd_palindromic {P : Poly}
    (hcyc : IsCyclotomicProduct P) (hpos : 1 ≤ eval P 1) :
    ∃ D : Nat, IsPalindromicOfDeg P D := by
  rcases hcyc with ⟨ds, hd1, rfl⟩
  have hd2 := cyclotomicProd_indices_ge2 hd1 hpos
  exact ⟨sumNatList (ds.map cycloDeg),
         polyProd_palindromic ds cyclotomic cycloDeg (fun d hd => cyclotomic_palindromic d (hd2 d hd))⟩

theorem cyclotomicProd_orders_le_two {ds : List Nat}
    (hd1 : ∀ d ∈ ds, 1 ≤ d ∧ d ≤ 2)
    (hpos : 1 ≤ eval (polyProd ds cyclotomic) 1) :
    ∃ k : Nat, eval (polyProd ds cyclotomic) 1 = Int.ofNat (2 ^ k) := by
  have hd2 : ∀ d ∈ ds, d = 2 := by
    have hge2 := cyclotomicProd_indices_ge2 (fun d hd => (hd1 d hd).1) hpos
    intro d hd
    have h1 := hge2 d hd
    have h2 := (hd1 d hd).2
    omega
  clear hd1 hpos
  induction ds with
  | nil => exact ⟨0, by simp [polyProd, eval_one_poly]⟩
  | cons d ds ih =>
    have hd_eq2 : d = 2 := hd2 d (List.mem_cons.mpr (Or.inl rfl))
    subst hd_eq2
    rcases ih (fun x hx => hd2 x (List.mem_cons.mpr (Or.inr hx))) with ⟨k, hk⟩
    refine ⟨k + 1, ?_⟩
    have hp2 : IsPrimeNat 2 := ⟨Nat.le_refl 2, fun m hm => by
      have hm_pos : 1 ≤ m := by
        by_cases h0 : m = 0
        · subst h0; simp at hm
        · omega
      have hm_le : m ≤ 2 := Nat.le_of_dvd (by omega) hm
      omega⟩
    have hc2 : eval (cyclotomic 2) 1 = Int.ofNat 2 :=
      (cyclotomic_prime_pow hp2 (Nat.le_refl 1)).2.2
    rw [polyProd, eval_mul, hc2, hk, Nat.pow_succ, int_ofNat_mul, Int.mul_comm]

theorem cyclotomicProd_prime_order_bound {ds : List Nat} {p : Nat}
    (hd1 : ∀ d ∈ ds, 1 ≤ d)
    (hpos : 1 ≤ eval (polyProd ds cyclotomic) 1)
    (hp : IsPrimeNat p)
    (hdvd : p ∣ (eval (polyProd ds cyclotomic) 1).toNat) :
    ∃ d ∈ ds, p ≤ d := by
  have hd2 := cyclotomicProd_indices_ge2 hd1 hpos
  have hdvd_prod : p ∣ (ds.map (fun d => (eval (cyclotomic d) 1).toNat)).foldr (· * ·) 1 := by
    rw [← (eval_polyProd_toNat_eq hd2).1]; exact hdvd
  suffices haux : ∀ (xs : List Nat), (∀ x ∈ xs, 2 ≤ x) →
      p ∣ (xs.map (fun d => (eval (cyclotomic d) 1).toNat)).foldr (· * ·) 1 →
      ∃ d ∈ xs, p ≤ d from
    haux ds hd2 hdvd_prod
  intro xs
  induction xs with
  | nil =>
    intro _ hnil
    simp only [List.map, List.foldr] at hnil
    have : p ≤ 1 := Nat.le_of_dvd (Nat.le_refl 1) hnil
    have := hp.1; omega
  | cons d xs ih =>
    intro hxs2 hcons
    simp only [List.map, List.foldr] at hcons
    rcases prime_dvd_mul hp hcons with h_head | h_tail
    · have hd_ge2 := hxs2 d (List.mem_cons.mpr (Or.inl rfl))
      by_cases hpp : IsPrimePowNat d
      · rcases hpp with ⟨q, k, hq, hk1, rfl⟩
        rw [(cyclotomic_prime_pow hq hk1).2.2] at h_head
        dsimp only [Int.toNat] at h_head
        rcases hq.2 p h_head with hp1 | hpq
        · have := hp.1; omega
        · subst hpq
          refine ⟨p ^ k, List.mem_cons.mpr (Or.inl rfl), ?_⟩
          cases k with
          | zero => omega
          | succ k' =>
            rw [Nat.pow_succ]
            exact Nat.le_mul_of_pos_left p (Nat.pow_pos (by have := hp.1; omega))
      · rw [eval_cyclotomic_one_non_prime_pow hd_ge2 hpp] at h_head
        dsimp only [Int.toNat] at h_head
        have : p ≤ 1 := Nat.le_of_dvd (Nat.le_refl 1) h_head
        have := hp.1; omega
    · rcases ih (fun x hx => hxs2 x (List.mem_cons.mpr (Or.inr hx))) h_tail with ⟨d', hd', hle⟩
      exact ⟨d', List.mem_cons.mpr (Or.inr hd'), hle⟩

theorem sum_decr_at_prime (ps : List Nat) (hps_nodup : ps.Nodup) (q : Nat) (e : Nat → Nat) :
    sumNatList (ps.map (fun p => e p * (p - 1))) ≤
      (q - 1) + sumNatList (ps.map (fun p => (if p == q then e p - 1 else e p) * (p - 1))) := by
  induction ps with
  | nil => simp [sumNatList]
  | cons x xs ih =>
    cases hps_nodup with
    | cons hx_not_xs hxs_nodup =>
      simp only [List.map, sumNatList]
      by_cases hxq : x = q
      · subst hxq
        have htrue : (if x == x then e x - 1 else e x) = e x - 1 := by simp
        rw [htrue]
        have hrest_eq : List.map (fun p => (if p == x then e p - 1 else e p) * (p - 1)) xs =
            List.map (fun p => e p * (p - 1)) xs := by
          apply List.map_congr_left
          intro p hp_xs
          have hpne : p ≠ x := fun heq => hx_not_xs p hp_xs heq.symm
          have hfalse : (if p == x then e p - 1 else e p) = e p := by simp [beq_false_of_ne hpne]
          rw [hfalse]
        rw [hrest_eq]
        cases hex : e x with
        | zero => simp
        | succ m =>
          simp only [Nat.add_sub_cancel, Nat.succ_mul]
          omega
      · have hfalse : (if x == q then e x - 1 else e x) = e x := by simp [beq_false_of_ne hxq]
        rw [hfalse]
        have hxs := ih hxs_nodup
        omega

theorem sum_zero_of_pow_dvd_one (ps : List Nat) (ex : Nat → Nat)
    (hps_prime : ∀ p ∈ ps, IsPrimeNat p)
    (hnil : ∀ p ∈ ps, p ^ (ex p) ∣ 1) :
    sumNatList (ps.map (fun p => ex p * (p - 1))) = 0 := by
  induction ps with
  | nil => rfl
  | cons p ps ihp =>
    have hp := hps_prime p (List.mem_cons.mpr (Or.inl rfl))
    have hpe1 : p ^ (ex p) ∣ 1 := hnil p (List.mem_cons.mpr (Or.inl rfl))
    have hep0 : ex p = 0 := by
      cases hep : ex p with
      | zero => rfl
      | succ m =>
        rw [hep, Nat.pow_succ] at hpe1
        have hle1 : p ^ m * p ≤ 1 := Nat.le_of_dvd (Nat.le_refl 1) hpe1
        have hmpos : 1 ≤ p ^ m := Nat.pow_pos (by have := hp.1; omega)
        have : 1 * 2 ≤ p ^ m * p := Nat.mul_le_mul hmpos hp.1
        omega
    simp [sumNatList, hep0,
          ihp (fun x hx => hps_prime x (List.mem_cons.mpr (Or.inr hx)))
              (fun x hx => hnil x (List.mem_cons.mpr (Or.inr hx)))]

/-- Universal Prime-Power Degree Lower Bound:
    For any `Nodup` list of primes `ps` and exponent map `e`, if `p ^ (e p) | P(1)` for every `p ∈ ps`,
    then `∑_{p ∈ ps} e(p) * (p - 1) <= deg P`. -/
theorem cyclotomicProd_prime_pow_deg_bound {ds : List Nat} (ps : List Nat) (e : Nat → Nat)
    (hps_nodup : ps.Nodup)
    (hps_prime : ∀ p ∈ ps, IsPrimeNat p)
    (hd1 : ∀ d ∈ ds, 1 ≤ d)
    (hpos : 1 ≤ eval (polyProd ds cyclotomic) 1)
    (hdvd : ∀ p ∈ ps, p ^ (e p) ∣ (eval (polyProd ds cyclotomic) 1).toNat) :
    sumNatList (ps.map (fun p => e p * (p - 1))) ≤ sumNatList (ds.map cycloDeg) := by
  have hd2 := cyclotomicProd_indices_ge2 hd1 hpos
  have hdvd_prod : ∀ p ∈ ps, p ^ (e p) ∣
      (ds.map (fun d => (eval (cyclotomic d) 1).toNat)).foldr (· * ·) 1 := by
    rw [← (eval_polyProd_toNat_eq hd2).1]; exact hdvd
  suffices haux : ∀ (xs : List Nat) (ex : Nat → Nat),
      (∀ x ∈ xs, 2 ≤ x) →
      (∀ p ∈ ps, p ^ (ex p) ∣ (xs.map (fun d => (eval (cyclotomic d) 1).toNat)).foldr (· * ·) 1) →
      sumNatList (ps.map (fun p => ex p * (p - 1))) ≤ sumNatList (xs.map cycloDeg) from
    haux ds e hd2 hdvd_prod
  intro xs
  induction xs with
  | nil =>
    intro ex _ hnil
    simp only [List.map, List.foldr] at hnil
    rw [sum_zero_of_pow_dvd_one ps ex hps_prime hnil]
    exact Nat.zero_le _
  | cons d xs ih =>
    intro ex hxs2 hcons
    have hd_ge2 := hxs2 d (List.mem_cons.mpr (Or.inl rfl))
    have htl_ge2 : ∀ x ∈ xs, 2 ≤ x := fun x hx => hxs2 x (List.mem_cons.mpr (Or.inr hx))
    simp only [List.map, List.foldr, sumNatList] at hcons ⊢
    by_cases hpp : IsPrimePowNat d
    · rcases hpp with ⟨q, k, hq, hk1, rfl⟩
      have hval_q : (eval (cyclotomic (q ^ k)) 1).toNat = q := by
        rw [(cyclotomic_prime_pow hq hk1).2.2]; rfl
      have hdeg_q : q - 1 ≤ cycloDeg (q ^ k) := by
        rw [(cyclotomic_prime_pow hq hk1).2.1]
        have hqk_pos : 1 ≤ q ^ (k - 1) := Nat.pow_pos (by have := hq.1; omega)
        exact Nat.le_mul_of_pos_right _ hqk_pos
      rw [hval_q] at hcons
      let ex' : Nat → Nat := fun p => if p == q then ex p - 1 else ex p
      have hdvd' : ∀ p ∈ ps, p ^ (ex' p) ∣
          (xs.map (fun t => (eval (cyclotomic t) 1).toNat)).foldr (· * ·) 1 := by
        intro p hp_mem
        have hp := hps_prime p hp_mem
        have hp_dvd := hcons p hp_mem
        by_cases hpq : p = q
        · subst hpq
          have hexp_eq : ex' p = ex p - 1 := by simp [ex']
          rw [hexp_eq]
          cases hep : ex p with
          | zero => exact Nat.one_dvd _
          | succ m =>
            simp only [Nat.add_sub_cancel]
            rw [hep, Nat.pow_succ, Nat.mul_comm (p ^ m) p] at hp_dvd
            exact Nat.dvd_of_mul_dvd_mul_left (by have := hp.1; omega) hp_dvd
        · have hexp_eq : ex' p = ex p := by simp [ex', hpq]
          rw [hexp_eq]
          cases hep : ex p with
          | zero => exact Nat.one_dvd _
          | succ r =>
            have hgcd1 : Nat.gcd (p ^ (r + 1)) q = 1 := by
              rcases hq.2 (Nat.gcd (p ^ (r + 1)) q) (Nat.gcd_dvd_right _ q) with h1 | hged
              · exact h1
              · exfalso
                have hqp : q ∣ p := prime_dvd_pow hq (hged ▸ Nat.gcd_dvd_left (p ^ (r + 1)) q)
                rcases hp.2 q hqp with hq1 | hqp_eq
                · have := hq.1; omega
                · exact hpq hqp_eq.symm
            rw [hep] at hp_dvd
            exact coprime_dvd_of_dvd_mul (Nat.pow_pos (by have := hp.1; omega)) hgcd1 hp_dvd
      have hih := ih ex' htl_ge2 hdvd'
      have hstep := sum_decr_at_prime ps hps_nodup q ex
      exact Nat.le_trans hstep (Nat.add_le_add hdeg_q hih)
    · have hval1 : (eval (cyclotomic d) 1).toNat = 1 := by
        rw [eval_cyclotomic_one_non_prime_pow hd_ge2 hpp]; rfl
      rw [hval1, Nat.one_mul] at hcons
      have hih := ih ex htl_ge2 hcons
      exact Nat.le_trans hih (Nat.le_add_left _ _)

end Conjecture00000004769
