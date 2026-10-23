import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic

set_option maxHeartbeats 0
set_option maxRecDepth 10000
set_option exponentiation.threshold 20000
set_option linter.unnecessarySeqFocus false
set_option backward.isDefEq.respectTransparency false

namespace TLMC39

def residue : Fin 28 → ℕ := ![0, 0, 1, 1, 8, 8, 4, 7, 5, 29, 2, 14, 17, 34, 43, 13, 37, 16, 19, 26, 62, 52, 37, 49, 121, 103, 106, 229]
def period : Fin 28 → ℕ := ![3, 5, 9, 10, 12, 15, 18, 20, 24, 30, 36, 36, 40, 45, 45, 48, 48, 60, 60, 72, 72, 90, 120, 144, 144, 180, 180, 360]
def modulus : Fin 28 → ℕ := ![7, 31, 73, 11, 13, 151, 19, 41, 241, 331, 37, 109, 61681, 631, 23311, 97, 673, 61, 1321, 433, 38737, 18837001, 4562284561, 577, 487824887233, 181, 54001, 79247505326224968612036218881]
def D : ℕ := 16851481097713401344722606144432989016962242918221343407423226512657956650517689294593736821747391489499820355757682942576
def Q : ℕ := 1053217568607087584045162884027061813560140182388833962963951657041122290657355580912108551359211968093738772234855183911
def G : ℕ := 3942951359960012586542991835686376608231592127249807732373409846031135195659174148737161255930050543559319182152642816343958573976075461198274610155058226350701077796608546283231637018483208223116080561800334422176622099740983337736621316898600121619871377542107047343253864459964167331555646795960321
def target : ℕ := 14105361477916114570737258104493241655354019344940573425140720525837701276167724450285261325054855422208435392507600721311

theorem fixedConstants :
    D = 16 * Q ∧ 1 < D ∧ D < G ∧ G * 45592577 = 2^1024+1 ∧
    G % 16 = 1 ∧ target < D ∧ target % 16 = 15 ∧ target % 8191 = 0 ∧
    8191 ∣ D := by norm_num [D, Q, G, target]

theorem tableFacts (i : Fin 28) :
    1 < modulus i ∧ modulus i ∣ D ∧ 0 < period i ∧ period i ∣ 720 ∧
    residue i < period i ∧ 2^(period i) % modulus i = 1 ∧
    target % modulus i = 2^(residue i) % modulus i := by
  fin_cases i <;> norm_num [modulus, period, residue, target, D]

theorem cover720 : ∀ r : Fin 720, ∃ i : Fin 28,
    (r : ℕ) % period i = residue i := by decide

theorem oddModulusFacts :
    0 < Q ∧ 2^9360 % Q = 1 ∧ Nat.Coprime (2^4096-1) Q := by
  norm_num [Q, Nat.Coprime]

theorem pow_reduce {M : Type*} [Monoid M] (x : M) (p n : ℕ)
    (h : x^p = 1) : x^n = x^(n%p) := by
  calc
    x^n = x^(n%p+p*(n/p)) := congrArg (fun k => x^k) (Nat.mod_add_div n p).symm
    _ = x^(n%p) := by rw [pow_add, pow_mul, h, one_pow, mul_one]

def height (k : ℕ) : ℕ := 12*(k+1)

theorem height_ge (k : ℕ) : 12 ≤ height k := by unfold height; omega

theorem exponentResidue (k : ℕ) : 2^(height k) % 9360 = 4096 := by
  induction k with
  | zero => norm_num [height]
  | succ k ih =>
      rw [show height (k+1) = height k + 12 by unfold height; omega,
        pow_add, Nat.mul_mod, ih]
      norm_num

def fermat (r : ℕ) : ℕ := 2^(2^r)+1
def retained (r : ℕ) : ℕ := if r=10 then 45592577 else fermat r
def base (n : ℕ) : ℕ := ∏ r ∈ Finset.range n, retained r

theorem fermat_gt_one (r : ℕ) : 1 < fermat r := by
  have h : 0 < 2^(2^r) := Nat.pow_pos (by decide : 0<2)
  unfold fermat; omega

theorem retained_gt_one (r : ℕ) : 1 < retained r := by
  by_cases h:r=10
  · simp [retained,h]
  · simpa [retained,h] using fermat_gt_one r

theorem fermatProduct (n : ℕ) : (∏ r ∈ Finset.range n, fermat r)+1 = 2^(2^n) := by
  induction n with
  | zero => norm_num [fermat]
  | succ n ih =>
      rw [Finset.prod_range_succ]
      have hh : 2^(2^(n+1)) = (2^(2^n))^2 := by rw [pow_succ 2 n, pow_mul]
      unfold fermat
      simp only [fermat] at ih
      rw [hh]
      have hmul := congrArg (fun t : ℕ => t*(2^(2^n)+1)) ih
      nlinarith

theorem base_succ (n : ℕ) : base (n+1) = base n * retained n := by
  simp [base, Finset.prod_range_succ]

theorem base_positive (n : ℕ) : 0 < base n := by
  apply Finset.prod_pos
  intro i hi
  exact lt_trans (by decide) (retained_gt_one i)

theorem base_lower (n : ℕ) : 2^n ≤ base n := by
  induction n with
  | zero => simp [base]
  | succ n ih =>
      rw [base_succ, pow_succ]
      exact Nat.mul_le_mul ih (retained_gt_one n)

theorem base_relation (n : ℕ) (hn : 11 ≤ n) : base n * G + 1 = 2^(2^n) := by
  induction n, hn using Nat.le_induction with
  | base => norm_num [base, Finset.prod_range_succ, retained, fermat, G]
  | succ n hn ih =>
      have hne : n ≠ 10 := by omega
      have hp : 2^(2^(n+1)) = (2^(2^n))^2 := by rw [pow_succ 2 n, pow_mul]
      rw [base_succ, retained, if_neg hne, fermat, hp]
      have hmul := congrArg (fun t : ℕ => t*(2^(2^n)+1)) ih
      nlinarith

def big (n : ℕ) : ℕ := 2^(2^n)-1

theorem big_relation (n : ℕ) (hn : 11 ≤ n) : big n = base n * G := by
  have h := base_relation n hn
  unfold big
  omega

theorem big_mod_sixteen (n : ℕ) (hn : 2 ≤ n) : big n % 16 = 15 := by
  have h4 : 4 ≤ 2^n := by
    calc
      4 = 2^2 := by decide
      _ ≤ 2^n := Nat.pow_le_pow_right (by decide) hn
  have hd : 16 ∣ 2^(2^n) := by
    simpa using (pow_dvd_pow (2:ℕ) h4)
  have hm : 2^(2^n) % 16 = 0 := Nat.mod_eq_zero_of_dvd hd
  have hpos : 0 < 2^(2^n) := Nat.pow_pos (by decide)
  unfold big
  omega

theorem big_mod_odd (k : ℕ) : Nat.ModEq Q (big (height k)) (2^4096-1) := by
  have hpNat : Nat.ModEq Q (2^9360) 1 := by
    change 2^9360 % Q = 1 % Q
    rw [oddModulusFacts.2.1]
    norm_num [Q]
  have hp : (2 : ZMod Q)^9360 = 1 := by
    simpa only [Nat.cast_pow, Nat.cast_ofNat, Nat.cast_one] using
      (ZMod.natCast_eq_natCast_iff (2^9360) 1 Q).mpr hpNat
  have he := pow_reduce (2 : ZMod Q) 9360 (2^(height k)) hp
  rw [exponentResidue] at he
  have hpos : 1 ≤ 2^(2^(height k)) := Nat.pow_pos (by decide)
  apply (ZMod.natCast_eq_natCast_iff _ _ _).mp
  simpa only [big, Nat.cast_sub hpos, Nat.cast_pow, Nat.cast_ofNat, Nat.cast_one,
    show ((2^4096-1:ℕ):ZMod Q) = (2:ZMod Q)^4096-1 by norm_num [Q]] using
      congrArg (fun t : ZMod Q => t-1) he

theorem big_coprime (k : ℕ) : Nat.Coprime (big (height k)) D := by
  obtain ⟨hDQ, hD, hDG, hGF, hG16, hCD, hC16, hC8191, h8191⟩ := fixedConstants
  have hQ : Nat.Coprime (big (height k)) Q := by
    rw [Nat.Coprime, (big_mod_odd k).gcd_eq]
    exact oddModulusFacts.2.2
  have h16 : Nat.Coprime (big (height k)) 16 := by
    rw [← ZMod.coprime_mod_iff_coprime, big_mod_sixteen _ (by have := height_ge k; omega)]
    decide
  rw [hDQ]
  exact h16.mul_right hQ

theorem base_coprime (k : ℕ) : Nat.Coprime (base (height k)) D := by
  have hb := big_relation (height k) (by have := height_ge k; omega)
  have h := big_coprime k
  rw [hb] at h
  exact h.of_dvd_left (dvd_mul_right _ _)

instance nonzero_D : NeZero D := ⟨by norm_num [D]⟩

noncomputable def multiplier (k : ℕ) : ℕ :=
  ((base (height k) : ZMod D)⁻¹ * (target : ZMod D)).val

noncomputable def bad (k : ℕ) : ℕ := multiplier k * base (height k)

theorem multiplier_lt (k : ℕ) : multiplier k < D := ZMod.val_lt _

theorem bad_mod (k : ℕ) : Nat.ModEq D (bad k) target := by
  apply (ZMod.natCast_eq_natCast_iff _ _ _).mp
  have hw : (multiplier k : ZMod D) =
      (base (height k) : ZMod D)⁻¹ * (target : ZMod D) := ZMod.natCast_zmod_val _
  change ((multiplier k * base (height k) : ℕ) : ZMod D) = _
  rw [Nat.cast_mul, hw]
  calc
    ((base (height k) : ZMod D)⁻¹ * target) * base (height k) =
        ((base (height k) : ZMod D) * (base (height k) : ZMod D)⁻¹) * target := by ring
    _ = target := by rw [ZMod.coe_mul_inv_eq_one _ (base_coprime k), one_mul]

theorem bad_mod_sixteen (k : ℕ) : bad k % 16 = 15 := by
  have h := (bad_mod k).of_dvd (show 16 ∣ D by norm_num [D])
  calc
    bad k % 16 = target % 16 := h
    _ = 15 := by norm_num [target]

theorem multiplier_positive (k : ℕ) : 0 < multiplier k := by
  have h := bad_mod_sixteen k
  by_contra hw
  have hz : multiplier k = 0 := by omega
  simp [bad, hz] at h

theorem bad_lower (k : ℕ) : 2^(height k) ≤ bad k := by
  have hw := multiplier_positive k
  have hb := base_lower (height k)
  unfold bad
  nlinarith

theorem bad_upper (k : ℕ) : bad k < big (height k) := by
  have hw := lt_trans (multiplier_lt k) fixedConstants.2.2.1
  have hb := base_positive (height k)
  rw [big_relation _ (by have := height_ge k; omega)]
  unfold bad
  nlinarith

theorem powModReduce (a m q n : ℕ) (h : Nat.ModEq q (a^m) 1) :
    Nat.ModEq q (a^n) (a^(n%m)) := by
  have hp : (a : ZMod q)^m = 1 := by
    simpa only [Nat.cast_pow, Nat.cast_one] using
      (ZMod.natCast_eq_natCast_iff (a^m) 1 q).mpr h
  apply (ZMod.natCast_eq_natCast_iff _ _ _).mp
  simpa only [Nat.cast_pow] using pow_reduce (a : ZMod q) m n hp

theorem extraExclusion (i : Fin 28) (j : Fin 13) :
    (modulus i + 2^(j:ℕ)) % 8191 ≠ 0 := by
  decide +revert

theorem covering (a : ℕ) : ∃ i : Fin 28, a % period i = residue i := by
  obtain ⟨i, hi⟩ := cover720 ⟨a%720, Nat.mod_lt _ (by decide)⟩
  obtain ⟨hq, hqD, hm, hm720, hd, hp, ht⟩ := tableFacts i
  rw [Nat.mod_mod_of_dvd _ hm720] at hi
  exact ⟨i, hi⟩

theorem no_one_power (k p a : ℕ) (hp : p.Prime) : bad k ≠ p+2^a := by
  intro heq
  obtain ⟨i, hi⟩ := covering a
  obtain ⟨hq, hqD, hm, hm720, hd, hpow, ht⟩ := tableFacts i
  have hper : Nat.ModEq (modulus i) (2^(period i)) 1 := by
    change 2^(period i) % modulus i = 1 % modulus i
    rw [hpow, Nat.mod_eq_of_lt hq]
  have ha := powModReduce 2 (period i) (modulus i) a hper
  rw [hi] at ha
  have hsum : Nat.ModEq (modulus i) (p+2^a) (0+2^a) := by
    simpa only [zero_add, ← heq] using
      ((bad_mod k).of_dvd hqD).trans ((show Nat.ModEq (modulus i) target (2^(residue i)) from ht).trans ha.symm)
  have hprime : modulus i ∣ p := Nat.modEq_zero_iff_dvd.mp
    (Nat.ModEq.add_right_cancel (Nat.ModEq.refl (2^a)) hsum)
  have heqi : modulus i = p := by
    rcases (Nat.dvd_prime hp).mp hprime with h | h
    · omega
    · exact h
  have hN : bad k % 8191 = 0 := by
    have h := (bad_mod k).of_dvd (show 8191 ∣ D by norm_num [D])
    calc
      bad k % 8191 = target % 8191 := h
      _ = 0 := by norm_num [target]
  have hper13 : Nat.ModEq 8191 (2^13) 1 := by decide
  have hpow13 := powModReduce 2 13 8191 a hper13
  have hsum13 := (Nat.ModEq.refl (modulus i)).add hpow13
  have hzero : (modulus i+2^(a%13)) % 8191 = 0 := by
    calc
      (modulus i+2^(a%13)) % 8191 = (modulus i+2^a) % 8191 := hsum13.symm
      _ = bad k % 8191 := by rw [heqi, heq]
      _ = 0 := hN
  exact extraExclusion i ⟨a%13, Nat.mod_lt _ (by decide)⟩ hzero

theorem retained_dvd_fermat (r : ℕ) : retained r ∣ fermat r := by
  by_cases hr : r=10
  · subst r
    obtain ⟨hDQ, hD, hDG, hGF, rest⟩ := fixedConstants
    change 45592577 ∣ 2^(2^10)+1
    refine ⟨G, ?_⟩
    calc
      2^(2^10)+1 = 2^1024+1 := by norm_num
      _ = G*45592577 := hGF.symm
      _ = 45592577*G := Nat.mul_comm _ _
  · simp [retained, hr]

theorem retained_dvd_base (n r : ℕ) (hr : r<n) : retained r ∣ base n := by
  exact Finset.dvd_prod_of_mem retained (Finset.mem_range.mpr hr)

theorem pair_dvd_base (n r s : ℕ) (hrs : r≠s) (hr : r<n) (hs : s<n) :
    retained r * retained s ∣ base n := by
  have hsubset : ({r,s}:Finset ℕ) ⊆ Finset.range n := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact Finset.mem_range.mpr hr
    · exact Finset.mem_range.mpr hs
  have h := Finset.prod_dvd_prod_of_subset ({r,s}:Finset ℕ) (Finset.range n) retained hsubset
  simpa [base, Finset.prod_insert, hrs] using h

theorem retained_gap (n r : ℕ) (hn : 3≤n) (hr : r<n) : retained r+16 < base n := by
  have hp := base_positive n
  by_cases h2 : r=2
  · subst r
    have hdiv := pair_dvd_base n 0 2 (by decide) (by omega) (by omega)
    have hbound := Nat.le_of_dvd hp hdiv
    norm_num [retained, fermat] at hbound ⊢
    omega
  · have hdiv := pair_dvd_base n 2 r (Ne.symm h2) (by omega) hr
    have hbound := Nat.le_of_dvd hp hdiv
    have hval : retained 2=17 := by norm_num [retained, fermat]
    rw [hval] at hbound
    have hret := retained_gt_one r
    omega

theorem base_le_bad (k : ℕ) : base (height k) ≤ bad k := by
  have hw := multiplier_positive k
  unfold bad
  nlinarith

theorem power_residue_zero (a : ℕ) (ha : 4≤a) : 2^a % 16=0 := by
  apply Nat.mod_eq_zero_of_dvd
  simpa using (pow_dvd_pow (2:ℕ) ha)

theorem retained_residues (r : ℕ) :
    retained r %16=1 ∨ retained r %16=3 ∨ retained r %16=5 := by
  by_cases h0 : r=0
  · subst r; norm_num [retained, fermat]
  by_cases h1 : r=1
  · subst r; norm_num [retained, fermat]
  left
  by_cases h10 : r=10
  · simp [retained, h10]
  have hpow : 4≤2^r := by
    calc
      4=2^2 := by decide
      _≤2^r := Nat.pow_le_pow_right (by decide) (by omega)
  rw [retained, if_neg h10, fermat, Nat.add_mod, power_residue_zero _ hpow]

theorem positive_power_residues (b : ℕ) (hb : 0<b) :
    2^b%16=0 ∨ 2^b%16=2 ∨ 2^b%16=4 ∨ 2^b%16=8 := by
  by_cases h : 4≤b
  · exact Or.inl (power_residue_zero b h)
  interval_cases b <;> norm_num at *

theorem fermat_dvd_odd_power (r m : ℕ) (hm : Odd m) :
    fermat r ∣ 2^(2^r*m)+1 := by
  have hroot : (2 : ZMod (fermat r))^(2^r) = -1 := by
    have hz : (2 : ZMod (fermat r))^(2^r)+1=0 := by
      simpa only [fermat, Nat.cast_add, Nat.cast_pow, Nat.cast_ofNat, Nat.cast_one] using
        (ZMod.natCast_self (fermat r))
    exact eq_neg_of_add_eq_zero_left hz
  apply (ZMod.natCast_eq_zero_iff _ _).mp
  simp only [Nat.cast_add, Nat.cast_pow, Nat.cast_ofNat, Nat.cast_one,
    pow_mul, hroot, hm.neg_one_pow, neg_add_cancel]

theorem no_distinct_powers (k p a b : ℕ) (hp : p.Prime) (hb : 0<b) (hba : b<a) :
    bad k ≠ p+2^a+2^b := by
  intro heq
  let n := height k
  have hn : 12≤n := height_ge k
  have hupper := bad_upper k
  have ha : a < 2^n := by
    by_contra h
    have hpow : 2^(2^n) ≤ 2^a := Nat.pow_le_pow_right (by decide) (by omega)
    unfold big at hupper
    change bad k < 2^(2^n)-1 at hupper
    have hNlt : bad k < 2^(2^n) := lt_of_lt_of_le hupper (Nat.sub_le _ _)
    have hLower : 2^a ≤ bad k := by
      rw [heq]
      exact le_trans (Nat.le_add_left _ _) (Nat.le_add_right _ _)
    exact (not_lt_of_ge (le_trans hpow hLower)) hNlt
  obtain ⟨r,m,hm,hdecomp⟩ := Nat.exists_eq_two_pow_mul_odd (show a-b≠0 by omega)
  have hmpos : 0<m := hm.pos
  have hr : r<n := by
    by_contra h
    have hpow : 2^n ≤ 2^r := Nat.pow_le_pow_right (by decide) (by omega)
    have hpowle : 2^r ≤ 2^r*m := by
      simpa using Nat.mul_le_mul_left (2^r) (show 1≤m by omega)
    have hdlt : a-b < 2^n := lt_of_le_of_lt (Nat.sub_le _ _) ha
    omega
  have hF := fermat_dvd_odd_power r m hm
  rw [← hdecomp] at hF
  have hsmall : retained r ∣ 2^(a-b)+1 := dvd_trans (retained_dvd_fermat r) hF
  have hsum : retained r ∣ 2^a+2^b := by
    have he : 2^a+2^b = 2^b*(2^(a-b)+1) := by
      calc
        2^a+2^b = 2^(a-b)*2^b+2^b := by rw [← pow_add, Nat.sub_add_cancel (by omega)]
        _ = 2^b*(2^(a-b)+1) := by ring
    rw [he]
    exact dvd_mul_of_dvd_right hsmall _
  have hN : retained r ∣ bad k :=
    dvd_mul_of_dvd_right (retained_dvd_base n r hr) (multiplier k)
  have hpdiv : retained r ∣ p := by
    apply (Nat.dvd_add_iff_left hsum).mpr
    simpa only [heq, Nat.add_assoc] using hN
  have hp_eq : retained r=p := by
    rcases (Nat.dvd_prime hp).mp hpdiv with h | h
    · have := retained_gt_one r; omega
    · exact h
  have hgap : p+16 < bad k := by
    rw [← hp_eq]
    exact lt_of_lt_of_le (retained_gap n r (by omega) hr) (base_le_bad k)
  have ha4 : 4≤a := by
    by_contra h
    have hpa : 2^a≤8 := by
      calc
        2^a ≤ 2^3 := Nat.pow_le_pow_right (by decide) (by omega)
        _ = 8 := by decide
    have hpb : 2^b≤4 := by
      calc
        2^b ≤ 2^2 := Nat.pow_le_pow_right (by decide) (by omega)
        _ = 4 := by decide
    omega
  have hzero := power_residue_zero a ha4
  have hmod := congrArg (fun z : ℕ => z%16) heq
  have hsum16 : (p+2^a+2^b)%16 = (p%16+2^b%16)%16 := by omega
  rw [bad_mod_sixteen, hsum16] at hmod
  rw [← hp_eq] at hmod
  rcases retained_residues r with hpr | hpr | hpr <;>
    rcases positive_power_residues b hb with hbr | hbr | hbr | hbr <;>
    norm_num [hpr,hbr] at hmod

theorem bad_odd (k : ℕ) : Odd (bad k) := by
  apply Nat.odd_iff.mpr
  have h := bad_mod_sixteen k
  omega

theorem no_zero_power (k p b : ℕ) (hp : p.Prime) (hb : 0<b) :
    bad k ≠ p+1+2^b := by
  intro heq
  have hodd := Nat.odd_iff.mp (bad_odd k)
  have hpow : 2^b%2=0 := by
    have hd : 2 ∣ 2^b := by
      simpa using (pow_dvd_pow (2:ℕ) (show 1≤b by omega))
    exact Nat.mod_eq_zero_of_dvd hd
  have hpeven : p%2=0 := by omega
  have hpdiv : 2∣p := Nat.dvd_of_mod_eq_zero hpeven
  have hp2 : p=2 := by
    rcases (Nat.dvd_prime hp).mp hpdiv with h | h
    · contradiction
    · exact h.symm
  subst p
  have hmod := congrArg (fun z : ℕ => z%16) heq
  rw [bad_mod_sixteen, Nat.add_mod] at hmod
  rcases positive_power_residues b hb with h | h | h | h <;> norm_num [h] at hmod

theorem no_two_powers (k p a b : ℕ) (hp : p.Prime) :
    bad k ≠ p+2^a+2^b := by
  intro heq
  by_cases ha : a=0
  · subst a
    by_cases hb : b=0
    · subst b
      apply no_one_power k p 1 hp
      simpa [Nat.add_assoc] using heq
    · apply no_zero_power k p b hp (Nat.pos_of_ne_zero hb)
      simpa using heq
  by_cases hb : b=0
  · subst b
    apply no_zero_power k p a hp (Nat.pos_of_ne_zero ha)
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using heq
  rcases lt_trichotomy a b with hab | hab | hab
  · apply no_distinct_powers k p b a hp (Nat.pos_of_ne_zero ha) hab
    omega
  · subst b
    apply no_one_power k p (a+1) hp
    rw [pow_succ]
    omega
  · exact no_distinct_powers k p a b hp (Nat.pos_of_ne_zero hb) hab heq

theorem nat_lt_two_pow (n : ℕ) : n<2^n := by
  induction n with
  | zero => decide
  | succ n ih => rw [pow_succ]; omega

theorem arbitrarily_large_counterexamples (bound : ℕ) :
    ∃ N : ℕ, bound<N ∧ Odd N ∧
      ¬∃ p a b : ℕ, p.Prime ∧ N=p+2^a+2^b := by
  refine ⟨bad bound, ?_, bad_odd bound, ?_⟩
  · have h1 : bound<height bound := by unfold height; omega
    exact lt_of_lt_of_le (h1.trans (nat_lt_two_pow _)) (bad_lower bound)
  · rintro ⟨p,a,b,hp,heq⟩
    exact no_two_powers bound p a b hp heq

theorem not_eventually_representable :
    ¬∃ cutoff : ℕ, ∀ N : ℕ, cutoff≤N → Odd N →
      ∃ p a b : ℕ, p.Prime ∧ N=p+2^a+2^b := by
  rintro ⟨cutoff,h⟩
  obtain ⟨N,hN,ho,hnot⟩ := arbitrarily_large_counterexamples cutoff
  exact hnot (h N hN.le ho)

end TLMC39
