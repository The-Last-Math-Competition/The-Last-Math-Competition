/-
  Conjecture 00000007675 — Complete Self-Contained Core Lean 4.19.0 Formalization

  Official Conjecture (00000007675):
    Definition: The valuation v_p([n choose k]_q) at a prime power is defined by
    substituting q=p and then taking the p-adic valuation.
    Conjecture: v_p([n choose k]_p) = sum_{j>=1} (floor(n/p^j) - floor(k/p^j) -
    floor((n-k)/p^j) - carry_j(k,n-k)), where carry_j counts the j-th carry; and
    the alternative LCM-expression holds only when p<=n-k.
    (中文: 特别地该值等于 floor(log_p LCM(k+1,…,n)/(k!(n-k)!)) 型表达式时仅当 p≤n-k。)

  Summary of Formalized Results (Complete First-Principles Core Lean 4 Proofs):
    1. Canonical Gaussian Binomial Coefficients (`qBinom`):
       Defined via the q-Pascal recurrence, and proved to satisfy BOTH the canonical
       q-factorial identity `[k]_q! [n-k]_q! [n choose k]_q = [n]_q!` for all q ∈ ℕ
       and the multiplicative cross-identity
       `(∏_{i=1}^k (q^i - 1)) * [n choose k]_q = ∏_{i=1}^k (q^(n-k+i) - 1)` for q ≥ 2.
    2. Vanishing p-adic Valuation at q = p and All Prime Powers q = p^r (r ≥ 1):
       `[n choose k]_q = 1 + q * m` for all 0 ≤ k ≤ n, so `p ∤ [n choose k]_{p^r}`,
       and hence `v_p([n choose k]_p) = 0` and `v_p([n choose k]_{p^r}) = 0` identically.
    3. Clause 1 Analysis (Base-p Carries & Kummer's Termwise Identity):
       Both the ripple-carry recursion (`carryRipple`) and modulo-p^j carry (`carryResidue`)
       agree for all j, and satisfy Kummer's exact termwise identity
       `⌊(a+b)/p^j⌋ - ⌊a/p^j⌋ - ⌊b/p^j⌋ = carry_j(a, b)` over ℤ, making Clause 1 a
       tautological `0 = 0` cancellation under 1-indexed carries (while failing at
       `(p, n, k) = (2, 2, 1)` under 0-indexed carries).
    4. Clause 2 & Full Conjecture Disproof Across All Parsings and Quantifier Scopes:
       - Exact interval LCM (`lcmInterval`) proved against its universal property `IsIntervalLCM`.
       - Exact rational floor base-p logarithm (`floorLogQ`) proved against its unique
         characterization `p^e ≤ u/v < p^(e+1)` (`IsFloorLogQ`).
       - All 8 natural parsings `lcmExpr1` .. `lcmExpr8` of the Clause 2 LCM-expression are
         formalized and refuted in BOTH directions ("only when p ≤ n - k", "when p ≤ n - k",
         and biconditional "iff p ≤ n - k") on strictly interior parameters `0 < k < n`.
       - Furthermore, for EVERY individual prime p (both p = 2 and every odd prime p ≥ 3),
         the primary literal conjecture fails in BOTH directions at that prime p.
-/

namespace Conjecture00000007675

/-! ## Section 1: Primality and Elementary Arithmetic Helpers -/

/-- Primality predicate on `Nat` from first principles. -/
def IsPrime (p : Nat) : Prop :=
  2 ≤ p ∧ ∀ d : Nat, d ∣ p → d = 1 ∨ d = p

theorem isPrime_two : IsPrime 2 := by
  refine ⟨by omega, ?_⟩
  intro d hd
  have hle : d ≤ 2 := Nat.le_of_dvd (by omega) hd
  rcases hd with ⟨k, hk⟩
  have hcases : d = 0 ∨ d = 1 ∨ d = 2 := by omega
  rcases hcases with rfl | rfl | rfl <;> omega

theorem isPrime_three : IsPrime 3 := by
  refine ⟨by omega, ?_⟩
  intro d hd
  have hle : d ≤ 3 := Nat.le_of_dvd (by omega) hd
  rcases hd with ⟨k, hk⟩
  have hcases : d = 0 ∨ d = 1 ∨ d = 2 ∨ d = 3 := by omega
  rcases hcases with rfl | rfl | rfl | rfl <;> omega

theorem isPrime_five : IsPrime 5 := by
  refine ⟨by omega, ?_⟩
  intro d hd
  have hle : d ≤ 5 := Nat.le_of_dvd (by omega) hd
  rcases hd with ⟨k, hk⟩
  have hcases : d = 0 ∨ d = 1 ∨ d = 2 ∨ d = 3 ∨ d = 4 ∨ d = 5 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl <;> omega

theorem pow_pos_of_pos {b : Nat} (hb : 0 < b) : ∀ e : Nat, 0 < b ^ e
  | 0 => by simp
  | e + 1 => by
    rw [Nat.pow_succ]
    exact Nat.mul_pos (pow_pos_of_pos hb e) hb

theorem pow_le_pow_of_le {b : Nat} (hb : 1 ≤ b) {e₁ e₂ : Nat} (h : e₁ ≤ e₂) :
    b ^ e₁ ≤ b ^ e₂ := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [Nat.pow_add]
  have hd : 1 ≤ b ^ d := pow_pos_of_pos hb d
  calc
    b ^ e₁ = b ^ e₁ * 1 := (Nat.mul_one _).symm
    _ ≤ b ^ e₁ * b ^ d := Nat.mul_le_mul_left _ hd

theorem pow_dvd_pow_of_le (b : Nat) {e₁ e₂ : Nat} (h : e₁ ≤ e₂) :
    b ^ e₁ ∣ b ^ e₂ := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [Nat.pow_add]
  exact ⟨b ^ d, rfl⟩

theorem dvd_of_mul_dvd_mul_left_pos {a b c : Nat} (ha : 0 < a) (h : a * b ∣ a * c) :
    b ∣ c := by
  rcases h with ⟨k, hk⟩
  rw [Nat.mul_assoc] at hk
  exact ⟨k, Nat.eq_of_mul_eq_mul_left ha hk⟩

theorem not_dvd_one_add_mul {p m : Nat} (hp : 2 ≤ p) : ¬ (p ∣ 1 + p * m) := by
  rintro ⟨k, hk⟩
  have h1 : k ≤ m ∨ m + 1 ≤ k := by omega
  rcases h1 with hle | hge
  · have hmul : p * k ≤ p * m := Nat.mul_le_mul_left p hle
    omega
  · have hmul : p * (m + 1) ≤ p * k := Nat.mul_le_mul_left p hge
    rw [Nat.mul_add, Nat.mul_one] at hmul
    omega

/-- Euclidean division uniqueness: if `m * q + r = x` with `r < m`,
    then `x / m = q` and `x % m = r`. -/
theorem div_mod_unique {m q r x : Nat} (hr : r < m) (h : m * q + r = x) :
    x / m = q ∧ x % m = r := by
  have hm : 0 < m := by omega
  have hdm : m * (x / m) + x % m = x := Nat.div_add_mod x m
  have hrm : x % m < m := Nat.mod_lt x hm
  generalize hQ : x / m = Q at hdm
  generalize hR : x % m = R at hdm hrm
  have hcmp : Q < q ∨ q < Q ∨ Q = q := by omega
  rcases hcmp with hlt | hgt | rfl
  · exfalso
    have hle : Q + 1 ≤ q := by omega
    have hmul : m * (Q + 1) ≤ m * q := Nat.mul_le_mul_left m hle
    rw [Nat.mul_add, Nat.mul_one] at hmul
    omega
  · exfalso
    have hle : q + 1 ≤ Q := by omega
    have hmul : m * (q + 1) ≤ m * Q := Nat.mul_le_mul_left m hle
    rw [Nat.mul_add, Nat.mul_one] at hmul
    omega
  · exact ⟨rfl, by omega⟩

theorem div_eq_one_of_bounds {p x : Nat} (h1 : p ≤ x) (h2 : x < p * 2) :
    x / p = 1 :=
  (div_mod_unique (m := p) (q := 1) (r := x - p) (x := x) (by omega) (by omega)).1

/-! ## Section 2: Exact `p`-adic Valuation `padicVal` and Canonical Specification -/

/-- Canonical specification of the `p`-adic valuation `v = v_p(x)`:
    `p^v ∣ x` and `p^(v+1) ∤ x`. -/
def IsPadicVal (p x v : Nat) : Prop :=
  p ^ v ∣ x ∧ ¬ (p ^ (v + 1) ∣ x)

/-- Fuel-bounded auxiliary computation of `v_p(x)`. -/
def padicValAux (p x : Nat) : Nat → Nat
  | 0 => 0
  | fuel + 1 =>
    if x % p = 0 then 1 + padicValAux p (x / p) fuel else 0

/-- Exact `p`-adic valuation `v_p(x)` for `p ≥ 2` and `x ≥ 1` (0 outside domain). -/
def padicVal (p x : Nat) : Nat :=
  if 2 ≤ p ∧ 1 ≤ x then padicValAux p x x else 0

theorem padicValAux_spec {p : Nat} (hp : 2 ≤ p) :
    ∀ {fuel x : Nat}, 1 ≤ x → x ≤ fuel → IsPadicVal p x (padicValAux p x fuel)
  | 0, x, hx1, hxf => by omega
  | fuel + 1, x, hx1, hxf => by
    unfold padicValAux
    by_cases hmod : x % p = 0
    · simp [hmod]
      have hx_eq : p * (x / p) = x := by
        have h := Nat.div_add_mod x p
        omega
      have hq_pos : 1 ≤ x / p := by
        cases hq : x / p with
        | zero => rw [hq, Nat.mul_zero] at hx_eq; omega
        | succ _ => omega
      have hq_lt : x / p < x := by
        have h2 : 2 * (x / p) ≤ p * (x / p) := Nat.mul_le_mul_right (x / p) hp
        omega
      have hq_le : x / p ≤ fuel := by omega
      have ih := padicValAux_spec hp hq_pos hq_le
      let v := padicValAux p (x / p) fuel
      change IsPadicVal p x (1 + v)
      refine ⟨?_, ?_⟩
      · rcases ih.1 with ⟨t, ht⟩
        refine ⟨t, ?_⟩
        calc
          x = p * (x / p) := hx_eq.symm
          _ = p * (p ^ v * t) := by rw [ht]
          _ = (p ^ v * p) * t := by ac_rfl
          _ = p ^ (1 + v) * t := by rw [Nat.add_comm 1 v, Nat.pow_succ]
      · intro hdvd2
        apply ih.2
        have hdvd2' : p * p ^ (v + 1) ∣ p * (x / p) := by
          have hp_eq : p ^ (1 + v + 1) = p * p ^ (v + 1) := by
            rw [Nat.add_comm 1 v, Nat.pow_succ, Nat.mul_comm]
          rw [← hp_eq, hx_eq]
          exact hdvd2
        exact dvd_of_mul_dvd_mul_left_pos (by omega) hdvd2'
    · simp [hmod]
      refine ⟨⟨x, by simp⟩, ?_⟩
      intro hdvd1
      rw [Nat.pow_one] at hdvd1
      exact hmod (Nat.mod_eq_zero_of_dvd hdvd1)

theorem padicVal_spec {p x : Nat} (hp : 2 ≤ p) (hx : 1 ≤ x) :
    IsPadicVal p x (padicVal p x) := by
  unfold padicVal
  have hcond : 2 ≤ p ∧ 1 ≤ x := ⟨hp, hx⟩
  simp [hcond]
  exact padicValAux_spec hp hx (Nat.le_refl x)

theorem isPadicVal_unique {p x v₁ v₂ : Nat}
    (h₁ : IsPadicVal p x v₁) (h₂ : IsPadicVal p x v₂) : v₁ = v₂ := by
  have hcmp : v₁ < v₂ ∨ v₂ < v₁ ∨ v₁ = v₂ := by omega
  rcases hcmp with hlt | hgt | heq
  · exfalso
    have hdvd : p ^ (v₁ + 1) ∣ p ^ v₂ := pow_dvd_pow_of_le p hlt
    exact h₁.2 (Nat.dvd_trans hdvd h₂.1)
  · exfalso
    have hdvd : p ^ (v₂ + 1) ∣ p ^ v₁ := pow_dvd_pow_of_le p hgt
    exact h₂.2 (Nat.dvd_trans hdvd h₁.1)
  · exact heq

theorem padicVal_eq_of_isPadicVal {p x v : Nat} (hp : 2 ≤ p) (hx : 1 ≤ x)
    (hv : IsPadicVal p x v) : padicVal p x = v :=
  isPadicVal_unique (padicVal_spec hp hx) hv

theorem padicVal_eq_zero_of_not_dvd {p x : Nat} (hp : 2 ≤ p) (hx : 1 ≤ x)
    (hndvd : ¬ (p ∣ x)) : padicVal p x = 0 := by
  apply padicVal_eq_of_isPadicVal hp hx
  refine ⟨⟨x, by simp⟩, ?_⟩
  simpa using hndvd

/-! ## Section 3: Gaussian Binomial Coefficients and Vanishing `p`-adic Valuation -/

/-- Standard `q`-integer `[m]_q = 1 + q + ... + q^(m-1)`. -/
def qInt (q : Nat) : Nat → Nat
  | 0 => 0
  | m + 1 => qInt q m + q ^ m

/-- Standard `q`-factorial `[m]_q! = [1]_q * [2]_q * ... * [m]_q`. -/
def qFact (q : Nat) : Nat → Nat
  | 0 => 1
  | m + 1 => qFact q m * qInt q (m + 1)

/-- Gaussian binomial coefficient `[n choose k]_q` defined by the `q`-Pascal recurrence. -/
def qBinom (q : Nat) : Nat → Nat → Nat
  | _, 0 => 1
  | 0, _ + 1 => 0
  | n + 1, k + 1 => qBinom q n (k + 1) + q ^ (n - k) * qBinom q n k

/-- Multiplicative `q`-product `∏_{i=1}^k (q^(s+i) - 1)`. -/
def qFallProd (q s : Nat) : Nat → Nat
  | 0 => 1
  | k + 1 => qFallProd q s k * (q ^ (s + k + 1) - 1)

/-- Classical binomial coefficient `C(n, k)`. -/
def binom : Nat → Nat → Nat
  | _, 0 => 1
  | 0, _ + 1 => 0
  | n + 1, k + 1 => binom n (k + 1) + binom n k

/-- Classical factorial `m!`. -/
def fact : Nat → Nat
  | 0 => 1
  | m + 1 => (m + 1) * fact m

theorem fact_pos : ∀ m : Nat, 0 < fact m
  | 0 => by decide
  | m + 1 => Nat.mul_pos (by omega) (fact_pos m)

theorem qBinom_of_lt (q : Nat) : ∀ {n k : Nat}, n < k → qBinom q n k = 0
  | 0, 0, h => by omega
  | 0, _ + 1, _ => rfl
  | _ + 1, 0, h => by omega
  | n + 1, k + 1, h => by
    have hstep : qBinom q (n + 1) (k + 1) = qBinom q n (k + 1) + q ^ (n - k) * qBinom q n k := rfl
    rw [hstep, qBinom_of_lt q (by omega), qBinom_of_lt q (by omega)]
    simp

theorem qBinom_self (q : Nat) : ∀ n : Nat, qBinom q n n = 1
  | 0 => rfl
  | n + 1 => by
    have hstep : qBinom q (n + 1) (n + 1) = qBinom q n (n + 1) + q ^ (n - n) * qBinom q n n := rfl
    rw [hstep, qBinom_of_lt q (by omega), qBinom_self q n]
    simp

theorem qBinom_one_eq_binom : ∀ n k : Nat, qBinom 1 n k = binom n k
  | 0, 0 => rfl
  | _ + 1, 0 => rfl
  | 0, _ + 1 => rfl
  | n + 1, k + 1 => by
    have h1 : qBinom 1 (n + 1) (k + 1) = qBinom 1 n (k + 1) + 1 ^ (n - k) * qBinom 1 n k := rfl
    have h2 : binom (n + 1) (k + 1) = binom n (k + 1) + binom n k := rfl
    rw [h1, h2, qBinom_one_eq_binom n (k + 1), qBinom_one_eq_binom n k]
    simp

theorem qInt_add (q a : Nat) : ∀ b : Nat, qInt q a + q ^ a * qInt q b = qInt q (a + b)
  | 0 => by simp [qInt]
  | b + 1 => by
    calc
      qInt q a + q ^ a * qInt q (b + 1)
          = qInt q a + q ^ a * (qInt q b + q ^ b) := rfl
      _ = (qInt q a + q ^ a * qInt q b) + q ^ a * q ^ b := by
          rw [Nat.mul_add, Nat.add_assoc]
      _ = qInt q (a + b) + q ^ (a + b) := by
          rw [qInt_add q a b, ← Nat.pow_add]
      _ = qInt q (a + (b + 1)) := rfl

theorem qInt_pos_of_pos {q m : Nat} (hq : 1 ≤ q) (hm : 1 ≤ m) : 0 < qInt q m := by
  cases m with
  | zero => omega
  | succ m' =>
    unfold qInt
    have hp : 0 < q ^ m' := pow_pos_of_pos hq m'
    omega

theorem qFact_pos {q : Nat} (hq : 1 ≤ q) : ∀ m : Nat, 0 < qFact q m
  | 0 => by simp [qFact]
  | m + 1 => Nat.mul_pos (qFact_pos hq m) (qInt_pos_of_pos hq (by omega))

/-- Canonical `q`-factorial identity:
    `[k]_q! * [n - k]_q! * [n choose k]_q = [n]_q!` for all `q ∈ ℕ` and `k ≤ n`. -/
theorem qBinom_mul_qFact (q : Nat) :
    ∀ n k : Nat, k ≤ n → qFact q k * qFact q (n - k) * qBinom q n k = qFact q n
  | n, 0, _ => by
    simp [qFact, qBinom]
  | 0, _ + 1, hk => by omega
  | n + 1, k + 1, hk => by
    by_cases hkn : k = n
    · subst hkn
      rw [Nat.sub_self, qBinom_self]
      simp [qFact]
    · have hsub : n + 1 - (k + 1) = n - k := by omega
      obtain ⟨m, hm⟩ : ∃ m : Nat, n - k = m + 1 := ⟨n - (k + 1), by omega⟩
      have hm' : n - (k + 1) = m := by omega
      have hstep :
          qBinom q (n + 1) (k + 1) = qBinom q n (k + 1) + q ^ (n - k) * qBinom q n k := rfl
      rw [hsub, hstep, Nat.mul_add]
      have ih1 : qFact q (k + 1) * qFact q m * qBinom q n (k + 1) = qFact q n := by
        rw [← hm']
        exact qBinom_mul_qFact q n (k + 1) (by omega)
      have ih2 : qFact q k * qFact q (n - k) * qBinom q n k = qFact q n :=
        qBinom_mul_qFact q n k (by omega)
      have term1 :
          qFact q (k + 1) * qFact q (n - k) * qBinom q n (k + 1)
            = qInt q (n - k) * qFact q n := by
        rw [hm]
        have hqf_m : qFact q (m + 1) = qFact q m * qInt q (m + 1) := rfl
        rw [hqf_m]
        calc
          qFact q (k + 1) * (qFact q m * qInt q (m + 1)) * qBinom q n (k + 1)
              = qInt q (m + 1) * (qFact q (k + 1) * qFact q m * qBinom q n (k + 1)) := by ac_rfl
          _ = qInt q (m + 1) * qFact q n := by rw [ih1]
      have term2 :
          qFact q (k + 1) * qFact q (n - k) * (q ^ (n - k) * qBinom q n k)
            = (q ^ (n - k) * qInt q (k + 1)) * qFact q n := by
        have hqf_k : qFact q (k + 1) = qFact q k * qInt q (k + 1) := rfl
        rw [hqf_k]
        calc
          (qFact q k * qInt q (k + 1)) * qFact q (n - k) * (q ^ (n - k) * qBinom q n k)
              = (q ^ (n - k) * qInt q (k + 1)) * (qFact q k * qFact q (n - k) * qBinom q n k) := by
                ac_rfl
          _ = (q ^ (n - k) * qInt q (k + 1)) * qFact q n := by rw [ih2]
      rw [term1, term2, ← Nat.add_mul, qInt_add]
      have hsum : n - k + (k + 1) = n + 1 := by omega
      have hqf_n : qFact q (n + 1) = qFact q n * qInt q (n + 1) := rfl
      rw [hsum, hqf_n, Nat.mul_comm]

theorem sub_one_mul_qInt {q : Nat} (hq : 1 ≤ q) :
    ∀ m : Nat, (q - 1) * qInt q m = q ^ m - 1
  | 0 => by simp [qInt]
  | m + 1 => by
    unfold qInt
    rw [Nat.mul_add, sub_one_mul_qInt hq m]
    have hpow : 1 ≤ q ^ m := pow_pos_of_pos hq m
    have hmul : (q - 1) * q ^ m = q * q ^ m - q ^ m := by
      rw [Nat.sub_mul, Nat.one_mul]
    rw [hmul, Nat.pow_succ, Nat.mul_comm (q ^ m) q]
    have hle : q ^ m ≤ q * q ^ m := by
      calc
        q ^ m = 1 * q ^ m := (Nat.one_mul _).symm
        _ ≤ q * q ^ m := Nat.mul_le_mul_right _ hq
    omega

theorem pow_sub_one_mul_qFact {q : Nat} (hq : 1 ≤ q) :
    ∀ m : Nat, (q - 1) ^ m * qFact q m = qFallProd q 0 m
  | 0 => by simp [qFact, qFallProd]
  | m + 1 => by
    unfold qFact qFallProd
    rw [Nat.pow_succ]
    calc
      ((q - 1) ^ m * (q - 1)) * (qFact q m * qInt q (m + 1))
          = ((q - 1) ^ m * qFact q m) * ((q - 1) * qInt q (m + 1)) := by ac_rfl
      _ = qFallProd q 0 m * (q ^ (0 + m + 1) - 1) := by
          rw [pow_sub_one_mul_qFact hq m, sub_one_mul_qInt hq (m + 1), Nat.zero_add]

theorem qFallProd_split (q a : Nat) :
    ∀ b : Nat, qFallProd q 0 (a + b) = qFallProd q 0 a * qFallProd q a b
  | 0 => by simp [qFallProd]
  | b + 1 => by
    have h1 : qFallProd q 0 (a + (b + 1))
        = qFallProd q 0 (a + b) * (q ^ (0 + (a + b) + 1) - 1) := rfl
    have h2 : qFallProd q a (b + 1)
        = qFallProd q a b * (q ^ (a + b + 1) - 1) := rfl
    rw [h1, h2, qFallProd_split q a b]
    have hidx : 0 + (a + b) + 1 = a + b + 1 := by omega
    rw [hidx, Nat.mul_assoc]

theorem qFallProd_pos {q : Nat} (hq : 2 ≤ q) (s : Nat) :
    ∀ k : Nat, 0 < qFallProd q s k
  | 0 => by simp [qFallProd]
  | k + 1 => by
    unfold qFallProd
    have hpow : 2 ≤ q ^ (s + k + 1) := by
      calc
        2 ≤ q ^ 1 := by simp; omega
        _ ≤ q ^ (s + k + 1) := pow_le_pow_of_le (by omega) (by omega)
    exact Nat.mul_pos (qFallProd_pos hq s k) (by omega)

/-- Canonical multiplicative cross-identity for Gaussian binomial coefficients:
    `(∏_{i=1}^k (q^i - 1)) * [n choose k]_q = ∏_{i=1}^k (q^(n-k+i) - 1)` for `q ≥ 2`, `k ≤ n`. -/
theorem qFallProd_mul_qBinom {q n k : Nat} (hq : 2 ≤ q) (hk : k ≤ n) :
    qFallProd q 0 k * qBinom q n k = qFallProd q (n - k) k := by
  have hqf := qBinom_mul_qFact q n k hk
  have h1 : 1 ≤ q := by omega
  have hmul :
      qFallProd q 0 (n - k) * (qFallProd q 0 k * qBinom q n k)
        = qFallProd q 0 (n - k) * qFallProd q (n - k) k := by
    calc
      qFallProd q 0 (n - k) * (qFallProd q 0 k * qBinom q n k)
          = ((q - 1) ^ (n - k) * qFact q (n - k))
              * (((q - 1) ^ k * qFact q k) * qBinom q n k) := by
            rw [pow_sub_one_mul_qFact h1 (n - k), pow_sub_one_mul_qFact h1 k]
      _ = ((q - 1) ^ k * (q - 1) ^ (n - k))
            * (qFact q k * qFact q (n - k) * qBinom q n k) := by ac_rfl
      _ = (q - 1) ^ (k + (n - k)) * qFact q n := by
            rw [← Nat.pow_add, hqf]
      _ = (q - 1) ^ n * qFact q n := by rw [Nat.add_sub_of_le hk]
      _ = qFallProd q 0 n := pow_sub_one_mul_qFact h1 n
      _ = qFallProd q 0 ((n - k) + k) := by rw [Nat.sub_add_cancel hk]
      _ = qFallProd q 0 (n - k) * qFallProd q (n - k) k := qFallProd_split q (n - k) k
  exact Nat.eq_of_mul_eq_mul_left (qFallProd_pos hq 0 (n - k)) hmul

/-- Key arithmetic theorem: `[n choose k]_q ≡ 1 (mod q)` for ALL `q ∈ ℕ` and `0 ≤ k ≤ n`. -/
theorem qBinom_eq_one_add_mul (q : Nat) :
    ∀ n k : Nat, k ≤ n → ∃ m : Nat, qBinom q n k = 1 + q * m
  | n, 0, _ => ⟨0, by simp [qBinom]⟩
  | 0, _ + 1, hk => by omega
  | n + 1, k + 1, hk => by
    by_cases hkn : k = n
    · subst hkn
      exact ⟨0, by simp [qBinom_self]⟩
    · obtain ⟨d, hd⟩ : ∃ d : Nat, n - k = d + 1 := ⟨n - k - 1, by omega⟩
      obtain ⟨m₁, hm₁⟩ := qBinom_eq_one_add_mul q n (k + 1) (by omega)
      refine ⟨m₁ + q ^ d * qBinom q n k, ?_⟩
      have hstep :
          qBinom q (n + 1) (k + 1) = qBinom q n (k + 1) + q ^ (n - k) * qBinom q n k := rfl
      rw [hstep, hm₁, hd, Nat.pow_succ]
      calc
        1 + q * m₁ + q ^ d * q * qBinom q n k
            = 1 + (q * m₁ + q * (q ^ d * qBinom q n k)) := by ac_rfl
        _ = 1 + q * (m₁ + q ^ d * qBinom q n k) := by rw [← Nat.mul_add]

theorem qBinom_pos (q n k : Nat) (hk : k ≤ n) : 1 ≤ qBinom q n k := by
  obtain ⟨m, hm⟩ := qBinom_eq_one_add_mul q n k hk
  omega

/-- Exact value of `v_p([n choose k]_q)` whenever `p ∣ q` (for any integer `p ≥ 2`):
    `v_p([n choose k]_q) = 0` identically for all `0 ≤ k ≤ n`. -/
theorem padicVal_qBinom_of_dvd {p q n k : Nat} (hp : 2 ≤ p) (hdvd : p ∣ q) (hk : k ≤ n) :
    padicVal p (qBinom q n k) = 0 := by
  obtain ⟨m, hm⟩ := qBinom_eq_one_add_mul q n k hk
  rcases hdvd with ⟨t, rfl⟩
  apply padicVal_eq_zero_of_not_dvd hp (qBinom_pos (p * t) n k hk)
  have heq : qBinom (p * t) n k = 1 + p * (t * m) := by
    rw [hm, Nat.mul_assoc]
  rw [heq]
  exact not_dvd_one_add_mul hp

/-- Universal vanishing theorem at `q = p`:
    `v_p([n choose k]_p) = 0` for every prime `p` and all `0 ≤ k ≤ n`. -/
theorem padicVal_qBinom_prime_eq_zero {p n k : Nat} (hp : IsPrime p) (hk : k ≤ n) :
    padicVal p (qBinom p n k) = 0 :=
  padicVal_qBinom_of_dvd hp.1 (Nat.dvd_refl p) hk

/-- Universal vanishing theorem at every prime power `q = p^r` (`r ≥ 1`):
    `v_p([n choose k]_{p^r}) = 0` for every prime `p`, every `r ≥ 1`, and all `0 ≤ k ≤ n`. -/
theorem padicVal_qBinom_prime_pow_eq_zero {p r n k : Nat}
    (hp : IsPrime p) (hr : 1 ≤ r) (hk : k ≤ n) :
    padicVal p (qBinom (p ^ r) n k) = 0 := by
  have hdvd : p ∣ p ^ r := by
    simpa using pow_dvd_pow_of_le p hr
  exact padicVal_qBinom_of_dvd hp.1 hdvd hk

/-! ## Section 4: Clause 1 — Base-`p` Carries and Kummer's Termwise Identity -/

/-- The `i`-th base-`p` digit of `x` (`0`-indexed: coefficient of `p^i`). -/
def baseDigit (p x i : Nat) : Nat :=
  (x / (p ^ i)) % p

/-- Standard base-`p` ripple-carry recursion: `carryRipple p a b j` is the carry into `p^j`
    (so `j ≥ 1` indexes the `j`-th carry, out of digit `j - 1` into `p^j`). -/
def carryRipple (p a b : Nat) : Nat → Nat
  | 0 => 0
  | j + 1 => (baseDigit p a j + baseDigit p b j + carryRipple p a b j) / p

/-- Modulo-`p^j` characterization of the `j`-th base-`p` carry. -/
def carryResidue (p a b j : Nat) : Nat :=
  if p ^ j ≤ (a % (p ^ j)) + (b % (p ^ j)) then 1 else 0

theorem mod_pow_succ_decomp {p : Nat} (hp : 2 ≤ p) (x j : Nat) :
    x % (p ^ (j + 1)) = p ^ j * baseDigit p x j + x % (p ^ j) := by
  have hpj : 0 < p ^ j := pow_pos_of_pos (by omega) j
  have hxr : p ^ j * (x / (p ^ j)) + x % (p ^ j) = x := Nat.div_add_mod x (p ^ j)
  have hr_lt : x % (p ^ j) < p ^ j := Nat.mod_lt x hpj
  have hqd : p * ((x / (p ^ j)) / p) + baseDigit p x j = x / (p ^ j) :=
    Nat.div_add_mod (x / (p ^ j)) p
  have hd_lt : baseDigit p x j < p := Nat.mod_lt (x / (p ^ j)) (by omega)
  have hx_eq :
      p ^ (j + 1) * ((x / (p ^ j)) / p) + (p ^ j * baseDigit p x j + x % (p ^ j)) = x := by
    calc
      p ^ (j + 1) * ((x / (p ^ j)) / p) + (p ^ j * baseDigit p x j + x % (p ^ j))
          = (p ^ j * p) * ((x / (p ^ j)) / p) + (p ^ j * baseDigit p x j + x % (p ^ j)) := by
            rw [Nat.pow_succ]
      _ = (p ^ j * (p * ((x / (p ^ j)) / p)) + p ^ j * baseDigit p x j) + x % (p ^ j) := by ac_rfl
      _ = p ^ j * (p * ((x / (p ^ j)) / p) + baseDigit p x j) + x % (p ^ j) := by
            rw [← Nat.mul_add]
      _ = p ^ j * (x / (p ^ j)) + x % (p ^ j) := by rw [hqd]
      _ = x := hxr
  have hrem_lt : p ^ j * baseDigit p x j + x % (p ^ j) < p ^ (j + 1) := by
    have hd_le : baseDigit p x j + 1 ≤ p := by omega
    calc
      p ^ j * baseDigit p x j + x % (p ^ j)
          < p ^ j * baseDigit p x j + p ^ j := by omega
      _ = p ^ j * baseDigit p x j + p ^ j * 1 := by rw [Nat.mul_one]
      _ = p ^ j * (baseDigit p x j + 1) := (Nat.mul_add _ _ _).symm
      _ ≤ p ^ j * p := Nat.mul_le_mul_left _ hd_le
      _ = p ^ (j + 1) := (Nat.pow_succ p j).symm
  exact (div_mod_unique hrem_lt hx_eq).2

/-- Equivalence of schoolbook ripple-carry addition and modulo-`p^j` carry for all `j`. -/
theorem carryRipple_eq_carryResidue {p : Nat} (hp : 2 ≤ p) (a b : Nat) :
    ∀ j : Nat, carryRipple p a b j = carryResidue p a b j
  | 0 => by
    unfold carryRipple carryResidue
    simp [Nat.mod_one]
  | j + 1 => by
    unfold carryRipple
    rw [carryRipple_eq_carryResidue hp a b j]
    unfold carryResidue
    have hpj : 0 < p ^ j := pow_pos_of_pos (by omega) j
    have ha := mod_pow_succ_decomp hp a j
    have hb := mod_pow_succ_decomp hp b j
    rw [ha, hb, Nat.pow_succ]
    have hda : baseDigit p a j < p := Nat.mod_lt _ (by omega)
    have hdb : baseDigit p b j < p := Nat.mod_lt _ (by omega)
    have hra : a % (p ^ j) < p ^ j := Nat.mod_lt _ hpj
    have hrb : b % (p ^ j) < p ^ j := Nat.mod_lt _ hpj
    generalize baseDigit p a j = da at hda ⊢
    generalize baseDigit p b j = db at hdb ⊢
    generalize a % (p ^ j) = ra at hra ⊢
    generalize b % (p ^ j) = rb at hrb ⊢
    by_cases hprev : p ^ j ≤ ra + rb
    · simp [hprev]
      have hsum :
          (p ^ j * da + ra) + (p ^ j * db + rb)
            = p ^ j * (da + db + 1) + (ra + rb - p ^ j) := by
        have hs : ra + rb = p ^ j + (ra + rb - p ^ j) := by omega
        calc
          (p ^ j * da + ra) + (p ^ j * db + rb)
              = (p ^ j * da + p ^ j * db) + (ra + rb) := by ac_rfl
          _ = (p ^ j * da + p ^ j * db) + (p ^ j * 1 + (ra + rb - p ^ j)) := by
              rw [Nat.mul_one, ← hs]
          _ = (p ^ j * da + p ^ j * db + p ^ j * 1) + (ra + rb - p ^ j) := by ac_rfl
          _ = p ^ j * (da + db + 1) + (ra + rb - p ^ j) := by
              rw [← Nat.mul_add, ← Nat.mul_add]
      rw [hsum]
      by_cases hdig : p ≤ da + db + 1
      · have hge : p ^ j * p ≤ p ^ j * (da + db + 1) + (ra + rb - p ^ j) := by
          have hm : p ^ j * p ≤ p ^ j * (da + db + 1) := Nat.mul_le_mul_left _ hdig
          omega
        simp [hge]
        exact div_eq_one_of_bounds hdig (by omega)
      · have hlt_pow : p ^ j * (da + db + 1) + (ra + rb - p ^ j) < p ^ j * p := by
          calc
            p ^ j * (da + db + 1) + (ra + rb - p ^ j)
                < p ^ j * (da + db + 1) + p ^ j := by omega
            _ = p ^ j * (da + db + 1) + p ^ j * 1 := by rw [Nat.mul_one]
            _ = p ^ j * (da + db + 1 + 1) := (Nat.mul_add _ _ _).symm
            _ ≤ p ^ j * p := Nat.mul_le_mul_left _ (by omega)
        have hnot : ¬ (p ^ j * p ≤ p ^ j * (da + db + 1) + (ra + rb - p ^ j)) := by omega
        simp [hnot]
        exact Nat.div_eq_of_lt (by omega)
    · simp [hprev]
      have hsum :
          (p ^ j * da + ra) + (p ^ j * db + rb) = p ^ j * (da + db) + (ra + rb) := by
        calc
          (p ^ j * da + ra) + (p ^ j * db + rb)
              = (p ^ j * da + p ^ j * db) + (ra + rb) := by ac_rfl
          _ = p ^ j * (da + db) + (ra + rb) := by rw [← Nat.mul_add]
      rw [hsum]
      by_cases hdig : p ≤ da + db
      · have hge : p ^ j * p ≤ p ^ j * (da + db) + (ra + rb) := by
          have hm : p ^ j * p ≤ p ^ j * (da + db) := Nat.mul_le_mul_left _ hdig
          omega
        simp [hge]
        exact div_eq_one_of_bounds hdig (by omega)
      · have hlt_pow : p ^ j * (da + db) + (ra + rb) < p ^ j * p := by
          calc
            p ^ j * (da + db) + (ra + rb) < p ^ j * (da + db) + p ^ j := by omega
            _ = p ^ j * (da + db) + p ^ j * 1 := by rw [Nat.mul_one]
            _ = p ^ j * (da + db + 1) := (Nat.mul_add _ _ _).symm
            _ ≤ p ^ j * p := Nat.mul_le_mul_left _ (by omega)
        have hnot : ¬ (p ^ j * p ≤ p ^ j * (da + db) + (ra + rb)) := by omega
        simp [hnot]
        exact Nat.div_eq_of_lt (by omega)

/-- Kummer's exact termwise identity:
    `(a + b) / p^j = a / p^j + b / p^j + carry_j(a, b)` for all `p ≥ 2`, `a, b, j ∈ ℕ`. -/
theorem kummer_div_add_carry {p : Nat} (hp : 2 ≤ p) (a b j : Nat) :
    (a + b) / (p ^ j) = a / (p ^ j) + b / (p ^ j) + carryRipple p a b j := by
  rw [carryRipple_eq_carryResidue hp a b j]
  unfold carryResidue
  have hm : 0 < p ^ j := pow_pos_of_pos (by omega) j
  have ha := Nat.div_add_mod a (p ^ j)
  have hb := Nat.div_add_mod b (p ^ j)
  have hra : a % (p ^ j) < p ^ j := Nat.mod_lt a hm
  have hrb : b % (p ^ j) < p ^ j := Nat.mod_lt b hm
  generalize p ^ j = m at hm ha hb hra hrb ⊢
  generalize a / m = qa at ha ⊢
  generalize b / m = qb at hb ⊢
  generalize a % m = ra at ha hra ⊢
  generalize b % m = rb at hb hrb ⊢
  by_cases hc : m ≤ ra + rb
  · simp [hc]
    have hsum : m * (qa + qb + 1) + (ra + rb - m) = a + b := by
      rw [Nat.mul_add, Nat.mul_add, Nat.mul_one]
      omega
    exact (div_mod_unique (by omega) hsum).1
  · simp [hc]
    have hsum : m * (qa + qb) + (ra + rb) = a + b := by
      rw [Nat.mul_add]
      omega
    exact (div_mod_unique (by omega) hsum).1

/-- The `j`-th summand of Clause 1 over exact integers `ℤ` (no truncated subtraction):
    `⌊n/p^j⌋ - ⌊k/p^j⌋ - ⌊(n-k)/p^j⌋ - carry_j(k, n-k)`. -/
def clause1Term (p n k j : Nat) : Int :=
  ((n / (p ^ j) : Nat) : Int) - ((k / (p ^ j) : Nat) : Int)
    - (((n - k) / (p ^ j) : Nat) : Int) - (carryRipple p k (n - k) j : Int)

/-- Partial sum `∑_{j=1}^J clause1Term p n k j`. -/
def clause1Sum (p n k : Nat) : Nat → Int
  | 0 => 0
  | J + 1 => clause1Sum p n k J + clause1Term p n k (J + 1)

/-- Under standard 1-indexed carries, every summand of Clause 1 is identically `0`. -/
theorem clause1Term_eq_zero {p n k : Nat} (hp : 2 ≤ p) (hk : k ≤ n) (j : Nat) :
    clause1Term p n k j = 0 := by
  unfold clause1Term
  have hn : k + (n - k) = n := Nat.add_sub_of_le hk
  have hkummer := kummer_div_add_carry hp k (n - k) j
  rw [hn] at hkummer
  omega

/-- Finite support: for `n < p^j`, all four parts of `clause1Term` vanish individually. -/
theorem clause1_components_zero_of_lt {p n k j : Nat}
    (hp : 2 ≤ p) (hk : k ≤ n) (hlt : n < p ^ j) :
    n / (p ^ j) = 0 ∧ k / (p ^ j) = 0 ∧ (n - k) / (p ^ j) = 0 ∧
      carryRipple p k (n - k) j = 0 := by
  refine ⟨Nat.div_eq_of_lt hlt, Nat.div_eq_of_lt (by omega), Nat.div_eq_of_lt (by omega), ?_⟩
  rw [carryRipple_eq_carryResidue hp k (n - k) j]
  unfold carryResidue
  have h1 : k % (p ^ j) = k := Nat.mod_eq_of_lt (by omega)
  have h2 : (n - k) % (p ^ j) = n - k := Nat.mod_eq_of_lt (by omega)
  rw [h1, h2]
  have hnot : ¬ (p ^ j ≤ k + (n - k)) := by omega
  simp [hnot]

/-- Clause 1 holds tautologically (`0 = 0`) under 1-indexed carries for every prime `p`. -/
theorem clause1_holds_under_one_indexed_carry {p n k : Nat}
    (hp : IsPrime p) (hk : k ≤ n) (J : Nat) :
    (padicVal p (qBinom p n k) : Int) = clause1Sum p n k J := by
  rw [padicVal_qBinom_prime_eq_zero hp hk]
  induction J with
  | zero => rfl
  | succ J ih =>
    unfold clause1Sum
    rw [← ih, clause1Term_eq_zero hp.1 hk (J + 1)]
    simp

/-- Shifted 0-indexed carry variant (`carryRipple p k (n - k) (j + 1)` summed for `j ≥ 1`). -/
def clause1TermZeroIndexed (p n k j : Nat) : Int :=
  ((n / (p ^ j) : Nat) : Int) - ((k / (p ^ j) : Nat) : Int)
    - (((n - k) / (p ^ j) : Nat) : Int) - (carryRipple p k (n - k) (j + 1) : Int)

def clause1SumZeroIndexed (p n k : Nat) : Nat → Int
  | 0 => 0
  | J + 1 => clause1SumZeroIndexed p n k J + clause1TermZeroIndexed p n k (J + 1)

/-- Under 0-indexed carries, Clause 1 fails already at `(p, n, k) = (2, 2, 1)`. -/
theorem clause1_fails_under_zero_indexed_carry :
    (padicVal 2 (qBinom 2 2 1) : Int) ≠ clause1SumZeroIndexed 2 2 1 2 ∧
    ∀ j : Nat, 2 < j → clause1TermZeroIndexed 2 2 1 j = 0 := by
  refine ⟨by decide, ?_⟩
  intro j hj
  have hpow : 8 ≤ 2 ^ j := by
    calc
      8 = 2 ^ 3 := by decide
      _ ≤ 2 ^ j := pow_le_pow_of_le (by omega) (by omega)
  unfold clause1TermZeroIndexed
  have h1 : 2 / (2 ^ j) = 0 := Nat.div_eq_of_lt (by omega)
  have h2 : 1 / (2 ^ j) = 0 := Nat.div_eq_of_lt (by omega)
  have hc : carryRipple 2 1 1 (j + 1) = 0 := by
    rw [carryRipple_eq_carryResidue (by omega) 1 1 (j + 1)]
    unfold carryResidue
    have hp1 : 16 ≤ 2 ^ (j + 1) := by rw [Nat.pow_succ]; omega
    have hm1 : 1 % (2 ^ (j + 1)) = 1 := Nat.mod_eq_of_lt (by omega)
    rw [hm1]
    have hnot : ¬ (2 ^ (j + 1) ≤ 1 + 1) := by omega
    simp [hnot]
  simp [h1, h2, hc]

/-! ## Section 5: Interval LCM and Exact Floor Base-`p` Logarithm over `ℚ⁺` -/

/-- Auxiliary product/LCM over `{lo, lo + 1, ..., lo + count - 1}`. -/
def lcmRangeAux (lo : Nat) : Nat → Nat
  | 0 => 1
  | count + 1 => Nat.lcm (lcmRangeAux lo count) (lo + count)

/-- Exact least common multiple of all integers `m` with `lo ≤ m ≤ hi` (`1` if empty). -/
def lcmInterval (lo hi : Nat) : Nat :=
  if lo ≤ hi then lcmRangeAux lo (hi - lo + 1) else 1

/-- Canonical universal specification of `L = LCM(lo, ..., hi)`. -/
def IsIntervalLCM (lo hi L : Nat) : Prop :=
  0 < L ∧
  (∀ m : Nat, lo ≤ m → m ≤ hi → m ∣ L) ∧
  (∀ M : Nat, (∀ m : Nat, lo ≤ m → m ≤ hi → m ∣ M) → L ∣ M)

theorem lcmRangeAux_pos {lo : Nat} (hlo : 1 ≤ lo) : ∀ count : Nat, 0 < lcmRangeAux lo count
  | 0 => by simp [lcmRangeAux]
  | count + 1 => by
    unfold lcmRangeAux
    have ha : 0 < lcmRangeAux lo count := lcmRangeAux_pos hlo count
    have hb : 0 < lo + count := by omega
    have hab_pos : 0 < lcmRangeAux lo count * (lo + count) := Nat.mul_pos ha hb
    have hdvd_prod :
        Nat.lcm (lcmRangeAux lo count) (lo + count) ∣ lcmRangeAux lo count * (lo + count) :=
      Nat.lcm_dvd ⟨lo + count, rfl⟩ ⟨lcmRangeAux lo count, Nat.mul_comm _ _⟩
    cases hz : Nat.lcm (lcmRangeAux lo count) (lo + count) with
    | zero =>
      exfalso
      rw [hz] at hdvd_prod
      rcases hdvd_prod with ⟨k, hk⟩
      rw [Nat.zero_mul] at hk
      omega
    | succ _ => omega

theorem lcmRangeAux_dvd_all (lo : Nat) :
    ∀ (count m : Nat), lo ≤ m → m < lo + count → m ∣ lcmRangeAux lo count
  | 0, m, h1, h2 => by omega
  | count + 1, m, h1, h2 => by
    unfold lcmRangeAux
    by_cases hlast : m = lo + count
    · subst hlast
      exact Nat.dvd_lcm_right _ _
    · have hlt : m < lo + count := by omega
      exact Nat.dvd_trans (lcmRangeAux_dvd_all lo count m h1 hlt) (Nat.dvd_lcm_left _ _)

theorem lcmRangeAux_minimal (lo : Nat) :
    ∀ (count M : Nat), (∀ m : Nat, lo ≤ m → m < lo + count → m ∣ M) →
      lcmRangeAux lo count ∣ M
  | 0, M, _ => ⟨M, by simp [lcmRangeAux]⟩
  | count + 1, M, hM => by
    unfold lcmRangeAux
    apply Nat.lcm_dvd
    · exact lcmRangeAux_minimal lo count M (fun m hm1 hm2 => hM m hm1 (by omega))
    · exact hM (lo + count) (by omega) (by omega)

/-- `lcmInterval lo hi` satisfies the exact universal property of `LCM(lo, ..., hi)`. -/
theorem lcmInterval_spec {lo hi : Nat} (hlo : 1 ≤ lo) :
    IsIntervalLCM lo hi (lcmInterval lo hi) := by
  unfold lcmInterval
  by_cases hle : lo ≤ hi
  · simp [hle]
    refine ⟨lcmRangeAux_pos hlo (hi - lo + 1), ?_, ?_⟩
    · intro m hm1 hm2
      exact lcmRangeAux_dvd_all lo (hi - lo + 1) m hm1 (by omega)
    · intro M hM
      exact lcmRangeAux_minimal lo (hi - lo + 1) M (fun m hm1 hm2 => hM m hm1 (by omega))
  · simp [hle]
    refine ⟨by omega, ?_, ?_⟩
    · intro m hm1 hm2; omega
    · intro M _; exact ⟨M, by simp⟩

theorem isIntervalLCM_unique {lo hi L₁ L₂ : Nat}
    (h₁ : IsIntervalLCM lo hi L₁) (h₂ : IsIntervalLCM lo hi L₂) : L₁ = L₂ :=
  Nat.dvd_antisymm (h₁.2.2 L₂ h₂.2.1) (h₂.2.2 L₁ h₁.2.1)

/-- Fuel-bounded discrete floor logarithm `⌊log_p(q)⌋` on positive naturals. -/
def floorLogNatAux (p q : Nat) : Nat → Nat
  | 0 => 0
  | fuel + 1 =>
    if q < p then 0 else 1 + floorLogNatAux p (q / p) fuel

/-- Discrete floor logarithm `⌊log_p(q)⌋` for `p ≥ 2` and `q ≥ 1`. -/
def floorLogNat (p q : Nat) : Nat :=
  floorLogNatAux p q q

theorem floorLogNatAux_spec {p : Nat} (hp : 2 ≤ p) :
    ∀ {fuel q : Nat}, 1 ≤ q → q ≤ fuel →
      p ^ (floorLogNatAux p q fuel) ≤ q ∧ q < p ^ (floorLogNatAux p q fuel + 1)
  | 0, q, hq1, hqf => by omega
  | fuel + 1, q, hq1, hqf => by
    unfold floorLogNatAux
    by_cases hlt : q < p
    · simp [hlt]
      omega
    · simp [hlt]
      have hpq : p ≤ q := by omega
      have hdiv_mod := Nat.div_add_mod q p
      have hrem : q % p < p := Nat.mod_lt q (by omega)
      have hqp_pos : 1 ≤ q / p := by
        cases hqp : q / p with
        | zero => rw [hqp, Nat.mul_zero] at hdiv_mod; omega
        | succ _ => omega
      have hqp_lt : q / p < q := by
        have h2 : 2 * (q / p) ≤ p * (q / p) := Nat.mul_le_mul_right (q / p) hp
        omega
      have ih := floorLogNatAux_spec (fuel := fuel) hp hqp_pos (by omega)
      generalize hm : floorLogNatAux p (q / p) fuel = m at ih ⊢
      refine ⟨?_, ?_⟩
      · calc
          p ^ (1 + m) = p * p ^ m := by rw [Nat.add_comm 1 m, Nat.pow_succ, Nat.mul_comm]
          _ ≤ p * (q / p) := Nat.mul_le_mul_left p ih.1
          _ ≤ q := by omega
      · have hle1 : q / p + 1 ≤ p ^ (m + 1) := by omega
        have hmul : p * (q / p + 1) ≤ p * p ^ (m + 1) := Nat.mul_le_mul_left p hle1
        rw [Nat.mul_add, Nat.mul_one] at hmul
        have hpow : p * p ^ (m + 1) = p ^ (1 + m + 1) := by
          rw [Nat.add_comm 1 m, Nat.pow_succ p (m + 1), Nat.mul_comm]
        omega

theorem floorLogNat_spec {p q : Nat} (hp : 2 ≤ p) (hq : 1 ≤ q) :
    p ^ (floorLogNat p q) ≤ q ∧ q < p ^ (floorLogNat p q + 1) :=
  floorLogNatAux_spec hp hq (Nat.le_refl q)

/-- Exact cross-multiplied characterization of `e = ⌊log_p(u / v)⌋ ∈ ℤ` for `u, v ≥ 1`:
    - If `e = m ≥ 0`: `v * p^m ≤ u < v * p^(m + 1)` (i.e., `p^m ≤ u/v < p^(m+1)`).
    - If `e = -(m + 1) < 0`: `v ≤ u * p^(m + 1)` and `u * p^m < v`
      (i.e., `p^(-(m+1)) ≤ u/v < p^(-m)`). -/
def IsFloorLogQ (p u v : Nat) : Int → Prop
  | Int.ofNat m => v * p ^ m ≤ u ∧ u < v * p ^ (m + 1)
  | Int.negSucc m => v ≤ u * p ^ (m + 1) ∧ u * p ^ m < v

/-- Exact floor base-`p` logarithm `⌊log_p(u / v)⌋ ∈ ℤ` for `p ≥ 2` and `u, v ≥ 1`. -/
def floorLogQ (p u v : Nat) : Int :=
  if v ≤ u then
    Int.ofNat (floorLogNat p (u / v))
  else
    Int.negSucc (floorLogNat p ((v - 1) / u))

theorem floorLogQ_spec {p u v : Nat} (hp : 2 ≤ p) (hu : 1 ≤ u) (hv : 1 ≤ v) :
    IsFloorLogQ p u v (floorLogQ p u v) := by
  unfold floorLogQ
  by_cases hvu : v ≤ u
  · simp [hvu, IsFloorLogQ]
    have hdiv_mod := Nat.div_add_mod u v
    have hrem : u % v < v := Nat.mod_lt u hv
    have hq_pos : 1 ≤ u / v := by
      cases hq : u / v with
      | zero => rw [hq, Nat.mul_zero] at hdiv_mod; omega
      | succ _ => omega
    have hspec := floorLogNat_spec hp hq_pos
    generalize hm : floorLogNat p (u / v) = m at hspec ⊢
    refine ⟨?_, ?_⟩
    · calc
        v * p ^ m ≤ v * (u / v) := Nat.mul_le_mul_left v hspec.1
        _ ≤ u := by omega
    · have hle1 : u / v + 1 ≤ p ^ (m + 1) := by omega
      have hmul : v * (u / v + 1) ≤ v * p ^ (m + 1) := Nat.mul_le_mul_left v hle1
      rw [Nat.mul_add, Nat.mul_one] at hmul
      omega
  · simp [hvu, IsFloorLogQ]
    have hdiv_mod := Nat.div_add_mod (v - 1) u
    have hrem : (v - 1) % u < u := Nat.mod_lt (v - 1) hu
    have hq_pos : 1 ≤ (v - 1) / u := by
      cases hq : (v - 1) / u with
      | zero => rw [hq, Nat.mul_zero] at hdiv_mod; omega
      | succ _ => omega
    have hspec := floorLogNat_spec hp hq_pos
    generalize hm : floorLogNat p ((v - 1) / u) = m at hspec ⊢
    refine ⟨?_, ?_⟩
    · have hle1 : (v - 1) / u + 1 ≤ p ^ (m + 1) := by omega
      have hmul : u * ((v - 1) / u + 1) ≤ u * p ^ (m + 1) := Nat.mul_le_mul_left u hle1
      rw [Nat.mul_add, Nat.mul_one] at hmul
      omega
    · have hmul : u * p ^ m ≤ u * ((v - 1) / u) := Nat.mul_le_mul_left u hspec.1
      omega

theorem isFloorLogQ_unique {p u v : Nat} (hp : 2 ≤ p)
    {e₁ e₂ : Int} (h₁ : IsFloorLogQ p u v e₁) (h₂ : IsFloorLogQ p u v e₂) :
    e₁ = e₂ := by
  have hp1 : 1 ≤ p := by omega
  cases e₁ with
  | ofNat m₁ =>
    cases e₂ with
    | ofNat m₂ =>
      simp [IsFloorLogQ] at h₁ h₂
      have hcmp : m₁ < m₂ ∨ m₂ < m₁ ∨ m₁ = m₂ := by omega
      rcases hcmp with hlt | hgt | rfl
      · exfalso
        have hpow : p ^ (m₁ + 1) ≤ p ^ m₂ := pow_le_pow_of_le hp1 hlt
        have hmul : v * p ^ (m₁ + 1) ≤ v * p ^ m₂ := Nat.mul_le_mul_left v hpow
        omega
      · exfalso
        have hpow : p ^ (m₂ + 1) ≤ p ^ m₁ := pow_le_pow_of_le hp1 hgt
        have hmul : v * p ^ (m₂ + 1) ≤ v * p ^ m₁ := Nat.mul_le_mul_left v hpow
        omega
      · rfl
    | negSucc m₂ =>
      exfalso
      simp [IsFloorLogQ] at h₁ h₂
      have hpow1 : 1 ≤ p ^ m₁ := pow_pos_of_pos hp1 m₁
      have hpow2 : 1 ≤ p ^ m₂ := pow_pos_of_pos hp1 m₂
      have hv_le : v ≤ v * p ^ m₁ := by
        calc v = v * 1 := (Nat.mul_one v).symm
        _ ≤ v * p ^ m₁ := Nat.mul_le_mul_left v hpow1
      have hu_le : u ≤ u * p ^ m₂ := by
        calc u = u * 1 := (Nat.mul_one u).symm
        _ ≤ u * p ^ m₂ := Nat.mul_le_mul_left u hpow2
      omega
  | negSucc m₁ =>
    cases e₂ with
    | ofNat m₂ =>
      exfalso
      simp [IsFloorLogQ] at h₁ h₂
      have hpow1 : 1 ≤ p ^ m₁ := pow_pos_of_pos hp1 m₁
      have hpow2 : 1 ≤ p ^ m₂ := pow_pos_of_pos hp1 m₂
      have hv_le : v ≤ v * p ^ m₂ := by
        calc v = v * 1 := (Nat.mul_one v).symm
        _ ≤ v * p ^ m₂ := Nat.mul_le_mul_left v hpow2
      have hu_le : u ≤ u * p ^ m₁ := by
        calc u = u * 1 := (Nat.mul_one u).symm
        _ ≤ u * p ^ m₁ := Nat.mul_le_mul_left u hpow1
      omega
    | negSucc m₂ =>
      simp [IsFloorLogQ] at h₁ h₂
      have hcmp : m₁ < m₂ ∨ m₂ < m₁ ∨ m₁ = m₂ := by omega
      rcases hcmp with hlt | hgt | rfl
      · exfalso
        have hpow : p ^ (m₁ + 1) ≤ p ^ m₂ := pow_le_pow_of_le hp1 hlt
        have hmul : u * p ^ (m₁ + 1) ≤ u * p ^ m₂ := Nat.mul_le_mul_left u hpow
        omega
      · exfalso
        have hpow : p ^ (m₂ + 1) ≤ p ^ m₁ := pow_le_pow_of_le hp1 hgt
        have hmul : u * p ^ (m₂ + 1) ≤ u * p ^ m₁ := Nat.mul_le_mul_left u hpow
        omega
      · rfl

theorem floorLogQ_eq_of_isFloorLogQ {p u v : Nat} {e : Int}
    (hp : 2 ≤ p) (hu : 1 ≤ u) (hv : 1 ≤ v) (he : IsFloorLogQ p u v e) :
    floorLogQ p u v = e :=
  isFloorLogQ_unique hp (floorLogQ_spec hp hu hv) he

/-- Exact real-floor characterization of `(floorLogNat p L) / d`:
    for `p ≥ 2`, `L ≥ 1`, `d ≥ 1`, letting `q = floorLogNat p L / d`, we have
    `p^(d * q) ≤ L < p^(d * (q + 1))` (i.e., `q ≤ (log_p L) / d < q + 1`). -/
theorem floorLogNat_div_exact_spec {p L d : Nat} (hp : 2 ≤ p) (hL : 1 ≤ L) (hd : 1 ≤ d) :
    p ^ (d * (floorLogNat p L / d)) ≤ L ∧ L < p ^ (d * (floorLogNat p L / d + 1)) := by
  have hM := floorLogNat_spec hp hL
  generalize floorLogNat p L = M at hM ⊢
  have hdiv := Nat.div_add_mod M d
  have hrem : M % d < d := Nat.mod_lt M hd
  generalize M / d = q at hdiv ⊢
  have hle1 : d * q ≤ M := by omega
  have hle2 : M + 1 ≤ d * (q + 1) := by
    rw [Nat.mul_add, Nat.mul_one]
    omega
  exact ⟨Nat.le_trans (pow_le_pow_of_le (by omega) hle1) hM.1,
         Nat.lt_of_lt_of_le hM.2 (pow_le_pow_of_le (by omega) hle2)⟩

/-! ## Section 6: All Eight Parsings of Clause 2 and Complete Disproof -/

/-- Parsing 1 (Primary literal parsing):
    `⌊log_p(LCM(k+1, ..., n) / (k! * (n - k)!))⌋`. -/
def lcmExpr1 (p n k : Nat) : Int :=
  floorLogQ p (lcmInterval (k + 1) n) (fact k * fact (n - k))

/-- Parsing 2 (Outer-quotient parsing):
    `⌊(log_p LCM(k+1, ..., n)) / (k! * (n - k)!)⌋ = ⌊log_p LCM(k+1, ..., n)⌋ / (k! * (n - k)!)`. -/
def lcmExpr2 (p n k : Nat) : Int :=
  Int.ofNat (floorLogNat p (lcmInterval (k + 1) n) / (fact k * fact (n - k)))

/-- Parsing 3 (Reduced-denominator `log_p` parsing):
    `⌊log_p(LCM(k+1, ..., n) / (n - k)!)⌋`. -/
def lcmExpr3 (p n k : Nat) : Int :=
  floorLogQ p (lcmInterval (k + 1) n) (fact (n - k))

/-- Parsing 4 (`p`-adic valuation of full LCM quotient):
    `v_p(LCM(k+1, ..., n)) - v_p(k! * (n - k)!)`. -/
def lcmExpr4 (p n k : Nat) : Int :=
  (padicVal p (lcmInterval (k + 1) n) : Int) - (padicVal p (fact k * fact (n - k)) : Int)

/-- Parsing 5 (`p`-adic valuation of reduced LCM quotient):
    `v_p(LCM(k+1, ..., n)) - v_p((n - k)!)`. -/
def lcmExpr5 (p n k : Nat) : Int :=
  (padicVal p (lcmInterval (k + 1) n) : Int) - (padicVal p (fact (n - k)) : Int)

/-- Parsing 6 (Hybrid `⌊log_p LCM⌋ - v_p(k!(n-k)!)`): -/
def lcmExpr6 (p n k : Nat) : Int :=
  (floorLogNat p (lcmInterval (k + 1) n) : Int) - (padicVal p (fact k * fact (n - k)) : Int)

/-- Parsing 7 (Hybrid `⌊log_p LCM⌋ - v_p((n-k)!)`): -/
def lcmExpr7 (p n k : Nat) : Int :=
  (floorLogNat p (lcmInterval (k + 1) n) : Int) - (padicVal p (fact (n - k)) : Int)

/-- Parsing 8 (Classical binomial valuation `v_p(C(n, k))`): -/
def lcmExpr8 (p n k : Nat) : Int :=
  (padicVal p (binom n k) : Int)

/-- Generic predicate: `E` equals `v_p([n choose k]_p)` ONLY WHEN `p ≤ n - k`
    (on strictly interior parameters `0 < k < n`). -/
def HoldsOnlyWhenInterior (E : Nat → Nat → Nat → Int) (p : Nat) : Prop :=
  ∀ n k : Nat, 0 < k → k < n →
    E p n k = (padicVal p (qBinom p n k) : Int) → p ≤ n - k

/-- Generic predicate: `E` equals `v_p([n choose k]_p)` ONLY WHEN `p ≤ n - k`
    (on all parameters `0 ≤ k ≤ n`). -/
def HoldsOnlyWhenAll (E : Nat → Nat → Nat → Int) (p : Nat) : Prop :=
  ∀ n k : Nat, k ≤ n →
    E p n k = (padicVal p (qBinom p n k) : Int) → p ≤ n - k

/-- Generic predicate: `E` equals `v_p([n choose k]_p)` WHEN `p ≤ n - k`
    (on strictly interior parameters `0 < k < n`). -/
def HoldsWhenInterior (E : Nat → Nat → Nat → Int) (p : Nat) : Prop :=
  ∀ n k : Nat, 0 < k → k < n →
    p ≤ n - k → E p n k = (padicVal p (qBinom p n k) : Int)

/-- Generic predicate: `E` equals `v_p([n choose k]_p)` IF AND ONLY IF `p ≤ n - k`
    (on strictly interior parameters `0 < k < n`). -/
def HoldsIffInterior (E : Nat → Nat → Nat → Int) (p : Nat) : Prop :=
  ∀ n k : Nat, 0 < k → k < n →
    (E p n k = (padicVal p (qBinom p n k) : Int) ↔ p ≤ n - k)

/-- Full official statement of Conjecture `00000007675` (primary literal formalization):
    For all primes `p` and `0 ≤ k ≤ n`:
    (1) `v_p([n choose k]_p)` equals the Clause 1 carry-difference sum, AND
    (2) the alternative LCM-expression `⌊log_p(LCM(k+1,...,n)/(k!(n-k)!))⌋` equals
        `v_p([n choose k]_p)` only when `p ≤ n - k`. -/
def Conjecture00000007675Statement : Prop :=
  ∀ p : Nat, IsPrime p →
    (∀ n k J : Nat, k ≤ n → (padicVal p (qBinom p n k) : Int) = clause1Sum p n k J) ∧
    HoldsOnlyWhenAll lcmExpr1 p

/-! ### Infinite Family 1: Every Odd Prime `p ≥ 3` Refutes "Only When `p ≤ n - k`"
    Simultaneously for ALL EIGHT Parsings at `(n, k) = (2, 1)` -/

theorem lcmInterval_two_two : lcmInterval 2 2 = 2 := by decide

theorem floorLogNat_two_of_ge_three {p : Nat} (hp3 : 3 ≤ p) : floorLogNat p 2 = 0 := by
  have hspec := floorLogNat_spec (p := p) (q := 2) (by omega) (by omega)
  cases hm : floorLogNat p 2 with
  | zero => rfl
  | succ m' =>
    rw [hm] at hspec
    have hpow : p ≤ p ^ (m' + 1) := by
      simpa using pow_le_pow_of_le (b := p) (by omega) (e₁ := 1) (e₂ := m' + 1) (by omega)
    omega

theorem floorLogQ_two_one_of_ge_three {p : Nat} (hp3 : 3 ≤ p) : floorLogQ p 2 1 = 0 := by
  apply floorLogQ_eq_of_isFloorLogQ (by omega) (by omega) (by omega)
  simp [IsFloorLogQ]
  omega

theorem padicVal_two_of_ge_three {p : Nat} (hp3 : 3 ≤ p) : padicVal p 2 = 0 := by
  apply padicVal_eq_zero_of_not_dvd (by omega) (by omega)
  intro hdvd
  have hle : p ≤ 2 := Nat.le_of_dvd (by omega) hdvd
  omega

theorem padicVal_one_of_ge_two {p : Nat} (hp : 2 ≤ p) : padicVal p 1 = 0 := by
  apply padicVal_eq_zero_of_not_dvd hp (by omega)
  intro hdvd
  have hle : p ≤ 1 := Nat.le_of_dvd (by omega) hdvd
  omega

/-- Universal infinite-family refutation:
    For EVERY odd prime `p ≥ 3`, at the strictly interior pair `(n, k) = (2, 1)` (`0 < 1 < 2`),
    we have `¬ (p ≤ n - k)` (since `n - k = 1 < 3 ≤ p`), yet ALL EIGHT parsings
    `lcmExpr1 .. lcmExpr8` equal `0 = v_p([2 choose 1]_p)`. -/
theorem odd_prime_refutes_only_when_all_eight {p : Nat} (hp : IsPrime p) (hp3 : 3 ≤ p) :
    let n := 2
    let k := 1
    0 < k ∧ k < n ∧ ¬ (p ≤ n - k) ∧
    (padicVal p (qBinom p n k) : Int) = 0 ∧
    lcmExpr1 p n k = 0 ∧
    lcmExpr2 p n k = 0 ∧
    lcmExpr3 p n k = 0 ∧
    lcmExpr4 p n k = 0 ∧
    lcmExpr5 p n k = 0 ∧
    lcmExpr6 p n k = 0 ∧
    lcmExpr7 p n k = 0 ∧
    lcmExpr8 p n k = 0 := by
  have hv0 : padicVal p (qBinom p 2 1) = 0 := padicVal_qBinom_prime_eq_zero hp (by omega)
  have hf1 : fact 1 = 1 := rfl
  have hb21 : binom 2 1 = 2 := rfl
  have hlcm : lcmInterval 2 2 = 2 := lcmInterval_two_two
  have hflnat : floorLogNat p 2 = 0 := floorLogNat_two_of_ge_three hp3
  have hflq : floorLogQ p 2 1 = 0 := floorLogQ_two_one_of_ge_three hp3
  have hvp2 : padicVal p 2 = 0 := padicVal_two_of_ge_three hp3
  have hvp1 : padicVal p 1 = 0 := padicVal_one_of_ge_two hp.1
  refine ⟨by omega, by omega, by omega, by simp [hv0], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [lcmExpr1, hlcm, hf1, hflq]
  · simp [lcmExpr2, hlcm, hf1, hflnat]
  · simp [lcmExpr3, hlcm, hf1, hflq]
  · simp [lcmExpr4, hlcm, hf1, hvp2, hvp1]
  · simp [lcmExpr5, hlcm, hf1, hvp2, hvp1]
  · simp [lcmExpr6, hlcm, hf1, hflnat, hvp1]
  · simp [lcmExpr7, hlcm, hf1, hflnat, hvp1]
  · simp [lcmExpr8, hb21, hvp2]

/-! ### Infinite Family 2: Every Individual Prime `p` (Including `p = 2`) Refutes BOTH
    "Only When `p ≤ n - k`" AND "When `p ≤ n - k`" for `lcmExpr1` -/

/-- Auxiliary interval product `∏_{j=lo}^{lo+count-1} j`. -/
def prodRangeAux (lo : Nat) : Nat → Nat
  | 0 => 1
  | count + 1 => prodRangeAux lo count * (lo + count)

/-- Product of all integers in `[lo, hi]` (`1` if empty). -/
def prodInterval (lo hi : Nat) : Nat :=
  if lo ≤ hi then prodRangeAux lo (hi - lo + 1) else 1

theorem prodRangeAux_pos {lo : Nat} (hlo : 1 ≤ lo) : ∀ count : Nat, 0 < prodRangeAux lo count
  | 0 => by simp [prodRangeAux]
  | count + 1 => Nat.mul_pos (prodRangeAux_pos hlo count) (by omega)

theorem mem_dvd_prodRangeAux (lo : Nat) :
    ∀ (count m : Nat), lo ≤ m → m < lo + count → m ∣ prodRangeAux lo count
  | 0, m, h1, h2 => by omega
  | count + 1, m, h1, h2 => by
    unfold prodRangeAux
    by_cases hlast : m = lo + count
    · subst hlast
      exact ⟨prodRangeAux lo count, Nat.mul_comm _ _⟩
    · rcases mem_dvd_prodRangeAux lo count m h1 (by omega) with ⟨t, ht⟩
      exact ⟨t * (lo + count), by rw [ht, Nat.mul_assoc]⟩

theorem mem_dvd_prodInterval {lo hi m : Nat} (h1 : lo ≤ m) (h2 : m ≤ hi) :
    m ∣ prodInterval lo hi := by
  unfold prodInterval
  have hle : lo ≤ hi := by omega
  simp [hle]
  exact mem_dvd_prodRangeAux lo (hi - lo + 1) m h1 (by omega)

theorem prodRangeAux_add (lo a : Nat) :
    ∀ b : Nat, prodRangeAux lo (a + b) = prodRangeAux lo a * prodRangeAux (lo + a) b
  | 0 => by simp [prodRangeAux]
  | b + 1 => by
    have h1 : prodRangeAux lo (a + (b + 1)) = prodRangeAux lo (a + b) * (lo + (a + b)) := rfl
    have h2 : prodRangeAux (lo + a) (b + 1) = prodRangeAux (lo + a) b * (lo + a + b) := rfl
    rw [h1, h2, prodRangeAux_add lo a b]
    have hidx : lo + (a + b) = lo + a + b := by omega
    rw [hidx, Nat.mul_assoc]

theorem prodInterval_split {lo mid hi : Nat} (h1 : lo ≤ mid) (h2 : mid < hi) :
    prodInterval lo hi = prodInterval lo mid * prodInterval (mid + 1) hi := by
  unfold prodInterval
  have hle1 : lo ≤ hi := by omega
  have hle2 : mid + 1 ≤ hi := by omega
  simp [hle1, h1, hle2]
  have hcnt : hi - lo + 1 = (mid - lo + 1) + (hi - (mid + 1) + 1) := by omega
  have hbase : lo + (mid - lo + 1) = mid + 1 := by omega
  rw [hcnt, prodRangeAux_add, hbase]

theorem mul_dvd_prodInterval_of_lt {lo hi a b : Nat}
    (ha : lo ≤ a) (hab : a < b) (hb : b ≤ hi) :
    a * b ∣ prodInterval lo hi := by
  rw [prodInterval_split ha (Nat.lt_of_lt_of_le hab hb)]
  rcases mem_dvd_prodInterval ha (Nat.le_refl a) with ⟨x, hx⟩
  rcases mem_dvd_prodInterval (lo := a + 1) (hi := hi) (by omega) hb with ⟨y, hy⟩
  refine ⟨x * y, ?_⟩
  rw [hx, hy]
  ac_rfl

theorem fact_eq_two_mul_prodInterval :
    ∀ t : Nat, fact (t + 3) = 2 * prodInterval 3 (t + 3)
  | 0 => by decide
  | t + 1 => by
    have hstep : fact (t + 4) = (t + 4) * fact (t + 3) := rfl
    rw [hstep, fact_eq_two_mul_prodInterval t]
    unfold prodInterval
    have h1 : 3 ≤ t + 3 := by omega
    have h2 : 3 ≤ t + 4 := by omega
    simp [h1, h2]
    have hpr : prodRangeAux 3 (t + 1 + 1) = prodRangeAux 3 (t + 1) * (3 + (t + 1)) := rfl
    have hidx : 3 + (t + 1) = t + 4 := by omega
    rw [hpr, hidx]
    ac_rfl

/-- For EVERY integer `p ≥ 2`, at `(n, k) = (2 * p + 6, 1)` we have `p ≤ n - k` and
    `LCM(2, ..., 2p + 6) < 1! * (2p + 5)!`, so `lcmExpr1 p (2 * p + 6) 1 < 0`. -/
theorem lcmExpr1_neg_at_two_mul_add_six {p : Nat} (hp : 2 ≤ p) :
    lcmExpr1 p (2 * p + 6) 1 < 0 := by
  let M := prodInterval 3 (2 * p + 5)
  have hM_pos : 0 < M := by
    change 0 < prodInterval 3 (2 * p + 5)
    unfold prodInterval
    have hle : 3 ≤ 2 * p + 5 := by omega
    simp [hle]
    exact prodRangeAux_pos (by omega) (2 * p + 5 - 3 + 1)
  have h4p3 : 4 * (p + 3) ∣ M :=
    mul_dvd_prodInterval_of_lt (lo := 3) (hi := 2 * p + 5) (a := 4) (b := p + 3)
      (by omega) (by omega) (by omega)
  have hlcm_spec := lcmInterval_spec (lo := 2) (hi := 2 * p + 6) (by omega)
  have hlcm_dvd_M : lcmInterval 2 (2 * p + 6) ∣ M := by
    apply hlcm_spec.2.2
    intro m hm1 hm2
    by_cases hm_eq2 : m = 2
    · subst hm_eq2
      have h2_4 : 2 ∣ 4 * (p + 3) := ⟨2 * (p + 3), by omega⟩
      exact Nat.dvd_trans h2_4 h4p3
    · by_cases hm_top : m = 2 * p + 6
      · subst hm_top
        have htop : 2 * p + 6 ∣ 4 * (p + 3) := ⟨2, by omega⟩
        exact Nat.dvd_trans htop h4p3
      · exact mem_dvd_prodInterval (by omega) (by omega)
  have hlcm_le_M : lcmInterval 2 (2 * p + 6) ≤ M := Nat.le_of_dvd hM_pos hlcm_dvd_M
  have hfact : fact 1 * fact (2 * p + 6 - 1) = 2 * M := by
    have hsub : 2 * p + 6 - 1 = (2 * p + 2) + 3 := by omega
    rw [show fact 1 = 1 from rfl, Nat.one_mul, hsub, fact_eq_two_mul_prodInterval (2 * p + 2)]
  have hsub5 : 2 * p + 6 - 1 = 2 * p + 5 := by omega
  have hlcm_lt_denom : lcmInterval 2 (2 * p + 6) < fact 1 * fact (2 * p + 5) := by
    rw [← hsub5]
    omega
  unfold lcmExpr1 floorLogQ
  rw [hsub5]
  have hnot_le : ¬ (fact 1 * fact (2 * p + 5) ≤ lcmInterval 2 (2 * p + 6)) := by omega
  simp [hnot_le]

/-- Per-prime two-sided refutation for `lcmExpr1`:
    For EVERY prime `p` (both `p = 2` and every odd prime `p ≥ 3`), BOTH
    `HoldsOnlyWhenInterior lcmExpr1 p` AND `HoldsWhenInterior lcmExpr1 p` are FALSE! -/
theorem every_prime_refutes_both_directions_lcmExpr1 (p : Nat) (hp : IsPrime p) :
    ¬ HoldsOnlyWhenInterior lcmExpr1 p ∧ ¬ HoldsWhenInterior lcmExpr1 p := by
  refine ⟨?_, ?_⟩
  · intro honly
    by_cases hp2 : p = 2
    · subst hp2
      have h32 : lcmExpr1 2 3 2 = (padicVal 2 (qBinom 2 3 2) : Int) := by decide
      have hle := honly 3 2 (by omega) (by omega) h32
      omega
    · have hp3 : 3 ≤ p := by
        have h := hp.1
        omega
      have hfam := odd_prime_refutes_only_when_all_eight hp hp3
      have heq : lcmExpr1 p 2 1 = (padicVal p (qBinom p 2 1) : Int) := by
        rw [hfam.2.2.2.2.1, hfam.2.2.2.1]
      exact hfam.2.2.1 (honly 2 1 (by omega) (by omega) heq)
  · intro hwhen
    have heq := hwhen (2 * p + 6) 1 (by omega) (by omega) (by omega)
    have hzero : padicVal p (qBinom p (2 * p + 6) 1) = 0 :=
      padicVal_qBinom_prime_eq_zero (n := 2 * p + 6) (k := 1) hp (by omega)
    rw [hzero] at heq
    have hneg := lcmExpr1_neg_at_two_mul_add_six hp.1
    omega

/-- Per-prime refutation of "only when `p ≤ n - k`" for `lcmExpr2` as well:
    fails for EVERY prime `p` (`(3, 2)` at `p = 2`, and `(2, 1)` for all `p ≥ 3`). -/
theorem every_prime_refutes_only_when_lcmExpr2 (p : Nat) (hp : IsPrime p) :
    ¬ HoldsOnlyWhenInterior lcmExpr2 p := by
  intro honly
  by_cases hp2 : p = 2
  · subst hp2
    have h32 : lcmExpr2 2 3 2 = (padicVal 2 (qBinom 2 3 2) : Int) := by decide
    have hle := honly 3 2 (by omega) (by omega) h32
    omega
  · have hp3 : 3 ≤ p := by have h := hp.1; omega
    have hfam := odd_prime_refutes_only_when_all_eight hp hp3
    have heq : lcmExpr2 p 2 1 = (padicVal p (qBinom p 2 1) : Int) := by
      rw [hfam.2.2.2.2.2.1, hfam.2.2.2.1]
    exact hfam.2.2.1 (honly 2 1 (by omega) (by omega) heq)

/-! ### Master Disproof Theorems Across All Eight Parsings and Both Directions -/

/-- Master Disproof Theorem 1: Official Conjecture `00000007675` is FALSE. -/
theorem conjecture_00000007675_disproved : ¬ Conjecture00000007675Statement := by
  intro hconj
  have h3 := (hconj 3 isPrime_three).2
  have honly_int : HoldsOnlyWhenInterior lcmExpr1 3 :=
    fun n k _ hkn heq => h3 n k (Nat.le_of_lt hkn) heq
  exact (every_prime_refutes_both_directions_lcmExpr1 3 isPrime_three).1 honly_int

/-- Master Disproof Theorem 2: All eight parsings `lcmExpr1 .. lcmExpr8` fail BOTH
    the literal "only when `p ≤ n - k`" condition (witnessed at `(p, n, k) = (3, 2, 1)`)
    AND the converse "when `p ≤ n - k`" condition (witnessed at `(2, 3, 1)` / `(2, 4, 1)`),
    and therefore also fail the biconditional "iff `p ≤ n - k`" on interior `0 < k < n`. -/
theorem all_eight_parsings_refuted_both_directions :
    (¬ ∀ p, IsPrime p → HoldsOnlyWhenInterior lcmExpr1 p) ∧
    (¬ ∀ p, IsPrime p → HoldsWhenInterior lcmExpr1 p) ∧
    (¬ ∀ p, IsPrime p → HoldsIffInterior lcmExpr1 p) ∧
    (¬ ∀ p, IsPrime p → HoldsOnlyWhenInterior lcmExpr2 p) ∧
    (¬ ∀ p, IsPrime p → HoldsWhenInterior lcmExpr2 p) ∧
    (¬ ∀ p, IsPrime p → HoldsIffInterior lcmExpr2 p) ∧
    (¬ ∀ p, IsPrime p → HoldsOnlyWhenInterior lcmExpr3 p) ∧
    (¬ ∀ p, IsPrime p → HoldsWhenInterior lcmExpr3 p) ∧
    (¬ ∀ p, IsPrime p → HoldsIffInterior lcmExpr3 p) ∧
    (¬ ∀ p, IsPrime p → HoldsOnlyWhenInterior lcmExpr4 p) ∧
    (¬ ∀ p, IsPrime p → HoldsWhenInterior lcmExpr4 p) ∧
    (¬ ∀ p, IsPrime p → HoldsIffInterior lcmExpr4 p) ∧
    (¬ ∀ p, IsPrime p → HoldsOnlyWhenInterior lcmExpr5 p) ∧
    (¬ ∀ p, IsPrime p → HoldsWhenInterior lcmExpr5 p) ∧
    (¬ ∀ p, IsPrime p → HoldsIffInterior lcmExpr5 p) ∧
    (¬ ∀ p, IsPrime p → HoldsOnlyWhenInterior lcmExpr6 p) ∧
    (¬ ∀ p, IsPrime p → HoldsWhenInterior lcmExpr6 p) ∧
    (¬ ∀ p, IsPrime p → HoldsIffInterior lcmExpr6 p) ∧
    (¬ ∀ p, IsPrime p → HoldsOnlyWhenInterior lcmExpr7 p) ∧
    (¬ ∀ p, IsPrime p → HoldsWhenInterior lcmExpr7 p) ∧
    (¬ ∀ p, IsPrime p → HoldsIffInterior lcmExpr7 p) ∧
    (¬ ∀ p, IsPrime p → HoldsOnlyWhenInterior lcmExpr8 p) ∧
    (¬ ∀ p, IsPrime p → HoldsWhenInterior lcmExpr8 p) ∧
    (¬ ∀ p, IsPrime p → HoldsIffInterior lcmExpr8 p) := by
  have h3 := odd_prime_refutes_only_when_all_eight isPrime_three (by omega)
  have c231_2 : lcmExpr2 2 3 1 ≠ (padicVal 2 (qBinom 2 3 1) : Int) := by decide
  have c241_1 : lcmExpr1 2 4 1 ≠ (padicVal 2 (qBinom 2 4 1) : Int) := by decide
  have c241_3 : lcmExpr3 2 4 1 ≠ (padicVal 2 (qBinom 2 4 1) : Int) := by decide
  have c241_4 : lcmExpr4 2 4 1 ≠ (padicVal 2 (qBinom 2 4 1) : Int) := by decide
  have c241_5 : lcmExpr5 2 4 1 ≠ (padicVal 2 (qBinom 2 4 1) : Int) := by decide
  have c241_6 : lcmExpr6 2 4 1 ≠ (padicVal 2 (qBinom 2 4 1) : Int) := by decide
  have c241_7 : lcmExpr7 2 4 1 ≠ (padicVal 2 (qBinom 2 4 1) : Int) := by decide
  have c241_8 : lcmExpr8 2 4 1 ≠ (padicVal 2 (qBinom 2 4 1) : Int) := by decide
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro h; exact h3.2.2.1 (h 3 isPrime_three 2 1 (by omega) (by omega) (by rw [h3.2.2.2.2.1, h3.2.2.2.1]))
  · intro h; exact c241_1 (h 2 isPrime_two 4 1 (by omega) (by omega) (by omega))
  · intro h; exact c241_1 ((h 2 isPrime_two 4 1 (by omega) (by omega)).mpr (by omega))
  · intro h; exact h3.2.2.1 (h 3 isPrime_three 2 1 (by omega) (by omega) (by rw [h3.2.2.2.2.2.1, h3.2.2.2.1]))
  · intro h; exact c231_2 (h 2 isPrime_two 3 1 (by omega) (by omega) (by omega))
  · intro h; exact c231_2 ((h 2 isPrime_two 3 1 (by omega) (by omega)).mpr (by omega))
  · intro h; exact h3.2.2.1 (h 3 isPrime_three 2 1 (by omega) (by omega) (by rw [h3.2.2.2.2.2.2.1, h3.2.2.2.1]))
  · intro h; exact c241_3 (h 2 isPrime_two 4 1 (by omega) (by omega) (by omega))
  · intro h; exact c241_3 ((h 2 isPrime_two 4 1 (by omega) (by omega)).mpr (by omega))
  · intro h; exact h3.2.2.1 (h 3 isPrime_three 2 1 (by omega) (by omega) (by rw [h3.2.2.2.2.2.2.2.1, h3.2.2.2.1]))
  · intro h; exact c241_4 (h 2 isPrime_two 4 1 (by omega) (by omega) (by omega))
  · intro h; exact c241_4 ((h 2 isPrime_two 4 1 (by omega) (by omega)).mpr (by omega))
  · intro h; exact h3.2.2.1 (h 3 isPrime_three 2 1 (by omega) (by omega) (by rw [h3.2.2.2.2.2.2.2.2.1, h3.2.2.2.1]))
  · intro h; exact c241_5 (h 2 isPrime_two 4 1 (by omega) (by omega) (by omega))
  · intro h; exact c241_5 ((h 2 isPrime_two 4 1 (by omega) (by omega)).mpr (by omega))
  · intro h; exact h3.2.2.1 (h 3 isPrime_three 2 1 (by omega) (by omega) (by rw [h3.2.2.2.2.2.2.2.2.2.1, h3.2.2.2.1]))
  · intro h; exact c241_6 (h 2 isPrime_two 4 1 (by omega) (by omega) (by omega))
  · intro h; exact c241_6 ((h 2 isPrime_two 4 1 (by omega) (by omega)).mpr (by omega))
  · intro h; exact h3.2.2.1 (h 3 isPrime_three 2 1 (by omega) (by omega) (by rw [h3.2.2.2.2.2.2.2.2.2.2.1, h3.2.2.2.1]))
  · intro h; exact c241_7 (h 2 isPrime_two 4 1 (by omega) (by omega) (by omega))
  · intro h; exact c241_7 ((h 2 isPrime_two 4 1 (by omega) (by omega)).mpr (by omega))
  · intro h; exact h3.2.2.1 (h 3 isPrime_three 2 1 (by omega) (by omega) (by rw [h3.2.2.2.2.2.2.2.2.2.2.2, h3.2.2.2.1]))
  · intro h; exact c241_8 (h 2 isPrime_two 4 1 (by omega) (by omega) (by omega))
  · intro h; exact c241_8 ((h 2 isPrime_two 4 1 (by omega) (by omega)).mpr (by omega))

/-- Explicit non-vacuity sanity checks on concrete Gaussian binomial values and counterexamples. -/
theorem concrete_witness_checks :
    IsPrime 2 ∧ IsPrime 3 ∧ IsPrime 5 ∧
    qBinom 2 4 2 = 35 ∧
    qBinom 3 3 2 = 13 ∧
    padicVal 3 (qBinom 3 2 1) = 0 ∧
    lcmInterval 2 4 = 12 ∧
    lcmExpr1 3 2 1 = 0 ∧
    lcmExpr1 2 4 1 = 1 ∧
    lcmExpr1 3 6 1 = -1 := by
  refine ⟨isPrime_two, isPrime_three, isPrime_five, ?_⟩
  decide

end Conjecture00000007675

/-! ## Axiom Audit -/
#print axioms Conjecture00000007675.qBinom_mul_qFact
#print axioms Conjecture00000007675.qFallProd_mul_qBinom
#print axioms Conjecture00000007675.padicVal_qBinom_prime_eq_zero
#print axioms Conjecture00000007675.padicVal_qBinom_prime_pow_eq_zero
#print axioms Conjecture00000007675.carryRipple_eq_carryResidue
#print axioms Conjecture00000007675.clause1_holds_under_one_indexed_carry
#print axioms Conjecture00000007675.clause1_fails_under_zero_indexed_carry
#print axioms Conjecture00000007675.lcmInterval_spec
#print axioms Conjecture00000007675.floorLogQ_spec
#print axioms Conjecture00000007675.isFloorLogQ_unique
#print axioms Conjecture00000007675.odd_prime_refutes_only_when_all_eight
#print axioms Conjecture00000007675.every_prime_refutes_both_directions_lcmExpr1
#print axioms Conjecture00000007675.conjecture_00000007675_disproved
#print axioms Conjecture00000007675.all_eight_parsings_refuted_both_directions
#print axioms Conjecture00000007675.concrete_witness_checks
