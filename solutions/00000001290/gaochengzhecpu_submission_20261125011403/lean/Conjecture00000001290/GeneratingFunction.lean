/-
  Conjecture 00000001290 — Rational Generating Functions of Sprague–Grundy Values
  Core Lean 4.19.0 (zero external dependencies)
-/
import Conjecture00000001290.Basic

namespace Conjecture00000001290

/-! ### Polynomials in `ℤ[x]` and formal power series multiplication -/

/-- Coefficient of `x^n` in the polynomial represented by `P : List Int`. -/
def coeff : List Int → Nat → Int
  | [], _ => 0
  | c :: _, 0 => c
  | _ :: cs, n + 1 => coeff cs n

theorem coeff_eq_zero_of_le : {P : List Int} → {n : Nat} → P.length ≤ n → coeff P n = 0
  | [], _, _ => rfl
  | _ :: _, 0, h => by simp at h
  | _ :: cs, n + 1, h => coeff_eq_zero_of_le (P := cs) (n := n) (by simp at h; omega)

/-- A polynomial `P ∈ ℤ[x]` is nonzero iff at least one coefficient is nonzero. -/
def PolyNonzero (P : List Int) : Prop :=
  ∃ i : Nat, coeff P i ≠ 0

/-- Every nonzero polynomial has a smallest index `i₀ < Q.length` with `coeff Q i₀ ≠ 0`. -/
theorem exists_first_nonzero : {Q : List Int} → PolyNonzero Q →
    ∃ i₀ : Nat, i₀ < Q.length ∧ coeff Q i₀ ≠ 0 ∧ ∀ j : Nat, j < i₀ → coeff Q j = 0
  | [], ⟨_, hi⟩ => absurd rfl hi
  | c :: cs, hQ => by
    by_cases hc : c = 0
    · subst hc
      have hcs : PolyNonzero cs := by
        rcases hQ with ⟨i, hi⟩
        cases i with
        | zero => exact absurd rfl hi
        | succ i' => exact ⟨i', hi⟩
      rcases exists_first_nonzero hcs with ⟨i₀', hlt, hne, hzero⟩
      refine ⟨i₀' + 1, by simp; omega, hne, ?_⟩
      intro j hj
      cases j with
      | zero => rfl
      | succ j' => exact hzero j' (by omega)
    · exact ⟨0, by simp, hc, fun _ hj => by omega⟩

/-- Finite sum `f 0 + f 1 + ... + f (m - 1)`. -/
def sumRange (f : Nat → Int) : Nat → Int
  | 0 => 0
  | m + 1 => sumRange f m + f m

theorem sumRange_congr {f g : Nat → Int} :
    {m : Nat} → (∀ j : Nat, j < m → f j = g j) → sumRange f m = sumRange g m
  | 0, _ => rfl
  | m + 1, h => by
    rw [sumRange, sumRange, sumRange_congr (m := m) (fun j hj => h j (by omega)), h m (by omega)]

theorem sumRange_zero {f : Nat → Int} :
    {m : Nat} → (∀ j : Nat, j < m → f j = 0) → sumRange f m = 0
  | 0, _ => rfl
  | m + 1, h => by
    rw [sumRange, sumRange_zero (m := m) (fun j hj => h j (by omega)), h m (by omega)]
    rfl

theorem sumRange_eq_single {f : Nat → Int} {i₀ : Nat} :
    {m : Nat} → i₀ < m → (∀ j : Nat, j < m → j ≠ i₀ → f j = 0) → sumRange f m = f i₀
  | 0, hi, _ => by omega
  | m + 1, hi, h => by
    by_cases him : i₀ = m
    · subst him
      have hz : sumRange f i₀ = 0 :=
        sumRange_zero (m := i₀) (fun j hj => h j (by omega) (by omega))
      simp [sumRange, hz]
    · have ih := sumRange_eq_single (m := m) (by omega)
        (fun j hj hne => h j (by omega) hne)
      have hm0 : f m = 0 := h m (by omega) (fun heq => him heq.symm)
      simp [sumRange, ih, hm0]

theorem sumRange_eq_pair {f : Nat → Int} {i₁ i₂ : Nat} (h12 : i₁ < i₂) :
    {m : Nat} → i₂ < m →
    (∀ j : Nat, j < m → j ≠ i₁ → j ≠ i₂ → f j = 0) →
    sumRange f m = f i₁ + f i₂
  | 0, hi₂, _ => by omega
  | m + 1, hi₂, h => by
    by_cases him : i₂ = m
    · subst him
      have hs1 : sumRange f i₂ = f i₁ :=
        sumRange_eq_single (m := i₂) h12 (fun j hj hne => h j (by omega) hne (by omega))
      simp [sumRange, hs1]
    · have ih := sumRange_eq_pair h12 (m := m) (by omega)
        (fun j hj hne1 hne2 => h j (by omega) hne1 hne2)
      have hm0 : f m = 0 := h m (by omega) (by omega) (fun heq => him heq.symm)
      simp [sumRange, ih, hm0]

/-- Coefficient of `x^n` in `Q(x) * (∑_{k≥0} a_k x^k)` in `ℤ[[x]]`. -/
def seriesMulPolyCoeff (Q : List Int) (a : Nat → Int) (n : Nat) : Int :=
  sumRange (fun j => coeff Q j * a (n - j)) (n + 1)

theorem sumRange_trim_right {f : Nat → Int} {k : Nat} :
    {m : Nat} → k ≤ m → (∀ j : Nat, k ≤ j → j < m → f j = 0) →
    sumRange f m = sumRange f k
  | 0, hk, _ => by
    have hk0 : k = 0 := by omega
    subst hk0; rfl
  | m + 1, hk, h => by
    by_cases hkm : k = m + 1
    · subst hkm; rfl
    · have ih := sumRange_trim_right (m := m) (by omega)
        (fun j hj1 hj2 => h j hj1 (by omega))
      have hm0 : f m = 0 := h m (by omega) (by omega)
      simp [sumRange, ih, hm0]

theorem seriesMulPolyCoeff_eq_sumRange_len (Q : List Int) (a : Nat → Int) {n : Nat}
    (hle : Q.length ≤ n + 1) :
    seriesMulPolyCoeff Q a n = sumRange (fun j => coeff Q j * a (n - j)) Q.length := by
  unfold seriesMulPolyCoeff
  apply sumRange_trim_right hle
  intro j hj _
  rw [coeff_eq_zero_of_le hj, Int.zero_mul]

/-- Ordinary generating function `∑_{n≥0} a_n x^n` is rational iff `Q(x) * A(x) = P(x)`
    for polynomials `P, Q ∈ ℤ[x]` with `Q ≠ 0`. -/
def IsRationalOGF (a : Nat → Int) : Prop :=
  ∃ P Q : List Int, PolyNonzero Q ∧ ∀ n : Nat, seriesMulPolyCoeff Q a n = coeff P n

/-! ### Equivalence with rational-coefficient polynomials `ℚ[x]` -/

/-- Exact representation of a rational number `num / den` with `0 < den`. -/
structure RatCoeff where
  num : Int
  den : Nat
  den_pos : 0 < den

def ratZero : RatCoeff := ⟨0, 1, Nat.zero_lt_one⟩

def ratOfInt (z : Int) : RatCoeff := ⟨z, 1, Nat.zero_lt_one⟩

def ratAdd (r₁ r₂ : RatCoeff) : RatCoeff :=
  ⟨r₁.num * (r₂.den : Int) + r₂.num * (r₁.den : Int),
   r₁.den * r₂.den,
   Nat.mul_pos r₁.den_pos r₂.den_pos⟩

def ratMulInt (r : RatCoeff) (z : Int) : RatCoeff :=
  ⟨r.num * z, r.den, r.den_pos⟩

def RatEqv (r₁ r₂ : RatCoeff) : Prop :=
  r₁.num * (r₂.den : Int) = r₂.num * (r₁.den : Int)

def coeffQ : List RatCoeff → Nat → RatCoeff
  | [], _ => ratZero
  | c :: _, 0 => c
  | _ :: cs, n + 1 => coeffQ cs n

def PolyQNonzero (Q : List RatCoeff) : Prop :=
  ∃ i : Nat, (coeffQ Q i).num ≠ 0

def sumRangeQ (f : Nat → RatCoeff) : Nat → RatCoeff
  | 0 => ratZero
  | m + 1 => ratAdd (sumRangeQ f m) (f m)

def seriesMulPolyQCoeff (Q : List RatCoeff) (a : Nat → Int) (n : Nat) : RatCoeff :=
  sumRangeQ (fun j => ratMulInt (coeffQ Q j) (a (n - j))) (n + 1)

/-- Rationality directly over `ℚ[x]` without prior denominator clearing. -/
def IsRationalOGF_Q (a : Nat → Int) : Prop :=
  ∃ P Q : List RatCoeff, PolyQNonzero Q ∧
    ∀ n : Nat, RatEqv (seriesMulPolyQCoeff Q a n) (coeffQ P n)

/-- Product of denominators of a rational polynomial list. -/
def prodDens : List RatCoeff → Nat
  | [] => 1
  | r :: rs => r.den * prodDens rs

theorem prodDens_pos : (L : List RatCoeff) → 0 < prodDens L
  | [] => Nat.zero_lt_one
  | r :: rs => Nat.mul_pos r.den_pos (prodDens_pos rs)

/-- Scale a rational polynomial by `scale * prodDens L` to clear all denominators into `ℤ[x]`. -/
def clearPolyAux (scale : Nat) : List RatCoeff → List Int
  | [] => []
  | r :: rs =>
    (r.num * (scale : Int) * (prodDens rs : Int)) ::
      clearPolyAux (scale * r.den) rs

private theorem coeff_clearPolyAux :
    (L : List RatCoeff) → (scale n : Nat) →
    coeff (clearPolyAux scale L) n * ((coeffQ L n).den : Int) =
      (coeffQ L n).num * (scale : Int) * (prodDens L : Int)
  | [], scale, n => by
    cases n <;> simp [clearPolyAux, coeff, coeffQ, ratZero]
  | r :: rs, scale, 0 => by
    simp only [clearPolyAux, coeff, coeffQ, prodDens, Int.ofNat_mul]
    ac_rfl
  | r :: rs, scale, n + 1 => by
    simp only [clearPolyAux, coeff, coeffQ, prodDens]
    have ih := coeff_clearPolyAux rs (scale * r.den) n
    rw [ih]
    simp only [Int.ofNat_mul]
    ac_rfl

private theorem sumRange_mul_const (f : Nat → Int) (c : Int) :
    (m : Nat) → sumRange f m * c = sumRange (fun j => f j * c) m
  | 0 => by simp [sumRange]
  | m + 1 => by
    simp [sumRange, Int.add_mul, sumRange_mul_const f c m]

private theorem sumRangeQ_scale (Q : List RatCoeff) (a : Nat → Int) (D : Int)
    (hQ : ∀ j : Nat, coeff (clearPolyAux 1 Q) j * ((coeffQ Q j).den : Int) =
      (coeffQ Q j).num * D) :
    ∀ (m n : Nat),
      sumRange (fun j => coeff (clearPolyAux 1 Q) j * a (n - j)) m *
        ((sumRangeQ (fun j => ratMulInt (coeffQ Q j) (a (n - j))) m).den : Int) =
      (sumRangeQ (fun j => ratMulInt (coeffQ Q j) (a (n - j))) m).num * D
  | 0, _ => by
    simp [sumRange, sumRangeQ, ratZero]
  | m + 1, n => by
    simp only [sumRange, sumRangeQ, ratAdd, ratMulInt, Int.ofNat_mul]
    have ih := sumRangeQ_scale Q a D hQ m n
    let S_int := sumRange (fun j => coeff (clearPolyAux 1 Q) j * a (n - j)) m
    let S_q := sumRangeQ (fun j => ratMulInt (coeffQ Q j) (a (n - j))) m
    let qm := coeffQ Q m
    have hstep := hQ m
    have hdistr1 :
        (S_int + coeff (clearPolyAux 1 Q) m * a (n - m)) * ((S_q.den : Int) * (qm.den : Int)) =
        (S_int * (S_q.den : Int)) * (qm.den : Int) +
          (coeff (clearPolyAux 1 Q) m * (qm.den : Int)) * a (n - m) * (S_q.den : Int) := by
      rw [Int.add_mul]
      congr 1 <;> ac_rfl
    have hdistr2 :
        (S_q.num * D) * (qm.den : Int) + (qm.num * D) * a (n - m) * (S_q.den : Int) =
        (S_q.num * (qm.den : Int) + qm.num * a (n - m) * (S_q.den : Int)) * D := by
      rw [Int.add_mul]
      congr 1 <;> ac_rfl
    calc
      (S_int + coeff (clearPolyAux 1 Q) m * a (n - m)) * ((S_q.den : Int) * (qm.den : Int))
          = (S_int * (S_q.den : Int)) * (qm.den : Int) +
            (coeff (clearPolyAux 1 Q) m * (qm.den : Int)) * a (n - m) * (S_q.den : Int) := hdistr1
      _ = (S_q.num * D) * (qm.den : Int) + (qm.num * D) * a (n - m) * (S_q.den : Int) := by
            rw [ih, hstep]
      _ = (S_q.num * (qm.den : Int) + qm.num * a (n - m) * (S_q.den : Int)) * D := hdistr2

private theorem coeff_map_ratOfInt :
    (L : List Int) → (n : Nat) → coeffQ (L.map ratOfInt) n = ratOfInt (coeff L n)
  | [], n => by cases n <;> rfl
  | _ :: _, 0 => rfl
  | _ :: cs, n + 1 => coeff_map_ratOfInt cs n

private theorem sumRangeQ_ofInt (f : Nat → Int) :
    (m : Nat) → sumRangeQ (fun j => ratOfInt (f j)) m = ratOfInt (sumRange f m)
  | 0 => rfl
  | m + 1 => by
    rw [sumRangeQ, sumRange, sumRangeQ_ofInt f m]
    simp [ratAdd, ratOfInt]

/-- Clearing denominators: rationality over `ℚ[x]` is equivalent to `IsRationalOGF` over `ℤ[x]`. -/
theorem isRationalOGF_iff_Q (a : Nat → Int) :
    IsRationalOGF_Q a ↔ IsRationalOGF a := by
  constructor
  · rintro ⟨Pq, Qq, ⟨i₀, hi₀⟩, hrel⟩
    let dP := prodDens Pq
    let dQ := prodDens Qq
    let Pz := (clearPolyAux 1 Pq).map (fun c => c * (dQ : Int))
    let Qz := (clearPolyAux 1 Qq).map (fun c => c * (dP : Int))
    have hcoeff_map : ∀ (L : List Int) (k : Int) (n : Nat),
        coeff (L.map (fun c => c * k)) n = coeff L n * k := by
      intro L k n
      induction L generalizing n with
      | nil => cases n <;> simp [coeff]
      | cons _ cs ih =>
        cases n with
        | zero => simp [coeff]
        | succ n' => exact ih n'
    have hdP_pos : (0 : Int) < (dP : Int) := Int.ofNat_lt.mpr (prodDens_pos Pq)
    have hdQ_pos : (0 : Int) < (dQ : Int) := Int.ofNat_lt.mpr (prodDens_pos Qq)
    refine ⟨Pz, Qz, ?_, ?_⟩
    · refine ⟨i₀, ?_⟩
      rw [hcoeff_map]
      intro hzero
      have h1 := coeff_clearPolyAux Qq 1 i₀
      simp at h1
      have hmul0 : coeff (clearPolyAux 1 Qq) i₀ * (dP : Int) * ((coeffQ Qq i₀).den : Int) = 0 := by
        rw [hzero, Int.zero_mul]
      have hrew : coeff (clearPolyAux 1 Qq) i₀ * (dP : Int) * ((coeffQ Qq i₀).den : Int) =
          (coeffQ Qq i₀).num * (dQ : Int) * (dP : Int) := by
        calc
          coeff (clearPolyAux 1 Qq) i₀ * (dP : Int) * ((coeffQ Qq i₀).den : Int)
              = (coeff (clearPolyAux 1 Qq) i₀ * ((coeffQ Qq i₀).den : Int)) * (dP : Int) := by
                ac_rfl
          _ = (coeffQ Qq i₀).num * (dQ : Int) * (dP : Int) := by rw [h1]
      rw [hrew] at hmul0
      rcases Int.mul_eq_zero.mp hmul0 with hleft | hdP0
      · rcases Int.mul_eq_zero.mp hleft with hnum0 | hdQ0
        · exact hi₀ hnum0
        · omega
      · omega
    · intro n
      have hQn : ∀ j : Nat,
          coeff (clearPolyAux 1 Qq) j * ((coeffQ Qq j).den : Int) =
          (coeffQ Qq j).num * (dQ : Int) := by
        intro j
        have h := coeff_clearPolyAux Qq 1 j
        simp at h
        exact h
      have hPn := coeff_clearPolyAux Pq 1 n
      simp at hPn
      have hS := sumRangeQ_scale Qq a (dQ : Int) hQn (n + 1) n
      let Sq := seriesMulPolyQCoeff Qq a n
      let Pn_q := coeffQ Pq n
      have hSq_den_pos : (0 : Int) < (Sq.den : Int) := Int.ofNat_lt.mpr Sq.den_pos
      have hPn_den_pos : (0 : Int) < (Pn_q.den : Int) := Int.ofNat_lt.mpr Pn_q.den_pos
      have hEqv : Sq.num * (Pn_q.den : Int) = Pn_q.num * (Sq.den : Int) := hrel n
      have hLHS : seriesMulPolyCoeff Qz a n =
          sumRange (fun j => coeff (clearPolyAux 1 Qq) j * a (n - j)) (n + 1) * (dP : Int) := by
        unfold seriesMulPolyCoeff
        rw [sumRange_mul_const]
        apply sumRange_congr
        intro j _
        rw [hcoeff_map]
        ac_rfl
      have hRHS : coeff Pz n = coeff (clearPolyAux 1 Pq) n * (dQ : Int) := hcoeff_map _ _ _
      rw [hLHS, hRHS]
      have hscale_eq :
          (sumRange (fun j => coeff (clearPolyAux 1 Qq) j * a (n - j)) (n + 1) * (dP : Int)) *
            ((Sq.den : Int) * (Pn_q.den : Int)) =
          (coeff (clearPolyAux 1 Pq) n * (dQ : Int)) *
            ((Sq.den : Int) * (Pn_q.den : Int)) := by
        calc
          (sumRange (fun j => coeff (clearPolyAux 1 Qq) j * a (n - j)) (n + 1) * (dP : Int)) *
              ((Sq.den : Int) * (Pn_q.den : Int))
              = (sumRange (fun j => coeff (clearPolyAux 1 Qq) j * a (n - j)) (n + 1) *
                  (Sq.den : Int)) * (Pn_q.den : Int) * (dP : Int) := by ac_rfl
          _ = (Sq.num * (dQ : Int)) * (Pn_q.den : Int) * (dP : Int) := by
                dsimp [Sq, seriesMulPolyQCoeff]
                rw [hS]
          _ = (Sq.num * (Pn_q.den : Int)) * (dQ : Int) * (dP : Int) := by ac_rfl
          _ = (Pn_q.num * (Sq.den : Int)) * (dQ : Int) * (dP : Int) := by rw [hEqv]
          _ = (Pn_q.num * (dP : Int)) * (dQ : Int) * (Sq.den : Int) := by ac_rfl
          _ = (coeff (clearPolyAux 1 Pq) n * (Pn_q.den : Int)) * (dQ : Int) * (Sq.den : Int) := by
                dsimp [Pn_q]
                rw [hPn]
          _ = (coeff (clearPolyAux 1 Pq) n * (dQ : Int)) *
                ((Sq.den : Int) * (Pn_q.den : Int)) := by ac_rfl
      have hden_ne : ((Sq.den : Int) * (Pn_q.den : Int)) ≠ 0 := by
        have hpos : (0 : Int) < (Sq.den : Int) * (Pn_q.den : Int) :=
          Int.mul_pos hSq_den_pos hPn_den_pos
        omega
      exact Int.eq_of_mul_eq_mul_right hden_ne hscale_eq
  · rintro ⟨Pz, Qz, ⟨i₀, hi₀⟩, hrel⟩
    refine ⟨Pz.map ratOfInt, Qz.map ratOfInt, ⟨i₀, ?_⟩, ?_⟩
    · rw [coeff_map_ratOfInt]
      exact hi₀
    · intro n
      rw [coeff_map_ratOfInt]
      have hmul : seriesMulPolyQCoeff (Qz.map ratOfInt) a n =
          ratOfInt (seriesMulPolyCoeff Qz a n) := by
        unfold seriesMulPolyQCoeff seriesMulPolyCoeff
        have hfun : (fun j => ratMulInt (coeffQ (Qz.map ratOfInt) j) (a (n - j))) =
            (fun j => ratOfInt (coeff Qz j * a (n - j))) := by
          funext j
          rw [coeff_map_ratOfInt]
          rfl
        rw [hfun, sumRangeQ_ofInt]
      rw [hmul, hrel n]
      rfl

/-! ### Game generating function predicates & eventual periodicity -/

/-- Integer-valued sequence of Sprague–Grundy values. -/
def grundyIntSeq (g : Nat → Nat) (n : Nat) : Int :=
  Int.ofNat (g n)

/-- Indicator sequence of the `v`-fiber `{n | g n = v}`. -/
def grundyFiberSeq (g : Nat → Nat) (v : Nat) (n : Nat) : Int :=
  if g n = v then 1 else 0

/-- `G` admits a Sprague–Grundy sequence whose value OGF `∑ g(n) x^n` is rational. -/
def HasRationalGrundyOGF (G : ImpartialGame) : Prop :=
  ∃ g : Nat → Nat, G.IsGrundySeq g ∧ IsRationalOGF (grundyIntSeq g)

/-- `G` admits a Sprague–Grundy sequence whose `P`-position indicator GF
    `∑_{g(n)=0} x^n` is rational. -/
def HasRationalPPositionOGF (G : ImpartialGame) : Prop :=
  ∃ g : Nat → Nat, G.IsGrundySeq g ∧ IsRationalOGF (grundyFiberSeq g 0)

/-- `G` admits a Sprague–Grundy sequence all of whose fiber indicator GFs
    `∑_{g(n)=v} x^n` (`v ∈ ℕ`) are rational. -/
def HasAllRationalGrundyFibers (G : ImpartialGame) : Prop :=
  ∃ g : Nat → Nat, G.IsGrundySeq g ∧ ∀ v : Nat, IsRationalOGF (grundyFiberSeq g v)

/-- Eventual periodicity of a sequence `a : Nat → Int`. -/
def EventuallyPeriodicInt (a : Nat → Int) : Prop :=
  ∃ N₀ p : Nat, 0 < p ∧ ∀ n : Nat, N₀ ≤ n → a (n + p) = a n

/-- Eventual periodicity of a natural-number sequence `g : Nat → Nat`. -/
def EventuallyPeriodic (g : Nat → Nat) : Prop :=
  ∃ N₀ p : Nat, 0 < p ∧ ∀ n : Nat, N₀ ≤ n → g (n + p) = g n

/-- Build `[f 0, f 1, ..., f (len - 1)]`. -/
def tabulateInt (f : Nat → Int) : Nat → List Int
  | 0 => []
  | len + 1 => tabulateInt f len ++ [f len]

private theorem length_tabulateInt (f : Nat → Int) :
    (len : Nat) → (tabulateInt f len).length = len
  | 0 => rfl
  | len + 1 => by simp [tabulateInt, length_tabulateInt f len]

private theorem coeff_append_left :
    {L₁ L₂ : List Int} → {n : Nat} → n < L₁.length → coeff (L₁ ++ L₂) n = coeff L₁ n
  | [], _, _, h => by simp at h
  | _ :: _, _, 0, _ => rfl
  | _ :: cs, L₂, n + 1, h => coeff_append_left (L₁ := cs) (L₂ := L₂) (by simp at h; omega)

private theorem coeff_append_right_zero :
    {L₁ : List Int} → (c : Int) → coeff (L₁ ++ [c]) L₁.length = c
  | [], _ => rfl
  | _ :: cs, c => coeff_append_right_zero (L₁ := cs) c

private theorem coeff_tabulateInt (f : Nat → Int) :
    {len n : Nat} → n < len → coeff (tabulateInt f len) n = f n
  | 0, _, h => by omega
  | len + 1, n, h => by
    unfold tabulateInt
    by_cases hnl : n < len
    · rw [coeff_append_left]
      · exact coeff_tabulateInt f hnl
      · rw [length_tabulateInt]; exact hnl
    · have hneq : n = len := by omega
      subst hneq
      have hlen : (tabulateInt f n).length = n := length_tabulateInt f n
      have hcr := coeff_append_right_zero (L₁ := tabulateInt f n) (f n)
      rw [hlen] at hcr
      exact hcr

/-- Polynomial `1 - x^p` for `0 < p`. -/
def oneMinusXPow (p : Nat) : List Int :=
  1 :: (List.replicate (p - 1) 0 ++ [-1])

theorem coeff_replicate_zero_append (c : Int) :
    (k j : Nat) → coeff (List.replicate k 0 ++ [c]) j = (if j = k then c else 0)
  | 0, 0 => rfl
  | 0, _ + 1 => rfl
  | k + 1, 0 => by simp [List.replicate, coeff]
  | k + 1, j + 1 => by
    simp only [List.replicate, List.cons_append, coeff]
    rw [coeff_replicate_zero_append c k j]
    by_cases hjk : j = k
    · subst hjk; simp
    · have hne : j + 1 ≠ k + 1 := by omega
      simp [hjk, hne]

private theorem coeff_oneMinusXPow {p : Nat} (hp : 0 < p) (j : Nat) :
    coeff (oneMinusXPow p) j = if j = 0 then 1 else if j = p then -1 else 0 := by
  cases j with
  | zero =>
    have hne : (0 : Nat) ≠ p := by omega
    simp [oneMinusXPow, coeff, hne]
  | succ j' =>
    simp only [oneMinusXPow, coeff]
    rw [coeff_replicate_zero_append (-1) (p - 1) j']
    by_cases hjp : j' + 1 = p
    · have hj' : j' = p - 1 := by omega
      simp only [hj', ↓reduceIte]
      omega
    · have hj' : j' ≠ p - 1 := by omega
      simp only [hj', ↓reduceIte]
      omega

/-- Every eventually periodic integer sequence has a rational generating function. -/
theorem eventuallyPeriodicInt_rational_ogf {a : Nat → Int}
    (hep : EventuallyPeriodicInt a) : IsRationalOGF a := by
  rcases hep with ⟨N₀, p, hp, hper⟩
  let Q := oneMinusXPow p
  let P := tabulateInt (fun n => seriesMulPolyCoeff Q a n) (N₀ + p)
  refine ⟨P, Q, ⟨0, by simp [Q, oneMinusXPow, coeff]⟩, ?_⟩
  intro n
  by_cases hn : n < N₀ + p
  · symm
    exact coeff_tabulateInt (fun k => seriesMulPolyCoeff Q a k) hn
  · have hP0 : coeff P n = 0 := by
      apply coeff_eq_zero_of_le
      rw [length_tabulateInt]
      omega
    rw [hP0]
    unfold seriesMulPolyCoeff
    have hpair := sumRange_eq_pair (f := fun j => coeff Q j * a (n - j))
      (i₁ := 0) (i₂ := p) hp (m := n + 1) (by omega) ?_
    · rw [hpair]
      dsimp only
      have hc0 : coeff Q 0 = 1 := by
        rw [coeff_oneMinusXPow hp 0]; simp
      have hcp : coeff Q p = -1 := by
        rw [coeff_oneMinusXPow hp p]
        have hne : p ≠ 0 := by omega
        simp [hne]
      rw [hc0, hcp]
      have han : a n = a (n - p) := by
        have hsub : n = (n - p) + p := by omega
        conv => lhs; rw [hsub]
        exact hper (n - p) (by omega)
      simp [han]
      omega
    · intro j _ hj0 hjp
      dsimp only
      have hcj : coeff Q j = 0 := by
        rw [coeff_oneMinusXPow hp j]
        simp [hj0, hjp]
      rw [hcj, Int.zero_mul]

theorem eventuallyPeriodic_rational_ogf {g : Nat → Nat}
    (hep : EventuallyPeriodic g) : IsRationalOGF (grundyIntSeq g) := by
  rcases hep with ⟨N₀, p, hp, hper⟩
  apply eventuallyPeriodicInt_rational_ogf
  refine ⟨N₀, p, hp, fun n hn => ?_⟩
  simp [grundyIntSeq, hper n hn]

theorem eventuallyPeriodic_rational_fibers {g : Nat → Nat}
    (hep : EventuallyPeriodic g) (v : Nat) : IsRationalOGF (grundyFiberSeq g v) := by
  rcases hep with ⟨N₀, p, hp, hper⟩
  apply eventuallyPeriodicInt_rational_ogf
  refine ⟨N₀, p, hp, fun n hn => ?_⟩
  simp [grundyFiberSeq, hper n hn]

end Conjecture00000001290
