/-
Copyright (c) 2026 The Last Math Competition Authors. All rights reserved.
 Exact finite-field zero-divisor & annihilator point-count theorems over arbitrary
 finite fields `𝔽_q` (`FiniteFieldOps K`), plus concrete `𝔽₃` witness.
-/
import ZeroDivisorMetricRankDeficit.CliffordAlgebras

namespace ZeroDivisorMetricRankDeficit

open AssocInvolAlg

/-!
## 1. Duplicate-Free Exact Enumeration (`NoDup` & `IsExactEnum`)
-/

/-- Self-contained duplicate-freeness predicate on lists. -/
inductive NoDup {α : Type u} : List α → Prop where
  | nil : NoDup []
  | cons {x : α} {xs : List α} : x ∉ xs → NoDup xs → NoDup (x :: xs)

/-- `IsExactEnum P L` certifies that `L` enumerates `{x : α | P x}` bijectively without duplicates,
so `L.length` is the exact finite cardinality `|{x | P x}|`. -/
def IsExactEnum {α : Type u} (P : α → Prop) (L : List α) : Prop :=
  NoDup L ∧ ∀ x : α, x ∈ L ↔ P x

section ListCombinatorics

/-- Erase the first occurrence of `a` from `L`. -/
def eraseFirst {α : Type u} [DecidableEq α] (a : α) : List α → List α
  | [] => []
  | b :: bs => if a = b then bs else b :: eraseFirst a bs

theorem eraseFirst_length_succ {α : Type u} [DecidableEq α] {a : α} :
    ∀ {L : List α}, a ∈ L → (eraseFirst a L).length + 1 = L.length
  | [], h => nomatch h
  | b :: bs, h => by
    dsimp only [eraseFirst]
    by_cases hab : a = b
    · rw [if_pos hab]
      rfl
    · rw [if_neg hab]
      rcases List.mem_cons.mp h with rfl | hMem
      · exact False.elim (hab rfl)
      · dsimp only [List.length]
        rw [eraseFirst_length_succ hMem]

theorem mem_eraseFirst_of_nodup {α : Type u} [DecidableEq α] {a x : α} :
    ∀ {L : List α}, NoDup L → (x ∈ eraseFirst a L ↔ x ∈ L ∧ x ≠ a)
  | [], _ => by
    dsimp only [eraseFirst]
    constructor
    · intro h; nomatch h
    · rintro ⟨h, _⟩; nomatch h
  | b :: bs, NoDup.cons hbNotMem hBs => by
    dsimp only [eraseFirst]
    by_cases hab : a = b
    · subst hab
      rw [if_pos rfl]
      constructor
      · intro hx
        refine ⟨List.mem_cons_of_mem a hx, ?_⟩
        intro hxa
        subst hxa
        exact hbNotMem hx
      · rintro ⟨hxCons, hxa⟩
        rcases List.mem_cons.mp hxCons with rfl | hx
        · exact False.elim (hxa rfl)
        · exact hx
    · rw [if_neg hab]
      constructor
      · intro hxCons
        rcases List.mem_cons.mp hxCons with rfl | hx
        · exact ⟨List.mem_cons_self, fun hEq => hab hEq.symm⟩
        · rcases (mem_eraseFirst_of_nodup hBs).mp hx with ⟨hxBs, hxa⟩
          exact ⟨List.mem_cons_of_mem b hxBs, hxa⟩
      · rintro ⟨hxCons, hxa⟩
        rcases List.mem_cons.mp hxCons with rfl | hx
        · exact List.mem_cons_self
        · exact List.mem_cons_of_mem b ((mem_eraseFirst_of_nodup hBs).mpr ⟨hx, hxa⟩)

theorem nodup_eraseFirst {α : Type u} [DecidableEq α] (a : α) :
    ∀ {L : List α}, NoDup L → NoDup (eraseFirst a L)
  | [], _ => NoDup.nil
  | b :: bs, NoDup.cons hbNotMem hBs => by
    dsimp only [eraseFirst]
    by_cases hab : a = b
    · rw [if_pos hab]; exact hBs
    · rw [if_neg hab]
      refine NoDup.cons ?_ (nodup_eraseFirst a hBs)
      intro hbEr
      have hbMem := ((mem_eraseFirst_of_nodup hBs).mp hbEr).1
      exact hbNotMem hbMem

/-- Canonical cardinality uniqueness: any two `IsExactEnum` lists for `P` have equal length. -/
theorem nodup_ext_length_eq {α : Type u} [DecidableEq α] :
    ∀ {L₁ L₂ : List α}, NoDup L₁ → NoDup L₂ → (∀ x, x ∈ L₁ ↔ x ∈ L₂) → L₁.length = L₂.length
  | [], [], _, _, _ => rfl
  | [], b :: _, _, _, hExt => False.elim (List.not_mem_nil ((hExt b).mpr List.mem_cons_self))
  | a :: as, L₂, NoDup.cons haNotMem hAs, hL2, hExt => by
    have haL2 : a ∈ L₂ := (hExt a).mp List.mem_cons_self
    have hSub : ∀ x, x ∈ as ↔ x ∈ eraseFirst a L₂ := by
      intro x
      rw [mem_eraseFirst_of_nodup hL2]
      constructor
      · intro hxAs
        have hxne : x ≠ a := by
          intro hEq; subst hEq; exact haNotMem hxAs
        exact ⟨(hExt x).mp (List.mem_cons_of_mem a hxAs), hxne⟩
      · rintro ⟨hxL2, hxne⟩
        rcases List.mem_cons.mp ((hExt x).mpr hxL2) with rfl | hxAs
        · exact False.elim (hxne rfl)
        · exact hxAs
    have ih := nodup_ext_length_eq hAs (nodup_eraseFirst a hL2) hSub
    dsimp only [List.length]
    rw [ih, eraseFirst_length_succ haL2]

theorem nodup_append {α : Type u} {L₁ L₂ : List α}
    (h1 : NoDup L₁) (h2 : NoDup L₂) (hDisj : ∀ x, x ∈ L₁ → x ∈ L₂ → False) :
    NoDup (L₁ ++ L₂) := by
  induction h1 with
  | nil => exact h2
  | @cons a as haNotMem _ ih =>
    refine NoDup.cons ?_ (ih (fun x hx1 hx2 => hDisj x (List.mem_cons_of_mem a hx1) hx2))
    intro haApp
    rcases List.mem_append.mp haApp with haAs | haL2
    · exact haNotMem haAs
    · exact hDisj a List.mem_cons_self haL2

theorem nodup_map {α : Type u} {β : Type v} {f : α → β}
    (hf : ∀ x y, f x = f y → x = y) :
    ∀ {L : List α}, NoDup L → NoDup (L.map f)
  | [], _ => NoDup.nil
  | a :: as, NoDup.cons haNotMem hAs => by
    refine NoDup.cons ?_ (nodup_map hf hAs)
    intro hMem
    rcases List.mem_map.mp hMem with ⟨x, hxAs, hfx⟩
    have hEq := hf x a hfx
    subst hEq
    exact haNotMem hxAs

/-- Cartesian product of two lists. -/
def listProd {α : Type u} {β : Type v} : List α → List β → List (α × β)
  | [], _ => []
  | a :: as, bs => bs.map (fun b => (a, b)) ++ listProd as bs

theorem length_listProd {α : Type u} {β : Type v} :
    ∀ (as : List α) (bs : List β), (listProd as bs).length = as.length * bs.length
  | [], _ => by simp [listProd]
  | a :: as, bs => by
    dsimp only [listProd]
    rw [List.length_append, List.length_map, length_listProd as bs]
    dsimp only [List.length]
    rw [Nat.succ_mul, Nat.add_comm]

theorem mem_listProd {α : Type u} {β : Type v} :
    ∀ {as : List α} {bs : List β} {p : α × β},
      p ∈ listProd as bs ↔ p.1 ∈ as ∧ p.2 ∈ bs
  | [], _, _ => by
    dsimp only [listProd]
    constructor
    · intro h; nomatch h
    · rintro ⟨h, _⟩; nomatch h
  | a :: as, bs, (x, y) => by
    dsimp only [listProd]
    rw [List.mem_append, List.mem_map, mem_listProd]
    constructor
    · rintro (⟨b, hb, hEq⟩ | ⟨hx, hy⟩)
      · injection hEq with h1 h2
        subst h1; subst h2
        exact ⟨List.mem_cons_self, hb⟩
      · exact ⟨List.mem_cons_of_mem a hx, hy⟩
    · rintro ⟨hxCons, hy⟩
      rcases List.mem_cons.mp hxCons with rfl | hx
      · exact Or.inl ⟨y, hy, rfl⟩
      · exact Or.inr ⟨hx, hy⟩

theorem nodup_listProd {α : Type u} {β : Type v} :
    ∀ {as : List α} {bs : List β}, NoDup as → NoDup bs → NoDup (listProd as bs)
  | [], _, _, _ => NoDup.nil
  | a :: as, bs, NoDup.cons haNotMem hAs, hBs => by
    dsimp only [listProd]
    refine nodup_append ?_ (nodup_listProd hAs hBs) ?_
    · exact nodup_map (fun _ _ h => congrArg Prod.snd h) hBs
    · intro p hp1 hp2
      rcases List.mem_map.mp hp1 with ⟨b, _, rfl⟩
      have haInAs := (mem_listProd.mp hp2).1
      exact haNotMem haInAs

end ListCombinatorics

/-!
## 2. Finite Fields (`FiniteFieldOps K`) & Exact Point-Count Theorems
-/

class FiniteFieldOps (K : Type u) extends FieldOps K where
  decEq : DecidableEq K
  elems : List K
  nodup_elems : NoDup elems
  mem_elems : ∀ x : K, x ∈ elems

instance {K : Type u} [FiniteFieldOps K] : DecidableEq K := FiniteFieldOps.decEq

namespace FiniteFieldOps

section ArbitraryFiniteField

variable (K : Type u) [FiniteFieldOps K]

/-- Cardinality `q = |K|` of the finite field `K`. -/
def card : Nat := (elems (K := K)).length

/-- Nonzero elements `Kˣ` obtained by erasing `0` from `elems`. -/
def nonzeroElems : List K := eraseFirst (0 : K) elems

theorem nodup_nonzeroElems : NoDup (nonzeroElems K) :=
  nodup_eraseFirst (0 : K) nodup_elems

theorem mem_nonzeroElems (x : K) : x ∈ nonzeroElems K ↔ x ≠ 0 := by
  dsimp only [nonzeroElems]
  rw [mem_eraseFirst_of_nodup nodup_elems]
  constructor
  · exact fun h => h.2
  · exact fun hx => ⟨mem_elems x, hx⟩

theorem nonzeroElems_length_succ : (nonzeroElems K).length + 1 = card K :=
  eraseFirst_length_succ (mem_elems (0 : K))

theorem two_le_card : 2 ≤ card K := by
  have h1In : (1 : K) ∈ nonzeroElems K := (mem_nonzeroElems K 1).mpr FieldOps.zero_ne_one.symm
  cases hL : nonzeroElems K with
  | nil =>
    rw [hL] at h1In
    nomatch h1In
  | cons _ rest =>
    have hEq := nonzeroElems_length_succ K
    rw [hL] at hEq
    dsimp only [List.length] at hEq
    omega

theorem nonzeroElems_length : (nonzeroElems K).length = card K - 1 := by
  have h := nonzeroElems_length_succ K
  omega

/--
**Finite-Field Point Count 1 — Division Algebra `Cl_{0,1}(K)` (`n = 1, r = 0`):**
Whenever `-1` is not a square in `K` (`IsTwoSqAnisotropic K`, i.e., `Cl_{0,1}(𝔽_q) ≅ 𝔽_{q²}`),
`|Z(Cl_{0,1}(K))| = 1` (polynomial degree `0` in `q`).
-/
theorem cl01_zeroDivisor_card (hAniso : IsTwoSqAnisotropic K) :
    ∃ L : List (K × K),
      IsExactEnum (IsZeroDivisor (cl01Alg K).zero (cl01Alg K).mul) L ∧ L.length = 1 := by
  refine ⟨[(0, 0)], ⟨NoDup.cons List.not_mem_nil NoDup.nil, ?_⟩, rfl⟩
  intro z
  rw [cl01_isZeroDivisor_iff hAniso]
  simp

/--
**Finite-Field Point Count 2 — Split Algebra `Cl_{1,0}(K)` (`n = 1, r = 0`, `char K ≠ 2`):**
`|Z(Cl_{1,0}(K))| = 2q - 1` (polynomial degree `1` in `q`, contrasting with `1` at the same `n = 1, r = 0`).
-/
theorem cl10_zeroDivisor_card (hChar2 : (1 : K) + 1 ≠ 0) :
    ∃ L : List (K × K),
      IsExactEnum (IsZeroDivisor (cl10Alg K).zero (cl10Alg K).mul) L ∧
      L.length = 2 * card K - 1 := by
  let nz := nonzeroElems K
  let diagPos := nz.map (fun a => (a, a))
  let diagNeg := nz.map (fun a => (a, -a))
  let L : List (K × K) := (0, 0) :: (diagPos ++ diagNeg)
  have hNeNeg : ∀ a : K, a ≠ 0 → a ≠ -a := by
    intro a ha hEq
    have hSum : a + a = 0 := by
      have h1 := congrArg (fun t => a + t) hEq
      dsimp only at h1
      rw [FieldOps.add_neg_cancel] at h1
      exact h1
    have hTwo : a * ((1 : K) + 1) = 0 := by
      rw [FieldOps.left_distrib, FieldOps.mul_one, hSum]
    rcases FieldOps.mul_eq_zero.mp hTwo with haZ | h2Z
    · exact ha haZ
    · exact hChar2 h2Z
  have hNodupPos : NoDup diagPos :=
    nodup_map (fun _ _ h => congrArg Prod.fst h) (nodup_nonzeroElems K)
  have hNodupNeg : NoDup diagNeg :=
    nodup_map (fun _ _ h => congrArg Prod.fst h) (nodup_nonzeroElems K)
  have hDisjPN : ∀ p, p ∈ diagPos → p ∈ diagNeg → False := by
    intro p hp1 hp2
    rcases List.mem_map.mp hp1 with ⟨a, haNz, rfl⟩
    rcases List.mem_map.mp hp2 with ⟨b, _, hEq⟩
    injection hEq with hab haNegb
    subst hab
    exact hNeNeg b ((mem_nonzeroElems K b).mp haNz) haNegb.symm
  have hZeroNotIn : (0, 0) ∉ diagPos ++ diagNeg := by
    intro hMem
    rcases List.mem_append.mp hMem with hp | hn
    · rcases List.mem_map.mp hp with ⟨a, haNz, hEq⟩
      exact ((mem_nonzeroElems K a).mp haNz) (congrArg Prod.fst hEq)
    · rcases List.mem_map.mp hn with ⟨a, haNz, hEq⟩
      exact ((mem_nonzeroElems K a).mp haNz) (congrArg Prod.fst hEq)
  refine ⟨L, ⟨NoDup.cons hZeroNotIn (nodup_append hNodupPos hNodupNeg hDisjPN), ?_⟩, ?_⟩
  · intro ⟨a, b⟩
    rw [cl10_isZeroDivisor_iff]
    dsimp only [L, diagPos, diagNeg]
    rw [List.mem_cons, List.mem_append, List.mem_map, List.mem_map]
    constructor
    · rintro (hZ | ⟨x, _, hEq⟩ | ⟨x, _, hEq⟩)
      · injection hZ with ha hb; subst ha; subst hb; exact Or.inl rfl
      · injection hEq with hx1 hx2; subst hx1; subst hx2; exact Or.inl rfl
      · injection hEq with hx1 hx2; subst hx1; subst hx2
        right; rw [FieldOps.neg_neg]
    · rintro (rfl | rfl)
      · by_cases ha : a = 0
        · subst ha; exact Or.inl rfl
        · exact Or.inr (Or.inl ⟨a, (mem_nonzeroElems K a).mpr ha, rfl⟩)
      · by_cases hb : b = 0
        · subst hb; rw [FieldOps.neg_zero]; exact Or.inl rfl
        · have hnb : -b ≠ 0 := by
            intro hZ
            have h1 := congrArg Neg.neg hZ
            rw [FieldOps.neg_neg, FieldOps.neg_zero] at h1
            exact hb h1
          refine Or.inr (Or.inr ⟨-b, (mem_nonzeroElems K (-b)).mpr hnb, ?_⟩)
          rw [FieldOps.neg_neg]
  · dsimp only [L, diagPos, diagNeg, List.length]
    rw [List.length_append, List.length_map, List.length_map]
    have hNz := nonzeroElems_length K
    have hCard := two_le_card K
    dsimp only [nz]
    rw [hNz]
    omega

/-- Pure `Nat` polynomial identity `(q³ + q² - q) + (q² - 1)(q² - q) = q⁴` for `q ≥ 2`. -/
theorem mat2_card_poly_identity (q : Nat) (hq : 2 ≤ q) :
    let zCount := q * q + ((q - 1) * (q * q) + (q - 1) * q)
    zCount = q ^ 3 + q ^ 2 - q ∧ zCount + (q ^ 2 - 1) * (q ^ 2 - q) = q ^ 4 := by
  rcases Nat.exists_eq_add_of_le hq with ⟨k, rfl⟩
  dsimp only
  have h1 : (2 + k) - 1 = k + 1 := by omega
  have h2 : (2 + k) ^ 2 - 1 = k * k + 4 * k + 3 := by
    have hsq : (2 + k) ^ 2 = k * k + 4 * k + 4 := by
      calc
        (2 + k) ^ 2 = (2 + k) * (2 + k) := Nat.pow_two (2 + k)
        _ = 2 * (2 + k) + k * (2 + k) := Nat.add_mul 2 k (2 + k)
        _ = (4 + 2 * k) + (2 * k + k * k) := by
              rw [Nat.mul_add 2 2 k, Nat.mul_add k 2 k, Nat.mul_comm k 2]
        _ = k * k + 4 * k + 4 := by omega
    rw [hsq]
    omega
  have h3 : (2 + k) ^ 2 - (2 + k) = k * k + 3 * k + 2 := by
    have hsq : (2 + k) ^ 2 = k * k + 4 * k + 4 := by
      calc
        (2 + k) ^ 2 = (2 + k) * (2 + k) := Nat.pow_two (2 + k)
        _ = 2 * (2 + k) + k * (2 + k) := Nat.add_mul 2 k (2 + k)
        _ = (4 + 2 * k) + (2 * k + k * k) := by
              rw [Nat.mul_add 2 2 k, Nat.mul_add k 2 k, Nat.mul_comm k 2]
        _ = k * k + 4 * k + 4 := by omega
    rw [hsq]
    omega
  rw [h1, h2, h3]
  -- Expand powers on `m := 2 + k` using `Nat` ring distributivity
  let m := 2 + k
  change m * m + ((k + 1) * (m * m) + (k + 1) * m) = m ^ 3 + m ^ 2 - m ∧
         m * m + ((k + 1) * (m * m) + (k + 1) * m) +
           (k * k + 4 * k + 3) * (k * k + 3 * k + 2) = m ^ 4
  constructor
  · have hExpand : m * m + ((k + 1) * (m * m) + (k + 1) * m) = m * (m * m) + m * m - m := by
      have hk1 : (k + 1) * (m * m) + m * m = m * (m * m) := by
        calc
          (k + 1) * (m * m) + m * m = ((k + 1) + 1) * (m * m) := (Nat.succ_mul (k + 1) (m * m)).symm
          _ = m * (m * m) := by
                have hkm : (k + 1) + 1 = m := by omega
                rw [hkm]
      have hk2 : (k + 1) * m + m = m * m := by
        calc
          (k + 1) * m + m = ((k + 1) + 1) * m := (Nat.succ_mul (k + 1) m).symm
          _ = m * m := by
                have hkm : (k + 1) + 1 = m := by omega
                rw [hkm]
      omega
    have hPow3 : m ^ 3 = m * (m * m) := by
      calc
        m ^ 3 = m ^ 2 * m := Nat.pow_succ m 2
        _ = (m * m) * m := by rw [Nat.pow_two]
        _ = m * (m * m) := Nat.mul_comm (m * m) m
    rw [hPow3, Nat.pow_two]
    exact hExpand
  · -- Prove `(m³ + m² - m) + (m² - 1)(m² - m) = m⁴` directly in `Nat`
    have hGl : (k * k + 4 * k + 3) * (k * k + 3 * k + 2) = (m * m - 1) * (m * (m - 1)) := by
      have ha : k * k + 4 * k + 3 = m * m - 1 := by
        have hsq : m * m = k * k + 4 * k + 4 := by
          dsimp only [m]
          calc
            (2 + k) * (2 + k) = 2 * (2 + k) + k * (2 + k) := Nat.add_mul 2 k (2 + k)
            _ = (4 + 2 * k) + (2 * k + k * k) := by
                  rw [Nat.mul_add 2 2 k, Nat.mul_add k 2 k, Nat.mul_comm k 2]
            _ = k * k + 4 * k + 4 := by omega
        omega
      have hb : k * k + 3 * k + 2 = m * (m - 1) := by
        have hm1 : m - 1 = k + 1 := by omega
        rw [hm1]
        dsimp only [m]
        calc
          k * k + 3 * k + 2 = (2 + 2 * k) + (k + k * k) := by omega
          _ = 2 * (k + 1) + k * (k + 1) := by
                rw [Nat.mul_add 2 k 1, Nat.mul_add k k 1]
                omega
          _ = (2 + k) * (k + 1) := (Nat.add_mul 2 k (k + 1)).symm
      rw [ha, hb]
    rw [hGl]
    -- Factor common `m`:
    -- LHS = m * (m + (k + 1) * m + (k + 1)) + m * ((m * m - 1) * (m - 1))
    have hm1 : m - 1 = k + 1 := by omega
    rw [hm1]
    have hFact :
        (m * m + ((k + 1) * (m * m) + (k + 1) * m)) + (m * m - 1) * (m * (k + 1)) =
        m * ((m + (k + 1) * m + (k + 1)) + (m * m - 1) * (k + 1)) := by
      have p1 : (k + 1) * (m * m) = m * ((k + 1) * m) := by
        calc
          (k + 1) * (m * m) = ((k + 1) * m) * m := (Nat.mul_assoc (k + 1) m m).symm
          _ = m * ((k + 1) * m) := Nat.mul_comm ((k + 1) * m) m
      have p12 : (k + 1) * (m * m) + (k + 1) * m = m * ((k + 1) * m + (k + 1)) := by
        rw [Nat.left_distrib m ((k + 1) * m) (k + 1), ← p1, Nat.mul_comm m (k + 1)]
      have p3 : (m * m - 1) * (m * (k + 1)) = m * ((m * m - 1) * (k + 1)) := by
        rw [← Nat.mul_assoc (m * m - 1) m (k + 1), Nat.mul_comm (m * m - 1) m,
            Nat.mul_assoc m (m * m - 1) (k + 1)]
      rw [p12, p3]
      simp only [Nat.left_distrib]
      omega
    rw [hFact]
    have hInner : (m + (k + 1) * m + (k + 1)) + (m * m - 1) * (k + 1) = m * (m * m) := by
      have hSub1 : (k + 1) + (m * m - 1) * (k + 1) = (m * m) * (k + 1) := by
        calc
          (k + 1) + (m * m - 1) * (k + 1)
            = ((m * m - 1) + 1) * (k + 1) := by
                rw [Nat.succ_mul (m * m - 1) (k + 1), Nat.add_comm]
          _ = (m * m) * (k + 1) := by
                have hpos : 1 ≤ m * m := by
                  have : 2 ≤ m := by omega
                  exact Nat.le_trans (by decide : 1 ≤ 4) (Nat.mul_le_mul this this)
                have hrestore : (m * m - 1) + 1 = m * m := by omega
                rw [hrestore]
      have hRearr : (m + (k + 1) * m + (k + 1)) + (m * m - 1) * (k + 1) =
          (m + (k + 1) * m) + ((k + 1) + (m * m - 1) * (k + 1)) := by omega
      rw [hRearr, hSub1]
      have hFirst : m + (k + 1) * m = m * m := by
        calc
          m + (k + 1) * m = ((k + 1) + 1) * m := by
            rw [Nat.succ_mul (k + 1) m, Nat.add_comm]
          _ = m * m := by
            have hkm : (k + 1) + 1 = m := by omega
            rw [hkm]
      rw [hFirst]
      calc
        m * m + (m * m) * (k + 1) = (m * m) * ((k + 1) + 1) := by
          rw [Nat.mul_succ (m * m) (k + 1), Nat.add_comm]
        _ = (m * m) * m := by
          have hkm : (k + 1) + 1 = m := by omega
          rw [hkm]
        _ = m * (m * m) := Nat.mul_comm (m * m) m
    rw [hInner]
    calc
      m * (m * (m * m)) = ((m * m) * m) * m := by
        rw [← Nat.mul_assoc m m (m * m), ← Nat.mul_assoc (m * m) m m]
      _ = m ^ 4 := by
        calc
          ((m * m) * m) * m = (m ^ 2 * m) * m := by rw [Nat.pow_two]
          _ = m ^ 3 * m := by rw [Nat.pow_succ m 2]
          _ = m ^ 4 := (Nat.pow_succ m 3).symm

/--
**Finite-Field Point Count 3 — Matrix / Split Clifford Algebra `M₂(K) ≅ Cl_{1,1}(K)` (`n = 2, r = 0`):**
Over every finite field `K` of cardinality `q`, the zero-divisor variety `Z(M₂(K))` has exact size
`q³ + q² - q = q⁴ - (q² - 1)(q² - q)` (polynomial degree `3` in `q`, codimension `1` in `K⁴`,
despite metric nullity `r = 0`).
-/
theorem mat2_zeroDivisor_card :
    let q := card K
    ∃ L : List (Mat2 K),
      IsExactEnum (IsZeroDivisor (Mat2.alg K).zero (Mat2.alg K).mul) L ∧
      L.length = q ^ 3 + q ^ 2 - q ∧
      L.length + (q ^ 2 - 1) * (q ^ 2 - q) = q ^ 4 := by
  intro q
  let el := elems (K := K)
  let nz := nonzeroElems K
  let L1 : List (Mat2 K) := (listProd el el).map (fun p => ⟨0, 0, p.1, p.2⟩)
  let L2 : List (Mat2 K) :=
    (listProd nz (listProd el el)).map (fun t => ⟨t.1, t.2.1, t.2.2, t.1⁻¹ * (t.2.1 * t.2.2)⟩)
  let L3 : List (Mat2 K) := (listProd nz el).map (fun p => ⟨0, p.1, 0, p.2⟩)
  let L := L1 ++ (L2 ++ L3)
  have hNd1 : NoDup L1 := by
    refine nodup_map ?_ (nodup_listProd nodup_elems nodup_elems)
    intro ⟨c1, d1⟩ ⟨c2, d2⟩ h
    rcases Mat2.ext_iff.mp h with ⟨_, _, hc, hd⟩
    exact Prod.ext hc hd
  have hNd2 : NoDup L2 := by
    refine nodup_map ?_ (nodup_listProd (nodup_nonzeroElems K) (nodup_listProd nodup_elems nodup_elems))
    intro ⟨a1, b1, c1⟩ ⟨a2, b2, c2⟩ h
    rcases Mat2.ext_iff.mp h with ⟨ha, hb, hc, _⟩
    exact Prod.ext ha (Prod.ext hb hc)
  have hNd3 : NoDup L3 := by
    refine nodup_map ?_ (nodup_listProd (nodup_nonzeroElems K) nodup_elems)
    intro ⟨b1, d1⟩ ⟨b2, d2⟩ h
    rcases Mat2.ext_iff.mp h with ⟨_, hb, _, hd⟩
    exact Prod.ext hb hd
  have hDisj23 : ∀ M, M ∈ L2 → M ∈ L3 → False := by
    intro M h2 h3
    rcases List.mem_map.mp h2 with ⟨t, ht, rfl⟩
    rcases List.mem_map.mp h3 with ⟨p, _, hEq⟩
    have haNz : t.1 ≠ 0 := (mem_nonzeroElems K t.1).mp (mem_listProd.mp ht).1
    exact haNz (congrArg Mat2.m11 hEq).symm
  have hDisj1_23 : ∀ M, M ∈ L1 → M ∈ L2 ++ L3 → False := by
    intro M h1 h23
    rcases List.mem_map.mp h1 with ⟨p, _, rfl⟩
    rcases List.mem_append.mp h23 with h2 | h3
    · rcases List.mem_map.mp h2 with ⟨t, ht, hEq⟩
      have haNz : t.1 ≠ 0 := (mem_nonzeroElems K t.1).mp (mem_listProd.mp ht).1
      exact haNz (congrArg Mat2.m11 hEq)
    · rcases List.mem_map.mp h3 with ⟨q2, hq2, hEq⟩
      have hbNz : q2.1 ≠ 0 := (mem_nonzeroElems K q2.1).mp (mem_listProd.mp hq2).1
      exact hbNz (congrArg Mat2.m12 hEq)
  have hPoly := mat2_card_poly_identity q (two_le_card K)
  refine ⟨L, ⟨nodup_append hNd1 (nodup_append hNd2 hNd3 hDisj23) hDisj1_23, ?_⟩, ?_⟩
  · intro ⟨a, b, c, d⟩
    rw [Mat2.isZeroDivisor_iff_det_eq_zero]
    dsimp only [Mat2.det, L, L1, L2, L3]
    rw [List.mem_append, List.mem_append, List.mem_map, List.mem_map, List.mem_map]
    constructor
    · rintro (⟨⟨c', d'⟩, _, hEq⟩ | ⟨⟨a', b', c'⟩, ht, hEq⟩ | ⟨⟨b', d'⟩, _, hEq⟩)
      · rcases Mat2.ext_iff.mp hEq with ⟨rfl, rfl, rfl, rfl⟩
        dsimp only
        rw [FieldOps.zero_mul, FieldOps.zero_mul, FieldOps.sub_self]
      · rcases Mat2.ext_iff.mp hEq with ⟨rfl, rfl, rfl, rfl⟩
        dsimp only
        have haNz : a' ≠ 0 := (mem_nonzeroElems K a').mp (mem_listProd.mp ht).1
        rw [← FieldOps.mul_assoc a' a'⁻¹, FieldOps.mul_inv_cancel a' haNz,
            FieldOps.one_mul, FieldOps.sub_self]
      · rcases Mat2.ext_iff.mp hEq with ⟨rfl, rfl, rfl, rfl⟩
        dsimp only
        rw [FieldOps.zero_mul, FieldOps.mul_zero, FieldOps.sub_self]
    · intro hDet
      by_cases ha : a = 0
      · subst ha
        by_cases hb : b = 0
        · subst hb
          exact Or.inl ⟨(c, d), mem_listProd.mpr ⟨mem_elems c, mem_elems d⟩, rfl⟩
        · rw [FieldOps.zero_mul, FieldOps.zero_sub] at hDet
          have hbc : b * c = 0 := by
            have h1 := congrArg Neg.neg hDet
            rw [FieldOps.neg_neg, FieldOps.neg_zero] at h1
            exact h1
          rcases FieldOps.mul_eq_zero.mp hbc with hbZ | hcZ
          · exact False.elim (hb hbZ)
          · subst hcZ
            refine Or.inr (Or.inr ⟨(b, d), ?_, rfl⟩)
            exact mem_listProd.mpr ⟨(mem_nonzeroElems K b).mpr hb, mem_elems d⟩
      · have had : a * d = b * c := FieldOps.sub_eq_zero.mp hDet
        have hdEq : a⁻¹ * (b * c) = d := by
          rw [← had, ← FieldOps.mul_assoc, FieldOps.inv_mul_cancel ha, FieldOps.one_mul]
        refine Or.inr (Or.inl ⟨(a, (b, c)), ?_, ?_⟩)
        · exact mem_listProd.mpr
            ⟨(mem_nonzeroElems K a).mpr ha, mem_listProd.mpr ⟨mem_elems b, mem_elems c⟩⟩
        · dsimp only
          rw [hdEq]
  · have hLen : L.length = q * q + ((q - 1) * (q * q) + (q - 1) * q) := by
      dsimp only [L, L1, L2, L3]
      rw [List.length_append, List.length_append,
          List.length_map, List.length_map, List.length_map,
          length_listProd, length_listProd, length_listProd, length_listProd]
      dsimp only [el, nz, q]
      rw [nonzeroElems_length K]
      rfl
    rw [hLen]
    exact hPoly

/-- Exact right-annihilator cardinality `|Ann_R(E₁₁)| = q²` in `M₂(K)` (`dim = 2 ≠ 0 = r`). -/
theorem mat2_annR_e11_card :
    ∃ L : List (Mat2 K),
      IsExactEnum (InRightAnn (Mat2.alg K).zero (Mat2.alg K).mul Mat2.e11) L ∧
      L.length = (card K) ^ 2 := by
  let el := elems (K := K)
  let L := (listProd el el).map (fun p => (⟨0, 0, p.1, p.2⟩ : Mat2 K))
  refine ⟨L, ⟨?_, ?_⟩, ?_⟩
  · refine nodup_map ?_ (nodup_listProd nodup_elems nodup_elems)
    intro ⟨c1, d1⟩ ⟨c2, d2⟩ h
    rcases Mat2.ext_iff.mp h with ⟨_, _, hc, hd⟩
    exact Prod.ext hc hd
  · intro ⟨y11, y12, y21, y22⟩
    rw [Mat2.inRightAnn_e11_iff]
    dsimp only [L]
    rw [List.mem_map]
    constructor
    · rintro ⟨⟨c, d⟩, _, hEq⟩
      rcases Mat2.ext_iff.mp hEq with ⟨h1, h2, _, _⟩
      exact ⟨h1.symm, h2.symm⟩
    · rintro ⟨rfl, rfl⟩
      exact ⟨(y21, y22), mem_listProd.mpr ⟨mem_elems y21, mem_elems y22⟩, rfl⟩
  · dsimp only [L]
    rw [List.length_map, length_listProd, Nat.pow_two]
    rfl

/-!
## 3. Exact Point Counts for `Λ(K^r) = Cl_{0,0,r}(K)` and Its Annihilators
-/

/-- Enumerate all `q^{2^r}` elements of `Λ(K^r)`. -/
def allExtElems : (r : Nat) → List (ExtAlg K r)
  | 0 => elems (K := K)
  | m + 1 => listProd (allExtElems m) (allExtElems m)

theorem nodup_allExtElems : ∀ r : Nat, NoDup (allExtElems K r)
  | 0 => nodup_elems
  | m + 1 => nodup_listProd (nodup_allExtElems m) (nodup_allExtElems m)

theorem mem_allExtElems : ∀ (r : Nat) (x : ExtAlg K r), x ∈ allExtElems K r
  | 0, x => mem_elems x
  | m + 1, (u, v) => mem_listProd.mpr ⟨mem_allExtElems m u, mem_allExtElems m v⟩

theorem length_allExtElems : ∀ r : Nat, (allExtElems K r).length = (card K) ^ (2 ^ r)
  | 0 => by
    dsimp only [allExtElems, card]
    rw [Nat.pow_zero, Nat.pow_one]
  | m + 1 => by
    dsimp only [allExtElems]
    rw [length_listProd, length_allExtElems m, ← Nat.pow_add]
    have h2 : 2 ^ m + 2 ^ m = 2 ^ (m + 1) := by
      rw [Nat.pow_succ, Nat.mul_two]
    rw [h2]

/-- Enumerate all `q^{2^r - 1}` zero divisors (`scalarPart r x = 0`) of `Λ(K^r)`. -/
def zdExtElems : (r : Nat) → List (ExtAlg K r)
  | 0 => [(0 : K)]
  | m + 1 => listProd (zdExtElems m) (allExtElems K m)

theorem nodup_zdExtElems : ∀ r : Nat, NoDup (zdExtElems K r)
  | 0 => NoDup.cons List.not_mem_nil NoDup.nil
  | m + 1 => nodup_listProd (nodup_zdExtElems m) (nodup_allExtElems K m)

theorem mem_zdExtElems : ∀ (r : Nat) (x : ExtAlg K r), x ∈ zdExtElems K r ↔ scalarPart r x = 0
  | 0, x => by
    dsimp only [zdExtElems, scalarPart, radProj]
    simp
  | m + 1, (u, v) => by
    dsimp only [zdExtElems, scalarPart, radProj]
    rw [mem_listProd, mem_zdExtElems m u]
    exact ⟨fun h => h.1, fun h => ⟨h, mem_allExtElems K m v⟩⟩

theorem one_le_two_pow : ∀ m : Nat, 1 ≤ 2 ^ m
  | 0 => Nat.le_refl 1
  | m + 1 => by
    rw [Nat.pow_succ]
    have ih := one_le_two_pow m
    omega

theorem length_zdExtElems : ∀ r : Nat, (zdExtElems K r).length = (card K) ^ (2 ^ r - 1)
  | 0 => by
    dsimp only [zdExtElems, List.length]
    rw [Nat.pow_zero]
  | m + 1 => by
    dsimp only [zdExtElems]
    rw [length_listProd, length_zdExtElems m, length_allExtElems K m, ← Nat.pow_add]
    have hm : 1 ≤ 2 ^ m := one_le_two_pow m
    have hExp : (2 ^ m - 1) + 2 ^ m = 2 ^ (m + 1) - 1 := by
      rw [Nat.pow_succ, Nat.mul_two]
      omega
    rw [hExp]

/--
**Finite-Field Point Count 4 — Purely Degenerate Exterior Algebra `Λ(K^r) = Cl_{0,0,r}(K)`:**
For every `r : Nat` and every finite field `K` of cardinality `q`,
`|Z(Λ(K^r))| = q^{2^r - 1}` (polynomial degree `2^r - 1`, codimension `1` in `K^{2^r}`).
At `r = 2`, `|Z(Λ(K²))| = q³` has the exact same top degree `3` as `|Z(M₂(K))| = q³ + q² - q` (`r = 0`).
-/
theorem extAlg_zeroDivisor_card (r : Nat) :
    ∃ L : List (ExtAlg K r),
      IsExactEnum (IsZeroDivisor (extAlg K r).zero (extAlg K r).mul) L ∧
      L.length = (card K) ^ (2 ^ r - 1) := by
  refine ⟨zdExtElems K r, ⟨nodup_zdExtElems K r, ?_⟩, length_zdExtElems K r⟩
  intro x
  rw [extAlg_isZeroDivisor_iff K r x]
  exact mem_zdExtElems K r x

/-- Right annihilator of `topMonomial K r` has exact size `q^{2^r - 1}` (`dim = 2^r - 1`). -/
theorem extAlg_annR_topMonomial_card (r : Nat) :
    ∃ L : List (ExtAlg K r),
      IsExactEnum (InRightAnn (extAlg K r).zero (extAlg K r).mul (topMonomial K r)) L ∧
      L.length = (card K) ^ (2 ^ r - 1) := by
  refine ⟨zdExtElems K r, ⟨nodup_zdExtElems K r, ?_⟩, length_zdExtElems K r⟩
  intro y
  rw [inRightAnn_topMonomial_iff K r y]
  exact mem_zdExtElems K r y

/-- Right annihilator of `lastGen K m` (`e_{m+1}`) in `Λ(K^{m+1})` has exact size `q^{2^m}` (`dim = 2^{r-1}`). -/
theorem extAlg_annR_lastGen_card (m : Nat) :
    ∃ L : List (ExtAlg K (m + 1)),
      IsExactEnum (InRightAnn (extAlg K (m + 1)).zero (extAlg K (m + 1)).mul (lastGen K m)) L ∧
      L.length = (card K) ^ (2 ^ m) := by
  let L := (allExtElems K m).map (fun v => ((extAlg K m).zero, v))
  refine ⟨L, ⟨?_, ?_⟩, ?_⟩
  · exact nodup_map (fun _ _ h => congrArg Prod.snd h) (nodup_allExtElems K m)
  · intro ⟨u, v⟩
    rw [inRightAnn_lastGen_iff K m (u, v)]
    dsimp only [L]
    rw [List.mem_map]
    constructor
    · rintro ⟨w, _, hEq⟩
      exact (congrArg Prod.fst hEq).symm
    · intro hu
      subst hu
      exact ⟨v, mem_allExtElems K m v, rfl⟩
  · dsimp only [L]
    rw [List.length_map, length_allExtElems K m]

end ArbitraryFiniteField

end FiniteFieldOps

/-!
## 4. Concrete Field Witness `F3 = 𝔽₃` (`q = 3`, `char ≠ 2`, 2-Square Anisotropic)
-/

/-- Concrete prime field `𝔽₃ = {0, 1, 2}` certifying simultaneous non-vacuity of all finite-field hypotheses. -/
inductive F3 where
  | f0
  | f1
  | f2
  deriving DecidableEq, Repr

namespace F3

def add : F3 → F3 → F3
  | .f0, x => x
  | x, .f0 => x
  | .f1, .f1 => .f2
  | .f1, .f2 => .f0
  | .f2, .f1 => .f0
  | .f2, .f2 => .f1

def neg : F3 → F3
  | .f0 => .f0
  | .f1 => .f2
  | .f2 => .f1

def sub (a b : F3) : F3 := add a (neg b)

def mul : F3 → F3 → F3
  | .f0, _ => .f0
  | _, .f0 => .f0
  | .f1, x => x
  | x, .f1 => x
  | .f2, .f2 => .f1

def inv : F3 → F3
  | .f0 => .f0
  | .f1 => .f1
  | .f2 => .f2

instance : FiniteFieldOps F3 where
  zero := .f0
  one := .f1
  add := add
  sub := sub
  neg := neg
  mul := mul
  inv := inv
  zero_ne_one := by decide
  add_assoc a b c := by cases a <;> cases b <;> cases c <;> rfl
  add_comm a b := by cases a <;> cases b <;> rfl
  zero_add a := by cases a <;> rfl
  add_zero a := by cases a <;> rfl
  neg_add_cancel a := by cases a <;> rfl
  sub_eq_add_neg _ _ := rfl
  mul_assoc a b c := by cases a <;> cases b <;> cases c <;> rfl
  mul_comm a b := by cases a <;> cases b <;> rfl
  one_mul a := by cases a <;> rfl
  mul_one a := by cases a <;> rfl
  left_distrib a b c := by cases a <;> cases b <;> cases c <;> rfl
  right_distrib a b c := by cases a <;> cases b <;> cases c <;> rfl
  mul_inv_cancel a ha := by
    cases a with
    | f0 => exact False.elim (ha rfl)
    | f1 => rfl
    | f2 => rfl
  decEq := inferInstance
  elems := [.f0, .f1, .f2]
  nodup_elems := by
    refine NoDup.cons ?_ (NoDup.cons ?_ (NoDup.cons ?_ NoDup.nil)) <;> decide
  mem_elems x := by cases x <;> decide

theorem two_ne_zero : (1 : F3) + 1 ≠ 0 := by decide

theorem two_sq_anisotropic : IsTwoSqAnisotropic F3 := by
  intro a b h
  cases a <;> cases b <;> cases h
  exact ⟨rfl, rfl⟩

end F3

end ZeroDivisorMetricRankDeficit
