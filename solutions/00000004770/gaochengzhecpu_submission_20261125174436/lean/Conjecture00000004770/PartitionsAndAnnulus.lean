import Conjecture00000004770.PosetMobius

namespace Conjecture00000004770

/-!
# Set Partitions, Disc Noncrossing Partitions, and Annular Lattice Dichotomy

First-principles formalization of set partitions, disc noncrossing partitions `NC(n)`,
Mingo–Nica annular noncrossing set partitions `NC_A(p, q)`, circular-boundary
noncrossing partitions `NC_∂^∘(p)`, the universal punctured-annulus equivalence
`NC_A(p, 1) = NC_∂^∘(p)` (yielding lattice structure for all `p`), and the universal
failure of the join-semilattice / lattice axiom for `NC_A(p, q)` whenever `p ≥ q ≥ 2`
and `p + q ≥ 6` (`(4, 2)`, `(3, 3)`, and all higher `(p, q)`).
-/

/-- Core injectivity predicate (avoiding external library imports). -/
def IsInjective {α β : Type} (f : α → β) : Prop :=
  ∀ x y : α, f x = f y → x = y

/-- A set partition of `Fin N`, represented by its decidable equivalence relation. -/
structure SetPartition (N : Nat) where
  rel : Fin N → Fin N → Bool
  rel_refl : ∀ i : Fin N, rel i i = true
  rel_symm : ∀ i j : Fin N, rel i j = true → rel j i = true
  rel_trans : ∀ i j k : Fin N, rel i j = true → rel j k = true → rel i k = true

theorem SetPartition.ext {N : Nat} {σ τ : SetPartition N}
    (h : ∀ i j : Fin N, σ.rel i j = τ.rel i j) : σ = τ := by
  cases σ; cases τ
  simp only [mk.injEq]
  funext i j
  exact h i j

/-- Partition refinement order: `σ ≤ τ` iff every `σ`-block is contained in a `τ`-block. -/
def Refines {N : Nat} (σ τ : SetPartition N) : Prop :=
  ∀ i j : Fin N, σ.rel i j = true → τ.rel i j = true

def refinesBool {N : Nat} (σ τ : SetPartition N) : Bool :=
  finAll N (fun i => finAll N (fun j => !σ.rel i j || τ.rel i j))

theorem refinesBool_iff {N : Nat} (σ τ : SetPartition N) :
    refinesBool σ τ = true ↔ Refines σ τ := by
  simp only [refinesBool, finAll_eq_true, Refines]
  constructor
  · intro h i j hij
    have hij' := h i j
    simp [hij] at hij'
    exact hij'
  · intro h i j
    cases hij : σ.rel i j <;> simp
    exact h i j hij

theorem refines_refl {N : Nat} (σ : SetPartition N) : Refines σ σ :=
  fun _ _ h => h

theorem refines_antisymm {N : Nat} {σ τ : SetPartition N}
    (h1 : Refines σ τ) (h2 : Refines τ σ) : σ = τ := by
  apply SetPartition.ext
  intro i j
  cases hσ : σ.rel i j <;> cases hτ : τ.rel i j
  · rfl
  · exfalso; exact Bool.noConfusion (hσ.symm.trans (h2 i j hτ))
  · exfalso; exact Bool.noConfusion (hτ.symm.trans (h1 i j hσ))
  · rfl

theorem refines_trans {N : Nat} {σ τ ρ : SetPartition N}
    (h1 : Refines σ τ) (h2 : Refines τ ρ) : Refines σ ρ :=
  fun i j h => h2 i j (h1 i j h)

/-- Finest partition `0̂` (all singletons). -/
def botPartition (N : Nat) : SetPartition N where
  rel i j := decide (i = j)
  rel_refl i := by simp
  rel_symm i j h := by simp at h ⊢; exact h.symm
  rel_trans i j k h1 h2 := by simp at h1 h2 ⊢; exact h1.trans h2

/-- Coarsest partition `1̂` (single block). -/
def topPartition (N : Nat) : SetPartition N where
  rel _ _ := true
  rel_refl _ := rfl
  rel_symm _ _ _ := rfl
  rel_trans _ _ _ _ _ := rfl

/-- Set-partition meet `σ ∧_Π τ` (pairwise block intersections). -/
def meetPartition {N : Nat} (σ τ : SetPartition N) : SetPartition N where
  rel i j := σ.rel i j && τ.rel i j
  rel_refl i := by simp [σ.rel_refl i, τ.rel_refl i]
  rel_symm i j h := by
    simp only [Bool.and_eq_true] at h ⊢
    exact ⟨σ.rel_symm i j h.1, τ.rel_symm i j h.2⟩
  rel_trans i j k h1 h2 := by
    simp only [Bool.and_eq_true] at h1 h2 ⊢
    exact ⟨σ.rel_trans i j k h1.1 h2.1, τ.rel_trans i j k h1.2 h2.2⟩

/-- Partition induced by a vertex-coloring `c : Fin N → Nat`. -/
def mkColorPartition {N : Nat} (c : Fin N → Nat) : SetPartition N where
  rel i j := decide (c i = c j)
  rel_refl i := by simp
  rel_symm i j h := by simp at h ⊢; exact h.symm
  rel_trans i j k h1 h2 := by simp at h1 h2 ⊢; exact h1.trans h2

/-- Partition defined by up to three pairwise disjoint non-singleton blocks `b1, b2, b3`
(all remaining elements being singletons). -/
def mkThreeBlocks {N : Nat} (b1 b2 b3 : Fin N → Bool)
    (h12 : ∀ v, b1 v = true → b2 v = false)
    (h13 : ∀ v, b1 v = true → b3 v = false)
    (h23 : ∀ v, b2 v = true → b3 v = false) : SetPartition N where
  rel x y := decide (x = y) || (b1 x && b1 y) || (b2 x && b2 y) || (b3 x && b3 y)
  rel_refl x := by simp
  rel_symm x y h := by
    by_cases hxy : x = y
    · subst hxy; exact h
    · have hyx : y ≠ x := fun e => hxy e.symm
      simp only [hxy, hyx, decide_false, Bool.false_or] at h ⊢
      rw [Bool.and_comm (b1 y), Bool.and_comm (b2 y), Bool.and_comm (b3 y)]
      exact h
  rel_trans x y z hxy hyz := by
    by_cases exy : x = y
    · subst exy; exact hyz
    · by_cases eyz : y = z
      · subst eyz; exact hxy
      · simp only [exy, eyz, decide_false, Bool.false_or, Bool.or_eq_true, Bool.and_eq_true] at hxy hyz
        rcases hxy with ((⟨hx1, hy1⟩ | ⟨hx2, hy2⟩) | ⟨hx3, hy3⟩)
        · have n2 := h12 y hy1; have n3 := h13 y hy1
          rcases hyz with ((⟨_, hz1⟩ | ⟨hy2', _⟩) | ⟨hy3', _⟩)
          · simp [hx1, hz1]
          · exact Bool.noConfusion (n2.symm.trans hy2')
          · exact Bool.noConfusion (n3.symm.trans hy3')
        · have n3 := h23 y hy2
          rcases hyz with ((⟨hy1', _⟩ | ⟨_, hz2⟩) | ⟨hy3', _⟩)
          · exact Bool.noConfusion ((h12 y hy1').symm.trans hy2)
          · simp [hx2, hz2]
          · exact Bool.noConfusion (n3.symm.trans hy3')
        · rcases hyz with ((⟨hy1', _⟩ | ⟨hy2', _⟩) | ⟨_, hz3⟩)
          · exact Bool.noConfusion ((h13 y hy1').symm.trans hy3)
          · exact Bool.noConfusion ((h23 y hy2').symm.trans hy3)
          · simp [hx3, hz3]

/-! ## Noncrossing Partitions with Respect to Linear and Cyclic Orders -/

/-- `π` is noncrossing with respect to the vertex listing `ord : Fin N → Fin N`. -/
def IsOrderNC {N : Nat} (ord : Fin N → Fin N) (π : SetPartition N) : Prop :=
  ∀ a b c d : Fin N,
    a.1 < b.1 → b.1 < c.1 → c.1 < d.1 →
    π.rel (ord a) (ord c) = true →
    π.rel (ord b) (ord d) = true →
    π.rel (ord a) (ord b) = true

/-- Classical disc noncrossing partition on `Fin N` (`0 < 1 < ... < N - 1`). -/
def IsDiscNC {N : Nat} (π : SetPartition N) : Prop :=
  IsOrderNC id π

theorem isOrderNC_meet {N : Nat} (ord : Fin N → Fin N) {σ τ : SetPartition N}
    (hσ : IsOrderNC ord σ) (hτ : IsOrderNC ord τ) :
    IsOrderNC ord (meetPartition σ τ) := by
  intro a b c d hab hbc hcd hac hbd
  simp only [meetPartition, Bool.and_eq_true] at hac hbd ⊢
  exact ⟨hσ a b c d hab hbc hcd hac.1 hbd.1, hτ a b c d hab hbc hcd hac.2 hbd.2⟩

theorem isDiscNC_meet {N : Nat} {σ τ : SetPartition N}
    (hσ : IsDiscNC σ) (hτ : IsDiscNC τ) : IsDiscNC (meetPartition σ τ) :=
  isOrderNC_meet id hσ hτ

theorem isDiscNC_bot (N : Nat) : IsDiscNC (botPartition N) := by
  intro a b c _ hab hbc _ hac _
  simp only [botPartition, id, decide_eq_true_eq] at hac
  have hval : a.1 = c.1 := congrArg Fin.val hac
  omega

theorem isDiscNC_top (N : Nat) : IsDiscNC (topPartition N) := by
  intro _ _ _ _ _ _ _ _ _
  rfl

/-- Left cyclic shift of a listing `ord : Fin N → Fin N`: `(ord 1, ..., ord (N-1), ord 0)`. -/
def shiftLeft1 {N : Nat} (ord : Fin N → Fin N) : Fin N → Fin N :=
  fun i =>
    if h : i.1 + 1 < N then ord ⟨i.1 + 1, h⟩
    else ord ⟨0, Nat.lt_of_le_of_lt (Nat.zero_le _) i.2⟩

/-- Right cyclic shift of a listing `ord : Fin N → Fin N`: `(ord (N-1), ord 0, ..., ord (N-2))`. -/
def shiftRight1 {N : Nat} (ord : Fin N → Fin N) : Fin N → Fin N :=
  fun i =>
    if _ : i.1 = 0 then ord ⟨N - 1, by have := i.2; omega⟩
    else ord ⟨i.1 - 1, by have := i.2; omega⟩

/-- `r`-fold iterated left cyclic shift (`iterShift (r + 1) ord = shiftLeft1 (iterShift r ord)`). -/
def iterShift {N : Nat} : Nat → (Fin N → Fin N) → (Fin N → Fin N)
  | 0, ord => ord
  | r + 1, ord => shiftLeft1 (iterShift r ord)

theorem iterShift_right_step {N : Nat} : ∀ (r : Nat) (ord : Fin N → Fin N),
    iterShift r (shiftLeft1 ord) = shiftLeft1 (iterShift r ord)
  | 0, _ => rfl
  | r + 1, ord => by
    simp only [iterShift]
    rw [iterShift_right_step r ord]

theorem shiftRight1_shiftLeft1 {N : Nat} (ord : Fin N → Fin N) :
    shiftRight1 (shiftLeft1 ord) = ord := by
  funext ⟨i, hi⟩
  simp only [shiftRight1, shiftLeft1]
  by_cases hi0 : i = 0
  · subst hi0
    simp only [↓reduceDIte]
    have hfalse : ¬ (N - 1 + 1 < N) := by omega
    simp only [hfalse, ↓reduceDIte]
  · simp only [hi0, ↓reduceDIte]
    have hlt : i - 1 + 1 < N := by omega
    simp only [hlt, ↓reduceDIte]
    congr 1
    apply Fin.ext
    dsimp only
    omega

theorem shiftLeft1_injective {N : Nat} {ord : Fin N → Fin N}
    (hinj : IsInjective ord) : IsInjective (shiftLeft1 ord) := by
  intro i j hij
  simp only [shiftLeft1] at hij
  by_cases hi : i.1 + 1 < N <;> by_cases hj : j.1 + 1 < N
  · simp only [hi, hj, ↓reduceDIte] at hij
    have h : i.1 + 1 = j.1 + 1 := congrArg Fin.val (hinj _ _ hij)
    apply Fin.ext; omega
  · simp only [hi, hj, ↓reduceDIte] at hij
    have h : i.1 + 1 = 0 := congrArg Fin.val (hinj _ _ hij)
    omega
  · simp only [hi, hj, ↓reduceDIte] at hij
    have h : 0 = j.1 + 1 := congrArg Fin.val (hinj _ _ hij)
    omega
  · apply Fin.ext; have := i.2; have := j.2; omega

theorem iterShift_injective {N : Nat} (r : Nat) {ord : Fin N → Fin N}
    (hinj : IsInjective ord) : IsInjective (iterShift r ord) := by
  induction r with
  | zero => exact hinj
  | succ r ih => exact shiftLeft1_injective ih

theorem isOrderNC_shiftLeft1 {N : Nat} (ord : Fin N → Fin N) (π : SetPartition N)
    (hnc : IsOrderNC ord π) : IsOrderNC (shiftLeft1 ord) π := by
  intro a b c d hab hbc hcd hac hbd
  have ha : a.1 + 1 < N := by have := d.2; omega
  have hb : b.1 + 1 < N := by have := d.2; omega
  have hc : c.1 + 1 < N := by have := d.2; omega
  by_cases hd : d.1 + 1 < N
  · simp only [shiftLeft1, ha, hb, hc, hd, ↓reduceDIte] at hac hbd ⊢
    exact hnc ⟨a.1 + 1, ha⟩ ⟨b.1 + 1, hb⟩ ⟨c.1 + 1, hc⟩ ⟨d.1 + 1, hd⟩
      (by dsimp only; omega) (by dsimp only; omega) (by dsimp only; omega) hac hbd
  · have hn_pos : 0 < N := Nat.lt_of_le_of_lt (Nat.zero_le _) d.2
    simp only [shiftLeft1, ha, hb, hc, hd, ↓reduceDIte] at hac hbd ⊢
    have h0b : π.rel (ord ⟨0, hn_pos⟩) (ord ⟨b.1 + 1, hb⟩) = true := π.rel_symm _ _ hbd
    have h0a : π.rel (ord ⟨0, hn_pos⟩) (ord ⟨a.1 + 1, ha⟩) = true :=
      hnc ⟨0, hn_pos⟩ ⟨a.1 + 1, ha⟩ ⟨b.1 + 1, hb⟩ ⟨c.1 + 1, hc⟩
        (by dsimp only; omega) (by dsimp only; omega) (by dsimp only; omega) h0b hac
    exact π.rel_trans _ _ _ (π.rel_symm _ _ h0a) h0b

theorem isOrderNC_shiftRight1 {N : Nat} (ord : Fin N → Fin N) (π : SetPartition N)
    (hnc : IsOrderNC ord π) : IsOrderNC (shiftRight1 ord) π := by
  intro a b c d hab hbc hcd hac hbd
  have hb0 : b.1 ≠ 0 := by omega
  have hc0 : c.1 ≠ 0 := by omega
  have hd0 : d.1 ≠ 0 := by omega
  have hbn : b.1 - 1 < N := by have := b.2; omega
  have hcn : c.1 - 1 < N := by have := c.2; omega
  have hdn : d.1 - 1 < N := by have := d.2; omega
  by_cases ha0 : a.1 = 0
  · have hn1 : N - 1 < N := by have := d.2; omega
    simp only [shiftRight1, ha0, hb0, hc0, hd0, ↓reduceDIte] at hac hbd ⊢
    have hca : π.rel (ord ⟨c.1 - 1, hcn⟩) (ord ⟨N - 1, hn1⟩) = true := π.rel_symm _ _ hac
    have hbc_rel : π.rel (ord ⟨b.1 - 1, hbn⟩) (ord ⟨c.1 - 1, hcn⟩) = true :=
      hnc ⟨b.1 - 1, hbn⟩ ⟨c.1 - 1, hcn⟩ ⟨d.1 - 1, hdn⟩ ⟨N - 1, hn1⟩
        (by dsimp only; omega) (by dsimp only; omega) (by dsimp only; have := d.2; omega) hbd hca
    exact π.rel_symm _ _ (π.rel_trans _ _ _ hbc_rel hca)
  · have han : a.1 - 1 < N := by have := a.2; omega
    simp only [shiftRight1, ha0, hb0, hc0, hd0, ↓reduceDIte] at hac hbd ⊢
    exact hnc ⟨a.1 - 1, han⟩ ⟨b.1 - 1, hbn⟩ ⟨c.1 - 1, hcn⟩ ⟨d.1 - 1, hdn⟩
      (by dsimp only; omega) (by dsimp only; omega) (by dsimp only; omega) hac hbd

theorem isOrderNC_iterShift_iff {N : Nat} (r : Nat) (ord : Fin N → Fin N) (π : SetPartition N) :
    IsOrderNC (iterShift r ord) π ↔ IsOrderNC ord π := by
  induction r with
  | zero => exact Iff.rfl
  | succ r ih =>
    simp only [iterShift]
    constructor
    · intro h
      have hr := isOrderNC_shiftRight1 (shiftLeft1 (iterShift r ord)) π h
      rw [shiftRight1_shiftLeft1] at hr
      exact ih.mp hr
    · intro h
      exact isOrderNC_shiftLeft1 (iterShift r ord) π (ih.mpr h)

/-! ## Mingo–Nica Annular Noncrossing Partitions `NC_A(p, q)` -/

def outerIdx {p q : Nat} (i : Fin p) : Fin (p + q) := ⟨i.1, by omega⟩
def innerIdx {p q : Nat} (j : Fin q) : Fin (p + q) := ⟨p + j.1, by omega⟩

def restrictOuter (p q : Nat) (π : SetPartition (p + q)) : SetPartition p where
  rel i i' := π.rel (outerIdx i) (outerIdx i')
  rel_refl i := π.rel_refl (outerIdx i)
  rel_symm _ _ h := π.rel_symm _ _ h
  rel_trans _ _ _ h1 h2 := π.rel_trans _ _ _ h1 h2

def restrictInner (p q : Nat) (π : SetPartition (p + q)) : SetPartition q where
  rel j j' := π.rel (innerIdx j) (innerIdx j')
  rel_refl j := π.rel_refl (innerIdx j)
  rel_symm _ _ h := π.rel_symm _ _ h
  rel_trans _ _ _ h1 h2 := π.rel_trans _ _ _ h1 h2

def HasThroughBlock (p q : Nat) (π : SetPartition (p + q)) : Prop :=
  ∃ (i : Fin p) (j : Fin q), π.rel (outerIdx i) (innerIdx j) = true

/-- Cut-annulus linear ordering `(rot_{r1}(0..p-1), p + rot_{r2}(0..q-1))`. -/
def annularCutOrder (p q : Nat) (r1 r2 : Nat) : Fin (p + q) → Fin (p + q) :=
  fun k =>
    if hk : k.1 < p then
      outerIdx ((iterShift r1 id) ⟨k.1, hk⟩)
    else
      innerIdx ((iterShift r2 id) ⟨k.1 - p, by omega⟩)

/-- Mingo–Nica annular noncrossing set partition predicate `NC_A(p, q)`. -/
def IsAnnularNC (p q : Nat) (π : SetPartition (p + q)) : Prop :=
  (¬ HasThroughBlock p q π ∧ IsDiscNC (restrictOuter p q π) ∧ IsDiscNC (restrictInner p q π)) ∨
  (HasThroughBlock p q π ∧ ∃ r1 r2 : Nat, IsOrderNC (annularCutOrder p q r1 r2) π)

/-- Circular-boundary noncrossing partition predicate `NC_∂^∘(p)` (`p` circle vertices + boundary `p`). -/
def IsCircBoundaryNC (p : Nat) (π : SetPartition (p + 1)) : Prop :=
  IsDiscNC (restrictOuter p 1 π)

/-! ## Universal Punctured-Annulus Theorem: `NC_A(p, 1) = NC_∂^∘(p)` -/

theorem iterShift_at_zero {p : Nat} (hp : 0 < p) :
    ∀ (k : Nat) (ord : Fin p → Fin p) (hk : k < p),
      (iterShift k ord) ⟨0, hp⟩ = ord ⟨k, hk⟩
  | 0, _, _ => rfl
  | k + 1, ord, hk => by
    simp only [iterShift]
    rw [← iterShift_right_step k ord]
    rw [iterShift_at_zero hp k (shiftLeft1 ord) (by omega)]
    simp only [shiftLeft1, hk, ↓reduceDIte]

theorem iterShift_put_last {p : Nat} (i₀ : Fin p) :
    (iterShift (i₀.1 + 1) (id : Fin p → Fin p)) ⟨p - 1, by have := i₀.2; omega⟩ = i₀ := by
  have hp : 0 < p := Nat.lt_of_le_of_lt (Nat.zero_le _) i₀.2
  simp only [iterShift, shiftLeft1]
  have hnot : ¬ (p - 1 + 1 < p) := by omega
  simp only [hnot, ↓reduceDIte]
  rw [iterShift_at_zero hp i₀.1 id i₀.2]
  rfl

/-- **Universal Theorem (Punctured Annulus = Circular Boundary):**
For every `p : Nat` and every partition `π` of `Fin (p + 1)`,
`π ∈ NC_A(p, 1)` if and only if `π|_{[p]} ∈ NC(p)` (`π ∈ NC_∂^∘(p)`). -/
theorem annularNC_p_one_iff_circBoundary (p : Nat) (π : SetPartition (p + 1)) :
    IsAnnularNC p 1 π ↔ IsCircBoundaryNC p π := by
  constructor
  · intro hann
    rcases hann with ⟨_, hout, _⟩ | ⟨_, r1, _, hcut⟩
    · exact hout
    · unfold IsCircBoundaryNC IsDiscNC
      rw [← isOrderNC_iterShift_iff r1 id (restrictOuter p 1 π)]
      intro a b c d hab hbc hcd hac hbd
      have ha : a.1 < p := a.2
      have hb : b.1 < p := b.2
      have hc : c.1 < p := c.2
      have hd : d.1 < p := d.2
      have hcut4 := hcut ⟨a.1, by omega⟩ ⟨b.1, by omega⟩ ⟨c.1, by omega⟩ ⟨d.1, by omega⟩
        (by dsimp only; exact hab) (by dsimp only; exact hbc) (by dsimp only; exact hcd)
      simp only [annularCutOrder, ha, hb, hc, hd, ↓reduceDIte] at hcut4
      exact hcut4 hac hbd
  · intro hout
    by_cases hth : HasThroughBlock p 1 π
    · right
      refine ⟨hth, ?_⟩
      rcases hth with ⟨i₀, j₀, hij₀⟩
      have hj0 : j₀ = ⟨0, Nat.zero_lt_one⟩ := by apply Fin.ext; have := j₀.2; omega
      subst hj0
      refine ⟨i₀.1 + 1, 0, ?_⟩
      have hout_rot : IsOrderNC (iterShift (i₀.1 + 1) id) (restrictOuter p 1 π) :=
        (isOrderNC_iterShift_iff (i₀.1 + 1) id (restrictOuter p 1 π)).mpr hout
      intro a b c d hab hbc hcd hac hbd
      have ha : a.1 < p := by have := d.2; omega
      have hb : b.1 < p := by have := d.2; omega
      have hc : c.1 < p := by have := d.2; omega
      by_cases hd : d.1 < p
      · simp only [annularCutOrder, ha, hb, hc, hd, ↓reduceDIte] at hac hbd ⊢
        exact hout_rot ⟨a.1, ha⟩ ⟨b.1, hb⟩ ⟨c.1, hc⟩ ⟨d.1, hd⟩
          (by dsimp only; exact hab) (by dsimp only; exact hbc) (by dsimp only; exact hcd) hac hbd
      · have hdp : d.1 = p := by have := d.2; omega
        have hlast_lt : p - 1 < p := by have := i₀.2; omega
        have hord_d : annularCutOrder p 1 (i₀.1 + 1) 0 d = innerIdx ⟨0, Nat.zero_lt_one⟩ := by
          simp only [annularCutOrder, hd, ↓reduceDIte, iterShift, id]
          congr 1; apply Fin.ext; dsimp only; omega
        have hord_last : annularCutOrder p 1 (i₀.1 + 1) 0 ⟨p - 1, by omega⟩ = outerIdx i₀ := by
          simp only [annularCutOrder, hlast_lt, ↓reduceDIte]
          rw [iterShift_put_last i₀]
        by_cases hcp1 : c.1 = p - 1
        · have hc_eq : c = ⟨p - 1, by omega⟩ := Fin.ext hcp1
          rw [hc_eq, hord_last] at hac
          rw [hord_d] at hbd
          have had : π.rel (annularCutOrder p 1 (i₀.1 + 1) 0 a) (innerIdx ⟨0, Nat.zero_lt_one⟩) = true :=
            π.rel_trans _ _ _ hac hij₀
          exact π.rel_trans _ _ _ had (π.rel_symm _ _ hbd)
        · have hc_lt : c.1 < p - 1 := by omega
          rw [hord_d] at hbd
          have hb_i0 : π.rel (annularCutOrder p 1 (i₀.1 + 1) 0 b) (outerIdx i₀) = true :=
            π.rel_trans _ _ _ hbd (π.rel_symm _ _ hij₀)
          simp only [annularCutOrder, ha, hb, hc, ↓reduceDIte] at hac hb_i0 ⊢
          have hb_last : (restrictOuter p 1 π).rel
              (iterShift (i₀.1 + 1) id ⟨b.1, hb⟩) (iterShift (i₀.1 + 1) id ⟨p - 1, hlast_lt⟩) = true := by
            dsimp only [restrictOuter]
            rw [iterShift_put_last i₀]
            exact hb_i0
          exact hout_rot ⟨a.1, ha⟩ ⟨b.1, hb⟩ ⟨c.1, hc⟩ ⟨p - 1, hlast_lt⟩
            (by dsimp only; exact hab) (by dsimp only; exact hbc) (by dsimp only; exact hc_lt) hac hb_last
    · left
      refine ⟨hth, hout, ?_⟩
      intro a b _ _ hab _ _ _ _
      have := a.2; have := b.2; omega

theorem annularNC_p_one_meet_closed (p : Nat) {σ τ : SetPartition (p + 1)}
    (hσ : IsAnnularNC p 1 σ) (hτ : IsAnnularNC p 1 τ) :
    IsAnnularNC p 1 (meetPartition σ τ) := by
  rw [annularNC_p_one_iff_circBoundary] at hσ hτ ⊢
  exact isDiscNC_meet hσ hτ

theorem annularNC_p_one_bot_top (p : Nat) :
    IsAnnularNC p 1 (botPartition (p + 1)) ∧ IsAnnularNC p 1 (topPartition (p + 1)) := by
  rw [annularNC_p_one_iff_circBoundary, annularNC_p_one_iff_circBoundary]
  have hbot : restrictOuter p 1 (botPartition (p + 1)) = botPartition p := by
    apply SetPartition.ext
    intro i j
    simp only [restrictOuter, botPartition, outerIdx]
    by_cases h : i = j
    · subst h; simp
    · have hv : i.1 ≠ j.1 := fun e => h (Fin.ext e)
      have hv' : (⟨i.1, by omega⟩ : Fin (p + 1)) ≠ ⟨j.1, by omega⟩ := fun e =>
        hv (by have he := congrArg Fin.val e; dsimp only at he; exact he)
      simp [h, hv']
  have htop : restrictOuter p 1 (topPartition (p + 1)) = topPartition p :=
    SetPartition.ext (fun _ _ => rfl)
  unfold IsCircBoundaryNC
  rw [hbot, htop]
  exact ⟨isDiscNC_bot p, isDiscNC_top p⟩

/-! ## Universal Annular Join-Semilattice Failure for `p ≥ q ≥ 2` with `p + q ≥ 6` -/

theorem annularCutOrder_injective (p q r1 r2 : Nat) :
    IsInjective (annularCutOrder p q r1 r2) := by
  have hinj1 := iterShift_injective r1 (fun (x y : Fin p) h => h)
  have hinj2 := iterShift_injective r2 (fun (x y : Fin q) h => h)
  intro i j hij
  simp only [annularCutOrder] at hij
  by_cases hi : i.1 < p <;> by_cases hj : j.1 < p
  · simp only [hi, hj, ↓reduceDIte, outerIdx, Fin.mk.injEq] at hij
    have heq := hinj1 ⟨i.1, hi⟩ ⟨j.1, hj⟩ (Fin.ext hij)
    have h : i.1 = j.1 := congrArg (@Fin.val p) heq
    exact Fin.ext h
  · simp only [hi, hj, ↓reduceDIte, outerIdx, innerIdx, Fin.mk.injEq] at hij
    have := ((iterShift r1 id) ⟨i.1, hi⟩).2
    omega
  · simp only [hi, hj, ↓reduceDIte, outerIdx, innerIdx, Fin.mk.injEq] at hij
    have := ((iterShift r1 id) ⟨j.1, hj⟩).2
    omega
  · simp only [hi, hj, ↓reduceDIte, innerIdx, Fin.mk.injEq] at hij
    have hval := Nat.add_left_cancel hij
    have heq := hinj2 ⟨i.1 - p, by omega⟩ ⟨j.1 - p, by omega⟩ (Fin.ext hval)
    have h : i.1 - p = j.1 - p := congrArg (@Fin.val q) heq
    apply Fin.ext; omega

theorem iterShift_two_at {m : Nat} (hm : 2 ≤ m) (k : Fin m) :
    ((iterShift 2 (id : Fin m → Fin m)) k).1 =
      if k.1 + 2 < m then k.1 + 2 else k.1 + 2 - m := by
  simp only [iterShift, shiftLeft1, id]
  by_cases hk1 : k.1 + 1 < m
  · rw [dif_pos hk1]
    by_cases hk2 : (⟨k.1 + 1, hk1⟩ : Fin m).1 + 1 < m
    · rw [dif_pos hk2, if_pos (by dsimp only at hk2; omega)]
    · rw [dif_neg hk2, if_neg (by dsimp only at hk2; omega)]
      dsimp only at hk2 ⊢; omega
  · rw [dif_neg hk1]
    have h01 : (⟨0, Nat.lt_of_le_of_lt (Nat.zero_le _) k.2⟩ : Fin m).1 + 1 < m := by
      dsimp only; omega
    rw [dif_pos h01, if_neg (by omega)]
    dsimp only; have := k.2; omega

theorem iterShift_surj {m : Nat} (r : Nat) (y : Fin m) :
    ∃ j : Fin m, (iterShift r (id : Fin m → Fin m)) j = y := by
  induction r with
  | zero => exact ⟨y, rfl⟩
  | succ r ih =>
    rcases ih with ⟨j', hj'⟩
    by_cases hj0 : j'.1 = 0
    · refine ⟨⟨m - 1, by have := j'.2; omega⟩, ?_⟩
      simp only [iterShift, shiftLeft1]
      rw [dif_neg (by have := j'.2; omega), ← hj']
      congr 1
      exact Fin.ext hj0.symm
    · refine ⟨⟨j'.1 - 1, by have := j'.2; omega⟩, ?_⟩
      simp only [iterShift, shiftLeft1]
      have hlt : (⟨j'.1 - 1, by have := j'.2; omega⟩ : Fin m).1 + 1 < m := by
        dsimp only; have := j'.2; omega
      rw [dif_pos hlt]
      have hjeq : (⟨j'.1 - 1 + 1, hlt⟩ : Fin m) = j' := by apply Fin.ext; dsimp only; omega
      rw [hjeq, hj']

/-- Noncrossing lemma for `mkThreeBlocks b1 false false` (single non-singleton block). -/
theorem isOrderNC_one_block {N : Nat} {b1 : Fin N → Bool} {ord : Fin N → Fin N}
    (hinj : IsInjective ord) :
    IsOrderNC ord (mkThreeBlocks b1 (fun _ => false) (fun _ => false)
      (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)) := by
  intro a b c d hab hbc hcd hac hbd
  have hne_ac : ord a ≠ ord c := fun h => by have hv : a.1 = c.1 := congrArg Fin.val (hinj _ _ h); omega
  have hne_bd : ord b ≠ ord d := fun h => by have hv : b.1 = d.1 := congrArg Fin.val (hinj _ _ h); omega
  simp only [mkThreeBlocks, hne_ac, hne_bd, decide_false, Bool.false_or, Bool.and_false, Bool.or_false,
             Bool.and_eq_true] at hac hbd ⊢
  simp [hac.1, hbd.1]

/-- Interval-separation lemma for `mkThreeBlocks b1 b2 false`: if `b2` lies inside index
interval `[L, R]` while `b1` lies strictly outside `[L, R]`, then `π` is `ord`-noncrossing. -/
theorem isOrderNC_two_blocks_sep {N : Nat} {b1 b2 : Fin N → Bool}
    (h12 : ∀ v, b1 v = true → b2 v = false)
    {ord : Fin N → Fin N} (hinj : IsInjective ord) (L R : Nat)
    (hin2 : ∀ idx : Fin N, b2 (ord idx) = true → L ≤ idx.1 ∧ idx.1 ≤ R)
    (hout1 : ∀ idx : Fin N, b1 (ord idx) = true → idx.1 < L ∨ R < idx.1) :
    IsOrderNC ord (mkThreeBlocks b1 b2 (fun _ => false) h12 (fun _ _ => rfl) (fun _ _ => rfl)) := by
  intro a b c d hab hbc hcd hac hbd
  have hne_ac : ord a ≠ ord c := fun h => by have hv : a.1 = c.1 := congrArg Fin.val (hinj _ _ h); omega
  have hne_bd : ord b ≠ ord d := fun h => by have hv : b.1 = d.1 := congrArg Fin.val (hinj _ _ h); omega
  simp only [mkThreeBlocks, hne_ac, hne_bd, decide_false, Bool.false_or, Bool.and_false, Bool.or_false,
             Bool.or_eq_true, Bool.and_eq_true] at hac hbd ⊢
  rcases hac with ⟨ha1, hc1⟩ | ⟨ha2, hc2⟩
  · rcases hbd with ⟨hb1, _⟩ | ⟨hb2, hd2⟩
    · simp [ha1, hb1]
    · have hb_in := hin2 b hb2
      have hd_in := hin2 d hd2
      rcases hout1 c hc1 with hc_lt | hc_gt <;> omega
  · rcases hbd with ⟨hb1, _⟩ | ⟨hb2, _⟩
    · have ha_in := hin2 a ha2
      have hc_in := hin2 c hc2
      rcases hout1 b hb1 with hb_lt | hb_gt <;> omega
    · simp [ha2, hb2]

/-- Adjacent-pair specialization of `isOrderNC_two_blocks_sep`. -/
theorem isOrderNC_two_blocks_adj_sep {N : Nat} {b1 b2 : Fin N → Bool}
    (h12 : ∀ v, b1 v = true → b2 v = false)
    {ord : Fin N → Fin N} (hinj : IsInjective ord)
    (idxA idxB vA vB : Fin N)
    (hadj : idxB.1 = idxA.1 + 1)
    (hA : ord idxA = vA) (hB : ord idxB = vB)
    (hb2_iff : ∀ v : Fin N, b2 v = true ↔ (v = vA ∨ v = vB)) :
    IsOrderNC ord (mkThreeBlocks b1 b2 (fun _ => false) h12 (fun _ _ => rfl) (fun _ _ => rfl)) := by
  apply isOrderNC_two_blocks_sep h12 hinj idxA.1 idxB.1
  · intro idx h2
    rcases (hb2_iff (ord idx)).mp h2 with heqA | heqB
    · have hidx : idx = idxA := hinj _ _ (heqA.trans hA.symm)
      subst hidx; omega
    · have hidx : idx = idxB := hinj _ _ (heqB.trans hB.symm)
      subst hidx; omega
  · intro idx h1
    by_cases hlt : idx.1 < idxA.1
    · exact Or.inl hlt
    · by_cases hgt : idxB.1 < idx.1
      · exact Or.inr hgt
      · exfalso
        have hcases : idx.1 = idxA.1 ∨ idx.1 = idxB.1 := by omega
        rcases hcases with heq | heq
        · have hidx : idx = idxA := Fin.ext heq
          rw [hidx, hA] at h1
          have h2 : b2 vA = true := (hb2_iff vA).mpr (Or.inl rfl)
          exact Bool.noConfusion ((h12 vA h1).symm.trans h2)
        · have hidx : idx = idxB := Fin.ext heq
          rw [hidx, hB] at h1
          have h2 : b2 vB = true := (hb2_iff vB).mpr (Or.inr rfl)
          exact Bool.noConfusion ((h12 vB h1).symm.trans h2)

/-- Cyclic 4-point order invariant under `shiftLeft1` on `Fin p` (`p ≥ 4`). -/
def IsCyclic4 {p : Nat} (x₀ x₁ x₂ x₃ : Fin p) (ord : Fin p → Fin p) : Prop :=
  ∃ i₀ i₁ i₂ i₃ : Fin p,
    ord i₀ = x₀ ∧ ord i₁ = x₁ ∧ ord i₂ = x₂ ∧ ord i₃ = x₃ ∧
    ((i₀.1 < i₁.1 ∧ i₁.1 < i₂.1 ∧ i₂.1 < i₃.1) ∨
     (i₁.1 < i₂.1 ∧ i₂.1 < i₃.1 ∧ i₃.1 < i₀.1) ∨
     (i₂.1 < i₃.1 ∧ i₃.1 < i₀.1 ∧ i₀.1 < i₁.1) ∨
     (i₃.1 < i₀.1 ∧ i₀.1 < i₁.1 ∧ i₁.1 < i₂.1))

theorem isCyclic4_shiftLeft1 {p : Nat} (hp : 4 ≤ p) {x₀ x₁ x₂ x₃ : Fin p} {ord : Fin p → Fin p}
    (hc : IsCyclic4 x₀ x₁ x₂ x₃ ord) : IsCyclic4 x₀ x₁ x₂ x₃ (shiftLeft1 ord) := by
  rcases hc with ⟨i₀, i₁, i₂, i₃, h0, h1, h2, h3, hord⟩
  let prevIdx (i : Fin p) : Fin p :=
    if i.1 = 0 then ⟨p - 1, by omega⟩ else ⟨i.1 - 1, by omega⟩
  have hprev : ∀ i : Fin p, shiftLeft1 ord (prevIdx i) = ord i := by
    intro i
    by_cases hi0 : i.1 = 0
    · have hp_eq : prevIdx i = ⟨p - 1, by omega⟩ := if_pos hi0
      rw [hp_eq]
      simp only [shiftLeft1]
      rw [dif_neg (by omega)]
      congr 1; exact Fin.ext hi0.symm
    · have hp_eq : prevIdx i = ⟨i.1 - 1, by omega⟩ := if_neg hi0
      rw [hp_eq]
      simp only [shiftLeft1]
      have hlt : (⟨i.1 - 1, by omega⟩ : Fin p).1 + 1 < p := by dsimp only; have := i.2; omega
      rw [dif_pos hlt]
      congr 1; apply Fin.ext; dsimp only; omega
  refine ⟨prevIdx i₀, prevIdx i₁, prevIdx i₂, prevIdx i₃,
          (hprev i₀).trans h0, (hprev i₁).trans h1, (hprev i₂).trans h2, (hprev i₃).trans h3, ?_⟩
  rcases hord with hA | hB | hC | hD
  · by_cases z : i₀.1 = 0
    · right; left
      have hne1 : i₁.1 ≠ 0 := by omega
      have hne2 : i₂.1 ≠ 0 := by omega
      have hne3 : i₃.1 ≠ 0 := by omega
      simp only [prevIdx, z, hne1, hne2, hne3, ↓reduceIte]; have := i₃.2; omega
    · left
      have hne1 : i₁.1 ≠ 0 := by omega
      have hne2 : i₂.1 ≠ 0 := by omega
      have hne3 : i₃.1 ≠ 0 := by omega
      simp only [prevIdx, z, hne1, hne2, hne3, ↓reduceIte]; omega
  · by_cases z : i₁.1 = 0
    · right; right; left
      have hne2 : i₂.1 ≠ 0 := by omega
      have hne3 : i₃.1 ≠ 0 := by omega
      have hne0 : i₀.1 ≠ 0 := by omega
      simp only [prevIdx, z, hne2, hne3, hne0, ↓reduceIte]; have := i₀.2; omega
    · right; left
      have hne2 : i₂.1 ≠ 0 := by omega
      have hne3 : i₃.1 ≠ 0 := by omega
      have hne0 : i₀.1 ≠ 0 := by omega
      simp only [prevIdx, z, hne2, hne3, hne0, ↓reduceIte]; omega
  · by_cases z : i₂.1 = 0
    · right; right; right
      have hne3 : i₃.1 ≠ 0 := by omega
      have hne0 : i₀.1 ≠ 0 := by omega
      have hne1 : i₁.1 ≠ 0 := by omega
      simp only [prevIdx, z, hne3, hne0, hne1, ↓reduceIte]; have := i₁.2; omega
    · right; right; left
      have hne3 : i₃.1 ≠ 0 := by omega
      have hne0 : i₀.1 ≠ 0 := by omega
      have hne1 : i₁.1 ≠ 0 := by omega
      simp only [prevIdx, z, hne3, hne0, hne1, ↓reduceIte]; omega
  · by_cases z : i₃.1 = 0
    · left
      have hne0 : i₀.1 ≠ 0 := by omega
      have hne1 : i₁.1 ≠ 0 := by omega
      have hne2 : i₂.1 ≠ 0 := by omega
      simp only [prevIdx, z, hne0, hne1, hne2, ↓reduceIte]; have := i₂.2; omega
    · right; right; right
      have hne0 : i₀.1 ≠ 0 := by omega
      have hne1 : i₁.1 ≠ 0 := by omega
      have hne2 : i₂.1 ≠ 0 := by omega
      simp only [prevIdx, z, hne0, hne1, hne2, ↓reduceIte]; omega

theorem isCyclic4_iter {p : Nat} (hp : 4 ≤ p) (r : Nat) :
    IsCyclic4 ⟨0, by omega⟩ ⟨1, by omega⟩ ⟨2, by omega⟩ ⟨3, by omega⟩
      (iterShift r (id : Fin p → Fin p)) := by
  induction r with
  | zero =>
    exact ⟨⟨0, by omega⟩, ⟨1, by omega⟩, ⟨2, by omega⟩, ⟨3, by omega⟩,
           rfl, rfl, rfl, rfl, Or.inl ⟨by dsimp only; omega, by dsimp only; omega, by dsimp only; omega⟩⟩
  | succ r ih => exact isCyclic4_shiftLeft1 hp ih

/-- Cyclic 3-point order invariant under `shiftLeft1` on `Fin m` (`m ≥ 3`). -/
def IsCyclic3 {m : Nat} (x₀ x₁ x₂ : Fin m) (ord : Fin m → Fin m) : Prop :=
  ∃ i₀ i₁ i₂ : Fin m,
    ord i₀ = x₀ ∧ ord i₁ = x₁ ∧ ord i₂ = x₂ ∧
    ((i₀.1 < i₁.1 ∧ i₁.1 < i₂.1) ∨
     (i₁.1 < i₂.1 ∧ i₂.1 < i₀.1) ∨
     (i₂.1 < i₀.1 ∧ i₀.1 < i₁.1))

theorem isCyclic3_shiftLeft1 {m : Nat} (hm : 3 ≤ m) {x₀ x₁ x₂ : Fin m} {ord : Fin m → Fin m}
    (hc : IsCyclic3 x₀ x₁ x₂ ord) : IsCyclic3 x₀ x₁ x₂ (shiftLeft1 ord) := by
  rcases hc with ⟨i₀, i₁, i₂, h0, h1, h2, hord⟩
  let prevIdx (i : Fin m) : Fin m :=
    if i.1 = 0 then ⟨m - 1, by omega⟩ else ⟨i.1 - 1, by omega⟩
  have hprev : ∀ i : Fin m, shiftLeft1 ord (prevIdx i) = ord i := by
    intro i
    by_cases hi0 : i.1 = 0
    · have hp_eq : prevIdx i = ⟨m - 1, by omega⟩ := if_pos hi0
      rw [hp_eq]
      simp only [shiftLeft1]
      rw [dif_neg (by omega)]
      congr 1; exact Fin.ext hi0.symm
    · have hp_eq : prevIdx i = ⟨i.1 - 1, by omega⟩ := if_neg hi0
      rw [hp_eq]
      simp only [shiftLeft1]
      have hlt : (⟨i.1 - 1, by omega⟩ : Fin m).1 + 1 < m := by dsimp only; have := i.2; omega
      rw [dif_pos hlt]
      congr 1; apply Fin.ext; dsimp only; omega
  refine ⟨prevIdx i₀, prevIdx i₁, prevIdx i₂,
          (hprev i₀).trans h0, (hprev i₁).trans h1, (hprev i₂).trans h2, ?_⟩
  rcases hord with hA | hB | hC
  · by_cases z : i₀.1 = 0
    · right; left
      have hne1 : i₁.1 ≠ 0 := by omega
      have hne2 : i₂.1 ≠ 0 := by omega
      simp only [prevIdx, z, hne1, hne2, ↓reduceIte]; have := i₂.2; omega
    · left
      have hne1 : i₁.1 ≠ 0 := by omega
      have hne2 : i₂.1 ≠ 0 := by omega
      simp only [prevIdx, z, hne1, hne2, ↓reduceIte]; omega
  · by_cases z : i₁.1 = 0
    · right; right
      have hne2 : i₂.1 ≠ 0 := by omega
      have hne0 : i₀.1 ≠ 0 := by omega
      simp only [prevIdx, z, hne2, hne0, ↓reduceIte]; have := i₀.2; omega
    · right; left
      have hne2 : i₂.1 ≠ 0 := by omega
      have hne0 : i₀.1 ≠ 0 := by omega
      simp only [prevIdx, z, hne2, hne0, ↓reduceIte]; omega
  · by_cases z : i₂.1 = 0
    · left
      have hne0 : i₀.1 ≠ 0 := by omega
      have hne1 : i₁.1 ≠ 0 := by omega
      simp only [prevIdx, z, hne0, hne1, ↓reduceIte]; have := i₁.2; omega
    · right; right
      have hne0 : i₀.1 ≠ 0 := by omega
      have hne1 : i₁.1 ≠ 0 := by omega
      simp only [prevIdx, z, hne0, hne1, ↓reduceIte]; omega

theorem isCyclic3_iter {m : Nat} (hm : 3 ≤ m) (r : Nat) :
    IsCyclic3 ⟨0, by omega⟩ ⟨1, by omega⟩ ⟨2, by omega⟩
      (iterShift r (id : Fin m → Fin m)) := by
  induction r with
  | zero =>
    exact ⟨⟨0, by omega⟩, ⟨1, by omega⟩, ⟨2, by omega⟩, rfl, rfl, rfl,
           Or.inl ⟨by dsimp only; omega, by dsimp only; omega⟩⟩
  | succ r ih => exact isCyclic3_shiftLeft1 hm ih

/-- **Universal Theorem (Join Failure of `NC_A(p, q)` for `p ≥ 4, q ≥ 2`):** -/
theorem annularNC_no_lub_ge_4_2 {p q : Nat} (hp : 4 ≤ p) (hq : 2 ≤ q) :
    ∃ σ τ : SetPartition (p + q),
      IsAnnularNC p q σ ∧ IsAnnularNC p q τ ∧
      ¬ ∃ u : SetPartition (p + q),
          IsAnnularNC p q u ∧ Refines σ u ∧ Refines τ u ∧
          (∀ w : SetPartition (p + q), IsAnnularNC p q w → Refines σ w → Refines τ w → Refines u w) := by
  let b02 (v : Fin (p + q)) : Bool := decide (v.1 = 0 ∨ v.1 = 2)
  let b1p1 (v : Fin (p + q)) : Bool := decide (v.1 = 1 ∨ v.1 = p + 1)
  let b3p (v : Fin (p + q)) : Bool := decide (v.1 = 3 ∨ v.1 = p)
  let b012p1 (v : Fin (p + q)) : Bool := decide (v.1 = 0 ∨ v.1 = 1 ∨ v.1 = 2 ∨ v.1 = p + 1)
  let b023p (v : Fin (p + q)) : Bool := decide (v.1 = 0 ∨ v.1 = 2 ∨ v.1 = 3 ∨ v.1 = p)

  have d_02_1p1 : ∀ v, b02 v = true → b1p1 v = false := by
    intro v h; simp only [b02, b1p1, decide_eq_true_eq, decide_eq_false_iff_not] at h ⊢; omega
  have d_02_3p : ∀ v, b02 v = true → b3p v = false := by
    intro v h; simp only [b02, b3p, decide_eq_true_eq, decide_eq_false_iff_not] at h ⊢; omega
  have d_1p1_3p : ∀ v, b1p1 v = true → b3p v = false := by
    intro v h; simp only [b1p1, b3p, decide_eq_true_eq, decide_eq_false_iff_not] at h ⊢; omega
  have d_u1 : ∀ v, b012p1 v = true → b3p v = false := by
    intro v h; simp only [b012p1, b3p, decide_eq_true_eq, decide_eq_false_iff_not] at h ⊢; omega
  have d_u2 : ∀ v, b023p v = true → b1p1 v = false := by
    intro v h; simp only [b023p, b1p1, decide_eq_true_eq, decide_eq_false_iff_not] at h ⊢; omega

  let σ := mkThreeBlocks b3p (fun _ => false) (fun _ => false) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
  let τ := mkThreeBlocks b02 b1p1 (fun _ => false) d_02_1p1 (fun _ _ => rfl) (fun _ _ => rfl)
  let u₁ := mkThreeBlocks b012p1 b3p (fun _ => false) d_u1 (fun _ _ => rfl) (fun _ _ => rfl)
  let u₂ := mkThreeBlocks b023p b1p1 (fun _ => false) d_u2 (fun _ _ => rfl) (fun _ _ => rfl)
  let w₀ := mkThreeBlocks b02 b1p1 b3p d_02_1p1 d_02_3p d_1p1_3p

  have hσ_ann : IsAnnularNC p q σ := by
    right
    refine ⟨⟨⟨3, by omega⟩, ⟨0, by omega⟩, by simp [σ, mkThreeBlocks, b3p, outerIdx, innerIdx]⟩,
            0, 0, isOrderNC_one_block (annularCutOrder_injective p q 0 0)⟩

  have hu1_ann : IsAnnularNC p q u₁ := by
    right
    refine ⟨⟨⟨3, by omega⟩, ⟨0, by omega⟩, by simp [u₁, mkThreeBlocks, b3p, outerIdx, innerIdx]⟩,
            0, 0, ?_⟩
    have hord_id : ∀ idx : Fin (p + q), annularCutOrder p q 0 0 idx = idx := by
      intro idx
      simp only [annularCutOrder, iterShift, id]
      by_cases hlt : idx.1 < p
      · simp only [hlt, ↓reduceDIte, outerIdx]
      · simp only [hlt, ↓reduceDIte, innerIdx]; apply Fin.ext; dsimp only; omega
    apply isOrderNC_two_blocks_sep d_u1 (annularCutOrder_injective p q 0 0) 3 p
    · intro idx h2; rw [hord_id idx] at h2; simp only [b3p, decide_eq_true_eq] at h2; omega
    · intro idx h1; rw [hord_id idx] at h1; simp only [b012p1, decide_eq_true_eq] at h1; omega

  have hcut21_A : annularCutOrder p q 2 1 ⟨p - 1, by omega⟩ = ⟨1, by omega⟩ := by
    have hlt : p - 1 < p := by omega
    simp only [annularCutOrder, hlt, ↓reduceDIte, outerIdx]
    apply Fin.ext; dsimp only
    rw [iterShift_two_at (by omega) ⟨p - 1, hlt⟩]
    have hnot : ¬ (p - 1 + 2 < p) := by omega
    simp only [hnot, ↓reduceIte]; omega

  have hcut21_B : annularCutOrder p q 2 1 ⟨p, by omega⟩ = ⟨p + 1, by omega⟩ := by
    have hnot : ¬ (p < p) := by omega
    simp only [annularCutOrder, hnot, ↓reduceDIte, innerIdx, iterShift, shiftLeft1, id]
    have hq1 : (⟨p - p, by omega⟩ : Fin q).1 + 1 < q := by dsimp only; omega
    simp only [hq1, ↓reduceDIte]
    apply Fin.ext; dsimp only; omega

  have hb1p1_iff : ∀ v : Fin (p + q), b1p1 v = true ↔ (v = ⟨1, by omega⟩ ∨ v = ⟨p + 1, by omega⟩) := by
    intro v; simp only [b1p1, decide_eq_true_eq]
    exact ⟨fun h => h.elim (fun e => Or.inl (Fin.ext e)) (fun e => Or.inr (Fin.ext e)),
           fun h => h.elim (fun e => Or.inl (congrArg Fin.val e)) (fun e => Or.inr (congrArg Fin.val e))⟩

  have hτ_ann : IsAnnularNC p q τ := by
    right
    refine ⟨⟨⟨1, by omega⟩, ⟨1, by omega⟩, by simp [τ, mkThreeBlocks, b1p1, outerIdx, innerIdx]⟩,
            2, 1, isOrderNC_two_blocks_adj_sep d_02_1p1 (annularCutOrder_injective p q 2 1)
                    ⟨p - 1, by omega⟩ ⟨p, by omega⟩ ⟨1, by omega⟩ ⟨p + 1, by omega⟩
                    (by dsimp only; omega) hcut21_A hcut21_B hb1p1_iff⟩

  have hu2_ann : IsAnnularNC p q u₂ := by
    right
    refine ⟨⟨⟨3, by omega⟩, ⟨0, by omega⟩, by simp [u₂, mkThreeBlocks, b023p, outerIdx, innerIdx]⟩,
            2, 1, isOrderNC_two_blocks_adj_sep d_u2 (annularCutOrder_injective p q 2 1)
                    ⟨p - 1, by omega⟩ ⟨p, by omega⟩ ⟨1, by omega⟩ ⟨p + 1, by omega⟩
                    (by dsimp only; omega) hcut21_A hcut21_B hb1p1_iff⟩

  have hw0_not_ann : ¬ IsAnnularNC p q w₀ := by
    intro hw0
    have hth_w0 : HasThroughBlock p q w₀ :=
      ⟨⟨3, by omega⟩, ⟨0, by omega⟩, by simp [w₀, mkThreeBlocks, b3p, outerIdx, innerIdx]⟩
    rcases hw0 with ⟨hnot, _⟩ | ⟨_, r1, r2, hcut⟩
    · exact hnot hth_w0
    · rcases isCyclic4_iter hp r1 with ⟨i₀, i₁, i₂, i₃, hi0, hi1, hi2, hi3, hcyc⟩
      rcases iterShift_surj r2 (⟨0, by omega⟩ : Fin q) with ⟨j₀, hj0⟩
      rcases iterShift_surj r2 (⟨1, by omega⟩ : Fin q) with ⟨j₁, hj1⟩
      let k₀ : Fin (p + q) := ⟨i₀.1, by have := i₀.2; omega⟩
      let k₁ : Fin (p + q) := ⟨i₁.1, by have := i₁.2; omega⟩
      let k₂ : Fin (p + q) := ⟨i₂.1, by have := i₂.2; omega⟩
      let k₃ : Fin (p + q) := ⟨i₃.1, by have := i₃.2; omega⟩
      let m₀ : Fin (p + q) := ⟨p + j₀.1, by have := j₀.2; omega⟩
      let m₁ : Fin (p + q) := ⟨p + j₁.1, by have := j₁.2; omega⟩
      have hk0 : annularCutOrder p q r1 r2 k₀ = ⟨0, by omega⟩ := by
        simp only [annularCutOrder, k₀, i₀.2, ↓reduceDIte, outerIdx]; rw [hi0]
      have hk1 : annularCutOrder p q r1 r2 k₁ = ⟨1, by omega⟩ := by
        simp only [annularCutOrder, k₁, i₁.2, ↓reduceDIte, outerIdx]; rw [hi1]
      have hk2 : annularCutOrder p q r1 r2 k₂ = ⟨2, by omega⟩ := by
        simp only [annularCutOrder, k₂, i₂.2, ↓reduceDIte, outerIdx]; rw [hi2]
      have hk3 : annularCutOrder p q r1 r2 k₃ = ⟨3, by omega⟩ := by
        simp only [annularCutOrder, k₃, i₃.2, ↓reduceDIte, outerIdx]; rw [hi3]
      have hm0 : annularCutOrder p q r1 r2 m₀ = ⟨p, by omega⟩ := by
        have hnot : ¬ ((p + j₀.1) < p) := by omega
        simp only [annularCutOrder, m₀, hnot, ↓reduceDIte, innerIdx]
        have hsub : (⟨p + j₀.1 - p, by have := j₀.2; omega⟩ : Fin q) = j₀ := by
          apply Fin.ext; dsimp only; omega
        rw [hsub, hj0]; apply Fin.ext; dsimp only; omega
      have hm1 : annularCutOrder p q r1 r2 m₁ = ⟨p + 1, by omega⟩ := by
        have hnot : ¬ ((p + j₁.1) < p) := by omega
        simp only [annularCutOrder, m₁, hnot, ↓reduceDIte, innerIdx]
        have hsub : (⟨p + j₁.1 - p, by have := j₁.2; omega⟩ : Fin q) = j₁ := by
          apply Fin.ext; dsimp only; omega
        rw [hsub, hj1]
      have rel02 : w₀.rel ⟨0, by omega⟩ ⟨2, by omega⟩ = true := by simp [w₀, mkThreeBlocks, b02]
      have rel20 : w₀.rel ⟨2, by omega⟩ ⟨0, by omega⟩ = true := by simp [w₀, mkThreeBlocks, b02]
      have rel1p1 : w₀.rel ⟨1, by omega⟩ ⟨p + 1, by omega⟩ = true := by simp [w₀, mkThreeBlocks, b1p1]
      have rel3p : w₀.rel ⟨3, by omega⟩ ⟨p, by omega⟩ = true := by simp [w₀, mkThreeBlocks, b3p]
      have nrel01 : w₀.rel ⟨0, by omega⟩ ⟨1, by omega⟩ = false := by
        simp [w₀, mkThreeBlocks, b02, b1p1, b3p, Fin.ext_iff]; omega
      have nrel23 : w₀.rel ⟨2, by omega⟩ ⟨3, by omega⟩ = false := by
        simp [w₀, mkThreeBlocks, b02, b1p1, b3p, Fin.ext_iff]; omega
      rcases hcyc with hA | hB | hC | hD
      · have hcr := hcut k₀ k₁ k₂ m₁ (by dsimp only [k₀, k₁]; exact hA.1)
          (by dsimp only [k₁, k₂]; exact hA.2.1) (by have := i₂.2; dsimp only [k₂, m₁]; omega)
          (by rw [hk0, hk2]; exact rel02) (by rw [hk1, hm1]; exact rel1p1)
        rw [hk0, hk1] at hcr; exact Bool.noConfusion (nrel01.symm.trans hcr)
      · have hcr := hcut k₂ k₃ k₀ m₀ (by dsimp only [k₂, k₃]; exact hB.2.1)
          (by dsimp only [k₃, k₀]; exact hB.2.2) (by have := i₀.2; dsimp only [k₀, m₀]; omega)
          (by rw [hk2, hk0]; exact rel20) (by rw [hk3, hm0]; exact rel3p)
        rw [hk2, hk3] at hcr; exact Bool.noConfusion (nrel23.symm.trans hcr)
      · have hcr := hcut k₂ k₃ k₀ m₀ (by dsimp only [k₂, k₃]; exact hC.1)
          (by dsimp only [k₃, k₀]; exact hC.2.1) (by have := i₀.2; dsimp only [k₀, m₀]; omega)
          (by rw [hk2, hk0]; exact rel20) (by rw [hk3, hm0]; exact rel3p)
        rw [hk2, hk3] at hcr; exact Bool.noConfusion (nrel23.symm.trans hcr)
      · have hcr := hcut k₀ k₁ k₂ m₁ (by dsimp only [k₀, k₁]; exact hD.2.1)
          (by dsimp only [k₁, k₂]; exact hD.2.2) (by have := i₂.2; dsimp only [k₂, m₁]; omega)
          (by rw [hk0, hk2]; exact rel02) (by rw [hk1, hm1]; exact rel1p1)
        rw [hk0, hk1] at hcr; exact Bool.noConfusion (nrel01.symm.trans hcr)

  refine ⟨σ, τ, hσ_ann, hτ_ann, ?_⟩
  rintro ⟨u, hu_ann, hσu, hτu, hmin⟩
  have hσ_u1 : Refines σ u₁ := by
    intro x y h; simp only [σ, u₁, mkThreeBlocks, Bool.or_eq_true, Bool.and_eq_true] at h ⊢
    rcases h with ((h | h) | h) | h
    · exact Or.inl (Or.inl (Or.inl h))
    · exact Or.inl (Or.inr h)
    · nomatch h
    · nomatch h
  have hτ_u1 : Refines τ u₁ := by
    intro x y h
    simp only [τ, u₁, mkThreeBlocks, b02, b1p1, b012p1, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h ⊢
    rcases h with ((h | ⟨hx, hy⟩) | ⟨hx, hy⟩) | ⟨_, hfalse⟩
    · exact Or.inl (Or.inl (Or.inl h))
    · exact Or.inl (Or.inl (Or.inr ⟨by omega, by omega⟩))
    · exact Or.inl (Or.inl (Or.inr ⟨by omega, by omega⟩))
    · nomatch hfalse
  have hσ_u2 : Refines σ u₂ := by
    intro x y h
    simp only [σ, u₂, mkThreeBlocks, b3p, b023p, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h ⊢
    rcases h with ((h | ⟨hx, hy⟩) | ⟨_, hfalse⟩) | ⟨_, hfalse⟩
    · exact Or.inl (Or.inl (Or.inl h))
    · exact Or.inl (Or.inl (Or.inr ⟨by omega, by omega⟩))
    · nomatch hfalse
    · nomatch hfalse
  have hτ_u2 : Refines τ u₂ := by
    intro x y h
    simp only [τ, u₂, mkThreeBlocks, b02, b023p, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h ⊢
    rcases h with ((h | ⟨hx, hy⟩) | h) | ⟨_, hfalse⟩
    · exact Or.inl (Or.inl (Or.inl h))
    · exact Or.inl (Or.inl (Or.inr ⟨by omega, by omega⟩))
    · exact Or.inl (Or.inr h)
    · nomatch hfalse
  have hu_le_u1 : Refines u u₁ := hmin u₁ hu1_ann hσ_u1 hτ_u1
  have hu_le_u2 : Refines u u₂ := hmin u₂ hu2_ann hσ_u2 hτ_u2
  have hu_eq_w0 : u = w₀ := by
    apply refines_antisymm
    · intro x y hxy
      have h1 := hu_le_u1 x y hxy
      have h2 := hu_le_u2 x y hxy
      by_cases heq : x = y
      · simp [w₀, mkThreeBlocks, heq]
      · simp only [u₁, u₂, w₀, mkThreeBlocks, heq, decide_false, Bool.false_or,
                   b012p1, b023p, b02, b1p1, b3p, Bool.and_false, Bool.or_false,
                   Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h1 h2 ⊢
        rcases h1 with ⟨hx1, hy1⟩ | ⟨hx3, hy3⟩
        · rcases h2 with ⟨hx2, hy2⟩ | ⟨hx1p, hy1p⟩
          · exact Or.inl (Or.inl ⟨by omega, by omega⟩)
          · exact Or.inl (Or.inr ⟨hx1p, hy1p⟩)
        · exact Or.inr ⟨hx3, hy3⟩
    · intro x y hxy
      by_cases heq : x = y
      · subst heq; exact u.rel_refl x
      · simp only [w₀, mkThreeBlocks, heq, decide_false, Bool.false_or, Bool.or_eq_true] at hxy
        rcases hxy with (h02 | h1p) | h3p
        · exact hτu x y (by simp [τ, mkThreeBlocks, h02])
        · exact hτu x y (by simp [τ, mkThreeBlocks, h1p])
        · exact hσu x y (by simp [σ, mkThreeBlocks, h3p])
  rw [hu_eq_w0] at hu_ann
  exact hw0_not_ann hu_ann

/-- **Universal Theorem (Join Failure of `NC_A(p, q)` for `p ≥ 3, q ≥ 3`):** -/
theorem annularNC_no_lub_ge_3_3 {p q : Nat} (hp : 3 ≤ p) (hq : 3 ≤ q) :
    ∃ σ τ : SetPartition (p + q),
      IsAnnularNC p q σ ∧ IsAnnularNC p q τ ∧
      ¬ ∃ u : SetPartition (p + q),
          IsAnnularNC p q u ∧ Refines σ u ∧ Refines τ u ∧
          (∀ w : SetPartition (p + q), IsAnnularNC p q w → Refines σ w → Refines τ w → Refines u w) := by
  let b0p1 (v : Fin (p + q)) : Bool := decide (v.1 = 0 ∨ v.1 = p + 1)
  let b1p2 (v : Fin (p + q)) : Bool := decide (v.1 = 1 ∨ v.1 = p + 2)
  let b2p (v : Fin (p + q)) : Bool := decide (v.1 = 2 ∨ v.1 = p)
  let bU1 (v : Fin (p + q)) : Bool := decide (v.1 = 0 ∨ v.1 = 1 ∨ v.1 = p + 1 ∨ v.1 = p + 2)
  let bU2 (v : Fin (p + q)) : Bool := decide (v.1 = 0 ∨ v.1 = 2 ∨ v.1 = p ∨ v.1 = p + 1)

  have d_0p1_1p2 : ∀ v, b0p1 v = true → b1p2 v = false := by
    intro v h; simp only [b0p1, b1p2, decide_eq_true_eq, decide_eq_false_iff_not] at h ⊢; omega
  have d_0p1_2p : ∀ v, b0p1 v = true → b2p v = false := by
    intro v h; simp only [b0p1, b2p, decide_eq_true_eq, decide_eq_false_iff_not] at h ⊢; omega
  have d_1p2_2p : ∀ v, b1p2 v = true → b2p v = false := by
    intro v h; simp only [b1p2, b2p, decide_eq_true_eq, decide_eq_false_iff_not] at h ⊢; omega
  have d_u1 : ∀ v, bU1 v = true → b2p v = false := by
    intro v h; simp only [bU1, b2p, decide_eq_true_eq, decide_eq_false_iff_not] at h ⊢; omega
  have d_u2 : ∀ v, bU2 v = true → b1p2 v = false := by
    intro v h; simp only [bU2, b1p2, decide_eq_true_eq, decide_eq_false_iff_not] at h ⊢; omega

  let σ := mkThreeBlocks b2p (fun _ => false) (fun _ => false) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
  let τ := mkThreeBlocks b0p1 b1p2 (fun _ => false) d_0p1_1p2 (fun _ _ => rfl) (fun _ _ => rfl)
  let u₁ := mkThreeBlocks bU1 b2p (fun _ => false) d_u1 (fun _ _ => rfl) (fun _ _ => rfl)
  let u₂ := mkThreeBlocks bU2 b1p2 (fun _ => false) d_u2 (fun _ _ => rfl) (fun _ _ => rfl)
  let w₀ := mkThreeBlocks b0p1 b1p2 b2p d_0p1_1p2 d_0p1_2p d_1p2_2p

  have hσ_ann : IsAnnularNC p q σ := by
    right
    refine ⟨⟨⟨2, by omega⟩, ⟨0, by omega⟩, by simp [σ, mkThreeBlocks, b2p, outerIdx, innerIdx]⟩,
            0, 0, isOrderNC_one_block (annularCutOrder_injective p q 0 0)⟩

  have hu1_ann : IsAnnularNC p q u₁ := by
    right
    refine ⟨⟨⟨2, by omega⟩, ⟨0, by omega⟩, by simp [u₁, mkThreeBlocks, b2p, outerIdx, innerIdx]⟩,
            0, 0, ?_⟩
    have hord_id : ∀ idx : Fin (p + q), annularCutOrder p q 0 0 idx = idx := by
      intro idx
      simp only [annularCutOrder, iterShift, id]
      by_cases hlt : idx.1 < p
      · simp only [hlt, ↓reduceDIte, outerIdx]
      · simp only [hlt, ↓reduceDIte, innerIdx]; apply Fin.ext; dsimp only; omega
    apply isOrderNC_two_blocks_sep d_u1 (annularCutOrder_injective p q 0 0) 2 p
    · intro idx h2; rw [hord_id idx] at h2; simp only [b2p, decide_eq_true_eq] at h2; omega
    · intro idx h1; rw [hord_id idx] at h1; simp only [bU1, decide_eq_true_eq] at h1; omega

  have hcut22_A : annularCutOrder p q 2 2 ⟨p - 1, by omega⟩ = ⟨1, by omega⟩ := by
    have hlt : p - 1 < p := by omega
    simp only [annularCutOrder, hlt, ↓reduceDIte, outerIdx]
    apply Fin.ext; dsimp only
    rw [iterShift_two_at (by omega) ⟨p - 1, hlt⟩]
    have hnot : ¬ (p - 1 + 2 < p) := by omega
    simp only [hnot, ↓reduceIte]; omega

  have hcut22_B : annularCutOrder p q 2 2 ⟨p, by omega⟩ = ⟨p + 2, by omega⟩ := by
    have hnot : ¬ (p < p) := by omega
    simp only [annularCutOrder, hnot, ↓reduceDIte, innerIdx]
    apply Fin.ext; dsimp only
    have hsub : (⟨p - p, by omega⟩ : Fin q) = ⟨0, by omega⟩ := by apply Fin.ext; dsimp only; omega
    rw [hsub, iterShift_two_at (by omega) ⟨0, by omega⟩]
    have hq2 : 0 + 2 < q := by omega
    simp only [hq2, ↓reduceIte]

  have hb1p2_iff : ∀ v : Fin (p + q), b1p2 v = true ↔ (v = ⟨1, by omega⟩ ∨ v = ⟨p + 2, by omega⟩) := by
    intro v; simp only [b1p2, decide_eq_true_eq]
    exact ⟨fun h => h.elim (fun e => Or.inl (Fin.ext e)) (fun e => Or.inr (Fin.ext e)),
           fun h => h.elim (fun e => Or.inl (congrArg Fin.val e)) (fun e => Or.inr (congrArg Fin.val e))⟩

  have hτ_ann : IsAnnularNC p q τ := by
    right
    refine ⟨⟨⟨0, by omega⟩, ⟨1, by omega⟩, by simp [τ, mkThreeBlocks, b0p1, outerIdx, innerIdx]⟩,
            2, 2, isOrderNC_two_blocks_adj_sep d_0p1_1p2 (annularCutOrder_injective p q 2 2)
                    ⟨p - 1, by omega⟩ ⟨p, by omega⟩ ⟨1, by omega⟩ ⟨p + 2, by omega⟩
                    (by dsimp only; omega) hcut22_A hcut22_B hb1p2_iff⟩

  have hu2_ann : IsAnnularNC p q u₂ := by
    right
    refine ⟨⟨⟨2, by omega⟩, ⟨0, by omega⟩, by simp [u₂, mkThreeBlocks, bU2, outerIdx, innerIdx]⟩,
            2, 2, isOrderNC_two_blocks_adj_sep d_u2 (annularCutOrder_injective p q 2 2)
                    ⟨p - 1, by omega⟩ ⟨p, by omega⟩ ⟨1, by omega⟩ ⟨p + 2, by omega⟩
                    (by dsimp only; omega) hcut22_A hcut22_B hb1p2_iff⟩

  have hw0_not_ann : ¬ IsAnnularNC p q w₀ := by
    intro hw0
    have hth_w0 : HasThroughBlock p q w₀ :=
      ⟨⟨2, by omega⟩, ⟨0, by omega⟩, by simp [w₀, mkThreeBlocks, b2p, outerIdx, innerIdx]⟩
    rcases hw0 with ⟨hnot, _⟩ | ⟨_, r1, r2, hcut⟩
    · exact hnot hth_w0
    · rcases isCyclic3_iter hp r1 with ⟨i₀, i₁, i₂, hi0, hi1, hi2, hcycOut⟩
      rcases isCyclic3_iter hq r2 with ⟨j₀, j₁, j₂, hj0, hj1, hj2, hcycIn⟩
      let k₀ : Fin (p + q) := ⟨i₀.1, by have := i₀.2; omega⟩
      let k₁ : Fin (p + q) := ⟨i₁.1, by have := i₁.2; omega⟩
      let k₂ : Fin (p + q) := ⟨i₂.1, by have := i₂.2; omega⟩
      let m₀ : Fin (p + q) := ⟨p + j₀.1, by have := j₀.2; omega⟩
      let m₁ : Fin (p + q) := ⟨p + j₁.1, by have := j₁.2; omega⟩
      let m₂ : Fin (p + q) := ⟨p + j₂.1, by have := j₂.2; omega⟩
      have hk0 : annularCutOrder p q r1 r2 k₀ = ⟨0, by omega⟩ := by
        simp only [annularCutOrder, k₀, i₀.2, ↓reduceDIte, outerIdx]; rw [hi0]
      have hk1 : annularCutOrder p q r1 r2 k₁ = ⟨1, by omega⟩ := by
        simp only [annularCutOrder, k₁, i₁.2, ↓reduceDIte, outerIdx]; rw [hi1]
      have hk2 : annularCutOrder p q r1 r2 k₂ = ⟨2, by omega⟩ := by
        simp only [annularCutOrder, k₂, i₂.2, ↓reduceDIte, outerIdx]; rw [hi2]
      have hm0 : annularCutOrder p q r1 r2 m₀ = ⟨p, by omega⟩ := by
        have hnot : ¬ ((p + j₀.1) < p) := by omega
        simp only [annularCutOrder, m₀, hnot, ↓reduceDIte, innerIdx]
        have hsub : (⟨p + j₀.1 - p, by have := j₀.2; omega⟩ : Fin q) = j₀ := by
          apply Fin.ext; dsimp only; omega
        rw [hsub, hj0]; apply Fin.ext; dsimp only; omega
      have hm1 : annularCutOrder p q r1 r2 m₁ = ⟨p + 1, by omega⟩ := by
        have hnot : ¬ ((p + j₁.1) < p) := by omega
        simp only [annularCutOrder, m₁, hnot, ↓reduceDIte, innerIdx]
        have hsub : (⟨p + j₁.1 - p, by have := j₁.2; omega⟩ : Fin q) = j₁ := by
          apply Fin.ext; dsimp only; omega
        rw [hsub, hj1]
      have hm2 : annularCutOrder p q r1 r2 m₂ = ⟨p + 2, by omega⟩ := by
        have hnot : ¬ ((p + j₂.1) < p) := by omega
        simp only [annularCutOrder, m₂, hnot, ↓reduceDIte, innerIdx]
        have hsub : (⟨p + j₂.1 - p, by have := j₂.2; omega⟩ : Fin q) = j₂ := by
          apply Fin.ext; dsimp only; omega
        rw [hsub, hj2]
      have r0 : w₀.rel ⟨0, by omega⟩ ⟨p + 1, by omega⟩ = true := by simp [w₀, mkThreeBlocks, b0p1]
      have r1_rel : w₀.rel ⟨1, by omega⟩ ⟨p + 2, by omega⟩ = true := by simp [w₀, mkThreeBlocks, b1p2]
      have r2_rel : w₀.rel ⟨2, by omega⟩ ⟨p, by omega⟩ = true := by simp [w₀, mkThreeBlocks, b2p]
      have n01 : w₀.rel ⟨0, by omega⟩ ⟨1, by omega⟩ = false := by
        simp [w₀, mkThreeBlocks, b0p1, b1p2, b2p, Fin.ext_iff]; omega
      have n12 : w₀.rel ⟨1, by omega⟩ ⟨2, by omega⟩ = false := by
        simp [w₀, mkThreeBlocks, b0p1, b1p2, b2p, Fin.ext_iff]; omega
      have n20 : w₀.rel ⟨2, by omega⟩ ⟨0, by omega⟩ = false := by
        simp [w₀, mkThreeBlocks, b0p1, b1p2, b2p, Fin.ext_iff]; omega
      rcases hcycOut with hO1 | hO2 | hO3 <;> rcases hcycIn with hI1 | hI2 | hI3
      · have hcr := hcut k₀ k₁ m₁ m₂ (by dsimp only [k₀, k₁]; exact hO1.1)
          (by have := i₁.2; dsimp only [k₁, m₁]; omega) (by dsimp only [m₁, m₂]; omega)
          (by rw [hk0, hm1]; exact r0) (by rw [hk1, hm2]; exact r1_rel)
        rw [hk0, hk1] at hcr; exact Bool.noConfusion (n01.symm.trans hcr)
      · have hcr := hcut k₀ k₁ m₁ m₂ (by dsimp only [k₀, k₁]; exact hO1.1)
          (by have := i₁.2; dsimp only [k₁, m₁]; omega) (by dsimp only [m₁, m₂]; omega)
          (by rw [hk0, hm1]; exact r0) (by rw [hk1, hm2]; exact r1_rel)
        rw [hk0, hk1] at hcr; exact Bool.noConfusion (n01.symm.trans hcr)
      · have hcr := hcut k₁ k₂ m₂ m₀ (by dsimp only [k₁, k₂]; exact hO1.2)
          (by have := i₂.2; dsimp only [k₂, m₂]; omega) (by dsimp only [m₂, m₀]; omega)
          (by rw [hk1, hm2]; exact r1_rel) (by rw [hk2, hm0]; exact r2_rel)
        rw [hk1, hk2] at hcr; exact Bool.noConfusion (n12.symm.trans hcr)
      · have hcr := hcut k₂ k₀ m₀ m₁ (by dsimp only [k₂, k₀]; exact hO2.2)
          (by have := i₀.2; dsimp only [k₀, m₀]; omega) (by dsimp only [m₀, m₁]; omega)
          (by rw [hk2, hm0]; exact r2_rel) (by rw [hk0, hm1]; exact r0)
        rw [hk2, hk0] at hcr; exact Bool.noConfusion (n20.symm.trans hcr)
      · have hcr := hcut k₁ k₂ m₂ m₀ (by dsimp only [k₁, k₂]; exact hO2.1)
          (by have := i₂.2; dsimp only [k₂, m₂]; omega) (by dsimp only [m₂, m₀]; omega)
          (by rw [hk1, hm2]; exact r1_rel) (by rw [hk2, hm0]; exact r2_rel)
        rw [hk1, hk2] at hcr; exact Bool.noConfusion (n12.symm.trans hcr)
      · have hcr := hcut k₁ k₂ m₂ m₀ (by dsimp only [k₁, k₂]; exact hO2.1)
          (by have := i₂.2; dsimp only [k₂, m₂]; omega) (by dsimp only [m₂, m₀]; omega)
          (by rw [hk1, hm2]; exact r1_rel) (by rw [hk2, hm0]; exact r2_rel)
        rw [hk1, hk2] at hcr; exact Bool.noConfusion (n12.symm.trans hcr)
      · have hcr := hcut k₂ k₀ m₀ m₁ (by dsimp only [k₂, k₀]; exact hO3.1)
          (by have := i₀.2; dsimp only [k₀, m₀]; omega) (by dsimp only [m₀, m₁]; omega)
          (by rw [hk2, hm0]; exact r2_rel) (by rw [hk0, hm1]; exact r0)
        rw [hk2, hk0] at hcr; exact Bool.noConfusion (n20.symm.trans hcr)
      · have hcr := hcut k₀ k₁ m₁ m₂ (by dsimp only [k₀, k₁]; exact hO3.2)
          (by have := i₁.2; dsimp only [k₁, m₁]; omega) (by dsimp only [m₁, m₂]; omega)
          (by rw [hk0, hm1]; exact r0) (by rw [hk1, hm2]; exact r1_rel)
        rw [hk0, hk1] at hcr; exact Bool.noConfusion (n01.symm.trans hcr)
      · have hcr := hcut k₂ k₀ m₀ m₁ (by dsimp only [k₂, k₀]; exact hO3.1)
          (by have := i₀.2; dsimp only [k₀, m₀]; omega) (by dsimp only [m₀, m₁]; omega)
          (by rw [hk2, hm0]; exact r2_rel) (by rw [hk0, hm1]; exact r0)
        rw [hk2, hk0] at hcr; exact Bool.noConfusion (n20.symm.trans hcr)

  refine ⟨σ, τ, hσ_ann, hτ_ann, ?_⟩
  rintro ⟨u, hu_ann, hσu, hτu, hmin⟩
  have hσ_u1 : Refines σ u₁ := by
    intro x y h; simp only [σ, u₁, mkThreeBlocks, Bool.or_eq_true, Bool.and_eq_true] at h ⊢
    rcases h with ((h | h) | h) | h
    · exact Or.inl (Or.inl (Or.inl h))
    · exact Or.inl (Or.inr h)
    · nomatch h
    · nomatch h
  have hτ_u1 : Refines τ u₁ := by
    intro x y h
    simp only [τ, u₁, mkThreeBlocks, b0p1, b1p2, bU1, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h ⊢
    rcases h with ((h | ⟨hx, hy⟩) | ⟨hx, hy⟩) | ⟨_, hfalse⟩
    · exact Or.inl (Or.inl (Or.inl h))
    · exact Or.inl (Or.inl (Or.inr ⟨by omega, by omega⟩))
    · exact Or.inl (Or.inl (Or.inr ⟨by omega, by omega⟩))
    · nomatch hfalse
  have hσ_u2 : Refines σ u₂ := by
    intro x y h
    simp only [σ, u₂, mkThreeBlocks, b2p, bU2, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h ⊢
    rcases h with ((h | ⟨hx, hy⟩) | ⟨_, hfalse⟩) | ⟨_, hfalse⟩
    · exact Or.inl (Or.inl (Or.inl h))
    · exact Or.inl (Or.inl (Or.inr ⟨by omega, by omega⟩))
    · nomatch hfalse
    · nomatch hfalse
  have hτ_u2 : Refines τ u₂ := by
    intro x y h
    simp only [τ, u₂, mkThreeBlocks, b0p1, bU2, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h ⊢
    rcases h with ((h | ⟨hx, hy⟩) | h) | ⟨_, hfalse⟩
    · exact Or.inl (Or.inl (Or.inl h))
    · exact Or.inl (Or.inl (Or.inr ⟨by omega, by omega⟩))
    · exact Or.inl (Or.inr h)
    · nomatch hfalse
  have hu_le_u1 : Refines u u₁ := hmin u₁ hu1_ann hσ_u1 hτ_u1
  have hu_le_u2 : Refines u u₂ := hmin u₂ hu2_ann hσ_u2 hτ_u2
  have hu_eq_w0 : u = w₀ := by
    apply refines_antisymm
    · intro x y hxy
      have h1 := hu_le_u1 x y hxy
      have h2 := hu_le_u2 x y hxy
      by_cases heq : x = y
      · simp [w₀, mkThreeBlocks, heq]
      · simp only [u₁, u₂, w₀, mkThreeBlocks, heq, decide_false, Bool.false_or,
                   bU1, bU2, b0p1, b1p2, b2p, Bool.and_false, Bool.or_false,
                   Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h1 h2 ⊢
        rcases h1 with ⟨hx1, hy1⟩ | ⟨hx2p, hy2p⟩
        · rcases h2 with ⟨hx2, hy2⟩ | ⟨hx1p2, hy1p2⟩
          · exact Or.inl (Or.inl ⟨by omega, by omega⟩)
          · exact Or.inl (Or.inr ⟨hx1p2, hy1p2⟩)
        · exact Or.inr ⟨hx2p, hy2p⟩
    · intro x y hxy
      by_cases heq : x = y
      · subst heq; exact u.rel_refl x
      · simp only [w₀, mkThreeBlocks, heq, decide_false, Bool.false_or, Bool.or_eq_true] at hxy
        rcases hxy with (h0 | h1) | h2
        · exact hτu x y (by simp [τ, mkThreeBlocks, h0])
        · exact hτu x y (by simp [τ, mkThreeBlocks, h1])
        · exact hσu x y (by simp [σ, mkThreeBlocks, h2])
  rw [hu_eq_w0] at hu_ann
  exact hw0_not_ann hu_ann

/-- Complete Dominant-Outer Join Failure Theorem: for all `p ≥ q ≥ 2` with `p + q ≥ 6`,
`NC_A(p, q)` fails to have least upper bounds (hence is NOT a lattice). -/
theorem annularNC_no_lub_of_pq_ge_two_sum_ge_six {p q : Nat}
    (hpq : q ≤ p) (hq : 2 ≤ q) (hsum : 6 ≤ p + q) :
    ∃ σ τ : SetPartition (p + q),
      IsAnnularNC p q σ ∧ IsAnnularNC p q τ ∧
      ¬ ∃ u : SetPartition (p + q),
          IsAnnularNC p q u ∧ Refines σ u ∧ Refines τ u ∧
          (∀ w : SetPartition (p + q), IsAnnularNC p q w → Refines σ w → Refines τ w → Refines u w) := by
  by_cases hq3 : 3 ≤ q
  · exact annularNC_no_lub_ge_3_3 (by omega) hq3
  · exact annularNC_no_lub_ge_4_2 (by omega) hq

end Conjecture00000004770
