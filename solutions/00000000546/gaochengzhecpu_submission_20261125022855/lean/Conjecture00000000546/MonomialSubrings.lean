/-
  Conjecture 00000000546 — Homological Depth of Monomial Subrings Over Any Field `K`
  1. Affine numerical semigroup ring `K[S_{a,k}] ⊆ K[t]` (exact maximal reg-seq length 1)
  2. Projective monomial curve ring `R_{a,k} ⊆ K[u,v]^{(a+k)}` (exact maximal reg-seq length 2)
  3. Symmetric-gap pinched Veronese subring `B_{a,k}^{(m)} ⊆ K[u,v]^{(m(a+k))}`
     (depth-2 threshold `m ≥ ⌈(a-1)/k⌉`, refuting `⌈a/k⌉` whenever `(a-1) % k = 0`)
  Core Lean 4.19.0
-/
import Conjecture00000000546.Semigroup

namespace Conjecture00000000546

/-! ## 1. Affine Numerical Semigroup Ring `K[S_{a,k}] ⊆ K[t]` -/

section AffineSemigroupRing

variable {K : Type} [FieldCoeff K]

/-- Full polynomial membership in `K[S_{a,k}] = K[t^a, t^{a+1}, …, t^{a+k}] ⊆ K[t]`. -/
def InAffineSemigroupRing (a k : Nat) (p : Poly1 K) : Prop :=
  ∀ n, coeff1 p n ≠ FieldCoeff.zero → InIntervalSemigroup a k n

/-- Homogeneous maximal ideal `m = (t^a, …, t^{a+k}) ⊂ K[S_{a,k}]`. -/
def InAffineMaxIdeal (a k : Nat) (p : Poly1 K) : Prop :=
  InAffineSemigroupRing a k p ∧ coeff1 p 0 = FieldCoeff.zero

theorem affine_zero_mem (a k : Nat) : InAffineSemigroupRing a k ([] : Poly1 K) :=
  fun _ h => False.elim (h rfl)

theorem affine_one_mem (a k : Nat) : InAffineSemigroupRing a k ([FieldCoeff.one] : Poly1 K) := by
  intro n hn
  cases n with
  | zero => exact InIntervalSemigroup.zero
  | succ m => exact False.elim (hn rfl)

theorem affine_add_mem {a k : Nat} {p q : Poly1 K}
    (hp : InAffineSemigroupRing a k p) (hq : InAffineSemigroupRing a k q) :
    InAffineSemigroupRing a k (polyAdd p q) := by
  intro n hn
  rw [coeff1_polyAdd] at hn
  by_cases hp0 : coeff1 p n = FieldCoeff.zero
  · rw [hp0, FieldCoeff.zero_add] at hn
    exact hq n hn
  · exact hp n hp0

theorem affine_mul_mem {a k : Nat} {p q : Poly1 K}
    (hp : InAffineSemigroupRing a k p) (hq : InAffineSemigroupRing a k q) :
    InAffineSemigroupRing a k (polyMul p q) :=
  coeff1_polyMul_support (fun _ _ => inIntervalSemigroup_add) p q hp hq

theorem affine_pow_mem {a k : Nat} {p : Poly1 K}
    (hp : InAffineSemigroupRing a k p) (m : Nat) :
    InAffineSemigroupRing a k (polyPow p m) := by
  induction m with
  | zero => exact affine_one_mem a k
  | succ m ih => exact affine_mul_mem hp ih

theorem affine_gen_mem_maxIdeal {a k g : Nat} (ha : 1 ≤ a) (hga : a ≤ g) (hgk : g ≤ a + k) :
    InAffineMaxIdeal a k (monomial1 (FieldCoeff.one : K) g) := by
  refine ⟨?_, ?_⟩
  · intro n hn
    by_cases hng : n = g
    · rw [hng]
      have hmem := InIntervalSemigroup.add_gen (a := a) (k := k)
        InIntervalSemigroup.zero hga hgk
      rwa [Nat.zero_add] at hmem
    · rw [coeff1_monomial1_ne _ hng] at hn
      exact False.elim (hn rfl)
  · exact coeff1_monomial1_ne _ (by omega)

/-- Principal ideal `f · K[S_{a,k}]` inside `K[S_{a,k}]`. -/
def InPrincipalIdeal1 (a k : Nat) (f h : Poly1 K) : Prop :=
  ∃ q, InAffineSemigroupRing a k q ∧ Poly1Eq h (polyMul f q)

/-- 2-generator ideal `f · K[S_{a,k}] + g · K[S_{a,k}]` inside `K[S_{a,k}]`. -/
def InIdeal2_1 (a k : Nat) (f g h : Poly1 K) : Prop :=
  ∃ q1 q2, InAffineSemigroupRing a k q1 ∧ InAffineSemigroupRing a k q2 ∧
    Poly1Eq h (polyAdd (polyMul f q1) (polyMul g q2))

/-- `f` forms a regular sequence of length `1` in `m_{S_{a,k}}` on `K[S_{a,k}]`. -/
def IsAffineRegSeq1 (a k : Nat) (f : Poly1 K) : Prop :=
  InAffineMaxIdeal a k f ∧
  ¬ InPrincipalIdeal1 a k f [FieldCoeff.one] ∧
  ∀ h, InAffineSemigroupRing a k h →
    Poly1Eq (polyMul f h) [] → Poly1Eq h []

/-- `(f, g)` forms a regular sequence of length `2` in `m_{S_{a,k}}` on `K[S_{a,k}]`. -/
def IsAffineRegSeq2 (a k : Nat) (f g : Poly1 K) : Prop :=
  IsAffineRegSeq1 a k f ∧
  InAffineMaxIdeal a k g ∧
  ¬ InIdeal2_1 a k f g [FieldCoeff.one] ∧
  ∀ h, InAffineSemigroupRing a k h →
    InPrincipalIdeal1 a k f (polyMul g h) → InPrincipalIdeal1 a k f h

/-- **Affine Depth Lower Bound (`depth ≥ 1`)**:
    `t^a` is a regular sequence of length `1` on `K[S_{a,k}]` for ALL `a ≥ 1, k ≥ 0`. -/
theorem affine_ta_is_regSeq1 {a k : Nat} (ha : 1 ≤ a) :
    IsAffineRegSeq1 a k (monomial1 (FieldCoeff.one : K) a) := by
  refine ⟨affine_gen_mem_maxIdeal ha (Nat.le_refl a) (by omega), ?_, ?_⟩
  · rintro ⟨q, _, h1⟩
    have h0 := h1 0
    rw [coeff1_mul_monomial1_lt a q (by omega)] at h0
    exact FieldCoeff.zero_ne_one h0.symm
  · intro h _ hmul n
    have hn := hmul (a + n)
    rwa [coeff1_mul_monomial1_add a h n] at hn

/-- Every polynomial `g ∈ m_{S_{a,k}}` satisfies `g^{⌈(a-1)/k⌉ + 1} ∈ (t^a) K[S_{a,k}]`. -/
theorem affine_maxIdeal_pow_in_ta {a k : Nat} (ha : 2 ≤ a) (hk : 1 ≤ k)
    {g : Poly1 K} (hg : InAffineMaxIdeal a k g) :
    InPrincipalIdeal1 a k (monomial1 (FieldCoeff.one : K) a)
      (polyPow g (ceilDiv (a - 1) k + 1)) := by
  let P := polyPow g (ceilDiv (a - 1) k + 1)
  have hg_ge_a : ∀ i, coeff1 g i ≠ FieldCoeff.zero → a ≤ i := by
    intro i hi
    have hpos : 0 < i := by
      cases i with
      | zero => exact False.elim (hi hg.2)
      | succ _ => omega
    exact inIntervalSemigroup_ge_a (hg.1 i hi) hpos
  have hP_ge : ∀ n, coeff1 P n ≠ FieldCoeff.zero → (ceilDiv (a - 1) k + 1) * a ≤ n :=
    coeff1_polyPow_lower_bound hg_ge_a (ceilDiv (a - 1) k + 1)
  refine ⟨P.drop a, ?_, poly1_div_by_monomial1 a P ?_⟩
  · intro m hm
    rw [coeff1_drop] at hm
    have hge : (ceilDiv (a - 1) k + 1) * a ≤ a + m := hP_ge (a + m) hm
    have hexp : (ceilDiv (a - 1) k + 1) * a = ceilDiv (a - 1) k * a + a :=
      Nat.succ_mul _ a
    exact mem_of_ge_conductor ha hk (by omega)
  · intro n hn
    have hge : (ceilDiv (a - 1) k + 1) * a ≤ n := hP_ge n hn
    have hexp : (ceilDiv (a - 1) k + 1) * a = ceilDiv (a - 1) k * a + a :=
      Nat.succ_mul _ a
    omega

/-- **Affine Depth Upper Bound (`depth ≤ 1`, Zero Depth Drop Everywhere)**:
    For ALL `a ≥ 2, k ≥ 1`, `(t^a)` cannot be extended to ANY regular sequence `(t^a, g)`
    of length `2` by ANY (even inhomogeneous) polynomial `g ∈ m_{S_{a,k}}`. -/
theorem affine_no_regSeq2_extending_ta {a k : Nat} (ha : 2 ≤ a) (hk : 1 ≤ k)
    (g : Poly1 K) :
    ¬ IsAffineRegSeq2 a k (monomial1 (FieldCoeff.one : K) a) g := by
  rintro ⟨hf1, hg_max, _, hreg2⟩
  have hpow := affine_maxIdeal_pow_in_ta ha hk hg_max
  have hdescend : ∀ m,
      InPrincipalIdeal1 a k (monomial1 (FieldCoeff.one : K) a) (polyPow g m) →
      InPrincipalIdeal1 a k (monomial1 (FieldCoeff.one : K) a) [FieldCoeff.one] := by
    intro m
    induction m with
    | zero => exact id
    | succ m ih =>
      intro hm1
      have hgm : InAffineSemigroupRing a k (polyPow g m) := affine_pow_mem hg_max.1 m
      exact ih (hreg2 (polyPow g m) hgm hm1)
  exact hf1.2.1 (hdescend (ceilDiv (a - 1) k + 1) hpow)

end AffineSemigroupRing

/-! ## 2. 2-Variable Graded Monomial Subrings `R(A, d) ⊆ K[u, v]^{(d)}` -/

/-- Sumset `r · A` for an arbitrary subset `A : Nat → Prop`. -/
inductive InSetSumset (A : Nat → Prop) : Nat → Nat → Prop where
  | zero : InSetSumset A 0 0
  | step {r s x : Nat} : InSetSumset A r s → A x → InSetSumset A (r + 1) (s + x)

theorem inSetSumset_add {A : Nat → Prop} {r1 r2 s1 s2 : Nat}
    (h1 : InSetSumset A r1 s1) (h2 : InSetSumset A r2 s2) :
    InSetSumset A (r1 + r2) (s1 + s2) := by
  induction h2 with
  | zero =>
    rw [Nat.add_zero, Nat.add_zero]
    exact h1
  | step _ hx ih =>
    rw [← Nat.add_assoc, ← Nat.add_assoc]
    exact InSetSumset.step ih hx

/-- Graded bivariate polynomials in `K[u,v]^{(d)} = ⨁_{r ≥ 0} K[u,v]_{r d}`:
    row `r` is the univariate polynomial in `v` (where `v^s` stands for `u^{r d - s} v^s`). -/
abbrev BivarPoly (K : Type) := List (Poly1 K)

section BivarAlgebra

variable {K : Type} [FieldCoeff K]

def bivarCoeff (F : BivarPoly K) (r s : Nat) : K :=
  match F, r with
  | [], _ => FieldCoeff.zero
  | row :: _, 0 => coeff1 row s
  | _ :: rows, r + 1 => bivarCoeff rows r s

def BivarEq (F G : BivarPoly K) : Prop :=
  ∀ r s, bivarCoeff F r s = bivarCoeff G r s

def bivarAdd : BivarPoly K → BivarPoly K → BivarPoly K
  | [], Gs => Gs
  | Fs, [] => Fs
  | f :: Fs, g :: Gs => polyAdd f g :: bivarAdd Fs Gs

def bivarScaleRow (p : Poly1 K) : BivarPoly K → BivarPoly K
  | [] => []
  | g :: Gs => polyMul p g :: bivarScaleRow p Gs

def bivarMul : BivarPoly K → BivarPoly K → BivarPoly K
  | [], _ => []
  | f :: Fs, Gs => bivarAdd (bivarScaleRow f Gs) ([] :: bivarMul Fs Gs)

def bivarPow (F : BivarPoly K) : Nat → BivarPoly K
  | 0 => [[FieldCoeff.one]]
  | m + 1 => bivarMul F (bivarPow F m)

/-- Generator `u^d` at `(r = 1, s = 0)`. -/
def uGen : BivarPoly K := [[], [FieldCoeff.one]]

/-- Generator `v^d` at `(r = 1, s = d)`. -/
def vGen (d : Nat) : BivarPoly K := [[], monomial1 FieldCoeff.one d]

@[simp] theorem bivarCoeff_nil (r s : Nat) :
    bivarCoeff ([] : BivarPoly K) r s = FieldCoeff.zero := rfl

theorem bivarCoeff_bivarAdd (F G : BivarPoly K) (r s : Nat) :
    bivarCoeff (bivarAdd F G) r s = FieldCoeff.add (bivarCoeff F r s) (bivarCoeff G r s) := by
  induction F generalizing G r with
  | nil => simp [bivarAdd, bivarCoeff_nil, FieldCoeff.zero_add]
  | cons f Fs ih =>
    cases G with
    | nil => simp [bivarAdd, bivarCoeff_nil, FieldCoeff.add_zero]
    | cons g Gs =>
      cases r with
      | zero => exact coeff1_polyAdd f g s
      | succ r' => exact ih Gs r'

/-- Helper extracting row `r` of `F` as a `Poly1 K`. -/
def bivarRow (F : BivarPoly K) (r : Nat) : Poly1 K :=
  match F, r with
  | [], _ => []
  | row :: _, 0 => row
  | _ :: rows, r + 1 => bivarRow rows r

theorem coeff1_bivarRow (F : BivarPoly K) (r s : Nat) :
    coeff1 (bivarRow F r) s = bivarCoeff F r s := by
  induction F generalizing r with
  | nil => rfl
  | cons row rows ih =>
    cases r with
    | zero => rfl
    | succ r => exact ih r

theorem coeff1_polyMul_nil_right (p : Poly1 K) (s : Nat) :
    coeff1 (polyMul p ([] : Poly1 K)) s = FieldCoeff.zero := by
  induction p generalizing s with
  | nil => rfl
  | cons c ps ih =>
    simp [polyMul, coeff1_polyAdd, coeff1_polyScale, FieldCoeff.mul_zero, FieldCoeff.zero_add]
    cases s with
    | zero => rfl
    | succ s' => exact ih s'

theorem bivarCoeff_bivarScaleRow' (p : Poly1 K) (G : BivarPoly K) (r s : Nat) :
    bivarCoeff (bivarScaleRow p G) r s = coeff1 (polyMul p (bivarRow G r)) s := by
  induction G generalizing r with
  | nil =>
    change FieldCoeff.zero = coeff1 (polyMul p []) s
    exact (coeff1_polyMul_nil_right p s).symm
  | cons g Gs ih =>
    cases r with
    | zero => rfl
    | succ r => exact ih r

theorem bivarCoeff_scaleRow_nil (G : BivarPoly K) (r s : Nat) :
    bivarCoeff (bivarScaleRow ([] : Poly1 K) G) r s = FieldCoeff.zero := by
  rw [bivarCoeff_bivarScaleRow']
  rfl

theorem bivarCoeff_singleton_nil (r s : Nat) :
    bivarCoeff ([[]] : BivarPoly K) r s = FieldCoeff.zero := by
  cases r <;> rfl

theorem bivarCoeff_uGen_mul_zero (G : BivarPoly K) (s : Nat) :
    bivarCoeff (bivarMul uGen G) 0 s = FieldCoeff.zero := by
  simp only [uGen, bivarMul, bivarCoeff_bivarAdd, bivarCoeff]
  rw [bivarCoeff_scaleRow_nil, FieldCoeff.zero_add]
  rfl

theorem bivarCoeff_uGen_mul_succ (G : BivarPoly K) (r s : Nat) :
    bivarCoeff (bivarMul uGen G) (r + 1) s = bivarCoeff G r s := by
  simp only [uGen, bivarMul, bivarCoeff_bivarAdd, bivarCoeff]
  rw [bivarCoeff_scaleRow_nil, FieldCoeff.zero_add, bivarCoeff_singleton_nil,
      FieldCoeff.add_zero, bivarCoeff_bivarScaleRow']
  have hone : [FieldCoeff.one] = monomial1 (FieldCoeff.one : K) 0 := rfl
  rw [hone]
  have hadd := coeff1_mul_monomial1_add 0 (bivarRow G r) s
  rw [Nat.zero_add] at hadd
  rw [hadd, coeff1_bivarRow]

theorem bivarCoeff_vGen_mul_zero (d : Nat) (G : BivarPoly K) (s : Nat) :
    bivarCoeff (bivarMul (vGen d) G) 0 s = FieldCoeff.zero := by
  simp only [vGen, bivarMul, bivarCoeff_bivarAdd, bivarCoeff]
  rw [bivarCoeff_scaleRow_nil, FieldCoeff.zero_add]
  rfl

theorem bivarCoeff_vGen_mul_succ_lt (d : Nat) (G : BivarPoly K) (r : Nat) {s : Nat} (hs : s < d) :
    bivarCoeff (bivarMul (vGen d) G) (r + 1) s = FieldCoeff.zero := by
  simp only [vGen, bivarMul, bivarCoeff_bivarAdd, bivarCoeff]
  rw [bivarCoeff_scaleRow_nil, FieldCoeff.zero_add, bivarCoeff_singleton_nil,
      FieldCoeff.add_zero, bivarCoeff_bivarScaleRow',
      coeff1_mul_monomial1_lt d (bivarRow G r) hs]

theorem bivarCoeff_vGen_mul_succ_add (d : Nat) (G : BivarPoly K) (r s : Nat) :
    bivarCoeff (bivarMul (vGen d) G) (r + 1) (d + s) = bivarCoeff G r s := by
  simp only [vGen, bivarMul, bivarCoeff_bivarAdd, bivarCoeff]
  rw [bivarCoeff_scaleRow_nil, FieldCoeff.zero_add, bivarCoeff_singleton_nil,
      FieldCoeff.add_zero, bivarCoeff_bivarScaleRow',
      coeff1_mul_monomial1_add d (bivarRow G r) s, coeff1_bivarRow]

/-- Shifted bivariate support preservation under `bivarMul`. -/
theorem bivarCoeff_bivarMul_support_shift {P Q R : Nat → Nat → Prop}
    (hcombine : ∀ r1 s1 r2 s2, P r1 s1 → Q r2 s2 → R (r1 + r2) (s1 + s2))
    (F G : BivarPoly K) (r0 : Nat)
    (hF : ∀ r1 s1, bivarCoeff F r1 s1 ≠ FieldCoeff.zero → P (r0 + r1) s1)
    (hG : ∀ r2 s2, bivarCoeff G r2 s2 ≠ FieldCoeff.zero → Q r2 s2) :
    ∀ r s, bivarCoeff (bivarMul F G) r s ≠ FieldCoeff.zero → R (r0 + r) s := by
  induction F generalizing r0 with
  | nil =>
    intro r s h
    exact False.elim (h rfl)
  | cons f Fs ih =>
    intro r s h
    rw [bivarMul, bivarCoeff_bivarAdd] at h
    by_cases h1 : bivarCoeff (bivarScaleRow f G) r s = FieldCoeff.zero
    · rw [h1, FieldCoeff.zero_add] at h
      cases r with
      | zero => exact False.elim (h rfl)
      | succ r' =>
        have hFs : ∀ r1 s1, bivarCoeff Fs r1 s1 ≠ FieldCoeff.zero → P ((r0 + 1) + r1) s1 := by
          intro r1 s1 hs1
          have : r0 + (r1 + 1) = (r0 + 1) + r1 := by omega
          rw [← this]
          exact hF (r1 + 1) s1 hs1
        have hres := ih (r0 + 1) hFs r' s h
        have : (r0 + 1) + r' = r0 + (r' + 1) := by omega
        rwa [this] at hres
    · rw [bivarCoeff_bivarScaleRow'] at h1
      have hf : ∀ s1, coeff1 f s1 ≠ FieldCoeff.zero → P r0 s1 := by
        intro s1 hs1
        have h0 := hF 0 s1 hs1
        rwa [Nat.add_zero] at h0
      have hg : ∀ s2, coeff1 (bivarRow G r) s2 ≠ FieldCoeff.zero → Q r s2 := by
        intro s2 hs2
        rw [coeff1_bivarRow] at hs2
        exact hG r s2 hs2
      exact coeff1_polyMul_support (fun s1 s2 hp hq => hcombine r0 s1 r s2 hp hq)
        f (bivarRow G r) hf hg s h1

theorem bivarCoeff_bivarMul_support {P Q R : Nat → Nat → Prop}
    (hcombine : ∀ r1 s1 r2 s2, P r1 s1 → Q r2 s2 → R (r1 + r2) (s1 + s2))
    (F G : BivarPoly K)
    (hF : ∀ r1 s1, bivarCoeff F r1 s1 ≠ FieldCoeff.zero → P r1 s1)
    (hG : ∀ r2 s2, bivarCoeff G r2 s2 ≠ FieldCoeff.zero → Q r2 s2) :
    ∀ r s, bivarCoeff (bivarMul F G) r s ≠ FieldCoeff.zero → R r s := by
  have hF0 : ∀ r1 s1, bivarCoeff F r1 s1 ≠ FieldCoeff.zero → P (0 + r1) s1 := by
    intro r1 s1 hs1
    rw [Nat.zero_add]
    exact hF r1 s1 hs1
  have h := bivarCoeff_bivarMul_support_shift hcombine F G 0 hF0 hG
  intro r s hs
  have hres := h r s hs
  rwa [Nat.zero_add] at hres

/-- Full polynomial membership in the 2-variable monomial subring `R(A, d) = K[u^{d-i} v^i : i ∈ A]`. -/
def InBivarSubring (A : Nat → Prop) (F : BivarPoly K) : Prop :=
  ∀ r s, bivarCoeff F r s ≠ FieldCoeff.zero → InSetSumset A r s

/-- Graded maximal ideal `m_{R(A, d)} = ⨁_{r ≥ 1} R(A, d)_r`. -/
def InBivarMaxIdeal (A : Nat → Prop) (F : BivarPoly K) : Prop :=
  InBivarSubring A F ∧ ∀ s, bivarCoeff F 0 s = FieldCoeff.zero

theorem bivarSubring_one (A : Nat → Prop) : InBivarSubring A ([[FieldCoeff.one]] : BivarPoly K) := by
  intro r s h
  cases r with
  | zero =>
    cases s with
    | zero => exact InSetSumset.zero
    | succ s' => exact False.elim (h rfl)
  | succ r' => exact False.elim (h rfl)

theorem bivarSubring_add {A : Nat → Prop} {F G : BivarPoly K}
    (hF : InBivarSubring A F) (hG : InBivarSubring A G) :
    InBivarSubring A (bivarAdd F G) := by
  intro r s h
  rw [bivarCoeff_bivarAdd] at h
  by_cases h1 : bivarCoeff F r s = FieldCoeff.zero
  · rw [h1, FieldCoeff.zero_add] at h
    exact hG r s h
  · exact hF r s h1

theorem bivarSubring_mul {A : Nat → Prop} {F G : BivarPoly K}
    (hF : InBivarSubring A F) (hG : InBivarSubring A G) :
    InBivarSubring A (bivarMul F G) :=
  bivarCoeff_bivarMul_support (fun _ _ _ _ => inSetSumset_add) F G hF hG

theorem bivarSubring_pow {A : Nat → Prop} {F : BivarPoly K}
    (hF : InBivarSubring A F) (m : Nat) :
    InBivarSubring A (bivarPow F m) := by
  induction m with
  | zero => exact bivarSubring_one A
  | succ m ih => exact bivarSubring_mul hF ih

theorem bivarPow_degree_lower_bound {A : Nat → Prop} {F : BivarPoly K}
    (hF : InBivarMaxIdeal A F) (m : Nat) :
    ∀ r s, bivarCoeff (bivarPow F m) r s ≠ FieldCoeff.zero → m ≤ r := by
  have hF1 : ∀ r s, bivarCoeff F r s ≠ FieldCoeff.zero → 1 ≤ r := by
    intro r s h
    cases r with
    | zero => exact False.elim (h (hF.2 s))
    | succ r' => omega
  induction m with
  | zero => intro _ _ _; omega
  | succ m ih =>
    intro r s h
    refine bivarCoeff_bivarMul_support (P := fun r1 _ => 1 ≤ r1) (Q := fun r2 _ => m ≤ r2)
      (R := fun r3 _ => m + 1 ≤ r3) ?_ F (bivarPow F m) hF1 ih r s h
    intro r1 _ r2 _ hr1 hr2
    omega

/-- Ideals `(u^d)` and `(u^d, v^d)` inside `R(A, d)` and regular-sequence predicates. -/
def InIdealU (A : Nat → Prop) (H : BivarPoly K) : Prop :=
  ∃ Q, InBivarSubring A Q ∧ BivarEq H (bivarMul uGen Q)

def InIdealUV (A : Nat → Prop) (d : Nat) (H : BivarPoly K) : Prop :=
  ∃ Q1 Q2, InBivarSubring A Q1 ∧ InBivarSubring A Q2 ∧
    BivarEq H (bivarAdd (bivarMul uGen Q1) (bivarMul (vGen d) Q2))

def InIdeal3 (A : Nat → Prop) (d : Nat) (G H : BivarPoly K) : Prop :=
  ∃ Q1 Q2 Q3, InBivarSubring A Q1 ∧ InBivarSubring A Q2 ∧ InBivarSubring A Q3 ∧
    BivarEq H (bivarAdd (bivarAdd (bivarMul uGen Q1) (bivarMul (vGen d) Q2)) (bivarMul G Q3))

def IsBivarRegSeq1_U (K : Type) [FieldCoeff K] (A : Nat → Prop) : Prop :=
  InBivarMaxIdeal A (uGen : BivarPoly K) ∧
  ¬ InIdealU A ([[FieldCoeff.one]] : BivarPoly K) ∧
  ∀ H : BivarPoly K, InBivarSubring A H →
    BivarEq (bivarMul uGen H) [] → BivarEq H []

def IsBivarRegSeq2_UV (K : Type) [FieldCoeff K] (A : Nat → Prop) (d : Nat) : Prop :=
  IsBivarRegSeq1_U K A ∧
  InBivarMaxIdeal A (vGen d : BivarPoly K) ∧
  ¬ InIdealUV A d ([[FieldCoeff.one]] : BivarPoly K) ∧
  ∀ H : BivarPoly K, InBivarSubring A H →
    InIdealU A (bivarMul (vGen d) H) → InIdealU A H

def IsBivarRegSeq3_UVG (K : Type) [FieldCoeff K] (A : Nat → Prop) (d : Nat) (G : BivarPoly K) : Prop :=
  IsBivarRegSeq2_UV K A d ∧
  InBivarMaxIdeal A G ∧
  ¬ InIdeal3 A d G ([[FieldCoeff.one]] : BivarPoly K) ∧
  ∀ H : BivarPoly K, InBivarSubring A H →
    InIdealUV A d (bivarMul G H) → InIdealUV A d H

/-- Exact characterization of `H ∈ u^d · R(A, d)` on full bivariate polynomials. -/
theorem inIdealU_iff (A : Nat → Prop) (H : BivarPoly K) :
    InIdealU A H ↔
      (∀ s, bivarCoeff H 0 s = FieldCoeff.zero) ∧
      (∀ r s, bivarCoeff H (r + 1) s ≠ FieldCoeff.zero → InSetSumset A r s) := by
  constructor
  · rintro ⟨Q, hQ, heq⟩
    refine ⟨?_, ?_⟩
    · intro s
      rw [heq 0 s, bivarCoeff_uGen_mul_zero]
    · intro r s hne
      rw [heq (r + 1) s, bivarCoeff_uGen_mul_succ] at hne
      exact hQ r s hne
  · rintro ⟨h0, hsucc⟩
    refine ⟨H.drop 1, ?_, ?_⟩
    · intro r s hne
      have hdrop : bivarCoeff (H.drop 1) r s = bivarCoeff H (r + 1) s := by
        cases H with
        | nil => rfl
        | cons _ rows => rfl
      rw [hdrop] at hne
      exact hsucc r s hne
    · intro r s
      cases r with
      | zero =>
        rw [h0 s, bivarCoeff_uGen_mul_zero]
      | succ r' =>
        rw [bivarCoeff_uGen_mul_succ]
        cases H with
        | nil => rfl
        | cons _ rows => rfl

theorem bivarCoeff_singleRow_eq (r s : Nat) :
    bivarCoeff (List.replicate r ([] : Poly1 K) ++ [monomial1 (FieldCoeff.one : K) s]) r s =
      FieldCoeff.one := by
  induction r with
  | zero => exact coeff1_monomial1_eq _ s
  | succ r' ih => exact ih

theorem bivarCoeff_singleRow_other (r s : Nat) :
    ∀ r' s', (r' ≠ r ∨ s' ≠ s) →
      bivarCoeff (List.replicate r ([] : Poly1 K) ++ [monomial1 (FieldCoeff.one : K) s]) r' s' =
        FieldCoeff.zero := by
  induction r with
  | zero =>
    intro r' s' hne
    cases r' with
    | zero =>
      rcases hne with h1 | h2
      · exact False.elim (h1 rfl)
      · exact coeff1_monomial1_ne _ h2
    | succ _ => rfl
  | succ r' ih =>
    intro r'' s' hne
    cases r'' with
    | zero => rfl
    | succ m =>
      apply ih m s'
      rcases hne with h1 | h2
      · exact Or.inl (by omega)
      · exact Or.inr h2

/-- Whenever `0 ∈ A` and `d ∈ A` (`d ≥ 1`), `(u^d, v^d)` is a regular sequence of length `2`
    on ALL full polynomials in `R(A, d)` IF AND ONLY IF for all `r ≥ 0` and `s`,
    `s ∈ r A ∧ d + s ∈ r A → r ≥ 1 ∧ s ∈ (r - 1) A`. -/
theorem isBivarRegSeq2_UV_iff (K : Type) [FieldCoeff K] {A : Nat → Prop} {d : Nat}
    (h0A : A 0) (hdA : A d) (_hd : 1 ≤ d) :
    IsBivarRegSeq2_UV K A d ↔
      ∀ r s, InSetSumset A r s → InSetSumset A r (d + s) →
        1 ≤ r ∧ InSetSumset A (r - 1) s := by
  have hu_max : InBivarMaxIdeal A (uGen : BivarPoly K) := by
    refine ⟨?_, fun _ => rfl⟩
    intro r s h
    cases r with
    | zero => exact False.elim (h rfl)
    | succ r' =>
      cases r' with
      | zero =>
        cases s with
        | zero => exact InSetSumset.step InSetSumset.zero h0A
        | succ s' => exact False.elim (h rfl)
      | succ r'' => exact False.elim (h rfl)
  have hv_max : InBivarMaxIdeal A (vGen d : BivarPoly K) := by
    refine ⟨?_, fun _ => rfl⟩
    intro r s h
    cases r with
    | zero => exact False.elim (h rfl)
    | succ r' =>
      cases r' with
      | zero =>
        by_cases hsd : s = d
        · rw [hsd]
          have hmem : InSetSumset A (0 + 1) (0 + d) := InSetSumset.step InSetSumset.zero hdA
          rw [Nat.zero_add d] at hmem
          exact hmem
        · change coeff1 (monomial1 FieldCoeff.one d) s ≠ FieldCoeff.zero at h
          rw [coeff1_monomial1_ne _ hsd] at h
          exact False.elim (h rfl)
      | succ r'' => exact False.elim (h rfl)
  have hu_reg1 : IsBivarRegSeq1_U K A := by
    refine ⟨hu_max, ?_, ?_⟩
    · intro h1
      have h0 := ((inIdealU_iff A [[FieldCoeff.one]]).mp h1).1 0
      exact FieldCoeff.zero_ne_one h0.symm
    · intro H _ hmul r s
      have hr := hmul (r + 1) s
      rwa [bivarCoeff_uGen_mul_succ] at hr
  have h1_not_uv : ¬ InIdealUV A d ([[FieldCoeff.one]] : BivarPoly K) := by
    rintro ⟨Q1, Q2, _, _, heq⟩
    have h0 := heq 0 0
    rw [bivarCoeff_bivarAdd, bivarCoeff_uGen_mul_zero, bivarCoeff_vGen_mul_zero,
        FieldCoeff.zero_add] at h0
    exact FieldCoeff.zero_ne_one h0.symm
  constructor
  · intro hreg2 r s hrs hd_rs
    let H : BivarPoly K := List.replicate r [] ++ [monomial1 (FieldCoeff.one : K) s]
    have hH_coeff_eq : bivarCoeff H r s = FieldCoeff.one := bivarCoeff_singleRow_eq r s
    have hH_coeff_other : ∀ r' s', (r' ≠ r ∨ s' ≠ s) → bivarCoeff H r' s' = FieldCoeff.zero :=
      bivarCoeff_singleRow_other r s
    have hH_mem : InBivarSubring A H := by
      intro r' s' hne
      by_cases heq : r' = r ∧ s' = s
      · rcases heq with ⟨rfl, rfl⟩
        exact hrs
      · have hor : r' ≠ r ∨ s' ≠ s := by
          by_cases hr' : r' = r
          · right; intro hs'; exact heq ⟨hr', hs'⟩
          · exact Or.inl hr'
        rw [hH_coeff_other r' s' hor] at hne
        exact False.elim (hne rfl)
    have hvH_in_u : InIdealU A (bivarMul (vGen d) H) := by
      rw [inIdealU_iff]
      refine ⟨fun s' => bivarCoeff_vGen_mul_zero d H s', ?_⟩
      intro r' s' hne
      by_cases hlt : s' < d
      · rw [bivarCoeff_vGen_mul_succ_lt d H r' hlt] at hne
        exact False.elim (hne rfl)
      · have hsplit : s' = d + (s' - d) := by omega
        rw [hsplit, bivarCoeff_vGen_mul_succ_add d H r' (s' - d)] at hne
        by_cases heq : r' = r ∧ s' - d = s
        · rcases heq with ⟨rfl, hsub⟩
          have hs'_eq : s' = d + s := by omega
          rwa [hs'_eq]
        · have hor : r' ≠ r ∨ s' - d ≠ s := by
            by_cases hr' : r' = r
            · right; intro hs'; exact heq ⟨hr', hs'⟩
            · exact Or.inl hr'
          rw [hH_coeff_other r' (s' - d) hor] at hne
          exact False.elim (hne rfl)
    have hH_in_u : InIdealU A H := hreg2.2.2.2 H hH_mem hvH_in_u
    rcases (inIdealU_iff A H).mp hH_in_u with ⟨hH0, hHsucc⟩
    cases r with
    | zero =>
      have := hH0 s
      rw [hH_coeff_eq] at this
      exact False.elim (FieldCoeff.zero_ne_one this.symm)
    | succ r' =>
      refine ⟨by omega, hHsucc r' s ?_⟩
      rw [hH_coeff_eq]
      exact FieldCoeff.zero_ne_one.symm
  · intro hcomb
    refine ⟨hu_reg1, hv_max, h1_not_uv, ?_⟩
    intro H hH hvH_u
    rcases (inIdealU_iff A (bivarMul (vGen d) H)).mp hvH_u with ⟨_, hvH_succ⟩
    rw [inIdealU_iff]
    refine ⟨?_, ?_⟩
    · intro s
      by_cases hne : bivarCoeff H 0 s = FieldCoeff.zero
      · exact hne
      · have hs0 : InSetSumset A 0 s := hH 0 s hne
        have hds0 : InSetSumset A 0 (d + s) := by
          apply hvH_succ 0 (d + s)
          rwa [bivarCoeff_vGen_mul_succ_add d H 0 s]
        have := (hcomb 0 s hs0 hds0).1
        omega
    · intro r s hne
      have hrs : InSetSumset A (r + 1) s := hH (r + 1) s hne
      have hds : InSetSumset A (r + 1) (d + s) := by
        apply hvH_succ (r + 1) (d + s)
        rwa [bivarCoeff_vGen_mul_succ_add d H (r + 1) s]
      exact (hcomb (r + 1) s hrs hds).2

/-! ## 3. Projective Monomial Curve `R_{a,k}` Has Constant Homological Depth `2` -/

/-- Exponent set `A^{\mathrm{proj}}_{a,k} = {0} ∪ [a, a + k]` of the projective closure `R_{a,k}`. -/
def AProj (a k i : Nat) : Prop :=
  i = 0 ∨ (a ≤ i ∧ i ≤ a + k)

theorem inSetSumset_AProj_iff (a k r s : Nat) :
    InSetSumset (AProj a k) r s ↔ ∃ j, j ≤ r ∧ j * a ≤ s ∧ s ≤ j * (a + k) := by
  induction r generalizing s with
  | zero =>
    constructor
    · intro h; cases h; exact ⟨0, Nat.le_refl 0, by omega, by omega⟩
    · rintro ⟨j, hj0, hlow, hhigh⟩
      have hj : j = 0 := by omega
      subst hj
      have hs : s = 0 := by omega
      subst hs
      exact InSetSumset.zero
  | succ r ih =>
    constructor
    · intro h
      cases h with
      | step hprev hx =>
        rcases (ih _).mp hprev with ⟨j, hjr, hlow, hhigh⟩
        rcases hx with rfl | ⟨hxa, hxk⟩
        · exact ⟨j, by omega, by omega, by omega⟩
        · refine ⟨j + 1, by omega, ?_, ?_⟩
          · have : (j + 1) * a = j * a + a := Nat.succ_mul j a
            omega
          · have : (j + 1) * (a + k) = j * (a + k) + (a + k) := Nat.succ_mul j (a + k)
            omega
    · rintro ⟨j, hjr, hlow, hhigh⟩
      by_cases hj0 : j = 0
      · subst hj0
        have hs : s = 0 := by omega
        subst hs
        have : 0 = 0 + 0 := rfl
        rw [this]
        exact InSetSumset.step ((ih 0).mpr ⟨0, by omega, by omega, by omega⟩) (Or.inl rfl)
      · -- Split off one generator in [a, a + k] without let-bound min
        have hj_eq : (j - 1) + 1 = j := by omega
        have h1 : j * a = (j - 1) * a + a := by
          calc j * a = ((j - 1) + 1) * a := by rw [hj_eq]
            _ = (j - 1) * a + a := Nat.succ_mul _ a
        have h2 : j * (a + k) = (j - 1) * (a + k) + (a + k) := by
          calc j * (a + k) = ((j - 1) + 1) * (a + k) := by rw [hj_eq]
            _ = (j - 1) * (a + k) + (a + k) := Nat.succ_mul _ _
        have hja_le : (j - 1) * a ≤ (j - 1) * (a + k) := Nat.mul_le_mul_left _ (by omega)
        by_cases hcase : s - (j - 1) * a ≤ a + k
        · have hs_eq : (j - 1) * a + (s - (j - 1) * a) = s := by omega
          rw [← hs_eq]
          exact InSetSumset.step
            ((ih ((j - 1) * a)).mpr ⟨j - 1, by omega, Nat.le_refl _, hja_le⟩)
            (Or.inr ⟨by omega, hcase⟩)
        · have hs_eq : (s - (a + k)) + (a + k) = s := by omega
          rw [← hs_eq]
          exact InSetSumset.step
            ((ih (s - (a + k))).mpr ⟨j - 1, by omega, by omega, by omega⟩)
            (Or.inr ⟨by omega, Nat.le_refl _⟩)

/-- **Projective Monomial Curve Depth Lower Bound (`depth ≥ 2` Everywhere)**:
    For ALL `a ≥ 1, k ≥ 1` and ANY field `K`, `(u^{a+k}, v^{a+k})` is a regular sequence
    of length `2` on `R_{a,k} = K[u^{a+k}, u^k v^a, …, v^{a+k}]`. -/
theorem projectiveClosure_isRegSeq2 (K : Type) [FieldCoeff K] {a k : Nat}
    (ha : 1 ≤ a) (hk : 1 ≤ k) :
    IsBivarRegSeq2_UV K (AProj a k) (a + k) := by
  rw [isBivarRegSeq2_UV_iff K (Or.inl rfl) (Or.inr ⟨by omega, Nat.le_refl _⟩) (by omega)]
  intro r s hrs hds
  rw [inSetSumset_AProj_iff] at hrs hds
  rcases hrs with ⟨j1, hj1_r, hj1_low, hj1_high⟩
  rcases hds with ⟨j2, hj2_r, _, hj2_high⟩
  have hr_pos : 1 ≤ r := by
    cases r with
    | zero =>
      have : j2 = 0 := by omega
      subst this
      omega
    | succ _ => omega
  refine ⟨hr_pos, ?_⟩
  rw [inSetSumset_AProj_iff]
  have hs_up : s ≤ (r - 1) * (a + k) := by
    have hmul : j2 * (a + k) ≤ r * (a + k) := Nat.mul_le_mul_right (a + k) hj2_r
    have hexp : r * (a + k) = (r - 1) * (a + k) + (a + k) := by
      have : r - 1 + 1 = r := by omega
      calc r * (a + k) = (r - 1 + 1) * (a + k) := by rw [this]
        _ = (r - 1) * (a + k) + (a + k) := Nat.succ_mul _ _
    omega
  by_cases hj1_lt : j1 ≤ r - 1
  · exact ⟨j1, hj1_lt, hj1_low, hj1_high⟩
  · have hj1_eq : j1 = r := by omega
    rw [hj1_eq] at hj1_low
    refine ⟨r - 1, Nat.le_refl _, ?_, hs_up⟩
    have : (r - 1) * a ≤ r * a := Nat.mul_le_mul_right a (by omega)
    omega

/-- Every monomial of `R_{a,k}` (`1 ≤ k ≤ a - 1`) of degree `r ≥ ⌈(a-1)/k⌉ + 2`
    lies in `u^{a+k} R_{a,k} + v^{a+k} R_{a,k}`. -/
theorem projectiveClosure_high_degree_split {a k r s : Nat}
    (ha : 2 ≤ a) (hk : 1 ≤ k) (hka : k ≤ a - 1) (hr : ceilDiv (a - 1) k + 2 ≤ r)
    (hs : InSetSumset (AProj a k) r s) :
    InSetSumset (AProj a k) (r - 1) s ∨
      (a + k ≤ s ∧ InSetSumset (AProj a k) (r - 1) (s - (a + k))) := by
  rw [inSetSumset_AProj_iff] at hs
  rcases hs with ⟨j, hjr, hj_low, hj_high⟩
  by_cases hj_lt : j ≤ r - 1
  · left
    exact (inSetSumset_AProj_iff a k (r - 1) s).mpr ⟨j, hj_lt, hj_low, hj_high⟩
  · right
    have hj_eq : j = r := by omega
    rw [hj_eq] at hj_low hj_high
    have hr_ge2 : 2 ≤ r := by omega
    have h2a : 2 * a ≤ r * a := Nat.mul_le_mul_right a hr_ge2
    have h2a_eq : 2 * a = a + a := Nat.two_mul a
    have hak_le : a + k ≤ s := by omega
    refine ⟨hak_le, (inSetSumset_AProj_iff a k (r - 1) (s - (a + k))).mpr ?_⟩
    by_cases hge_r1 : (r - 1) * a ≤ s - (a + k)
    · refine ⟨r - 1, Nat.le_refl _, hge_r1, ?_⟩
      have hexp : r * (a + k) = (r - 1) * (a + k) + (a + k) := by
        have : r - 1 + 1 = r := by omega
        calc r * (a + k) = (r - 1 + 1) * (a + k) := by rw [this]
          _ = (r - 1) * (a + k) + (a + k) := Nat.succ_mul _ _
      omega
    · refine ⟨r - 2, by omega, ?_, ?_⟩
      · have hexp : r * a = (r - 2) * a + a + a := by
          have : r - 2 + 1 + 1 = r := by omega
          calc r * a = (r - 2 + 1 + 1) * a := by rw [this]
            _ = (r - 2 + 1) * a + a := Nat.succ_mul _ a
            _ = (r - 2) * a + a + a := by rw [Nat.succ_mul]
        omega
      · have hq_le : ceilDiv (a - 1) k ≤ r - 2 := by omega
        have hr2_k : a - 1 ≤ (r - 2) * k := (le_ceilDiv_iff (by omega)).mp hq_le
        have hexp1 : (r - 2) * (a + k) = (r - 2) * a + (r - 2) * k := Nat.mul_add _ a k
        have hexp2 : (r - 1) * a = (r - 2) * a + a := by
          have : r - 2 + 1 = r - 1 := by omega
          calc (r - 1) * a = (r - 2 + 1) * a := by rw [this]
            _ = (r - 2) * a + a := Nat.succ_mul _ a
        omega

/-- Filter a `Poly1 K` by an index predicate `keep : Nat → Bool`, zeroing out rejected coefficients. -/
def filterPoly1 {K : Type} [FieldCoeff K] (keep : Nat → Bool) (idx : Nat) : Poly1 K → Poly1 K
  | [] => []
  | c :: cs =>
    (if keep idx then c else FieldCoeff.zero) :: filterPoly1 keep (idx + 1) cs

theorem coeff1_filterPoly1 {K : Type} [FieldCoeff K] (keep : Nat → Bool) (idx : Nat)
    (p : Poly1 K) (n : Nat) :
    coeff1 (filterPoly1 keep idx p) n =
      if keep (idx + n) then coeff1 p n else FieldCoeff.zero := by
  induction p generalizing idx n with
  | nil =>
    simp [filterPoly1, coeff1]
  | cons c cs ih =>
    cases n with
    | zero =>
      have : idx + 0 = idx := Nat.add_zero idx
      rw [this]
      rfl
    | succ m =>
      simp [filterPoly1, coeff1]
      rw [ih (idx + 1) m]
      have : idx + 1 + m = idx + (m + 1) := by omega
      rw [this]

def buildQ1 {K : Type} [FieldCoeff K] (sel : Nat → Nat → Bool) (r : Nat) :
    BivarPoly K → BivarPoly K
  | [] => []
  | row :: rows => filterPoly1 (sel r) 0 row :: buildQ1 sel (r + 1) rows

def buildQ2 {K : Type} [FieldCoeff K] (sel : Nat → Nat → Bool) (d r : Nat) :
    BivarPoly K → BivarPoly K
  | [] => []
  | row :: rows =>
    (filterPoly1 (fun s => !sel r s) 0 row).drop d :: buildQ2 sel d (r + 1) rows

theorem bivarCoeff_buildQ1 {K : Type} [FieldCoeff K] (sel : Nat → Nat → Bool)
    (r0 : Nat) ( rows : BivarPoly K) (r s : Nat) :
    bivarCoeff (buildQ1 sel r0 rows) r s =
      if sel (r0 + r) s then bivarCoeff rows r s else FieldCoeff.zero := by
  induction rows generalizing r0 r with
  | nil =>
    simp [buildQ1, bivarCoeff]
  | cons row rs ih =>
    cases r with
    | zero =>
      have : r0 + 0 = r0 := Nat.add_zero r0
      rw [this]
      simp [buildQ1, bivarCoeff, coeff1_filterPoly1]
    | succ r' =>
      simp [buildQ1, bivarCoeff]
      rw [ih (r0 + 1) r']
      have : r0 + 1 + r' = r0 + (r' + 1) := by omega
      rw [this]

theorem bivarCoeff_buildQ2 {K : Type} [FieldCoeff K] (sel : Nat → Nat → Bool)
    (d r0 : Nat) (rows : BivarPoly K) (r s : Nat) :
    bivarCoeff (buildQ2 sel d r0 rows) r s =
      if !sel (r0 + r) (d + s) then bivarCoeff rows r (d + s) else FieldCoeff.zero := by
  induction rows generalizing r0 r with
  | nil =>
    simp [buildQ2, bivarCoeff]
  | cons row rs ih =>
    cases r with
    | zero =>
      have : r0 + 0 = r0 := Nat.add_zero r0
      rw [this]
      simp [buildQ2, bivarCoeff, coeff1_drop, coeff1_filterPoly1]
    | succ r' =>
      change bivarCoeff (buildQ2 sel d (r0 + 1) rs) r' s =
        if (!sel (r0 + (r' + 1)) (d + s)) = true then bivarCoeff rs r' (d + s) else FieldCoeff.zero
      rw [ih (r0 + 1) r']
      have : r0 + 1 + r' = r0 + (r' + 1) := by omega
      rw [this]

theorem bivar_in_idealUV_of_selector {K : Type} [FieldCoeff K] {A : Nat → Prop} {d : Nat}
    (P : BivarPoly K) (sel : Nat → Nat → Bool)
    (hP0 : ∀ s, bivarCoeff P 0 s = FieldCoeff.zero)
    (htrue : ∀ r s, bivarCoeff P (r + 1) s ≠ FieldCoeff.zero → sel r s = true →
      InSetSumset A r s)
    (hfalse : ∀ r s, bivarCoeff P (r + 1) s ≠ FieldCoeff.zero → sel r s = false →
      d ≤ s ∧ InSetSumset A r (s - d)) :
    InIdealUV A d P := by
  let tail := P.drop 1
  have htail : ∀ r s, bivarCoeff tail r s = bivarCoeff P (r + 1) s := by
    intro r s
    cases P with
    | nil => rfl
    | cons _ _ => rfl
  let Q1 := buildQ1 sel 0 tail
  let Q2 := buildQ2 sel d 0 tail
  refine ⟨Q1, Q2, ?_, ?_, ?_⟩
  · intro r s hne
    rw [bivarCoeff_buildQ1, Nat.zero_add, htail] at hne
    cases hsel : sel r s
    · rw [hsel] at hne; simp at hne
    · rw [hsel] at hne; simp at hne
      exact htrue r s hne hsel
  · intro r s hne
    rw [bivarCoeff_buildQ2, Nat.zero_add, htail] at hne
    cases hsel : sel r (d + s)
    · rw [hsel] at hne; simp at hne
      have hres := (hfalse r (d + s) hne hsel).2
      have : d + s - d = s := by omega
      rwa [this] at hres
    · rw [hsel] at hne; simp at hne
  · intro r s
    cases r with
    | zero =>
      rw [hP0 s, bivarCoeff_bivarAdd, bivarCoeff_uGen_mul_zero,
          bivarCoeff_vGen_mul_zero, FieldCoeff.zero_add]
    | succ r' =>
      rw [bivarCoeff_bivarAdd, bivarCoeff_uGen_mul_succ, bivarCoeff_buildQ1,
          Nat.zero_add, htail]
      by_cases hlt : s < d
      · rw [bivarCoeff_vGen_mul_succ_lt d Q2 r' hlt, FieldCoeff.add_zero]
        cases hsel : sel r' s
        · simp
          by_cases hne : bivarCoeff P (r' + 1) s = FieldCoeff.zero
          · exact hne
          · have hd_le := (hfalse r' s hne hsel).1
            omega
        · simp
      · have hsplit : s = d + (s - d) := by omega
        conv => rhs; arg 2; rw [hsplit]
        rw [bivarCoeff_vGen_mul_succ_add d Q2 r' (s - d), bivarCoeff_buildQ2,
            Nat.zero_add, ← hsplit, htail]
        cases hsel : sel r' s
        · simp [FieldCoeff.zero_add]
        · simp [FieldCoeff.add_zero]

/-- Boolean decision for `InSetSumset (AProj a k) r s`. -/
def decideAProjSumset (a k r s : Nat) : Bool :=
  -- True iff ∃ j ≤ r, j * a ≤ s ∧ s ≤ j * (a + k)
  let rec loop : Nat → Bool
    | 0 => decide (s == 0)
    | j + 1 => decide ((j + 1) * a ≤ s ∧ s ≤ (j + 1) * (a + k)) || loop j
  loop r

theorem decideAProjSumset_iff (a k r s : Nat) :
    decideAProjSumset a k r s = true ↔ InSetSumset (AProj a k) r s := by
  rw [inSetSumset_AProj_iff]
  unfold decideAProjSumset
  induction r with
  | zero =>
    simp [decideAProjSumset.loop]
  | succ r ih =>
    simp [decideAProjSumset.loop]
    constructor
    · rintro (⟨h1, h2⟩ | hprev)
      · exact ⟨r + 1, Nat.le_refl _, h1, h2⟩
      · rcases ih.mp hprev with ⟨j, hjr, h1, h2⟩
        exact ⟨j, by omega, h1, h2⟩
    · rintro ⟨j, hjr, h1, h2⟩
      by_cases hjeq : j = r + 1
      · subst hjeq
        exact Or.inl ⟨h1, h2⟩
      · right
        exact ih.mpr ⟨j, by omega, h1, h2⟩

/-- **Projective Monomial Curve Depth Upper Bound (`depth ≤ 2`, Exact Depth `2`)**:
    For ALL `a ≥ 2, 1 ≤ k ≤ a - 1`, `(u^{a+k}, v^{a+k})` cannot be extended to ANY
    length-`3` regular sequence `(u^{a+k}, v^{a+k}, G)` by ANY polynomial `G ∈ m_{R_{a,k}}`. -/
theorem projectiveClosure_no_regSeq3 (K : Type) [FieldCoeff K] {a k : Nat}
    (ha : 2 ≤ a) (hk : 1 ≤ k) (hka : k ≤ a - 1) (G : BivarPoly K) :
    ¬ IsBivarRegSeq3_UVG K (AProj a k) (a + k) G := by
  rintro ⟨⟨_, _, h1_not_uv, _⟩, hG_max, _, hreg3⟩
  let P := bivarPow G (ceilDiv (a - 1) k + 2)
  have hP_deg : ∀ r s, bivarCoeff P r s ≠ FieldCoeff.zero → ceilDiv (a - 1) k + 2 ≤ r :=
    bivarPow_degree_lower_bound hG_max (ceilDiv (a - 1) k + 2)
  have hP_mem : InBivarSubring (AProj a k) P := bivarSubring_pow hG_max.1 (ceilDiv (a - 1) k + 2)
  have hP_uv : InIdealUV (AProj a k) (a + k) P := by
    refine bivar_in_idealUV_of_selector P (decideAProjSumset a k) ?_ ?_ ?_
    · intro s
      by_cases hne : bivarCoeff P 0 s = FieldCoeff.zero
      · exact hne
      · have := hP_deg 0 s hne
        omega
    · intro r s _ hsel
      exact (decideAProjSumset_iff a k r s).mp hsel
    · intro r s hne hsel
      have hdeg : ceilDiv (a - 1) k + 2 ≤ r + 1 := hP_deg (r + 1) s hne
      have hrs : InSetSumset (AProj a k) (r + 1) s := hP_mem (r + 1) s hne
      rcases projectiveClosure_high_degree_split ha hk hka hdeg hrs with hleft | hright
      · have htrue := (decideAProjSumset_iff a k r s).mpr hleft
        rw [htrue] at hsel
        exact False.elim (Bool.noConfusion hsel)
      · exact hright
  have hdescend : ∀ m,
      InIdealUV (AProj a k) (a + k) (bivarPow G m) →
      InIdealUV (AProj a k) (a + k) ([[FieldCoeff.one]] : BivarPoly K) := by
    intro m
    induction m with
    | zero => exact id
    | succ m ih =>
      intro hm1
      exact ih (hreg3 (bivarPow G m) (bivarSubring_pow hG_max.1 m) hm1)
  exact h1_not_uv (hdescend (ceilDiv (a - 1) k + 2) hP_uv)

/-! ## 4. Symmetric-Gap Pinched Veronese Subrings `B_{a,k}^{(m)}` -/

/-- Exponent set `A^{\mathrm{ver}}_{a,k,m} = ⋃_{j=0}^m [j a, j a + m k]` of the `m`-th Veronese
    subring `B_{a,k}^{(m)}` of `B_{a,k} = K[u^{a+k-i} v^i : i ∈ [0,k] ∪ [a,a+k]]`. -/
def AVer (a k m s : Nat) : Prop :=
  ∃ j, j ≤ m ∧ j * a ≤ s ∧ s ≤ j * a + m * k

/-- For `m = 1` and `k + 2 ≤ a`, `AVer a k 1` is literally `[0, k] ∪ [a, a + k]`, whose gaps
    `[k + 1, a - 1]` are symmetric in `[0, a + k]`. -/
theorem aVer_one_iff {a k s : Nat} :
    AVer a k 1 s ↔ (s ≤ k ∨ (a ≤ s ∧ s ≤ a + k)) := by
  unfold AVer
  constructor
  · rintro ⟨j, hj1, hlow, hhigh⟩
    by_cases hj0 : j = 0
    · subst hj0; exact Or.inl (by omega)
    · have hj : j = 1 := by omega
      subst hj; exact Or.inr ⟨by omega, by omega⟩
  · rintro (h0 | ⟨h1, h2⟩)
    · exact ⟨0, by omega, by omega, by omega⟩
    · exact ⟨1, Nat.le_refl 1, by omega, by omega⟩

theorem aVer_one_gaps_symmetric {a k s : Nat} (hs : s ≤ a + k) :
    (¬ AVer a k 1 s) ↔ (¬ AVer a k 1 (a + k - s)) := by
  rw [aVer_one_iff, aVer_one_iff]
  omega

theorem inSetSumset_AVer_iff (a k m r s : Nat) :
    InSetSumset (AVer a k m) r s ↔ ∃ j, j ≤ r * m ∧ j * a ≤ s ∧ s ≤ j * a + r * m * k := by
  induction r generalizing s with
  | zero =>
    constructor
    · intro h; cases h; exact ⟨0, by omega, by omega, by omega⟩
    · rintro ⟨j, hj0, hlow, hhigh⟩
      have hj : j = 0 := by omega
      subst hj
      have hs : s = 0 := by omega
      subst hs
      exact InSetSumset.zero
  | succ r ih =>
    constructor
    · intro h
      cases h with
      | step hprev hx =>
        rcases (ih _).mp hprev with ⟨j1, hj1, h1_low, h1_high⟩
        rcases hx with ⟨j2, hj2, h2_low, h2_high⟩
        refine ⟨j1 + j2, ?_, ?_, ?_⟩
        · have : (r + 1) * m = r * m + m := Nat.succ_mul r m
          omega
        · rw [Nat.add_mul]
          omega
        · have h1 : (j1 + j2) * a = j1 * a + j2 * a := Nat.add_mul j1 j2 a
          have h2 : (r + 1) * m * k = r * m * k + m * k := by
            rw [Nat.succ_mul r m, Nat.add_mul]
          omega
    · rintro ⟨j, hj_rm, hlow, hhigh⟩
      have hrm_eq : (r + 1) * m = r * m + m := Nat.succ_mul r m
      have hrmk_eq : (r + 1) * m * k = r * m * k + m * k := by
        rw [Nat.succ_mul r m, Nat.add_mul]
      by_cases hj_le : j ≤ r * m
      · by_cases hrem : s - j * a ≤ r * m * k
        · have hs_eq : s + 0 = s := Nat.add_zero s
          rw [← hs_eq]
          exact InSetSumset.step
            ((ih s).mpr ⟨j, hj_le, hlow, by omega⟩)
            ⟨0, by omega, by omega, by omega⟩
        · have hs_eq : (j * a + r * m * k) + (s - j * a - r * m * k) = s := by omega
          rw [← hs_eq]
          exact InSetSumset.step
            ((ih (j * a + r * m * k)).mpr ⟨j, hj_le, by omega, by omega⟩)
            ⟨0, by omega, by omega, by omega⟩
      · have hj_split : r * m + (j - r * m) = j := by omega
        have hja_eq : j * a = (r * m) * a + (j - r * m) * a := by
          calc j * a = (r * m + (j - r * m)) * a := by rw [hj_split]
            _ = (r * m) * a + (j - r * m) * a := Nat.add_mul _ _ a
        by_cases hrem : s - j * a ≤ r * m * k
        · have hs_eq : ((r * m) * a + (s - j * a)) + (j - r * m) * a = s := by omega
          rw [← hs_eq]
          exact InSetSumset.step
            ((ih ((r * m) * a + (s - j * a))).mpr ⟨r * m, Nat.le_refl _, by omega, by omega⟩)
            ⟨j - r * m, by omega, by omega, by omega⟩
        · have hs_eq : ((r * m) * a + r * m * k) + ((j - r * m) * a + (s - j * a - r * m * k)) = s := by omega
          rw [← hs_eq]
          exact InSetSumset.step
            ((ih ((r * m) * a + r * m * k)).mpr ⟨r * m, Nat.le_refl _, by omega, by omega⟩)
            ⟨j - r * m, by omega, by omega, by omega⟩

/-- When `r * m * k ≥ a - 1`, `r · AVer a k m` equals the entire interval `[0, r * m * (a + k)]`. -/
theorem inSetSumset_AVer_full_interval {a k m r s : Nat}
    (ha : 2 ≤ a) (hcover : a - 1 ≤ r * m * k) :
    InSetSumset (AVer a k m) r s ↔ s ≤ r * m * (a + k) := by
  rw [inSetSumset_AVer_iff]
  constructor
  · rintro ⟨j, hj, _, hhigh⟩
    have hmul : j * a ≤ r * m * a := Nat.mul_le_mul_right a hj
    have hexp : r * m * (a + k) = r * m * a + r * m * k := Nat.mul_add (r * m) a k
    omega
  · intro hs_le
    by_cases hlt : s / a ≤ r * m
    · refine ⟨s / a, hlt, ?_, ?_⟩
      · have hdiv := Nat.div_add_mod s a
        have hc : s / a * a = a * (s / a) := Nat.mul_comm _ _
        omega
      · have hdiv := Nat.div_add_mod s a
        have hmod : s % a < a := Nat.mod_lt s (by omega)
        have hc : s / a * a = a * (s / a) := Nat.mul_comm _ _
        omega
    · refine ⟨r * m, Nat.le_refl _, ?_, ?_⟩
      · have hdiv := Nat.div_add_mod s a
        have h1 : r * m + 1 ≤ s / a := by omega
        have hmul : a * (r * m + 1) ≤ a * (s / a) := Nat.mul_le_mul_left a h1
        have hc1 : a * (r * m + 1) = r * m * a + a := by rw [Nat.mul_succ, Nat.mul_comm]
        omega
      · have hexp : r * m * (a + k) = r * m * a + r * m * k := Nat.mul_add (r * m) a k
        omega

/-- **Exact Veronese Depth-2 Threshold Theorem (`⌈(a-1)/k⌉`)**:
    For ALL `a ≥ 3`, `1 ≤ k ≤ a - 2`, `m ≥ 1`, and ANY field `K`,
    `(u^{m(a+k)}, v^{m(a+k)})` is a regular sequence of length `2` on `B_{a,k}^{(m)}`
    IF AND ONLY IF `m ≥ ⌈(a-1)/k⌉`. -/
theorem pinchedVeronese_isRegSeq2_iff (K : Type) [FieldCoeff K] {a k m : Nat}
    (ha : 3 ≤ a) (hk : 1 ≤ k) (hka : k ≤ a - 2) (hm : 1 ≤ m) :
    IsBivarRegSeq2_UV K (AVer a k m) (m * (a + k)) ↔ ceilDiv (a - 1) k ≤ m := by
  have _ := hka
  have h0_mem : AVer a k m 0 := ⟨0, by omega, by omega, by omega⟩
  have hD_mem : AVer a k m (m * (a + k)) := by
    refine ⟨m, Nat.le_refl m, ?_, ?_⟩
    · exact Nat.mul_le_mul_left m (by omega)
    · rw [Nat.mul_add m a k]
      exact Nat.le_refl _
  have hD_pos : 1 ≤ m * (a + k) := Nat.mul_pos hm (by omega)
  rw [isBivarRegSeq2_UV_iff K h0_mem hD_mem hD_pos]
  constructor
  · intro hcomb
    rw [le_ceilDiv_iff (by omega)]
    by_cases hle : a - 1 ≤ m * k
    · exact hle
    · have hmk_pos : 0 < m * k := Nat.mul_pos hm hk
      have hr_gt1 : 1 < ceilDiv (a - 1) (m * k) := by
        rw [lt_ceilDiv_iff hmk_pos]
        omega
      have hr_ge2 : 2 ≤ ceilDiv (a - 1) (m * k) := by omega
      have hr_low : (ceilDiv (a - 1) (m * k) - 1) * (m * k) < a - 1 :=
        ceilDiv_spec_lower (by omega) hmk_pos
      have hr_up : a - 1 ≤ ceilDiv (a - 1) (m * k) * (m * k) := ceilDiv_spec_upper hmk_pos
      have hr_up' : a - 1 ≤ ceilDiv (a - 1) (m * k) * m * k := by rwa [Nat.mul_assoc]
      have hs_lt_a : (ceilDiv (a - 1) (m * k) - 1) * m * k + 1 ≤ a - 1 := by
        have : (ceilDiv (a - 1) (m * k) - 1) * m * k =
            (ceilDiv (a - 1) (m * k) - 1) * (m * k) := Nat.mul_assoc _ _ _
        omega
      have h2D : 2 * (m * (a + k)) ≤ ceilDiv (a - 1) (m * k) * (m * (a + k)) :=
        Nat.mul_le_mul_right (m * (a + k)) hr_ge2
      have hrmD : ceilDiv (a - 1) (m * k) * (m * (a + k)) =
          ceilDiv (a - 1) (m * k) * m * (a + k) :=
        (Nat.mul_assoc _ m (a + k)).symm
      have ha_lt_D : a ≤ m * (a + k) := by
        have : 1 * (a + k) ≤ m * (a + k) := Nat.mul_le_mul_right (a + k) hm
        omega
      have h2D_eq : 2 * (m * (a + k)) = m * (a + k) + m * (a + k) := Nat.two_mul _
      have hs_in_r : InSetSumset (AVer a k m) (ceilDiv (a - 1) (m * k))
          ((ceilDiv (a - 1) (m * k) - 1) * m * k + 1) := by
        rw [inSetSumset_AVer_full_interval (by omega) hr_up']
        omega
      have hDs_in_r : InSetSumset (AVer a k m) (ceilDiv (a - 1) (m * k))
          (m * (a + k) + ((ceilDiv (a - 1) (m * k) - 1) * m * k + 1)) := by
        rw [inSetSumset_AVer_full_interval (by omega) hr_up']
        omega
      have hs_in_r1 : InSetSumset (AVer a k m) (ceilDiv (a - 1) (m * k) - 1)
          ((ceilDiv (a - 1) (m * k) - 1) * m * k + 1) :=
        (hcomb _ _ hs_in_r hDs_in_r).2
      rw [inSetSumset_AVer_iff] at hs_in_r1
      rcases hs_in_r1 with ⟨j, _, hj_low, hj_high⟩
      by_cases hj0 : j = 0
      · subst hj0
        omega
      · have hja : a ≤ j * a := by
          have : 1 * a ≤ j * a := Nat.mul_le_mul_right a (by omega)
          omega
        omega
  · intro hm_ge r s _ hDs
    have hmk : a - 1 ≤ m * k := (le_ceilDiv_iff (by omega)).mp hm_ge
    have hr_pos : 1 ≤ r := by
      cases r with
      | zero =>
        rcases (inSetSumset_AVer_iff a k m 0 _).mp hDs with ⟨j, hj0, _, h0⟩
        simp at hj0
        subst hj0
        simp at h0
        omega
      | succ _ => omega
    refine ⟨hr_pos, ?_⟩
    have hrmk : a - 1 ≤ r * m * k := by
      have h1 : 1 * (m * k) ≤ r * (m * k) := Nat.mul_le_mul_right (m * k) hr_pos
      have h2 : r * (m * k) = r * m * k := (Nat.mul_assoc r m k).symm
      omega
    have hDs_le : m * (a + k) + s ≤ r * m * (a + k) :=
      (inSetSumset_AVer_full_interval (by omega) hrmk).mp hDs
    by_cases hr1 : r = 1
    · subst hr1
      have h1D : 1 * m * (a + k) = m * (a + k) := by rw [Nat.one_mul]
      rw [h1D] at hDs_le
      have hs0 : s = 0 := by omega
      subst hs0
      exact InSetSumset.zero
    · have hr1_pos : 1 ≤ r - 1 := by omega
      have hr1_mk : a - 1 ≤ (r - 1) * m * k := by
        have h1 : 1 * (m * k) ≤ (r - 1) * (m * k) := Nat.mul_le_mul_right (m * k) hr1_pos
        have h2 : (r - 1) * (m * k) = (r - 1) * m * k := (Nat.mul_assoc _ m k).symm
        omega
      rw [inSetSumset_AVer_full_interval (by omega) hr1_mk]
      have hexp : r * m * (a + k) = (r - 1) * m * (a + k) + m * (a + k) := by
        have : r - 1 + 1 = r := by omega
        calc r * m * (a + k) = (r - 1 + 1) * m * (a + k) := by rw [this]
          _ = ((r - 1) * m + m) * (a + k) := by rw [Nat.succ_mul]
          _ = (r - 1) * m * (a + k) + m * (a + k) := Nat.add_mul _ _ _
      omega

end BivarAlgebra

end Conjecture00000000546
