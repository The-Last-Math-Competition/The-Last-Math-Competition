/-
  Conjecture 00000000592 — Disproof and Complete Structural Analysis
  Core Lean 4.19.0 formalization (zero external dependencies, zero sorry, zero custom axioms).

  Contents:
  1. Commutative fields (`CommField`) and non-vacuity witness (`Bool` = GF(2)).
  2. Duplicate-free lists (`Nodup`) and finite pigeonhole lemmas.
  3. Numerical semigroups (`NumericalSemigroup`), minimal semigroup generators / embedding
     dimension, pseudo-Frobenius numbers (`IsPseudoFrobenius`), and constructive shift-to-PF.
  4. Graded semigroup algebra `K[S]`, top graded local cohomology `H^1_m(K[S]) = K[t, t⁻¹]/K[S]`,
     socle characterization (`socle_nontrivial_iff_pf`), shifted graded canonical `K[S]`-module
     `ω_S(c)` with Matlis duality pairing (`matlisPair_smul_compat`), and exact minimal
     homogeneous generator theorem (`minimal_gen_characterization`).
  5. Positive alignment theorem (`alignment_of_type_le_two`) explaining why the conjecture
     holds whenever `type(S) ≤ 2` (in particular for all embedding dimensions `e ≤ 3`),
     illustrated on `S357 = ⟨3, 5, 7⟩` (`e = 3`, `type = 2`, `PF = {2, 4}`).
  6. Primary counterexample `S4679 = ⟨4, 6, 7, 9⟩` (`dim K[S] = 1`, `edim = 4`, `genus = 4`,
     `multiplicity = 4`, `type = 3`, `PF = {2, 3, 5}`, `Deg_min(ω) = {-5, -3, -2} + c`),
     proving `conjecture_592_false_numerical` over every field `K` and every shift `c, c' ∈ ℤ`.
  7. Non-Cohen–Macaulay 2-dimensional standard `ℤ`-graded affine semigroup counterexample
     `SMacaulay = ⟨(1,0), (1,1), (1,3), (1,4)⟩` (Macaulay's smooth rational quartic curve),
     where `|PF| = 1` (`type = 1`) while `μ(ω) = 3 ≠ 1` (`conjecture_592_false_macaulay`).
-/

namespace Conjecture00000000592

open Classical

/-! ## Section 1: Commutative Fields and Non-Vacuity Witness -/

class CommField (K : Type) where
  zero : K
  one : K
  add : K → K → K
  neg : K → K
  mul : K → K → K
  inv : K → K
  add_assoc : ∀ a b c : K, add (add a b) c = add a (add b c)
  add_comm : ∀ a b : K, add a b = add b a
  zero_add : ∀ a : K, add zero a = a
  add_zero : ∀ a : K, add a zero = a
  add_left_neg : ∀ a : K, add (neg a) a = zero
  mul_assoc : ∀ a b c : K, mul (mul a b) c = mul a (mul b c)
  mul_comm : ∀ a b : K, mul a b = mul b a
  one_mul : ∀ a : K, mul one a = a
  mul_one : ∀ a : K, mul a one = a
  left_distrib : ∀ a b c : K, mul a (add b c) = add (mul a b) (mul a c)
  right_distrib : ∀ a b c : K, mul (add a b) c = add (mul a c) (mul b c)
  mul_zero : ∀ a : K, mul a zero = zero
  zero_mul : ∀ a : K, mul zero a = zero
  zero_ne_one : zero ≠ one
  mul_inv_cancel : ∀ a : K, a ≠ zero → mul a (inv a) = one

/-- Concrete field instance `GF(2)` on `Bool`, witnessing non-vacuity of `CommField`. -/
instance instCommFieldBool : CommField Bool where
  zero := false
  one := true
  add := xor
  neg := id
  mul := and
  inv := id
  add_assoc := by intro a b c; cases a <;> cases b <;> cases c <;> rfl
  add_comm := by intro a b; cases a <;> cases b <;> rfl
  zero_add := by intro a; cases a <;> rfl
  add_zero := by intro a; cases a <;> rfl
  add_left_neg := by intro a; cases a <;> rfl
  mul_assoc := by intro a b c; cases a <;> cases b <;> cases c <;> rfl
  mul_comm := by intro a b; cases a <;> cases b <;> rfl
  one_mul := by intro a; cases a <;> rfl
  mul_one := by intro a; cases a <;> rfl
  left_distrib := by intro a b c; cases a <;> cases b <;> cases c <;> rfl
  right_distrib := by intro a b c; cases a <;> cases b <;> cases c <;> rfl
  mul_zero := by intro a; cases a <;> rfl
  zero_mul := by intro a; cases a <;> rfl
  zero_ne_one := by decide
  mul_inv_cancel := by
    intro a ha
    cases a
    · exact False.elim (ha rfl)
    · rfl

/-! ## Section 2: Finite Duplicate-Free Lists and Pigeonhole Helpers -/

inductive Nodup {α : Type} : List α → Prop where
  | nil : Nodup []
  | cons {x : α} {xs : List α} : x ∉ xs → Nodup xs → Nodup (x :: xs)

noncomputable def eraseFirstBy {α : Type} (P : α → Prop) : List α → List α
  | [] => []
  | y :: ys => if P y then ys else y :: eraseFirstBy P ys

theorem length_eraseFirstBy_add_one {α : Type} (P : α → Prop) :
    ∀ (ys : List α), (∃ y ∈ ys, P y) → (eraseFirstBy P ys).length + 1 = ys.length
  | [], ⟨_, hy, _⟩ => False.elim (List.not_mem_nil hy)
  | y :: ys, hex => by
      unfold eraseFirstBy
      by_cases hpy : P y
      · simp [hpy]
      · simp [hpy]
        rcases hex with ⟨z, hz, hpz⟩
        cases hz with
        | head => exact False.elim (hpy hpz)
        | tail _ hz' =>
            have ih := length_eraseFirstBy_add_one P ys ⟨z, hz', hpz⟩
            omega

theorem mem_eraseFirstBy_of_not {α : Type} (P : α → Prop) :
    ∀ {ys : List α} {z : α}, z ∈ ys → ¬ P z → z ∈ eraseFirstBy P ys
  | [], _, hz, _ => False.elim (List.not_mem_nil hz)
  | y :: ys, z, hz, hnpz => by
      unfold eraseFirstBy
      by_cases hpy : P y
      · rw [if_pos hpy]
        cases hz with
        | head => exact False.elim (hnpz hpy)
        | tail _ hz' => exact hz'
      · rw [if_neg hpy]
        cases hz with
        | head => exact List.Mem.head _
        | tail _ hz' => exact List.Mem.tail _ (mem_eraseFirstBy_of_not P hz' hnpz)

/-- Pigeonhole lower bound: if every element of a duplicate-free list `xs` appears in `ys.map fn`,
    then `xs.length ≤ ys.length`. -/
theorem nodup_length_le_of_fiber {α β : Type} (fn : α → β) :
    ∀ {xs : List β}, Nodup xs → ∀ {ys : List α},
      (∀ x ∈ xs, ∃ y ∈ ys, fn y = x) → xs.length ≤ ys.length
  | [], _, _, _ => Nat.zero_le _
  | x :: xs, Nodup.cons hx hnodup, ys, hcov => by
      have hx_hit : ∃ y ∈ ys, fn y = x := hcov x (List.Mem.head _)
      let ys' := eraseFirstBy (fun y => fn y = x) ys
      have hlen : ys'.length + 1 = ys.length :=
        length_eraseFirstBy_add_one (fun y => fn y = x) ys hx_hit
      have hcov' : ∀ x' ∈ xs, ∃ y ∈ ys', fn y = x' := by
        intro x' hx'
        rcases hcov x' (List.Mem.tail _ hx') with ⟨y, hy, hfy⟩
        have hne : fn y ≠ x := by
          intro heq
          rw [hfy] at heq
          subst heq
          exact hx hx'
        exact ⟨y, mem_eraseFirstBy_of_not (fun z => fn z = x) hy hne, hfy⟩
      have ih := nodup_length_le_of_fiber fn hnodup hcov'
      have hcons : (x :: xs).length = xs.length + 1 := rfl
      rw [hcons]
      omega

/-- Pigeonhole equality saturation: if `xs` is duplicate-free, every `x ∈ xs` is hit by `fn` on `ys`,
    and `ys.length ≤ xs.length`, then every `y ∈ ys` maps into `xs`. -/
theorem fiber_mem_of_nodup_of_length_le {α β : Type} (fn : α → β) :
    ∀ {xs : List β}, Nodup xs → ∀ {ys : List α},
      (∀ x ∈ xs, ∃ y ∈ ys, fn y = x) → ys.length ≤ xs.length →
      ∀ y ∈ ys, fn y ∈ xs
  | [], _, ys, _, hlen, _, hy => by
      cases ys with
      | nil => exact False.elim (List.not_mem_nil hy)
      | cons _ _ => simp at hlen
  | x :: xs, Nodup.cons hx hnodup, ys, hcov, hlen, y, hy => by
      by_cases hfy : fn y = x
      · rw [hfy]
        exact List.Mem.head _
      · have hx_hit : ∃ z ∈ ys, fn z = x := hcov x (List.Mem.head _)
        let ys' := eraseFirstBy (fun z => fn z = x) ys
        have hlen_er : ys'.length + 1 = ys.length :=
          length_eraseFirstBy_add_one (fun z => fn z = x) ys hx_hit
        have hcov' : ∀ x' ∈ xs, ∃ z ∈ ys', fn z = x' := by
          intro x' hx'
          rcases hcov x' (List.Mem.tail _ hx') with ⟨z, hz, hfz⟩
          have hne : fn z ≠ x := by
            intro heq
            rw [hfz] at heq
            subst heq
            exact hx hx'
          exact ⟨z, mem_eraseFirstBy_of_not (fun w => fn w = x) hz hne, hfz⟩
        have hlen' : ys'.length ≤ xs.length := by
          have hcons : (x :: xs).length = xs.length + 1 := rfl
          rw [hcons] at hlen
          omega
        have hy' : y ∈ ys' := mem_eraseFirstBy_of_not (fun z => fn z = x) hy hfy
        exact List.Mem.tail _ (fiber_mem_of_nodup_of_length_le fn hnodup hcov' hlen' y hy')

theorem nodup_map_of_injective {α β : Type} (f : α → β)
    (hinj : ∀ a b : α, f a = f b → a = b) :
    ∀ {xs : List α}, Nodup xs → Nodup (xs.map f)
  | [], _ => Nodup.nil
  | x :: xs, Nodup.cons hx hnod => by
      refine Nodup.cons ?_ (nodup_map_of_injective f hinj hnod)
      intro hmem
      rw [List.mem_map] at hmem
      rcases hmem with ⟨y, hy, hfy⟩
      have heq : y = x := hinj y x hfy
      subst heq
      exact hx hy

/-! ## Section 3: Numerical Semigroups, Embedding Dimension, and Pseudo-Frobenius Numbers -/

/-- A numerical semigroup `S ⊆ ℕ` (represented on `ℤ` supported on `ℤ≥0` with finite complement). -/
structure NumericalSemigroup where
  mem : Int → Prop
  zero_mem : mem 0
  add_mem : ∀ {a b : Int}, mem a → mem b → mem (a + b)
  nonneg : ∀ {a : Int}, mem a → 0 ≤ a
  eventually_all : ∃ B : Int, 0 ≤ B ∧ ∀ n : Int, B < n → mem n

def IsPosElem (S : NumericalSemigroup) (s : Int) : Prop :=
  S.mem s ∧ s ≠ 0

theorem posElem_pos (S : NumericalSemigroup) {s : Int} (hs : IsPosElem S s) : 0 < s := by
  have h0 : 0 ≤ s := S.nonneg hs.1
  have hne : s ≠ 0 := hs.2
  omega

/-- Minimal semigroup generator of `S` (`g ∈ S \ {0}` indecomposable in `S \ {0}`),
    corresponding to a homogeneous basis element of `m / m²`. -/
def IsMinSemigroupGen (S : NumericalSemigroup) (g : Int) : Prop :=
  IsPosElem S g ∧ ¬ ∃ a b : Int, IsPosElem S a ∧ IsPosElem S b ∧ a + b = g

def HasEmbeddingDim (S : NumericalSemigroup) (e : Nat) : Prop :=
  ∃ gens : List Int, Nodup gens ∧ gens.length = e ∧
    ∀ g : Int, g ∈ gens ↔ IsMinSemigroupGen S g

/-- Classical definition of pseudo-Frobenius numbers of `S`:
    `x ∈ ℤ \ S` such that `x + s ∈ S` for every `s ∈ S \ {0}`. -/
def IsPseudoFrobenius (S : NumericalSemigroup) (x : Int) : Prop :=
  ¬ S.mem x ∧ ∀ s : Int, IsPosElem S s → S.mem (x + s)

/-- `pf` enumerates `PF(S)` without duplicates; `pf.length` is the Cohen–Macaulay type `t(S)`. -/
def HasPFList (S : NumericalSemigroup) (pf : List Int) : Prop :=
  Nodup pf ∧ ∀ x : Int, x ∈ pf ↔ IsPseudoFrobenius S x

theorem exists_max_nat (Q : Nat → Prop) (h0 : Q 0) :
    ∀ top : Nat, ∃ j : Nat, j ≤ top ∧ Q j ∧ ∀ k : Nat, j < k → k ≤ top → ¬ Q k
  | 0 => ⟨0, Nat.le_refl 0, h0, by intro k h1 h2; omega⟩
  | top + 1 => by
      by_cases htop : Q (top + 1)
      · exact ⟨top + 1, Nat.le_refl _, htop, by intro k h1 h2; omega⟩
      · rcases exists_max_nat Q h0 top with ⟨j, hjle, hqj, hmax⟩
        refine ⟨j, by omega, hqj, ?_⟩
        intro k hjk hkle
        by_cases hk : k = top + 1
        · subst hk; exact htop
        · exact hmax k hjk (by omega)

/-- For every `x ∉ S`, some `S`-translate `x + s` (`s ∈ S`) is a pseudo-Frobenius number of `S`. -/
theorem exists_shift_in_pf (S : NumericalSemigroup) (x : Int) (hx : ¬ S.mem x) :
    ∃ s : Int, S.mem s ∧ IsPseudoFrobenius S (x + s) := by
  rcases S.eventually_all with ⟨B, _, hB⟩
  let Q : Nat → Prop := fun k => S.mem (k : Int) ∧ ¬ S.mem (x + (k : Int))
  have hQ0 : Q 0 := by
    refine ⟨S.zero_mem, ?_⟩
    have h0 : x + ((0 : Nat) : Int) = x := by omega
    rw [h0]
    exact hx
  have hQbound : ∀ k : Nat, Q k → k ≤ (B - x).toNat := by
    intro k hk
    have hle : x + (k : Int) ≤ B := by
      apply byContradiction
      intro hgt
      exact hk.2 (hB _ (by omega))
    omega
  rcases exists_max_nat Q hQ0 (B - x).toNat with ⟨j, _, hQj, hmax⟩
  refine ⟨(j : Int), hQj.1, ⟨hQj.2, ?_⟩⟩
  intro t ht
  have htpos : 0 < t := posElem_pos S ht
  apply byContradiction
  intro hnot
  have htnat : ∃ m : Nat, 0 < m ∧ t = (m : Int) := ⟨t.toNat, by omega, by omega⟩
  rcases htnat with ⟨m, hmpos, rfl⟩
  have hQjm : Q (j + m) := by
    refine ⟨?_, ?_⟩
    · have heq : ((j + m : Nat) : Int) = (j : Int) + (m : Int) := by omega
      rw [heq]
      exact S.add_mem hQj.1 ht.1
    · have heq : x + ((j + m : Nat) : Int) = (x + (j : Int)) + (m : Int) := by omega
      rw [heq]
      exact hnot
  have hjm_le : j + m ≤ (B - x).toNat := hQbound (j + m) hQjm
  exact hmax (j + m) (by omega) hjm_le hQjm

/-- Every numerical semigroup has at least one pseudo-Frobenius number (`type(S) ≥ 1`). -/
theorem exists_pf_elem (S : NumericalSemigroup) : ∃ f : Int, IsPseudoFrobenius S f := by
  have hm1 : ¬ S.mem (-1) := by
    intro h
    have hnn := S.nonneg h
    omega
  rcases exists_shift_in_pf S (-1) hm1 with ⟨s, _, hpf⟩
  exact ⟨-1 + s, hpf⟩

/-! ## Section 4: Graded Semigroup Ring `K[S]`, Local Cohomology `H¹_m`, and Canonical Module `ω_S(c)` -/

/-- Homogeneous component `K[S]_s` of the `ℤ`-graded semigroup ring `K[S]`. -/
structure RingHomog (K : Type) [CommField K] (S : NumericalSemigroup) (s : Int) where
  coeff : K
  zero_of_not_mem : ¬ S.mem s → coeff = CommField.zero

/-- Homogeneous component `H¹_m(K[S])_n = (K[t, t⁻¹]/K[S])_n` of top graded local cohomology. -/
structure LocalCohomHomog (K : Type) [CommField K] (S : NumericalSemigroup) (n : Int) where
  coeff : K
  zero_of_mem : S.mem n → coeff = CommField.zero

/-- Graded `K[S]`-action `K[S]_s × H¹_m(K[S])_n → H¹_m(K[S])_{s+n}` induced by `K[t, t⁻¹]/K[S]`. -/
noncomputable def localCohomSmul {K : Type} [CommField K] {S : NumericalSemigroup} {s n : Int}
    (r : RingHomog K S s) (u : LocalCohomHomog K S n) : LocalCohomHomog K S (s + n) :=
  if h : S.mem (s + n) then
    ⟨CommField.zero, fun _ => rfl⟩
  else
    ⟨CommField.mul r.coeff u.coeff, fun hm => False.elim (h hm)⟩

/-- Socle membership in `H¹_m(K[S])_n`: annihilated by the homogeneous maximal ideal `m = K[S]_{>0}`. -/
def InLocalCohomSocle {K : Type} [CommField K] {S : NumericalSemigroup} {n : Int}
    (u : LocalCohomHomog K S n) : Prop :=
  ∀ (s : Int), IsPosElem S s → ∀ (r : RingHomog K S s),
    (localCohomSmul r u).coeff = CommField.zero

/-- Exact characterization of the socle of `H¹_m(K[S])`: degree `n` carries a nonzero socle
    element if and only if `n ∈ PF(S)`. Thus `dim_K Soc(H¹_m(K[S])) = type(K[S]) = |PF(S)|`. -/
theorem socle_nontrivial_iff_pf (K : Type) [CommField K] (S : NumericalSemigroup) (n : Int) :
    (∃ u : LocalCohomHomog K S n, u.coeff ≠ CommField.zero ∧ InLocalCohomSocle u) ↔
      IsPseudoFrobenius S n := by
  constructor
  · rintro ⟨u, hnz, hsoc⟩
    refine ⟨?_, ?_⟩
    · intro hmem
      exact hnz (u.zero_of_mem hmem)
    · intro s hs
      apply byContradiction
      intro hnot
      let r1 : RingHomog K S s := ⟨CommField.one, fun hns => False.elim (hns hs.1)⟩
      have hact := hsoc s hs r1
      unfold localCohomSmul at hact
      have hsn : ¬ S.mem (s + n) := by
        intro hmem
        have heq : n + s = s + n := by omega
        rw [← heq] at hmem
        exact hnot hmem
      simp [hsn] at hact
      rw [CommField.one_mul] at hact
      exact hnz hact
  · intro hpf
    let u1 : LocalCohomHomog K S n := ⟨CommField.one, fun hm => False.elim (hpf.1 hm)⟩
    refine ⟨u1, fun heq => CommField.zero_ne_one heq.symm, ?_⟩
    intro s hs r
    unfold localCohomSmul
    have hsn : S.mem (s + n) := by
      have heq : s + n = n + s := by omega
      rw [heq]
      exact hpf.2 s hs
    simp [hsn]

/-- Degree support of the shifted graded canonical module `ω_S(c) = Hom_K(H¹_m(K[S]), K)(-c)`.
    At `c = 0`, `OmegaSupp S 0 d ↔ -d ∉ S` is Goto–Watanabe's canonical module `ω_{K[S]}`. -/
def OmegaSupp (S : NumericalSemigroup) (c d : Int) : Prop :=
  ¬ S.mem (c - d)

theorem omegaSupp_smul_closed (S : NumericalSemigroup) (c d s : Int)
    (hd : OmegaSupp S c d) (hs : S.mem s) : OmegaSupp S c (d + s) := by
  intro hmem
  apply hd
  have heq : c - d = (c - (d + s)) + s := by omega
  rw [heq]
  exact S.add_mem hmem hs

/-- Homogeneous component `ω_S(c)_d` over a field `K`. -/
structure OmegaHomog (K : Type) [CommField K] (S : NumericalSemigroup) (c d : Int) where
  coeff : K
  zero_of_not_supp : ¬ OmegaSupp S c d → coeff = CommField.zero

theorem OmegaHomog.ext {K : Type} [CommField K] {S : NumericalSemigroup} {c d : Int}
    {w₁ w₂ : OmegaHomog K S c d} (h : w₁.coeff = w₂.coeff) : w₁ = w₂ := by
  cases w₁; cases w₂; simp at h; subst h; rfl

def omegaZero (K : Type) [CommField K] (S : NumericalSemigroup) (c d : Int) :
    OmegaHomog K S c d :=
  ⟨CommField.zero, fun _ => rfl⟩

def omegaAdd {K : Type} [CommField K] {S : NumericalSemigroup} {c d : Int}
    (w₁ w₂ : OmegaHomog K S c d) : OmegaHomog K S c d :=
  ⟨CommField.add w₁.coeff w₂.coeff, fun hns => by
    rw [w₁.zero_of_not_supp hns, w₂.zero_of_not_supp hns, CommField.add_zero]⟩

/-- Graded `K[S]`-module multiplication `K[S]_s × ω_S(c)_d → ω_S(c)_{d+s}`. -/
def omegaSmul {K : Type} [CommField K] {S : NumericalSemigroup} {c d s : Int}
    (r : RingHomog K S s) (w : OmegaHomog K S c d) : OmegaHomog K S c (d + s) :=
  ⟨CommField.mul r.coeff w.coeff, fun hns => by
    by_cases hs : S.mem s
    · have hnd : ¬ OmegaSupp S c d := fun hd => hns (omegaSupp_smul_closed S c d s hd hs)
      rw [w.zero_of_not_supp hnd, CommField.mul_zero]
    · rw [r.zero_of_not_mem hs, CommField.zero_mul]⟩

/-- Graded Matlis duality pairing `ω_S(c)_d × H¹_m(K[S])_{c-d} → K`. -/
def matlisPair {K : Type} [CommField K] {S : NumericalSemigroup} {c d : Int}
    (w : OmegaHomog K S c d) (u : LocalCohomHomog K S (c - d)) : K :=
  CommField.mul w.coeff u.coeff

/-- `K[S]`-equivariance (graded adjointness) of the Matlis duality pairing between `ω_S(c)`
    and `H¹_m(K[S])`. -/
theorem matlisPair_smul_compat {K : Type} [CommField K] {S : NumericalSemigroup} {c d s : Int}
    (r : RingHomog K S s) (w : OmegaHomog K S c d) (u : LocalCohomHomog K S (c - (d + s))) :
    matlisPair (omegaSmul r w) u =
      matlisPair w ⟨(localCohomSmul r u).coeff, by
        intro hmem
        unfold localCohomSmul
        have hmem' : S.mem (s + (c - (d + s))) := by
          have heq : s + (c - (d + s)) = c - d := by omega
          rw [heq]; exact hmem
        simp [hmem']⟩ := by
  unfold matlisPair omegaSmul localCohomSmul
  dsimp
  by_cases hcd : S.mem (c - d)
  · have hmem' : S.mem (s + (c - (d + s))) := by
      have heq : s + (c - (d + s)) = c - d := by omega
      rw [heq]; exact hcd
    have hnd : ¬ OmegaSupp S c d := fun hd => hd hcd
    simp [hmem', w.zero_of_not_supp hnd, CommField.mul_zero, CommField.zero_mul]
  · have hnmem' : ¬ S.mem (s + (c - (d + s))) := by
      intro hm
      have heq : s + (c - (d + s)) = c - d := by omega
      rw [heq] at hm; exact hcd hm
    simp [hnmem']
    rw [CommField.mul_comm r.coeff w.coeff, CommField.mul_assoc]

/-! ## Section 5: Minimal Homogeneous Generators of `ω_S(c)` over `K[S]` -/

/-- A homogeneous element of `ω_S(c)` bundled with its `ℤ`-degree. -/
structure HomogGen (K : Type) [CommField K] (S : NumericalSemigroup) (c : Int) where
  deg : Int
  elem : OmegaHomog K S c deg

def omegaCast {K : Type} [CommField K] {S : NumericalSemigroup} {c d₁ d₂ : Int}
    (heq : d₁ = d₂) (w : OmegaHomog K S c d₁) : OmegaHomog K S c d₂ :=
  heq ▸ w

theorem omegaCast_coeff {K : Type} [CommField K] {S : NumericalSemigroup} {c d₁ d₂ : Int}
    (heq : d₁ = d₂) (w : OmegaHomog K S c d₁) :
    (omegaCast heq w).coeff = w.coeff := by
  subst heq; rfl

/-- Formal homogeneous `K[S]`-linear combination in degree `d` over a generator list `G`. -/
inductive GenComb (K : Type) [CommField K] (S : NumericalSemigroup) (c d : Int) :
    List (HomogGen K S c) → Type where
  | nil : GenComb K S c d []
  | cons {g : HomogGen K S c} {gs : List (HomogGen K S c)}
      (r : RingHomog K S (d - g.deg)) (rest : GenComb K S c d gs) :
      GenComb K S c d (g :: gs)

/-- Evaluation of a homogeneous `K[S]`-linear combination inside `ω_S(c)_d`. -/
def evalComb {K : Type} [CommField K] {S : NumericalSemigroup} {c d : Int} :
    {G : List (HomogGen K S c)} → GenComb K S c d G → OmegaHomog K S c d
  | [], GenComb.nil => omegaZero K S c d
  | g :: _, GenComb.cons r rest =>
      omegaAdd (omegaCast (by omega : g.deg + (d - g.deg) = d) (omegaSmul r g.elem))
        (evalComb rest)

def zeroComb (K : Type) [CommField K] (S : NumericalSemigroup) (c d : Int) :
    (G : List (HomogGen K S c)) → GenComb K S c d G
  | [] => GenComb.nil
  | _ :: gs => GenComb.cons ⟨CommField.zero, fun _ => rfl⟩ (zeroComb K S c d gs)

theorem evalComb_zeroComb (K : Type) [CommField K] (S : NumericalSemigroup) (c d : Int) :
    ∀ (G : List (HomogGen K S c)), (evalComb (zeroComb K S c d G)).coeff = CommField.zero
  | [] => rfl
  | g :: gs => by
      unfold zeroComb evalComb omegaAdd
      dsimp
      rw [omegaCast_coeff]
      unfold omegaSmul
      dsimp
      rw [CommField.zero_mul, evalComb_zeroComb K S c d gs, CommField.zero_add]

/-- `G` generates `ω_S(c)` as a graded `K[S]`-module if every homogeneous element in every
    degree `d ∈ ℤ` is a homogeneous `K[S]`-linear combination of `G`. -/
def GeneratesOmega {K : Type} [CommField K] {S : NumericalSemigroup} {c : Int}
    (G : List (HomogGen K S c)) : Prop :=
  ∀ (d : Int) (w : OmegaHomog K S c d), ∃ comb : GenComb K S c d G, evalComb comb = w

/-- `G` is a minimal homogeneous generating set of `ω_S(c)` over `K[S]` if it generates `ω_S(c)`
    and has minimum cardinality among all homogeneous generating sets. -/
def IsMinimalHomogGenSet {K : Type} [CommField K] {S : NumericalSemigroup} {c : Int}
    (G : List (HomogGen K S c)) : Prop :=
  GeneratesOmega G ∧
    ∀ G' : List (HomogGen K S c), GeneratesOmega G' → G.length ≤ G'.length

/-- Key graded Nakayama obstruction: for `f ∈ PF(S)`, no generator outside degree `c - f`
    can contribute a nonzero multiple to `ω_S(c)_{c - f}`. -/
theorem smul_zero_at_pf_deg {K : Type} [CommField K] {S : NumericalSemigroup} {c f : Int}
    (hf : IsPseudoFrobenius S f) (g : HomogGen K S c) (r : RingHomog K S ((c - f) - g.deg))
    (havoid : g.deg ≠ c - f ∨ g.elem.coeff = CommField.zero) :
    (omegaSmul r g.elem).coeff = CommField.zero := by
  unfold omegaSmul
  dsimp
  rcases havoid with hdeg | hzero
  · by_cases hs : S.mem ((c - f) - g.deg)
    · have hpos : IsPosElem S ((c - f) - g.deg) := ⟨hs, by omega⟩
      have hmem : S.mem (f + ((c - f) - g.deg)) := hf.2 _ hpos
      have heq : f + ((c - f) - g.deg) = c - g.deg := by omega
      rw [heq] at hmem
      have hnsupp : ¬ OmegaSupp S c g.deg := fun hsupp => hsupp hmem
      rw [g.elem.zero_of_not_supp hnsupp, CommField.mul_zero]
    · rw [r.zero_of_not_mem hs, CommField.zero_mul]
  · rw [hzero, CommField.mul_zero]

theorem evalComb_zero_of_avoid_pf {K : Type} [CommField K] {S : NumericalSemigroup} {c f : Int}
    (hf : IsPseudoFrobenius S f) :
    ∀ {G : List (HomogGen K S c)} (comb : GenComb K S c (c - f) G),
      (∀ g ∈ G, g.deg ≠ c - f ∨ g.elem.coeff = CommField.zero) →
      (evalComb comb).coeff = CommField.zero
  | [], GenComb.nil, _ => rfl
  | g :: gs, GenComb.cons r rest, hall => by
      unfold evalComb omegaAdd
      dsimp
      rw [omegaCast_coeff]
      have hg := hall g (List.Mem.head _)
      have hrest := evalComb_zero_of_avoid_pf hf rest (fun g' hg' => hall g' (List.Mem.tail _ hg'))
      rw [smul_zero_at_pf_deg hf g r hg, hrest, CommField.zero_add]

/-- Every homogeneous generating set of `ω_S(c)` must contain a nonzero generator in degree
    `c - f = -f + c` for every `f ∈ PF(S)`. -/
theorem pf_neg_mem_generators {K : Type} [CommField K] {S : NumericalSemigroup} {c f : Int}
    {G : List (HomogGen K S c)} (hgen : GeneratesOmega G) (hf : IsPseudoFrobenius S f) :
    ∃ g ∈ G, g.deg = c - f ∧ g.elem.coeff ≠ CommField.zero := by
  apply byContradiction
  intro hnone
  have havoid : ∀ g ∈ G, g.deg ≠ c - f ∨ g.elem.coeff = CommField.zero := by
    intro g hg
    by_cases hd : g.deg = c - f
    · right
      apply byContradiction
      intro hnz
      exact hnone ⟨g, hg, hd, hnz⟩
    · left; exact hd
  have hsupp : OmegaSupp S c (c - f) := by
    unfold OmegaSupp
    have heq : c - (c - f) = f := by omega
    rw [heq]
    exact hf.1
  let w1 : OmegaHomog K S c (c - f) := ⟨CommField.one, fun hns => False.elim (hns hsupp)⟩
  rcases hgen (c - f) w1 with ⟨comb, hcomb⟩
  have hzero := evalComb_zero_of_avoid_pf hf comb havoid
  rw [hcomb] at hzero
  exact CommField.zero_ne_one hzero.symm

/-- Constructive canonical basis of `ω_S(c)` indexed by a pseudo-Frobenius list `pf`. -/
def canonicalGenList (K : Type) [CommField K] (S : NumericalSemigroup) (c : Int) :
    (pf : List Int) → (∀ x ∈ pf, IsPseudoFrobenius S x) → List (HomogGen K S c)
  | [], _ => []
  | f :: fs, hpf =>
      have hf : IsPseudoFrobenius S f := hpf f (List.Mem.head _)
      have hsupp : OmegaSupp S c (c - f) := by
        unfold OmegaSupp
        have heq : c - (c - f) = f := by omega
        rw [heq]; exact hf.1
      ⟨c - f, ⟨CommField.one, fun hns => False.elim (hns hsupp)⟩⟩ ::
        canonicalGenList K S c fs (fun x hx => hpf x (List.Mem.tail _ hx))

theorem canonicalGenList_length (K : Type) [CommField K] (S : NumericalSemigroup) (c : Int) :
    ∀ (pf : List Int) (hpf : ∀ x ∈ pf, IsPseudoFrobenius S x),
      (canonicalGenList K S c pf hpf).length = pf.length
  | [], _ => rfl
  | _ :: fs, hpf => by
      unfold canonicalGenList
      simp [canonicalGenList_length K S c fs]

theorem singleTerm_canonicalGenList (K : Type) [CommField K] (S : NumericalSemigroup) (c d : Int)
    (a : K) :
    ∀ (pf : List Int) (hpf : ∀ x ∈ pf, IsPseudoFrobenius S x) (f : Int),
      f ∈ pf → S.mem (d - (c - f)) →
      ∃ comb : GenComb K S c d (canonicalGenList K S c pf hpf),
        (evalComb comb).coeff = a
  | [], _, _, hmem, _ => False.elim (List.not_mem_nil hmem)
  | f₀ :: fs, hpf, f, hmem, hs => by
      cases hmem with
      | head =>
          dsimp [canonicalGenList]
          let r : RingHomog K S (d - (c - f₀)) := ⟨a, fun hns => False.elim (hns hs)⟩
          let rest := zeroComb K S c d
            (canonicalGenList K S c fs (fun x hx => hpf x (List.Mem.tail _ hx)))
          refine ⟨GenComb.cons r rest, ?_⟩
          unfold evalComb omegaAdd
          dsimp
          rw [omegaCast_coeff]
          unfold omegaSmul
          dsimp
          rw [CommField.mul_one, evalComb_zeroComb, CommField.add_zero]
      | tail _ hmem' =>
          dsimp [canonicalGenList]
          rcases singleTerm_canonicalGenList K S c d a fs
              (fun x hx => hpf x (List.Mem.tail _ hx)) f hmem' hs with ⟨rest, hrest⟩
          let r0 : RingHomog K S (d - (c - f₀)) := ⟨CommField.zero, fun _ => rfl⟩
          refine ⟨GenComb.cons r0 rest, ?_⟩
          unfold evalComb omegaAdd
          dsimp
          rw [omegaCast_coeff]
          unfold omegaSmul
          dsimp
          rw [CommField.zero_mul, hrest, CommField.zero_add]

/-- `canonicalGenList K S c pf` generates the entire graded module `ω_S(c)` over `K[S]`. -/
theorem canonicalGenList_generates (K : Type) [CommField K] (S : NumericalSemigroup) (c : Int)
    {pf : List Int} (hpf : HasPFList S pf) :
    GeneratesOmega (canonicalGenList K S c pf (fun x hx => (hpf.2 x).1 hx)) := by
  intro d w
  by_cases hsupp : OmegaSupp S c d
  · unfold OmegaSupp at hsupp
    rcases exists_shift_in_pf S (c - d) hsupp with ⟨s, hs, hpfs⟩
    let f := (c - d) + s
    have hf_mem : f ∈ pf := (hpf.2 f).2 hpfs
    have hs_eq : d - (c - f) = s := by omega
    have hs_mem : S.mem (d - (c - f)) := by rw [hs_eq]; exact hs
    rcases singleTerm_canonicalGenList K S c d w.coeff pf
        (fun x hx => (hpf.2 x).1 hx) f hf_mem hs_mem with ⟨comb, hcoeff⟩
    exact ⟨comb, OmegaHomog.ext hcoeff⟩
  · refine ⟨zeroComb K S c d _, OmegaHomog.ext ?_⟩
    rw [evalComb_zeroComb, w.zero_of_not_supp hsupp]

/-- **Exact Minimal Homogeneous Generator Theorem (`minimal_gen_characterization`):**
    Over *any* field `K`, for *any* numerical semigroup `S` with PF list `pf` and *any*
    canonical grading shift `c ∈ ℤ`:
    1. Minimal homogeneous generating sets of `ω_S(c)` over `K[S]` exist (`canonicalGenList`).
    2. Every minimal homogeneous generating set `G` has cardinality `G.length = pf.length = type(K[S])`
       (**confirming the generator-count half of Conjecture 00000000592 for all numerical semigroups**).
    3. The exact set of degrees of `G` is `{-f + c | f ∈ PF(S)}` (**negated** PF numbers plus `c`). -/
theorem minimal_gen_characterization (K : Type) [CommField K] (S : NumericalSemigroup) (c : Int)
    {pf : List Int} (hpf : HasPFList S pf) :
    (IsMinimalHomogGenSet (canonicalGenList K S c pf (fun x hx => (hpf.2 x).1 hx))) ∧
    (∀ G : List (HomogGen K S c), IsMinimalHomogGenSet G →
      G.length = pf.length ∧
      ∀ d : Int, d ∈ G.map HomogGen.deg ↔ ∃ f : Int, IsPseudoFrobenius S f ∧ d = -f + c) := by
  let Gcan := canonicalGenList K S c pf (fun x hx => (hpf.2 x).1 hx)
  have hcan_gen : GeneratesOmega Gcan := canonicalGenList_generates K S c hpf
  have hcan_len : Gcan.length = pf.length := canonicalGenList_length K S c pf _
  let negList : List Int := pf.map (fun f => c - f)
  have hnodup_neg : Nodup negList :=
    nodup_map_of_injective (fun f => c - f) (by intro a b h; dsimp at h; omega) hpf.1
  have hneg_len : negList.length = pf.length := by simp [negList]
  have hlower : ∀ G' : List (HomogGen K S c), GeneratesOmega G' → pf.length ≤ G'.length := by
    intro G' hgen'
    have hcov : ∀ d ∈ negList, ∃ g ∈ G', g.deg = d := by
      intro d hd
      rw [List.mem_map] at hd
      rcases hd with ⟨f, hfmem, rfl⟩
      rcases pf_neg_mem_generators hgen' ((hpf.2 f).1 hfmem) with ⟨g, hg, hdeg, _⟩
      exact ⟨g, hg, hdeg⟩
    have hle := nodup_length_le_of_fiber HomogGen.deg hnodup_neg hcov
    rw [hneg_len] at hle
    exact hle
  refine ⟨⟨hcan_gen, fun G' hgen' => by rw [hcan_len]; exact hlower G' hgen'⟩, ?_⟩
  intro G hmin
  have hge : pf.length ≤ G.length := hlower G hmin.1
  have hle : G.length ≤ pf.length := by
    have h := hmin.2 Gcan hcan_gen
    rw [hcan_len] at h
    exact h
  have hlen_eq : G.length = pf.length := by omega
  refine ⟨hlen_eq, ?_⟩
  intro d
  have hcov : ∀ d' ∈ negList, ∃ g ∈ G, g.deg = d' := by
    intro d' hd'
    rw [List.mem_map] at hd'
    rcases hd' with ⟨f, hfmem, rfl⟩
    rcases pf_neg_mem_generators hmin.1 ((hpf.2 f).1 hfmem) with ⟨g, hg, hdeg, _⟩
    exact ⟨g, hg, hdeg⟩
  constructor
  · intro hd
    rw [List.mem_map] at hd
    rcases hd with ⟨g, hg, rfl⟩
    have hmem_neg : g.deg ∈ negList :=
      fiber_mem_of_nodup_of_length_le HomogGen.deg hnodup_neg hcov
        (by omega) g hg
    rw [List.mem_map] at hmem_neg
    rcases hmem_neg with ⟨f, hfmem, hfeq⟩
    exact ⟨f, (hpf.2 f).1 hfmem, by omega⟩
  · rintro ⟨f, hf, rfl⟩
    rcases pf_neg_mem_generators hmin.1 hf with ⟨g, hg, hdeg, _⟩
    rw [List.mem_map]
    exact ⟨g, hg, by omega⟩

/-! ## Section 6: Positive Alignment Theorem for `type(S) ≤ 2` (and Concrete `e = 3` Witness) -/

/-- **Positive Alignment Theorem (`alignment_of_type_le_two`):**
    Whenever `type(S) = |PF(S)| ≤ 2` (which by Herzog 1970 holds for *every* numerical semigroup
    of embedding dimension `e ≤ 3`, as well as all symmetric and pseudo-symmetric numerical
    semigroups in any embedding dimension), `-PF(S) + c` IS a constant shift of `PF(S)`! -/
theorem alignment_of_type_le_two (K : Type) [CommField K] (S : NumericalSemigroup) (c : Int)
    {pf : List Int} (hpf : HasPFList S pf) (htype : pf.length ≤ 2) :
    ∃ constShift : Int, ∀ G : List (HomogGen K S c), IsMinimalHomogGenSet G →
      ∀ d : Int, d ∈ G.map HomogGen.deg ↔ ∃ f : Int, IsPseudoFrobenius S f ∧ d = f + constShift := by
  have hchar := (minimal_gen_characterization K S c hpf).2
  cases pf with
  | nil =>
      rcases exists_pf_elem S with ⟨f, hf⟩
      exact False.elim (List.not_mem_nil ((hpf.2 f).2 hf))
  | cons f₁ rest =>
      cases rest with
      | nil =>
          refine ⟨c - 2 * f₁, ?_⟩
          intro G hmin d
          rw [(hchar G hmin).2 d]
          constructor
          · rintro ⟨f, hf, rfl⟩
            have hmem : f ∈ [f₁] := (hpf.2 f).2 hf
            simp at hmem
            subst hmem
            exact ⟨f, hf, by omega⟩
          · rintro ⟨f, hf, rfl⟩
            have hmem : f ∈ [f₁] := (hpf.2 f).2 hf
            simp at hmem
            subst hmem
            exact ⟨f, hf, by omega⟩
      | cons f₂ rest₂ =>
          cases rest₂ with
          | nil =>
              refine ⟨c - (f₁ + f₂), ?_⟩
              intro G hmin d
              rw [(hchar G hmin).2 d]
              constructor
              · rintro ⟨f, hf, rfl⟩
                have hmem : f ∈ [f₁, f₂] := (hpf.2 f).2 hf
                simp at hmem
                rcases hmem with rfl | rfl
                · exact ⟨f₂, (hpf.2 f₂).1 (by simp), by omega⟩
                · exact ⟨f₁, (hpf.2 f₁).1 (by simp), by omega⟩
              · rintro ⟨f, hf, rfl⟩
                have hmem : f ∈ [f₁, f₂] := (hpf.2 f).2 hf
                simp at hmem
                rcases hmem with rfl | rfl
                · exact ⟨f₂, (hpf.2 f₂).1 (by simp), by omega⟩
                · exact ⟨f₁, (hpf.2 f₁).1 (by simp), by omega⟩
          | cons _ _ =>
              simp at htype

/-- Concrete embedding-dimension-3 non-symmetric numerical semigroup `S357 = ⟨3, 5, 7⟩`. -/
def S357 : NumericalSemigroup where
  mem n := 0 ≤ n ∧ n ≠ 1 ∧ n ≠ 2 ∧ n ≠ 4
  zero_mem := by omega
  add_mem := by intro a b ha hb; omega
  nonneg := by intro a ha; omega
  eventually_all := ⟨4, by omega, by intro n hn; omega⟩

theorem S357_edim_three : HasEmbeddingDim S357 3 := by
  refine ⟨[3, 5, 7], ?_, rfl, ?_⟩
  · exact Nodup.cons (by simp) (Nodup.cons (by simp) (Nodup.cons (by simp) Nodup.nil))
  · intro g
    constructor
    · intro hg
      simp at hg
      rcases hg with rfl | rfl | rfl
      · refine ⟨⟨by dsimp [S357]; omega, by omega⟩, ?_⟩
        rintro ⟨a, b, ha, hb, heq⟩; dsimp [IsPosElem, S357] at ha hb; omega
      · refine ⟨⟨by dsimp [S357]; omega, by omega⟩, ?_⟩
        rintro ⟨a, b, ha, hb, heq⟩; dsimp [IsPosElem, S357] at ha hb; omega
      · refine ⟨⟨by dsimp [S357]; omega, by omega⟩, ?_⟩
        rintro ⟨a, b, ha, hb, heq⟩; dsimp [IsPosElem, S357] at ha hb; omega
    · rintro ⟨hpos, hnsum⟩
      dsimp [IsPosElem, S357] at hpos
      by_cases h6 : g = 6
      · exfalso
        exact hnsum ⟨3, 3, ⟨by dsimp [S357]; omega, by omega⟩,
          ⟨by dsimp [S357]; omega, by omega⟩, by omega⟩
      · by_cases hle7 : g ≤ 7
        · simp; omega
        · exfalso
          exact hnsum ⟨3, g - 3, ⟨by dsimp [S357]; omega, by omega⟩,
            ⟨by dsimp [S357]; omega, by omega⟩, by omega⟩

theorem S357_pf_two_four : HasPFList S357 [2, 4] := by
  refine ⟨Nodup.cons (by simp) (Nodup.cons (by simp) Nodup.nil), ?_⟩
  intro x
  simp [IsPseudoFrobenius, IsPosElem, S357]
  constructor
  · rintro (rfl | rfl)
    · refine ⟨by omega, ?_⟩; intro s hs0 hs1 hs2 hs4 hsne; omega
    · refine ⟨by omega, ?_⟩; intro s hs0 hs1 hs2 hs4 hsne; omega
  · rintro ⟨hnx, hall⟩
    by_cases hx2 : x = 2
    · left; exact hx2
    · by_cases hx4 : x = 4
      · right; exact hx4
      · exfalso
        have h3 := hall 3 (by omega) (by omega) (by omega) (by omega) (by omega)
        have h5 := hall 5 (by omega) (by omega) (by omega) (by omega) (by omega)
        omega

/-! ## Section 7: Primary Counterexample `S4679 = ⟨4, 6, 7, 9⟩` (`edim = 4`, `type = 3`) -/

/-- The numerical semigroup `S4679 = ⟨4, 6, 7, 9⟩ = ℕ \ {1, 2, 3, 5}`. -/
def S4679 : NumericalSemigroup where
  mem n := 0 ≤ n ∧ n ≠ 1 ∧ n ≠ 2 ∧ n ≠ 3 ∧ n ≠ 5
  zero_mem := by omega
  add_mem := by intro a b ha hb; omega
  nonneg := by intro a ha; omega
  eventually_all := ⟨5, by omega, by intro n hn; omega⟩

/-- Proof that `S4679` is literally the submonoid of `ℤ` generated by `{4, 6, 7, 9}`. -/
theorem S4679_iff_generated_by_4_6_7_9 (n : Int) :
    S4679.mem n ↔ ∃ a b c d : Nat,
      n = 4 * (a : Int) + 6 * (b : Int) + 7 * (c : Int) + 9 * (d : Int) := by
  constructor
  · intro hn
    dsimp [S4679] at hn
    by_cases hn0 : n = 0
    · exact ⟨0, 0, 0, 0, by omega⟩
    · by_cases hn4 : n = 4
      · exact ⟨1, 0, 0, 0, by omega⟩
      · have hge6 : 6 ≤ n := by omega
        let q : Nat := ((n - 6) / 4).toNat
        let r : Int := (n - 6) % 4
        have hdiv : n - 6 = 4 * (q : Int) + r := by omega
        have hr : r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3 := by omega
        rcases hr with hr0 | hr1 | hr2 | hr3
        · exact ⟨q, 1, 0, 0, by omega⟩
        · exact ⟨q, 0, 1, 0, by omega⟩
        · exact ⟨q + 2, 0, 0, 0, by omega⟩
        · exact ⟨q, 0, 0, 1, by omega⟩
  · rintro ⟨a, b, c, d, rfl⟩
    dsimp [S4679]
    by_cases ha : a = 0 <;> by_cases hb : b = 0 <;> by_cases hc : c = 0 <;> omega

/-- `S4679` has exact minimal semigroup generating set `[4, 6, 7, 9]`, hence embedding dimension `4`. -/
theorem S4679_edim_four : HasEmbeddingDim S4679 4 := by
  refine ⟨[4, 6, 7, 9], ?_, rfl, ?_⟩
  · exact Nodup.cons (by simp) (Nodup.cons (by simp)
      (Nodup.cons (by simp) (Nodup.cons (by simp) Nodup.nil)))
  · intro g
    constructor
    · intro hg
      simp at hg
      rcases hg with rfl | rfl | rfl | rfl
      · refine ⟨⟨by dsimp [S4679]; omega, by omega⟩, ?_⟩
        rintro ⟨a, b, ha, hb, heq⟩; dsimp [IsPosElem, S4679] at ha hb; omega
      · refine ⟨⟨by dsimp [S4679]; omega, by omega⟩, ?_⟩
        rintro ⟨a, b, ha, hb, heq⟩; dsimp [IsPosElem, S4679] at ha hb; omega
      · refine ⟨⟨by dsimp [S4679]; omega, by omega⟩, ?_⟩
        rintro ⟨a, b, ha, hb, heq⟩; dsimp [IsPosElem, S4679] at ha hb; omega
      · refine ⟨⟨by dsimp [S4679]; omega, by omega⟩, ?_⟩
        rintro ⟨a, b, ha, hb, heq⟩; dsimp [IsPosElem, S4679] at ha hb; omega
    · rintro ⟨hpos, hnsum⟩
      dsimp [IsPosElem, S4679] at hpos
      by_cases h8 : g = 8
      · exfalso
        exact hnsum ⟨4, 4, ⟨by dsimp [S4679]; omega, by omega⟩,
          ⟨by dsimp [S4679]; omega, by omega⟩, by omega⟩
      · by_cases hle9 : g ≤ 9
        · simp; omega
        · exfalso
          exact hnsum ⟨4, g - 4, ⟨by dsimp [S4679]; omega, by omega⟩,
            ⟨by dsimp [S4679]; omega, by omega⟩, by omega⟩

/-- `S4679` has exact pseudo-Frobenius set `{2, 3, 5}`, hence Cohen–Macaulay type `3`. -/
theorem S4679_pf_two_three_five : HasPFList S4679 [2, 3, 5] := by
  refine ⟨Nodup.cons (by simp) (Nodup.cons (by simp) (Nodup.cons (by simp) Nodup.nil)), ?_⟩
  intro x
  simp [IsPseudoFrobenius, IsPosElem, S4679]
  constructor
  · rintro (rfl | rfl | rfl)
    · refine ⟨by omega, ?_⟩; intro s hs0 hs1 hs2 hs3 hs5 hsne; omega
    · refine ⟨by omega, ?_⟩; intro s hs0 hs1 hs2 hs3 hs5 hsne; omega
    · refine ⟨by omega, ?_⟩; intro s hs0 hs1 hs2 hs3 hs5 hsne; omega
  · rintro ⟨hnx, hall⟩
    by_cases hx2 : x = 2
    · left; exact hx2
    · by_cases hx3 : x = 3
      · right; left; exact hx3
      · by_cases hx5 : x = 5
        · right; right; exact hx5
        · exfalso
          have h4 := hall 4 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
          have h6 := hall 6 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
          omega

/-- **Main Disproof Theorem (`conjecture_592_false_numerical`):**
    For the numerical semigroup `S4679 = ⟨4, 6, 7, 9⟩` (Krull dimension `1`, embedding dimension `4`,
    genus `4`, multiplicity `4`, Cohen–Macaulay type `3`), over *every* commutative field `K`,
    for *every* grading shift `c ∈ ℤ` of the canonical module `ω_S(c)`, and for *every* minimal
    homogeneous generating set `G` of `ω_S(c)` over `K[S]`:
    1. `G.length = 3` (the minimal generator count DOES equal `type(K[S]) = 3`),
    2. `G` has exact degree set `{-5 + c, -3 + c, -2 + c}`, and
    3. For *every* constant `constShift ∈ ℤ`, the degree set of `G` is NOT equal to
       `PF(S4679) + constShift = {2 + constShift, 3 + constShift, 5 + constShift}`. -/
theorem conjecture_592_false_numerical (K : Type) [CommField K] (c : Int)
    (G : List (HomogGen K S4679 c)) (hmin : IsMinimalHomogGenSet G) :
    G.length = 3 ∧
    (∀ d : Int, d ∈ G.map HomogGen.deg ↔ d = -5 + c ∨ d = -3 + c ∨ d = -2 + c) ∧
    (∀ constShift : Int,
      ¬ (∀ d : Int, d ∈ G.map HomogGen.deg ↔
          ∃ f : Int, IsPseudoFrobenius S4679 f ∧ d = f + constShift)) := by
  have hchar := (minimal_gen_characterization K S4679 c S4679_pf_two_three_five).2 G hmin
  have hpf_iff : ∀ f : Int, IsPseudoFrobenius S4679 f ↔ f = 2 ∨ f = 3 ∨ f = 5 := by
    intro f
    have h := (S4679_pf_two_three_five.2 f).symm
    simp at h
    exact h
  have hdeg_iff : ∀ d : Int, d ∈ G.map HomogGen.deg ↔ d = -5 + c ∨ d = -3 + c ∨ d = -2 + c := by
    intro d
    rw [hchar.2 d]
    constructor
    · rintro ⟨f, hf, rfl⟩
      rw [hpf_iff] at hf
      omega
    · intro hd
      rcases hd with rfl | rfl | rfl
      · exact ⟨5, (hpf_iff 5).2 (by omega), by omega⟩
      · exact ⟨3, (hpf_iff 3).2 (by omega), by omega⟩
      · exact ⟨2, (hpf_iff 2).2 (by omega), by omega⟩
  refine ⟨hchar.1, hdeg_iff, ?_⟩
  intro constShift hall
  have hm5 : (-5 + c ∈ G.map HomogGen.deg) := (hdeg_iff (-5 + c)).2 (by omega)
  have hm3 : (-3 + c ∈ G.map HomogGen.deg) := (hdeg_iff (-3 + c)).2 (by omega)
  have hm2 : (-2 + c ∈ G.map HomogGen.deg) := (hdeg_iff (-2 + c)).2 (by omega)
  rcases (hall (-5 + c)).1 hm5 with ⟨f₁, hf₁, heq₁⟩
  rcases (hall (-3 + c)).1 hm3 with ⟨f₂, hf₂, heq₂⟩
  rcases (hall (-2 + c)).1 hm2 with ⟨f₃, hf₃, heq₃⟩
  rw [hpf_iff] at hf₁ hf₂ hf₃
  omega

/-- Specialized existential packaging over `GF(2)` (`Bool`) confirming non-vacuity: there exist
    a field `K`, a numerical semigroup `S` of embedding dimension `4`, and a minimal homogeneous
    generating set `G` of its unshifted Goto–Watanabe canonical module `ω_{K[S]} = ω_S(0)`
    refuting Conjecture 00000000592 for every shift constant `constShift ∈ ℤ`. -/
theorem conjecture_592_counterexample_exists :
    HasEmbeddingDim S4679 4 ∧
    ∃ G : List (HomogGen Bool S4679 0),
      IsMinimalHomogGenSet G ∧
      G.length = 3 ∧
      ∀ constShift : Int,
        ¬ (∀ d : Int, d ∈ G.map HomogGen.deg ↔
            ∃ f : Int, IsPseudoFrobenius S4679 f ∧ d = f + constShift) := by
  let G0 := canonicalGenList Bool S4679 0 [2, 3, 5]
    (fun x hx => (S4679_pf_two_three_five.2 x).1 hx)
  have hmin : IsMinimalHomogGenSet G0 :=
    (minimal_gen_characterization Bool S4679 0 S4679_pf_two_three_five).1
  have hmain := conjecture_592_false_numerical Bool 0 G0 hmin
  exact ⟨S4679_edim_four, G0, hmin, hmain.1, hmain.2.2⟩

/-! ## Section 8: Higher-Rank Non-Cohen–Macaulay Counterexample (Macaulay's Quartic Semigroup) -/

/-- Submonoids of `ℤ²` representing rank-2 affine semigroups. -/
structure AffineSemigroup2 where
  mem : Int × Int → Prop
  zero_mem : mem (0, 0)
  add_mem : ∀ {p q : Int × Int}, mem p → mem q → mem (p.1 + q.1, p.2 + q.2)

def IsAffinePF (S : AffineSemigroup2) (p : Int × Int) : Prop :=
  ¬ S.mem p ∧ ∀ q : Int × Int, S.mem q → q ≠ (0, 0) → S.mem (p.1 + q.1, p.2 + q.2)

/-- Macaulay's standard `ℤ`-graded affine semigroup `SMacaulay = ⟨(1,0), (1,1), (1,3), (1,4)⟩ ⊆ ℕ²`
    (isomorphic to `⟨(4,0), (3,1), (1,3), (0,4)⟩`), defining the smooth rational quartic curve in `ℙ³`
    of Krull dimension `2`, embedding dimension `4`, and depth `1` (non-Cohen–Macaulay). -/
def SMacaulay : AffineSemigroup2 where
  mem p :=
    (p.1 = 0 ∧ p.2 = 0) ∨
    (p.1 = 1 ∧ (p.2 = 0 ∨ p.2 = 1 ∨ p.2 = 3 ∨ p.2 = 4)) ∨
    (2 ≤ p.1 ∧ 0 ≤ p.2 ∧ p.2 ≤ 4 * p.1)
  zero_mem := Or.inl ⟨rfl, rfl⟩
  add_mem := by
    intro p q hp hq
    dsimp at hp hq ⊢
    omega

/-- Proof that `SMacaulay` is literally generated by `(1,0), (1,1), (1,3), (1,4)`. -/
theorem SMacaulay_iff_generated (p : Int × Int) :
    SMacaulay.mem p ↔ ∃ a b c d : Nat,
      p.1 = (a : Int) + (b : Int) + (c : Int) + (d : Int) ∧
      p.2 = (b : Int) + 3 * (c : Int) + 4 * (d : Int) := by
  constructor
  · intro hp
    dsimp [SMacaulay] at hp
    rcases hp with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2, h3⟩
    · exact ⟨0, 0, 0, 0, by omega, by omega⟩
    · rcases h2 with hb | hb | hb | hb
      · exact ⟨1, 0, 0, 0, by omega, by omega⟩
      · exact ⟨0, 1, 0, 0, by omega, by omega⟩
      · exact ⟨0, 0, 1, 0, by omega, by omega⟩
      · exact ⟨0, 0, 0, 1, by omega, by omega⟩
    · by_cases hspec : p.2 = 4 * p.1 - 2
      · exact ⟨0, 0, 2, (p.1 - 2).toNat, by omega, by omega⟩
      · let q : Nat := (p.2 / 4).toNat
        let r : Int := p.2 % 4
        have hdiv : p.2 = 4 * (q : Int) + r := by omega
        have hr : r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3 := by omega
        rcases hr with hr0 | hr1 | hr2 | hr3
        · exact ⟨(p.1 - (q : Int)).toNat, 0, 0, q, by omega, by omega⟩
        · exact ⟨(p.1 - (q : Int) - 1).toNat, 1, 0, q, by omega, by omega⟩
        · exact ⟨(p.1 - (q : Int) - 2).toNat, 2, 0, q, by omega, by omega⟩
        · exact ⟨(p.1 - (q : Int) - 1).toNat, 0, 1, q, by omega, by omega⟩
  · rintro ⟨a, b, c, d, h1, h2⟩
    dsimp [SMacaulay]
    by_cases hp0 : p.1 = 0
    · left; omega
    · by_cases hp1 : p.1 = 1
      · right; left
        by_cases ha : a = 0 <;> by_cases hb : b = 0 <;> by_cases hc : c = 0 <;> omega
      · right; right; omega

/-- `SMacaulay` has a unique pseudo-Frobenius element `(1, 2)` (`|PF| = 1 = type(K[SMacaulay])`). -/
theorem SMacaulay_unique_pf (p : Int × Int) :
    IsAffinePF SMacaulay p ↔ p = (1, 2) := by
  constructor
  · rintro ⟨hnp, hall⟩
    have h10 := hall (1, 0) (by dsimp [SMacaulay]; omega) (by decide)
    have h14 := hall (1, 4) (by dsimp [SMacaulay]; omega) (by decide)
    dsimp [SMacaulay] at hnp h10 h14
    cases p with
    | mk d b =>
        dsimp at hnp h10 h14
        have hd : d = 1 ∧ b = 2 := by omega
        rw [hd.1, hd.2]
  · rintro rfl
    refine ⟨by dsimp [SMacaulay]; omega, ?_⟩
    intro q hq hqne
    dsimp [SMacaulay] at hq ⊢
    have hq0 : ¬ (q.1 = 0 ∧ q.2 = 0) := by
      rintro ⟨h1, h2⟩
      apply hqne
      cases q; simp at h1 h2; subst h1 h2; rfl
    omega

/-- Bigraded support of the graded canonical module `ω_{K[SMacaulay]} = Hom_K(H²_m(K[SMacaulay]), K)`
    (interior lattice points of the cone `ℝ≥0 SMacaulay`). -/
def MacaulayOmegaSupp (p : Int × Int) : Prop :=
  1 ≤ p.1 ∧ 1 ≤ p.2 ∧ p.2 ≤ 4 * p.1 - 1

theorem MacaulayOmegaSupp_closed (p q : Int × Int)
    (hp : MacaulayOmegaSupp p) (hq : SMacaulay.mem q) :
    MacaulayOmegaSupp (p.1 + q.1, p.2 + q.2) := by
  dsimp [MacaulayOmegaSupp, SMacaulay] at hp hq ⊢
  omega

/-- Minimal canonical-module generator predicate for `ω_{K[SMacaulay]}`:
    `p ∈ ω` not expressible as `p' + q` with `p' ∈ ω` and `q ∈ SMacaulay \ {(0,0)}`. -/
def IsMacaulayOmegaMinGen (p : Int × Int) : Prop :=
  MacaulayOmegaSupp p ∧
    ¬ ∃ p' q : Int × Int, MacaulayOmegaSupp p' ∧ SMacaulay.mem q ∧ q ≠ (0, 0) ∧
      p = (p'.1 + q.1, p'.2 + q.2)

/-- **Non-Cohen–Macaulay Disproof (`conjecture_592_false_macaulay`):**
    For Macaulay's 2-dimensional standard `ℤ`-graded affine semigroup `SMacaulay`:
    1. `PF(SMacaulay) = {(1, 2)}` has cardinality `1` (matching `type(R) = dim_K Ext¹_R(K, R) = 1`),
    2. Yet `ω_{K[SMacaulay]}` has *three* minimal generators `(1, 1), (1, 2), (1, 3)` (`μ(ω) = 3 ≠ 1`),
       refuting even the generator-count equality `μ(ω) = type` when `K[S]` is not Cohen–Macaulay. -/
theorem conjecture_592_false_macaulay :
    (∀ p : Int × Int, IsAffinePF SMacaulay p ↔ p ∈ [(1, 2)]) ∧
    (∀ p : Int × Int, IsMacaulayOmegaMinGen p ↔ p ∈ [(1, 1), (1, 2), (1, 3)]) ∧
    ([(1, 1), (1, 2), (1, 3)] : List (Int × Int)).length ≠ ([(1, 2)] : List (Int × Int)).length := by
  refine ⟨?_, ?_, by decide⟩
  · intro p
    simp [SMacaulay_unique_pf]
  · intro p
    cases p with
    | mk d b =>
        simp [IsMacaulayOmegaMinGen, MacaulayOmegaSupp]
        constructor
        · rintro ⟨⟨hd1, hb1, hb4⟩, hndecomp⟩
          by_cases hd_eq1 : d = 1
          · omega
          · exfalso
            -- For `d ≥ 2` and `1 ≤ b ≤ 4d - 1`:
            -- if `b ≤ 4(d - 1) - 1 = 4d - 5`, subtract `(1, 0)`;
            -- otherwise `b ≥ 4d - 4 ≥ 4`, so subtract `(1, 4)` (leaving `b - 4` in `[1, 4d - 5]` unless `b = 4` and `d = 2`, where `b = 4`: `(1, 3) + (1, 1) = (2, 4)`!).
            by_cases hlow : b ≤ 4 * d - 5
            · exact hndecomp (d - 1) b (by omega) (by omega) (by omega)
                1 0 (by dsimp [SMacaulay]; omega) (by intro h1 h2; omega) (by omega) (by omega)
            · by_cases hb5 : 5 ≤ b
              · exact hndecomp (d - 1) (b - 4) (by omega) (by omega) (by omega)
                  1 4 (by dsimp [SMacaulay]; omega) (by intro h1 h2; omega) (by omega) (by omega)
              · -- Remaining case: `d = 2` and `b = 4`, decomposed as `(1, 3) + (1, 1)`.
                exact hndecomp 1 3 (by omega) (by omega) (by omega)
                  1 1 (by dsimp [SMacaulay]; omega) (by intro h1 h2; omega) (by omega) (by omega)
        · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
          · refine ⟨⟨by omega, by omega, by omega⟩, ?_⟩
            intro d' b' hd' hb' hb4' q1 q2 hq hqne heq1 heq2
            dsimp [SMacaulay] at hq
            have hq0 : ¬ (q1 = 0 ∧ q2 = 0) := by intro h; exact hqne h.1 h.2
            omega
          · refine ⟨⟨by omega, by omega, by omega⟩, ?_⟩
            intro d' b' hd' hb' hb4' q1 q2 hq hqne heq1 heq2
            dsimp [SMacaulay] at hq
            have hq0 : ¬ (q1 = 0 ∧ q2 = 0) := by intro h; exact hqne h.1 h.2
            omega
          · refine ⟨⟨by omega, by omega, by omega⟩, ?_⟩
            intro d' b' hd' hb' hb4' q1 q2 hq hqne heq1 heq2
            dsimp [SMacaulay] at hq
            have hq0 : ¬ (q1 = 0 ∧ q2 = 0) := by intro h; exact hqne h.1 h.2
            omega

end Conjecture00000000592

/-! ## Section 9: Axiom Verification (`#print axioms`) -/

#print axioms Conjecture00000000592.socle_nontrivial_iff_pf
#print axioms Conjecture00000000592.matlisPair_smul_compat
#print axioms Conjecture00000000592.minimal_gen_characterization
#print axioms Conjecture00000000592.alignment_of_type_le_two
#print axioms Conjecture00000000592.S4679_iff_generated_by_4_6_7_9
#print axioms Conjecture00000000592.S4679_edim_four
#print axioms Conjecture00000000592.S4679_pf_two_three_five
#print axioms Conjecture00000000592.conjecture_592_false_numerical
#print axioms Conjecture00000000592.conjecture_592_counterexample_exists
#print axioms Conjecture00000000592.SMacaulay_iff_generated
#print axioms Conjecture00000000592.conjecture_592_false_macaulay
