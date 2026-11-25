/-
  Conjecture 00000004766 — Two-Dimensional Noncrossing and Narayana Polynomials
  Grid2D.lean: Reading I — Cartesian Grid Bi-Lexicographic Joint Noncrossing NC(<_row) ∩ NC(<_col).
  Proves:
  1. Exact low-dimensional block polynomials: boundary grids (1, n) are palindromic Narayana,
     whereas (2, 2) gives t + 5 t^2 + 6 t^3 + t^4 (non-palindromic, total 13 ≠ 14),
     and slice-wise grid NC on (2, 2) gives t + 7 t^2 + 6 t^3 + t^4 (non-palindromic, total 15).
  2. Universal classification and exact cardinality theorem for ALL m ≥ 2, n ≥ 2:
     the number `c2Grid m n` of 2-block bi-lexicographic noncrossing partitions of [m] × [n]
     equals `m * n + 1` for all m ≥ 2, n ≥ 2, whereas `c2Grid 2 1 = 1`.
  3. Universal algebraic non-polynomiality theorem: NO bivariate polynomial over ℚ
     equals `c2Grid m n` for all m ≥ 1, n ≥ 1.
-/
import TwoDimNarayana.Basic
import TwoDimNarayana.Partitions

namespace TwoDimNarayana

abbrev Pt := Nat × Nat

/-- Grid membership on {0, ..., m-1} × {0, ..., n-1}. -/
def inGrid (m n : Nat) (p : Pt) : Prop :=
  p.1 < m ∧ p.2 < n

/-- Row-major lexicographic order <_row on grid points. -/
def ltRow (p q : Pt) : Prop :=
  p.1 < q.1 ∨ (p.1 = q.1 ∧ p.2 < q.2)

/-- Column-major colexicographic order <_col on grid points. -/
def ltCol (p q : Pt) : Prop :=
  p.2 < q.2 ∨ (p.2 = q.2 ∧ p.1 < q.1)

instance decLtRow (p q : Pt) : Decidable (ltRow p q) := by
  unfold ltRow; infer_instance

instance decLtCol (p q : Pt) : Decidable (ltCol p q) := by
  unfold ltCol; infer_instance

/-! ### Part A: Concrete RGS Grid Enumerations (`[m] × [n]`) -/

def gridRowOrder (m n : Nat) : List Nat :=
  List.range (m * n)

def gridColOrder (m n : Nat) : List Nat :=
  (List.range n).flatMap (fun j => (List.range m).map (fun i => i * n + j))

/-- Bi-lexicographic noncrossing partitions NC(<_row) ∩ NC(<_col) on [m] × [n]. -/
def gridBiNCPartitions (m n : Nat) : List (List Nat) :=
  let rOrd := gridRowOrder m n
  let cOrd := gridColOrder m n
  (allRGS (m * n)).filter (fun p => isNCOrder p rOrd && isNCOrder p cOrd)

/-- Univariate block-count polynomial of NC_2(m, n). -/
def gridBiNCPoly (m n : Nat) : Poly1 :=
  blockPoly1 (m * n) (gridBiNCPartitions m n)

/-- Slice-wise row & column noncrossing on [m] × [n]:
    every horizontal row is in NC(n) and every vertical column is in NC(m). -/
def isGridSliceNC (m n : Nat) (part : List Nat) : Bool :=
  let rowsOK := (List.range m).all (fun i =>
    !hasCrossingInSeq ((List.range n).map (fun j => part.getD (i * n + j) 0)))
  let colsOK := (List.range n).all (fun j =>
    !hasCrossingInSeq ((List.range m).map (fun i => part.getD (i * n + j) 0)))
  rowsOK && colsOK

def gridSliceNCPoly (m n : Nat) : Poly1 :=
  blockPoly1 (m * n) ((allRGS (m * n)).filter (isGridSliceNC m n))

/-- Degenerate 1 × 4 grid coincides with 1D Narayana polynomial t + 6 t^2 + 6 t^3 + t^4. -/
theorem gridBiNCPoly_1_4 :
    gridBiNCPoly 1 4 = [0, 1, 6, 6, 1] ∧ isPalindromic1 4 (gridBiNCPoly 1 4) = true := by
  decide

/-- Minimal genuine 2D grid 2 × 2 has 13 bi-noncrossing partitions with block polynomial
    t + 5 t^2 + 6 t^3 + t^4, violating Narayana palindromicity (5 ≠ 6). -/
theorem gridBiNCPoly_2_2_disproof :
    (gridBiNCPartitions 2 2).length = 13 ∧
    gridBiNCPoly 2 2 = [0, 1, 5, 6, 1] ∧
    isPalindromic1 4 (gridBiNCPoly 2 2) = false := by
  decide

/-- Slice-wise noncrossing on 2 × 2 imposes no restriction (all 15 Bell partitions),
    giving Stirling polynomial t + 7 t^2 + 6 t^3 + t^4, also non-palindromic (7 ≠ 6). -/
theorem gridSliceNCPoly_2_2_disproof :
    gridSliceNCPoly 2 2 = [0, 1, 7, 6, 1] ∧
    isPalindromic1 4 (gridSliceNCPoly 2 2) = false := by
  decide

/-! ### Part B: Universal Classification of 2-Block Bi-Noncrossing Grid Partitions -/

/-- Crossing predicate for a 2-coloring `f : Pt → Bool` on `[m] × [n]` wrt order `lt`. -/
def HasCrossing2 (lt : Pt → Pt → Prop) (m n : Nat) (f : Pt → Bool) : Prop :=
  ∃ a b c d : Pt,
    inGrid m n a ∧ inGrid m n b ∧ inGrid m n c ∧ inGrid m n d ∧
    lt a b ∧ lt b c ∧ lt c d ∧
    f a = f c ∧ f b = f d ∧ f a ≠ f b

/-- Order-convexity of a subset `T` on `[m] × [n]` wrt `lt`. -/
def IsConvexOnGrid (lt : Pt → Pt → Prop) (m n : Nat) (T : List Pt) : Prop :=
  ∀ a b c : Pt,
    inGrid m n a → inGrid m n b → inGrid m n c →
    lt a b → lt b c → a ∈ T → c ∈ T → b ∈ T

/-- Exact equivalence: for any subset `T` of the punctured grid (`(0,0) ∉ T`) on `m, n ≥ 1`,
    the 2-coloring `p ↦ decide (p ∈ T)` is `lt`-noncrossing iff `T` is `lt`-convex. -/
theorem noCrossing2_iff_convex (lt : Pt → Pt → Prop) (m n : Nat)
    (hm : 1 ≤ m) (hn : 1 ≤ n)
    (hmin : ∀ p : Pt, inGrid m n p → p ≠ (0, 0) → lt (0, 0) p)
    (T : List Pt) (h0 : (0, 0) ∉ T) :
    (¬ HasCrossing2 lt m n (fun p => decide (p ∈ T))) ↔ IsConvexOnGrid lt m n T := by
  constructor
  · intro hnc a b c ha hb hc hab hbc haT hcT
    by_cases hbT : b ∈ T
    · exact hbT
    · exfalso
      apply hnc
      have ha0 : a ≠ (0, 0) := fun h => h0 (h ▸ haT)
      refine ⟨(0, 0), a, b, c, ⟨hm, hn⟩, ha, hb, hc, hmin a ha ha0, hab, hbc, ?_, ?_, ?_⟩
      · simp [h0, hbT]
      · simp [haT, hcT]
      · simp [h0, haT]
  · intro hconv ⟨a, b, c, d, ha, hb, hc, hd, hab, hbc, hcd, hfac, hfbd, hfab⟩
    by_cases haT : a ∈ T
    · have hcT : c ∈ T := by
        have : decide (a ∈ T) = decide (c ∈ T) := hfac
        simpa [haT] using this.symm
      have hbT : b ∉ T := by
        intro hb_in
        apply hfab
        simp [haT, hb_in]
      exact hbT (hconv a b c ha hb hc hab hbc haT hcT)
    · have hbT : b ∈ T := by
        by_cases hb_in : b ∈ T
        · exact hb_in
        · exfalso; apply hfab; simp [haT, hb_in]
      have hdT : d ∈ T := by
        have : decide (b ∈ T) = decide (d ∈ T) := hfbd
        simpa [hbT] using this.symm
      have hcT : c ∉ T := by
        intro hc_in
        have : decide (a ∈ T) = decide (c ∈ T) := hfac
        simp [haT, hc_in] at this
      exact hcT (hconv b c d hb hc hd hbc hcd hbT hdT)

/-- Core structural lemma: if `m ≥ 2, n ≥ 2` and `T ⊆ G_{m,n} \ {(0,0)}` contains at least two
    distinct points `p ≠ q` and is convex in both `ltRow` and `ltCol`, then `(0, 1) ∈ T`. -/
theorem mem_zero_one_of_biConvex {m n : Nat} (hm : 2 ≤ m) (hn : 2 ≤ n)
    {T : List Pt} (hsub : ∀ x ∈ T, inGrid m n x ∧ x ≠ (0, 0))
    (hrow : IsConvexOnGrid ltRow m n T) (hcol : IsConvexOnGrid ltCol m n T)
    {p q : Pt} (hp : p ∈ T) (hq : q ∈ T) (hpq : p ≠ q) : (0, 1) ∈ T := by
  by_cases h01_dec : (0, 1) ∈ T
  · exact h01_dec
  · exfalso
    have h01 : (0, 1) ∉ T := h01_dec
    -- Step 1: T cannot have both a point in col 0 and a point in col ≥ 1
    have no_mix_col0 : ∀ u ∈ T, ∀ v ∈ T, u.2 = 0 → v.2 = 0 := by
      intro u hu v hv hu0
      by_cases hv0_dec : v.2 = 0
      · exact hv0_dec
      · exfalso
        have hv0 : v.2 ≠ 0 := hv0_dec
        have ⟨⟨hum, _⟩, hu_ne0⟩ := hsub u hu
        have ⟨⟨hvm, hvn⟩, _⟩ := hsub v hv
        have hu1_pos : 0 < u.1 := by
          cases u with
          | mk u1 u2 =>
            simp at hu0
            subst hu0
            by_cases hu1_0 : u1 = 0
            · subst hu1_0; exact False.elim (hu_ne0 rfl)
            · omega
        have hv_ne_01 : v ≠ (0, 1) := fun h => h01 (h ▸ hv)
        have hlt1 : ltCol u (0, 1) := Or.inl (by omega)
        have hlt2 : ltCol (0, 1) v := by
          cases v with
          | mk v1 v2 =>
            simp only at hv0 hvm hvn
            by_cases hv2_eq1 : v2 = 1
            · subst hv2_eq1
              have hv1_pos : 0 < v1 := by
                by_cases hv1_0 : v1 = 0
                · subst hv1_0; exact False.elim (hv_ne_01 rfl)
                · omega
              exact Or.inr ⟨rfl, hv1_pos⟩
            · exact Or.inl (by omega)
        exact h01 (hcol u (0, 1) v ⟨hum, by omega⟩ ⟨by omega, by omega⟩ ⟨hvm, hvn⟩ hlt1 hlt2 hu hv)
    -- Case split on whether p.2 = 0
    by_cases hp2 : p.2 = 0
    · have hq2 : q.2 = 0 := no_mix_col0 p hp q hq hp2
      have ⟨⟨hpm, _⟩, _⟩ := hsub p hp
      have ⟨⟨hqm, _⟩, _⟩ := hsub q hq
      have hp1_ne_q1 : p.1 ≠ q.1 := by
        intro h1
        apply hpq
        cases p; cases q; simp_all
      by_cases hlt : p.1 < q.1
      · have hin : (p.1, 1) ∈ T :=
          hrow p (p.1, 1) q ⟨hpm, by omega⟩ ⟨hpm, by omega⟩ ⟨hqm, by omega⟩
            (Or.inr ⟨rfl, by omega⟩) (Or.inl hlt) hp hq
        have hbad := no_mix_col0 p hp (p.1, 1) hin hp2
        simp at hbad
      · have hlt' : q.1 < p.1 := by omega
        have hin : (q.1, 1) ∈ T :=
          hrow q (q.1, 1) p ⟨hqm, by omega⟩ ⟨hqm, by omega⟩ ⟨hpm, by omega⟩
            (Or.inr ⟨rfl, by omega⟩) (Or.inl hlt') hq hp
        have hbad := no_mix_col0 q hq (q.1, 1) hin hq2
        simp at hbad
    · -- No point of T has col 0!
      have all_col_pos : ∀ u ∈ T, 1 ≤ u.2 := by
        intro u hu
        by_cases hu_z : u.2 = 0
        · exact False.elim (hp2 (no_mix_col0 u hu p hp hu_z))
        · omega
      have h10_not : (1, 0) ∉ T := by
        intro h10
        have := all_col_pos (1, 0) h10
        omega
      -- Step 2: T cannot mix row 0 and row ≥ 1
      have no_mix_row0 : ∀ u ∈ T, ∀ v ∈ T, u.1 = 0 → v.1 = 0 := by
        intro u hu v hv hu0
        by_cases hv0_dec : v.1 = 0
        · exact hv0_dec
        · exfalso
          have hv0 : v.1 ≠ 0 := hv0_dec
          have ⟨⟨hum, hun⟩, _⟩ := hsub u hu
          have ⟨⟨hvm, hvn⟩, _⟩ := hsub v hv
          have hv2_pos : 1 ≤ v.2 := all_col_pos v hv
          have hlt1 : ltRow u (1, 0) := Or.inl (by omega)
          have hlt2 : ltRow (1, 0) v := by
            by_cases hv1_eq1 : v.1 = 1
            · exact Or.inr ⟨hv1_eq1.symm, by omega⟩
            · exact Or.inl (by omega)
          exact h10_not (hrow u (1, 0) v ⟨hum, hun⟩ ⟨by omega, by omega⟩ ⟨hvm, hvn⟩ hlt1 hlt2 hu hv)
      by_cases hp1 : p.1 = 0
      · have hq1 : q.1 = 0 := no_mix_row0 p hp q hq hp1
        have ⟨⟨_, hpn⟩, _⟩ := hsub p hp
        have ⟨⟨_, hqn⟩, _⟩ := hsub q hq
        have hp2_ne_q2 : p.2 ≠ q.2 := by
          intro h2; apply hpq; cases p; cases q; simp_all
        by_cases hlt : p.2 < q.2
        · have hin : (1, p.2) ∈ T :=
            hcol p (1, p.2) q ⟨by omega, hpn⟩ ⟨by omega, hpn⟩ ⟨by omega, hqn⟩
              (Or.inr ⟨rfl, by omega⟩) (Or.inl hlt) hp hq
          have hbad := no_mix_row0 p hp (1, p.2) hin hp1
          simp at hbad
        · have hlt' : q.2 < p.2 := by omega
          have hin : (1, q.2) ∈ T :=
            hcol q (1, q.2) p ⟨by omega, hqn⟩ ⟨by omega, hqn⟩ ⟨by omega, hpn⟩
              (Or.inr ⟨rfl, by omega⟩) (Or.inl hlt') hq hp
          have hbad := no_mix_row0 q hq (1, q.2) hin hq1
          simp at hbad
      · -- Every point of T has row ≥ 1 AND col ≥ 1
        have all_row_pos : ∀ u ∈ T, 1 ≤ u.1 := by
          intro u hu
          by_cases hu_z : u.1 = 0
          · exact False.elim (hp1 (no_mix_row0 u hu p hp hu_z))
          · omega
        have ⟨⟨hpm, hpn⟩, _⟩ := hsub p hp
        have ⟨⟨hqm, hqn⟩, _⟩ := hsub q hq
        have hp1_pos := all_row_pos p hp
        have hq1_pos := all_row_pos q hq
        have hp2_pos := all_col_pos p hp
        have hq2_pos := all_col_pos q hq
        by_cases h1 : p.1 = q.1
        · have h2 : p.2 ≠ q.2 := by
            intro h2; apply hpq; cases p; cases q; simp_all
          by_cases hlt : p.2 < q.2
          · have hin : (0, q.2) ∈ T :=
              hcol p (0, q.2) q ⟨hpm, hpn⟩ ⟨by omega, hqn⟩ ⟨hqm, hqn⟩
                (Or.inl hlt) (Or.inr ⟨rfl, by omega⟩) hp hq
            have hbad := all_row_pos (0, q.2) hin
            omega
          · have hlt' : q.2 < p.2 := by omega
            have hin : (0, p.2) ∈ T :=
              hcol q (0, p.2) p ⟨hqm, hqn⟩ ⟨by omega, hpn⟩ ⟨hpm, hpn⟩
                (Or.inl hlt') (Or.inr ⟨rfl, by omega⟩) hq hp
            have hbad := all_row_pos (0, p.2) hin
            omega
        · by_cases hlt : p.1 < q.1
          · have hin : (q.1, 0) ∈ T :=
              hrow p (q.1, 0) q ⟨hpm, hpn⟩ ⟨hqm, by omega⟩ ⟨hqm, hqn⟩
                (Or.inl hlt) (Or.inr ⟨rfl, by omega⟩) hp hq
            have hbad := all_col_pos (q.1, 0) hin
            omega
          · have hlt' : q.1 < p.1 := by omega
            have hin : (p.1, 0) ∈ T :=
              hrow q (p.1, 0) p ⟨hqm, hqn⟩ ⟨hpm, by omega⟩ ⟨hpm, hpn⟩
                (Or.inl hlt') (Or.inr ⟨rfl, by omega⟩) hq hp
            have hbad := all_col_pos (p.1, 0) hin
            omega

/-- Transpose symmetry immediately gives `(1, 0) ∈ T` as well, and hence every grid point
    except `(0, 0)` and `(m - 1, n - 1)` belongs to `T`! -/
theorem doublyPunctured_subset_of_biConvex {m n : Nat} (hm : 2 ≤ m) (hn : 2 ≤ n)
    {T : List Pt} (hsub : ∀ x ∈ T, inGrid m n x ∧ x ≠ (0, 0))
    (hrow : IsConvexOnGrid ltRow m n T) (hcol : IsConvexOnGrid ltCol m n T)
    {p q : Pt} (hp : p ∈ T) (hq : q ∈ T) (hpq : p ≠ q) :
    ∀ r : Pt, inGrid m n r → r ≠ (0, 0) → r ≠ (m - 1, n - 1) → r ∈ T := by
  have h01 : (0, 1) ∈ T := mem_zero_one_of_biConvex hm hn hsub hrow hcol hp hq hpq
  let swapPt : Pt → Pt := fun u => (u.2, u.1)
  let T' : List Pt := T.map swapPt
  have hsub' : ∀ x ∈ T', inGrid n m x ∧ x ≠ (0, 0) := by
    intro x hx
    rw [List.mem_map] at hx
    rcases hx with ⟨u, hu, rfl⟩
    have ⟨⟨hum, hun⟩, hune⟩ := hsub u hu
    refine ⟨⟨hun, hum⟩, ?_⟩
    intro h0; apply hune; cases u; simp_all [swapPt]
  have hrow' : IsConvexOnGrid ltRow n m T' := by
    intro a b c ha hb hc hab hbc haT' hcT'
    rw [List.mem_map] at haT' hcT' ⊢
    rcases haT' with ⟨ua, hua, rfl⟩
    rcases hcT' with ⟨uc, huc, rfl⟩
    refine ⟨(b.2, b.1), ?_, by cases b; rfl⟩
    apply hcol ua (b.2, b.1) uc ⟨ha.2, ha.1⟩ ⟨hb.2, hb.1⟩ ⟨hc.2, hc.1⟩ hab hbc hua huc
  have hcol' : IsConvexOnGrid ltCol n m T' := by
    intro a b c ha hb hc hab hbc haT' hcT'
    rw [List.mem_map] at haT' hcT' ⊢
    rcases haT' with ⟨ua, hua, rfl⟩
    rcases hcT' with ⟨uc, huc, rfl⟩
    refine ⟨(b.2, b.1), ?_, by cases b; rfl⟩
    apply hrow ua (b.2, b.1) uc ⟨ha.2, ha.1⟩ ⟨hb.2, hb.1⟩ ⟨hc.2, hc.1⟩ hab hbc hua huc
  have hp' : swapPt p ∈ T' := List.mem_map_of_mem hp
  have hq' : swapPt q ∈ T' := List.mem_map_of_mem hq
  have hpq' : swapPt p ≠ swapPt q := by
    intro h; apply hpq; cases p; cases q; simp_all [swapPt]
  have h01' : (0, 1) ∈ T' := mem_zero_one_of_biConvex hn hm hsub' hrow' hcol' hp' hq' hpq'
  have h10 : (1, 0) ∈ T := by
    rw [List.mem_map] at h01'
    rcases h01' with ⟨u, hu, heq⟩
    cases u with
    | mk u1 u2 =>
      simp [swapPt] at heq
      rcases heq with ⟨rfl, rfl⟩
      exact hu
  have h0_last : (0, n - 1) ∈ T := by
    by_cases hn2 : n = 2
    · subst hn2; exact h01
    · exact hrow (0, 1) (0, n - 1) (1, 0)
        ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ ⟨by omega, by omega⟩
        (Or.inr ⟨rfl, by omega⟩) (Or.inl (by omega)) h01 h10
  have hm_first : (m - 1, 0) ∈ T := by
    by_cases hm2 : m = 2
    · subst hm2; exact h10
    · exact hcol (1, 0) (m - 1, 0) (0, 1)
        ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ ⟨by omega, by omega⟩
        (Or.inr ⟨rfl, by omega⟩) (Or.inl (by omega)) h10 h01
  intro r ⟨hrm, hrn⟩ hr0 hrmax
  cases r with
  | mk i j =>
    by_cases hi : i < m - 1
    · by_cases hij01 : (i, j) = (0, 1)
      · rw [hij01]; exact h01
      · have hlt1 : ltRow (0, 1) (i, j) := by
          by_cases hi0 : i = 0
          · subst hi0
            have hj2 : 1 < j := by
              by_cases hj0 : j = 0
              · subst hj0; exact False.elim (hr0 rfl)
              · by_cases hj1 : j = 1
                · subst hj1; exact False.elim (hij01 rfl)
                · omega
            exact Or.inr ⟨rfl, hj2⟩
          · exact Or.inl (by omega)
        have hlt2 : ltRow (i, j) (m - 1, 0) := Or.inl hi
        exact hrow (0, 1) (i, j) (m - 1, 0)
          ⟨by omega, by omega⟩ ⟨hrm, hrn⟩ ⟨by omega, by omega⟩ hlt1 hlt2 h01 hm_first
    · have hi_eq : i = m - 1 := by omega
      subst hi_eq
      have hj_lt : j < n - 1 := by
        by_cases hj_eq : j = n - 1
        · subst hj_eq; exact False.elim (hrmax rfl)
        · omega
      by_cases hij10 : (m - 1, j) = (1, 0)
      · rw [hij10]; exact h10
      · have hlt1 : ltCol (1, 0) (m - 1, j) := by
          by_cases hj0 : j = 0
          · subst hj0
            have hm3 : 1 < m - 1 := by
              by_cases hm2 : m - 1 = 1
              · rw [hm2] at hij10; exact False.elim (hij10 rfl)
              · omega
            exact Or.inr ⟨rfl, hm3⟩
          · exact Or.inl (by omega)
        have hlt2 : ltCol (m - 1, j) (0, n - 1) := Or.inl hj_lt
        exact hcol (1, 0) (m - 1, j) (0, n - 1)
          ⟨by omega, by omega⟩ ⟨hrm, hrn⟩ ⟨by omega, by omega⟩ hlt1 hlt2 h10 h0_last

/-! ### Part C: Exact Computable Cardinality `c2Grid m n = m * n + 1` for All `m ≥ 2, n ≥ 2` -/

def gridPts (m n : Nat) : List Pt :=
  (List.range m).flatMap (fun i => (List.range n).map (fun j => (i, j)))

def puncturedGrid (m n : Nat) : List Pt :=
  (gridPts m n).filter (fun p => p != (0, 0))

def doublyPuncturedGrid (m n : Nat) : List Pt :=
  (puncturedGrid m n).filter (fun p => p != (m - 1, n - 1))

def allSublists {α : Type} : List α → List (List α)
  | [] => [[]]
  | x :: xs => allSublists xs ++ (allSublists xs).map (fun s => x :: s)

def checkConvex (lt : Pt → Pt → Bool) (pts : List Pt) (T : List Pt) : Bool :=
  pts.all (fun a =>
    pts.all (fun b =>
      pts.all (fun c =>
        !(lt a b && lt b c && decide (a ∈ T) && decide (c ∈ T)) || decide (b ∈ T))))

def biNC2BlockList (m n : Nat) : List (List Pt) :=
  let pts := gridPts m n
  (allSublists (puncturedGrid m n)).filter (fun T =>
    !T.isEmpty &&
    checkConvex (fun a b => decide (ltRow a b)) pts T &&
    checkConvex (fun a b => decide (ltCol a b)) pts T)

/-- Exact combinatorial count `c_2(m, n)` of 2-block bi-lexicographic noncrossing partitions. -/
def c2Grid (m n : Nat) : Nat :=
  (biNC2BlockList m n).length

/-- Sanity checks on boundary and minimal 2D grids (`c2Grid 2 1 = 1`, `c2Grid 2 2 = 5`). -/
theorem c2Grid_small_values :
    c2Grid 2 1 = 1 ∧
    c2Grid 1 4 = 6 ∧
    c2Grid 2 2 = 5 ∧
    (c2Grid 2 2 : Int) = coeff1 (gridBiNCPoly 2 2) 2 := by
  decide

/-! #### Clean Free-Variable List Lemmas -/

private theorem nodup_map_of_inj {α β : Type} {f : α → β}
    (hinj : ∀ x y, f x = f y → x = y) {l : List α} (hl : l.Nodup) : (l.map f).Nodup := by
  induction l with
  | nil => exact List.Pairwise.nil
  | cons a as ih =>
    cases hl with
    | cons ha has =>
      simp only [List.map]
      apply List.Pairwise.cons
      · intro y hy heq
        rw [List.mem_map] at hy
        rcases hy with ⟨b, hb, rfl⟩
        exact ha b hb (hinj a b heq)
      · exact ih has

private theorem mem_gridPts_iff (m n : Nat) (p : Pt) :
    p ∈ gridPts m n ↔ inGrid m n p := by
  unfold gridPts inGrid
  cases p with
  | mk i j =>
    simp [List.mem_flatMap, List.mem_range, List.mem_map]

private theorem nodup_gridPts_aux (n : Nat) {rows : List Nat} (hr : rows.Nodup) :
    (rows.flatMap (fun i => (List.range n).map (fun j => (i, j)))).Nodup := by
  induction rows with
  | nil => exact List.Pairwise.nil
  | cons i is ih =>
    cases hr with
    | cons hi his =>
      simp only [List.flatMap_cons]
      have hmap : ((List.range n).map (fun j => (i, j))).Nodup :=
        nodup_map_of_inj (fun _ _ h => by injection h) List.nodup_range
      apply nodup_append_disjoint hmap (ih his)
      intro x hxi hxis
      rw [List.mem_map] at hxi
      rw [List.mem_flatMap] at hxis
      rcases hxi with ⟨j, _, rfl⟩
      rcases hxis with ⟨i', hi', hxi'⟩
      rw [List.mem_map] at hxi'
      rcases hxi' with ⟨j', _, heq'⟩
      injection heq' with hii _
      exact hi i' hi' hii.symm

private theorem nodup_gridPts (m n : Nat) : (gridPts m n).Nodup :=
  nodup_gridPts_aux n List.nodup_range

private theorem nodup_filter_list {α : Type} (p : α → Bool) {l : List α} (hl : l.Nodup) :
    (l.filter p).Nodup := by
  induction l with
  | nil => exact List.Pairwise.nil
  | cons a as ih =>
    cases hl with
    | cons ha has =>
      simp only [List.filter]
      split
      · apply List.Pairwise.cons
        · intro y hy hya
          rw [List.mem_filter] at hy
          exact ha y hy.1 hya
        · exact ih has
      · exact ih has

private theorem mem_puncturedGrid_iff (m n : Nat) (p : Pt) :
    p ∈ puncturedGrid m n ↔ inGrid m n p ∧ p ≠ (0, 0) := by
  simp [puncturedGrid, List.mem_filter, mem_gridPts_iff]

private theorem nodup_puncturedGrid (m n : Nat) : (puncturedGrid m n).Nodup :=
  nodup_filter_list _ (nodup_gridPts m n)

private theorem self_mem_allSublists {α : Type} (l : List α) : l ∈ allSublists l := by
  induction l with
  | nil => simp [allSublists]
  | cons a as ih =>
    simp only [allSublists, List.mem_append, List.mem_map]
    exact Or.inr ⟨as, ih, rfl⟩

private theorem sub_of_mem_allSublists {α : Type} {l s : List α}
    (hs : s ∈ allSublists l) : ∀ x ∈ s, x ∈ l := by
  induction l generalizing s with
  | nil =>
    simp [allSublists] at hs
    subst hs; intro _ hx; nomatch hx
  | cons a as ih =>
    simp only [allSublists, List.mem_append, List.mem_map] at hs
    rcases hs with hs1 | ⟨t, ht, rfl⟩
    · intro y hy; exact List.mem_cons_of_mem a (ih hs1 y hy)
    · intro y hy
      cases List.mem_cons.mp hy with
      | inl hya => subst hya; exact List.mem_cons_self
      | inr hyin => exact List.mem_cons_of_mem a (ih ht y hyin)

private theorem nodup_of_mem_allSublists {α : Type} {l s : List α}
    (hl : l.Nodup) (hs : s ∈ allSublists l) : s.Nodup := by
  induction l generalizing s with
  | nil =>
    simp [allSublists] at hs; subst hs; exact List.Pairwise.nil
  | cons a as ih =>
    cases hl with
    | cons ha has =>
      simp only [allSublists, List.mem_append, List.mem_map] at hs
      rcases hs with hs1 | ⟨t, ht, rfl⟩
      · exact ih has hs1
      · apply List.Pairwise.cons
        · intro y hy hya
          exact ha y (sub_of_mem_allSublists ht y hy) hya
        · exact ih has ht

private theorem eq_of_mem_allSublists_ext {α : Type} {l s1 s2 : List α}
    (hl : l.Nodup) (h1 : s1 ∈ allSublists l) (h2 : s2 ∈ allSublists l)
    (hext : ∀ x, x ∈ s1 ↔ x ∈ s2) : s1 = s2 := by
  induction l generalizing s1 s2 with
  | nil =>
    simp [allSublists] at h1 h2
    rw [h1, h2]
  | cons a as ih =>
    cases hl with
    | cons ha has =>
      simp only [allSublists, List.mem_append, List.mem_map] at h1 h2
      rcases h1 with h1L | ⟨t1, ht1, rfl⟩ <;> rcases h2 with h2L | ⟨t2, ht2, rfl⟩
      · exact ih has h1L h2L hext
      · exfalso
        have ha_in : a ∈ a :: t2 := List.mem_cons_self
        have ha_s1 : a ∈ s1 := (hext a).mpr ha_in
        exact ha a (sub_of_mem_allSublists h1L a ha_s1) rfl
      · exfalso
        have ha_in : a ∈ a :: t1 := List.mem_cons_self
        have ha_s2 : a ∈ s2 := (hext a).mp ha_in
        exact ha a (sub_of_mem_allSublists h2L a ha_s2) rfl
      · congr 1
        apply ih has ht1 ht2
        intro y
        constructor
        · intro hy1
          have hy_cons : y ∈ a :: t2 := (hext y).mp (List.mem_cons_of_mem a hy1)
          cases List.mem_cons.mp hy_cons with
          | inl hya =>
            exact False.elim (ha y (sub_of_mem_allSublists ht1 y hy1) hya.symm)
          | inr hy2 => exact hy2
        · intro hy2
          have hy_cons : y ∈ a :: t1 := (hext y).mpr (List.mem_cons_of_mem a hy2)
          cases List.mem_cons.mp hy_cons with
          | inl hya =>
            exact False.elim (ha y (sub_of_mem_allSublists ht2 y hy2) hya.symm)
          | inr hy1 => exact hy1

private theorem filter_mem_allSublists {α : Type} (l : List α) (P : α → Bool) :
    l.filter P ∈ allSublists l := by
  induction l with
  | nil => simp [allSublists]
  | cons a as ih =>
    simp only [List.filter, allSublists, List.mem_append, List.mem_map]
    split
    · exact Or.inr ⟨as.filter P, ih, rfl⟩
    · exact Or.inl ih

private theorem singleton_mem_allSublists {α : Type} [DecidableEq α] {l : List α} {p : α}
    (hl : l.Nodup) (hp : p ∈ l) : [p] ∈ allSublists l := by
  have hfilt : l.filter (fun x => decide (x = p)) = [p] := by
    induction l with
    | nil => nomatch hp
    | cons a as ih =>
      cases hl with
      | cons ha has =>
        cases List.mem_cons.mp hp with
        | inl hap =>
          subst hap
          simp only [List.filter, decide_true]
          congr 1
          have hnone : ∀ y ∈ as, decide (y = p) = false := by
            intro y hy
            simp only [decide_eq_false_iff_not]
            intro hya; exact ha y hy hya.symm
          clear ih hp ha has
          induction as with
          | nil => rfl
          | cons b bs ihb =>
            have hb : decide (b = p) = false := hnone b List.mem_cons_self
            simp [List.filter, hb, ihb (fun y hy => hnone y (List.mem_cons_of_mem b hy))]
        | inr hpin =>
          have hne : decide (a = p) = false := by
            simp only [decide_eq_false_iff_not]
            intro hap; exact ha p hpin hap
          simp [List.filter, hne, ih has hpin]
  rw [← hfilt]
  exact filter_mem_allSublists l (fun x => decide (x = p))

private theorem nodup_allSublists {α : Type} {l : List α} (hl : l.Nodup) :
    (allSublists l).Nodup := by
  induction l with
  | nil => simp [allSublists]
  | cons a as ih =>
    cases hl with
    | cons ha has =>
      simp only [allSublists]
      have hmap : ((allSublists as).map (fun xs => a :: xs)).Nodup :=
        nodup_map_of_inj (fun _ _ h => by injection h) (ih has)
      apply nodup_append_disjoint (ih has) hmap
      intro x hxL hxR
      rw [List.mem_map] at hxR
      rcases hxR with ⟨t, _, rfl⟩
      exact ha a (sub_of_mem_allSublists hxL a List.mem_cons_self) rfl

private def removeOne {α : Type} [DecidableEq α] (a : α) : List α → List α
  | [] => []
  | x :: xs => if x = a then xs else x :: removeOne a xs

private theorem length_removeOne_of_mem {α : Type} [DecidableEq α] {a : α} {l : List α}
    (h : a ∈ l) : (removeOne a l).length + 1 = l.length := by
  induction l with
  | nil => nomatch h
  | cons x xs ih =>
    simp only [removeOne]
    by_cases hxa : x = a
    · simp [hxa]
    · cases List.mem_cons.mp h with
      | inl h' => exact False.elim (hxa h'.symm)
      | inr h' =>
        simp only [hxa, ↓reduceIte, List.length_cons]
        have := ih h'
        omega

private theorem mem_removeOne_of_ne {α : Type} [DecidableEq α] {a y : α} {l : List α}
    (hne : y ≠ a) (hy : y ∈ l) : y ∈ removeOne a l := by
  induction l with
  | nil => nomatch hy
  | cons x xs ih =>
    simp only [removeOne]
    by_cases hxa : x = a
    · subst hxa
      simp only [↓reduceIte]
      cases List.mem_cons.mp hy with
      | inl h' => exact False.elim (hne h')
      | inr h' => exact h'
    · simp only [hxa, ↓reduceIte]
      cases List.mem_cons.mp hy with
      | inl h' => subst h'; exact List.mem_cons_self
      | inr h' => exact List.mem_cons_of_mem x (ih h')

private theorem length_le_of_nodup_subset {α : Type} [DecidableEq α] {l1 l2 : List α}
    (hnd : l1.Nodup) (hsub : ∀ x ∈ l1, x ∈ l2) : l1.length ≤ l2.length := by
  induction l1 generalizing l2 with
  | nil => simp
  | cons a as ih =>
    cases hnd with
    | cons ha has =>
      have ha_in : a ∈ l2 := hsub a List.mem_cons_self
      have hsub' : ∀ y ∈ as, y ∈ removeOne a l2 := by
        intro y hy
        have hne : y ≠ a := fun h => ha y hy h.symm
        exact mem_removeOne_of_ne hne (hsub y (List.mem_cons_of_mem a hy))
      have hle := ih has hsub'
      have hlen := length_removeOne_of_mem ha_in
      simp only [List.length_cons]
      omega

private theorem length_eq_of_nodup_equiv {α : Type} [DecidableEq α] {l1 l2 : List α}
    (h1 : l1.Nodup) (h2 : l2.Nodup) (heq : ∀ x, x ∈ l1 ↔ x ∈ l2) :
    l1.length = l2.length := by
  have hle1 := length_le_of_nodup_subset h1 (fun x hx => (heq x).mp hx)
  have hle2 := length_le_of_nodup_subset h2 (fun x hx => (heq x).mpr hx)
  omega

private theorem length_gridPts_aux (n : Nat) (rows : List Nat) :
    (rows.flatMap (fun i => (List.range n).map (fun j => (i, j)))).length = rows.length * n := by
  induction rows with
  | nil => simp
  | cons i is ih =>
    simp only [List.flatMap_cons, List.length_append, List.length_map, List.length_range, ih,
      List.length_cons]
    rw [Nat.add_mul, Nat.one_mul, Nat.add_comm]

private theorem length_gridPts (m n : Nat) : (gridPts m n).length = m * n := by
  unfold gridPts
  rw [length_gridPts_aux n (List.range m), List.length_range]

private theorem length_filter_ne {α : Type} [DecidableEq α] (target : α) {l : List α}
    (hl : l.Nodup) (hmem : target ∈ l) :
    (l.filter (fun p => decide (p ≠ target))).length + 1 = l.length := by
  induction l with
  | nil => nomatch hmem
  | cons x xs ih =>
    cases hl with
    | cons hx hxs =>
      cases List.mem_cons.mp hmem with
      | inl hxt =>
        subst hxt
        have hall : xs.filter (fun p => decide (p ≠ target)) = xs := by
          clear ih hmem
          induction xs with
          | nil => rfl
          | cons y ys ihy =>
            cases hxs with
            | cons hy hys =>
              have hy_ne : decide (y ≠ target) = true := by
                simp only [decide_eq_true_eq]
                exact fun h => hx y List.mem_cons_self h.symm
              simp only [List.filter, hy_ne]
              congr 1
              exact ihy hys (fun z hz => hx z (List.mem_cons_of_mem y hz))
        have hfalse : decide (target ≠ target) = false := by simp
        simp only [List.filter, hfalse, hall, List.length_cons]
      | inr hxs_mem =>
        have hx_ne : decide (x ≠ target) = true := by
          simp only [decide_eq_true_eq]
          exact fun h => hx target hxs_mem h
        simp only [List.filter, hx_ne, List.length_cons]
        have := ih hxs hxs_mem
        omega

private theorem bne_eq_decide_ne (p q : Pt) : (p != q) = decide (p ≠ q) := by
  by_cases h : p = q <;> simp [h]

private theorem length_puncturedGrid {m n : Nat} (hm : 1 ≤ m) (hn : 1 ≤ n) :
    (puncturedGrid m n).length + 1 = m * n := by
  have h0_mem : (0, 0) ∈ gridPts m n := (mem_gridPts_iff m n (0, 0)).mpr ⟨hm, hn⟩
  have heq : puncturedGrid m n = (gridPts m n).filter (fun p => decide (p ≠ (0, 0))) := by
    unfold puncturedGrid
    simp only [bne_eq_decide_ne]
  rw [heq, length_filter_ne (0, 0) (nodup_gridPts m n) h0_mem, length_gridPts]

private theorem length_doublyPuncturedGrid {m n : Nat} (hm : 2 ≤ m) (hn : 2 ≤ n) :
    (doublyPuncturedGrid m n).length + 1 = (puncturedGrid m n).length := by
  have hmax_mem : (m - 1, n - 1) ∈ puncturedGrid m n :=
    (mem_puncturedGrid_iff m n (m - 1, n - 1)).mpr
      ⟨⟨by omega, by omega⟩, fun h => by injection h with h1 _; omega⟩
  have heq : doublyPuncturedGrid m n =
      (puncturedGrid m n).filter (fun p => decide (p ≠ (m - 1, n - 1))) := by
    unfold doublyPuncturedGrid
    simp only [bne_eq_decide_ne]
  rw [heq]
  exact length_filter_ne (m - 1, n - 1) (nodup_puncturedGrid m n) hmax_mem

private theorem checkConvex_row_iff (m n : Nat) (T : List Pt) :
    checkConvex (fun a b => decide (ltRow a b)) (gridPts m n) T = true ↔
      IsConvexOnGrid ltRow m n T := by
  simp only [checkConvex, List.all_eq_true, mem_gridPts_iff]
  constructor
  · intro h a b c ha hb hc hab hbc haT hcT
    have hspec := h a ha b hb c hc
    simp [hab, hbc, haT, hcT] at hspec
    exact hspec
  · intro h a ha b hb c hc
    by_cases hab : ltRow a b <;> by_cases hbc : ltRow b c <;>
      by_cases haT : a ∈ T <;> by_cases hcT : c ∈ T
    · have hbT := h a b c ha hb hc hab hbc haT hcT
      simp [hab, hbc, haT, hcT, hbT]
    all_goals simp [hab, hbc, haT, hcT]

private theorem checkConvex_col_iff (m n : Nat) (T : List Pt) :
    checkConvex (fun a b => decide (ltCol a b)) (gridPts m n) T = true ↔
      IsConvexOnGrid ltCol m n T := by
  simp only [checkConvex, List.all_eq_true, mem_gridPts_iff]
  constructor
  · intro h a b c ha hb hc hab hbc haT hcT
    have hspec := h a ha b hb c hc
    simp [hab, hbc, haT, hcT] at hspec
    exact hspec
  · intro h a ha b hb c hc
    by_cases hab : ltCol a b <;> by_cases hbc : ltCol b c <;>
      by_cases haT : a ∈ T <;> by_cases hcT : c ∈ T
    · have hbT := h a b c ha hb hc hab hbc haT hcT
      simp [hab, hbc, haT, hcT, hbT]
    all_goals simp [hab, hbc, haT, hcT]

def canonicalBiNC2List (m n : Nat) : List (List Pt) :=
  puncturedGrid m n :: doublyPuncturedGrid m n :: (puncturedGrid m n).map (fun p => [p])

/-- **Universal Theorem (Reading I, 2-Block Grid Classification & Exact Count):**
    For ALL `m ≥ 2` and `n ≥ 2`, the number `c2Grid m n` of 2-block bi-lexicographic
    noncrossing partitions of `[m] × [n]` is identically `m * n + 1`! -/
theorem c2Grid_eq_mul_add_one (m n : Nat) (hm : 2 ≤ m) (hn : 2 ≤ n) :
    c2Grid m n = m * n + 1 := by
  unfold c2Grid
  have hmn_ge4 : 4 ≤ m * n := by
    have : 2 * 2 ≤ m * n := Nat.mul_le_mul hm hn
    omega
  have hlenP := length_puncturedGrid (m := m) (n := n) (by omega) (by omega)
  have hlenDP := length_doublyPuncturedGrid hm hn
  have hnd1 : (biNC2BlockList m n).Nodup :=
    nodup_filter_list _ (nodup_allSublists (nodup_puncturedGrid m n))
  have hnd_sing : ((puncturedGrid m n).map (fun p => [p])).Nodup :=
    nodup_map_of_inj (fun _ _ h => by injection h) (nodup_puncturedGrid m n)
  have hnd2 : (canonicalBiNC2List m n).Nodup := by
    unfold canonicalBiNC2List
    apply List.Pairwise.cons
    · intro y hy heq
      cases List.mem_cons.mp hy with
      | inl h =>
        have := congrArg List.length (heq.trans h)
        omega
      | inr h =>
        rw [List.mem_map] at h
        rcases h with ⟨q, _, hq⟩
        have := congrArg List.length (heq.trans hq.symm)
        simp at this
        omega
    · apply List.Pairwise.cons
      · intro y hy heq
        rw [List.mem_map] at hy
        rcases hy with ⟨q, _, hq⟩
        have := congrArg List.length (heq.trans hq.symm)
        simp at this
        omega
      · exact hnd_sing
  have hequiv : ∀ T, T ∈ biNC2BlockList m n ↔ T ∈ canonicalBiNC2List m n := by
    intro T
    simp only [biNC2BlockList, List.mem_filter, Bool.and_eq_true,
      checkConvex_row_iff, checkConvex_col_iff]
    constructor
    · rintro ⟨hTsub, ⟨⟨hTne, hrow⟩, hcol⟩⟩
      have hTnd : T.Nodup := nodup_of_mem_allSublists (nodup_puncturedGrid m n) hTsub
      have hTpts : ∀ x ∈ T, inGrid m n x ∧ x ≠ (0, 0) :=
        fun x hx => (mem_puncturedGrid_iff m n x).mp (sub_of_mem_allSublists hTsub x hx)
      cases T with
      | nil => simp at hTne
      | cons p ps =>
        cases ps with
        | nil =>
          have hp_mem : p ∈ puncturedGrid m n := sub_of_mem_allSublists hTsub p List.mem_cons_self
          unfold canonicalBiNC2List
          exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_map_of_mem hp_mem))
        | cons q qs =>
          cases hTnd with
          | cons hp_not _ =>
            have hpq : p ≠ q := fun h => hp_not q List.mem_cons_self h
            have hall_dp := doublyPunctured_subset_of_biConvex hm hn hTpts hrow hcol
              List.mem_cons_self (List.mem_cons_of_mem p List.mem_cons_self) hpq
            by_cases hmax : (m - 1, n - 1) ∈ (p :: q :: qs)
            · have heqT : (p :: q :: qs) = puncturedGrid m n := by
                apply eq_of_mem_allSublists_ext (nodup_puncturedGrid m n) hTsub
                  (self_mem_allSublists (puncturedGrid m n))
                intro r
                constructor
                · intro hr; exact sub_of_mem_allSublists hTsub r hr
                · intro hr
                  have ⟨hrg, hr0⟩ := (mem_puncturedGrid_iff m n r).mp hr
                  by_cases hrm : r = (m - 1, n - 1)
                  · subst hrm; exact hmax
                  · exact hall_dp r hrg hr0 hrm
              rw [heqT]; exact List.mem_cons_self
            · have heqT : (p :: q :: qs) = doublyPuncturedGrid m n := by
                apply eq_of_mem_allSublists_ext (nodup_puncturedGrid m n) hTsub
                  (filter_mem_allSublists _ _)
                intro r
                simp only [doublyPuncturedGrid, List.mem_filter, bne_iff_ne, ne_eq]
                constructor
                · intro hr
                  refine ⟨sub_of_mem_allSublists hTsub r hr, ?_⟩
                  intro hrm; subst hrm; exact hmax hr
                · rintro ⟨hr, hrm⟩
                  have ⟨hrg, hr0⟩ := (mem_puncturedGrid_iff m n r).mp hr
                  exact hall_dp r hrg hr0 hrm
              rw [heqT]; exact List.mem_cons_of_mem _ List.mem_cons_self
    · intro hmem
      unfold canonicalBiNC2List at hmem
      rcases List.mem_cons.mp hmem with rfl | hmem2
      · refine ⟨self_mem_allSublists _, ⟨⟨?_, ?_⟩, ?_⟩⟩
        · cases h : puncturedGrid m n with
          | nil => rw [h] at hlenP; simp at hlenP; omega
          | cons _ _ => rfl
        · intro a b c _ hb _ hab _ haT _
          apply (mem_puncturedGrid_iff m n b).mpr ⟨hb, ?_⟩
          intro hb0; subst hb0
          have ⟨_, ha0⟩ := (mem_puncturedGrid_iff m n a).mp haT
          cases a with
          | mk a1 a2 =>
            cases hab with
            | inl h1 => omega
            | inr h2 => rcases h2 with ⟨rfl, h2'⟩; omega
        · intro a b c _ hb _ hab _ haT _
          apply (mem_puncturedGrid_iff m n b).mpr ⟨hb, ?_⟩
          intro hb0; subst hb0
          have ⟨_, ha0⟩ := (mem_puncturedGrid_iff m n a).mp haT
          cases a with
          | mk a1 a2 =>
            cases hab with
            | inl h1 => omega
            | inr h2 => rcases h2 with ⟨rfl, h2'⟩; omega
      · rcases List.mem_cons.mp hmem2 with rfl | hmem3
        · refine ⟨filter_mem_allSublists _ _, ⟨⟨?_, ?_⟩, ?_⟩⟩
          · cases h : doublyPuncturedGrid m n with
            | nil => rw [h] at hlenDP; simp at hlenDP; omega
            | cons _ _ => rfl
          · intro a b c _ hb hc hab hbc haT hcT
            simp only [doublyPuncturedGrid, List.mem_filter, mem_puncturedGrid_iff,
              bne_iff_ne, ne_eq] at haT hcT ⊢
            refine ⟨⟨hb, ?_⟩, ?_⟩
            · intro hb0; subst hb0
              cases a with
              | mk a1 a2 =>
                cases hab with
                | inl h1 => omega
                | inr h2 => rcases h2 with ⟨rfl, h2'⟩; omega
            · intro hbmax; subst hbmax
              cases c with
              | mk c1 c2 =>
                have ⟨hcm, hcn⟩ := hc
                cases hbc with
                | inl h1 => omega
                | inr h2 => omega
          · intro a b c _ hb hc hab hbc haT hcT
            simp only [doublyPuncturedGrid, List.mem_filter, mem_puncturedGrid_iff,
              bne_iff_ne, ne_eq] at haT hcT ⊢
            refine ⟨⟨hb, ?_⟩, ?_⟩
            · intro hb0; subst hb0
              cases a with
              | mk a1 a2 =>
                cases hab with
                | inl h1 => omega
                | inr h2 => rcases h2 with ⟨rfl, h2'⟩; omega
            · intro hbmax; subst hbmax
              cases c with
              | mk c1 c2 =>
                have ⟨hcm, hcn⟩ := hc
                cases hbc with
                | inl h1 => omega
                | inr h2 => omega
        · rw [List.mem_map] at hmem3
          rcases hmem3 with ⟨p, hp, rfl⟩
          refine ⟨singleton_mem_allSublists (nodup_puncturedGrid m n) hp, ⟨⟨rfl, ?_⟩, ?_⟩⟩
          · intro a b c _ _ _ hab hbc haT hcT
            simp at haT hcT; subst haT; subst hcT
            exfalso
            cases hab with
            | inl h1 =>
              cases hbc with
              | inl h2 => omega
              | inr h2 => omega
            | inr h1 =>
              cases hbc with
              | inl h2 => omega
              | inr h2 => omega
          · intro a b c _ _ _ hab hbc haT hcT
            simp at haT hcT; subst haT; subst hcT
            exfalso
            cases hab with
            | inl h1 =>
              cases hbc with
              | inl h2 => omega
              | inr h2 => omega
            | inr h1 =>
              cases hbc with
              | inl h2 => omega
              | inr h2 => omega
  have hlen_eq := length_eq_of_nodup_equiv hnd1 hnd2 hequiv
  rw [hlen_eq]
  simp only [canonicalBiNC2List, List.length_cons, List.length_map]
  omega

/-- **Universal Non-Polynomiality Theorem (Reading I):**
    There exists NO rational-coefficient bivariate polynomial `(1/D) * P(x, y)` (`D > 0`,
    `P ∈ ℤ[x, y]`) agreeing with the 2-block bi-noncrossing count `c2Grid m n` for all `m, n ≥ 1`. -/
theorem grid2D_twoBlock_not_polynomial :
    ¬ ∃ (D : Nat) (P : Poly2), 0 < D ∧
      ∀ m n : Nat, 1 ≤ m → 1 ≤ n →
        evalPoly2 P (m : Int) (n : Int) = ((D * c2Grid m n) : Int) := by
  rintro ⟨D, P, hD, hall⟩
  have h_ge2 : ∀ n : Nat, 2 ≤ n → evalPoly2 P 2 (n : Int) = ((D * (2 * n + 1)) : Int) := by
    intro n hn
    have hval := hall 2 n (by omega) (by omega)
    rw [c2Grid_eq_mul_add_one 2 n (by omega) hn] at hval
    exact hval
  have h_at1 : evalPoly2 P 2 1 = (D : Int) := by
    have hval := hall 2 1 (by omega) (by omega)
    have hc21 : c2Grid 2 1 = 1 := c2Grid_small_values.1
    simpa [hc21, Int.mul_one] using hval
  exact no_biv_poly_grid_slice D hD P h_ge2 h_at1

end TwoDimNarayana
