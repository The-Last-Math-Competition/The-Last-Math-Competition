/-
Copyright (c) 2026. All rights reserved.
Core Lean 4.19.0 formalization for Conjecture 00000008533:
"The LYM inequality on lattices: LYM type inequalities hold on all geometric lattices;
the optimal weighting is the normalization of the absolute value of the Mobius function;
and the weighting constant cannot be improved further."

Complete Resolution (Disproof of the Conjecture + Positive Non-Vacuity Theorem):
1. Positive LYM-Type Theorem (`lubell_lym_holds_on_all_geometric_lattices`):
   On EVERY finite geometric lattice `L`, Lubell's maximal-chain probability weighting
   `w_chain(x) = c(x) / |C(L)|` satisfies `∑_{x ∈ A} w_chain(x) ≤ 1` for all antichains `A`,
   and achieves exact equality `1` on every rank level `L_k`, so the constant `1` cannot be
   improved further.
2. Refutation of Classical Rank-Uniform LYM (`classical_lym_fails_on_geometric_lattices`):
   On the 34-element rank-3 geometric lattice `L34 = L(U_{2,5} ⊕_{e₀} U_{2,6})`, there is an
   explicit 21-element antichain achieving `∑_{x ∈ A} (1 / W_{rk x}) = 111 / 110 > 1`.
3. Complete Refutation of ALL Normalizations of `|μ|` (`all_mobius_normalizations_fail`):
   Every standard normalization of the absolute value of the Möbius function fails at least
   one clause of the conjecture:
   - Global `|μ(⊥, x)| / ∑_{y ∈ L} |μ(⊥, y)|`: constant `1` is ALWAYS strictly improvable
     (`C ≤ (S - 1)/S < 1`) on every geometric lattice of rank ≥ 1;
   - Proper-global `|μ(⊥, x)| / ∑_{y ∈ L^\circ} |μ(⊥, y)|`: constant `1` is ALWAYS strictly
     improvable (`C < 1`) on every geometric lattice of rank ≥ 3;
   - Rank-normalized two-sided `|μ(⊥, x) μ(x, ⊤)|`: violates `≤ 1` (`66/65 > 1`) on `L46`;
   - Rank-normalized upper `|μ(x, ⊤)|`: violates `≤ 1` (`23788/23725 > 1`) on `L922`;
   - Rank-normalized lower `|μ(⊥, x)| / |w_{rk x}|`: strictly suboptimal already on the
     10-element modular geometric lattice `L10 = B_1 × M_3` (`min = 1/5 < 2/9 < 1/4`, failing
     Sperner maximin optimality and pointwise dominance).
-/
import Conjecture00000008533.Basic
import Conjecture00000008533.LubellLYM
import Conjecture00000008533.SimpleMatroid
import Conjecture00000008533.Counterexamples

namespace Conjecture00000008533

/--
**Main Positive Theorem:**
Tight LYM-type inequalities (via Lubell's maximal-chain probability weighting) hold on ALL
finite geometric lattices with unimprovable constant `1`.
-/
theorem lubell_lym_holds_on_all_geometric_lattices
    {α : Type} [DecidableEq α] (L : GeometricLattice α) :
    0 < L.maxChains.length ∧
    (∀ A : List α, L.IsAntichain A → QRat.le (QRat.sumList A L.lubellWeight) QRat.one) ∧
    (∀ k : Nat, k ≤ L.rk L.top →
      L.IsAntichain (L.rankLevel k) ∧
      QRat.eqv (QRat.sumList (L.rankLevel k) L.lubellWeight) QRat.one) :=
  ⟨L.maxChains_pos,
   fun _ hA => L.lubell_lym_qrat hA,
   fun k hk => ⟨L.rankLevel_isAntichain k, (L.lubell_rankLevel_tight hk).2⟩⟩

/-- Enumeration of the five standard normalizations of `|μ|` on a geometric lattice. -/
inductive MobiusNormalization where
  | globalLower       -- |μ(⊥, x)| / ∑_{y ∈ L} |μ(⊥, y)|
  | properGlobalLower -- |μ(⊥, x)| / ∑_{y ∈ L \ {⊥, ⊤}} |μ(⊥, y)|
  | rankTwoSided      -- |μ(⊥, x) μ(x, ⊤)| / ∑_{rk y = rk x} |μ(⊥, y) μ(y, ⊤)|
  | rankUpper         -- |μ(x, ⊤)| / ∑_{rk y = rk x} |μ(y, ⊤)|
  | rankLower         -- |μ(⊥, x)| / |w_{rk x}(L)|
  deriving DecidableEq

/--
A weighting `w : α → QRat` on a finite geometric lattice `L` satisfies the three joint
optimality/tightness requirements of Conjecture `00000008533` on domain `D ⊆ L` if:
1. **LYM Validity (`≤ 1`):** `∑_{x ∈ A} w(x) ≤ 1` for every antichain `A ⊆ D`;
2. **Constant Tightness (Unimprovable `1`):** there is no `C < 1` bounding `∑_{x ∈ A} w(x) ≤ C`
   for all antichains `A ⊆ D`;
3. **Maximin / Sperner Optimality on Proper Flats:** for every valid LYM weighting `w'` on `L`,
   there is no proper flat guarantee `m'` strictly exceeding `min_{x ∈ L^\circ} w(x)` everywhere
   on `L^\circ` (i.e., `¬ ∃ w' m', valid(w') ∧ (∀ x ∈ L^\circ, m' ≤ w'(x)) ∧ (∃ x₀ ∈ L^\circ, w(x₀) < m')`).
-/
def SatisfiesOptimalTightLYM {α : Type} [DecidableEq α]
    (L : GeometricLattice α) (D : List α) (w : α → QRat) : Prop :=
  (∀ A : List α, L.IsAntichain A → (∀ x ∈ A, x ∈ D) → QRat.le (QRat.sumList A w) QRat.one) ∧
  (¬ ∃ C : QRat, QRat.lt C QRat.one ∧
      ∀ A : List α, L.IsAntichain A → (∀ x ∈ A, x ∈ D) → QRat.le (QRat.sumList A w) C) ∧
  (¬ ∃ (w' : α → QRat) (m' : QRat),
      (∀ A : List α, L.IsAntichain A → QRat.le (QRat.sumList A w') QRat.one) ∧
      (∀ x ∈ L.properElems, QRat.le m' (w' x)) ∧
      (∃ x₀ ∈ L.properElems, QRat.lt (w x₀) m'))

/-- Canonical `|μ|`-normalized weighting attached to any `L` under convention `mode`. -/
def mobiusWeightOf {α : Type} [DecidableEq α]
    (mode : MobiusNormalization) (L : GeometricLattice α) (x : α) : QRat :=
  match mode with
  | .globalLower =>
    if h : 0 < L.totalAbsMobiusBot then
      QRat.mkNat (L.absMobius L.bot x) L.totalAbsMobiusBot h
    else QRat.zero
  | .properGlobalLower =>
    if h : 0 < L.totalProperAbsMobiusBot then
      QRat.mkNat (L.absMobius L.bot x) L.totalProperAbsMobiusBot h
    else QRat.zero
  | .rankTwoSided =>
    let d := L.twoSidedMobiusRankSum (L.rk x)
    if h : 0 < d then QRat.mkNat (L.absMobius L.bot x * L.absMobius x L.top) d h
    else QRat.zero
  | .rankUpper =>
    let d := L.upperMobiusRankSum (L.rk x)
    if h : 0 < d then QRat.mkNat (L.absMobius x L.top) d h
    else QRat.zero
  | .rankLower =>
    let d := L.absWhitney1 (L.rk x)
    if h : 0 < d then QRat.mkNat (L.absMobius L.bot x) d h
    else QRat.zero

def domainOf {α : Type} [DecidableEq α]
    (mode : MobiusNormalization) (L : GeometricLattice α) : List α :=
  match mode with
  | .properGlobalLower => L.properElems
  | _ => L.elems

/--
**Master Disproof Theorem (`optimal_mobius_lym_conjecture_false`):**
For EVERY normalization convention `mode` of the absolute value of the Möbius function, there
exists an explicit finite `GeometricLattice` (of rank ≥ 3) on which `mobiusWeightOf mode`
FAILS `SatisfiesOptimalTightLYM`! Moreover, the classical rank-uniform LYM inequality also
fails on the explicit 34-element rank-3 geometric lattice `L34`.
-/
theorem optimal_mobius_lym_conjecture_false :
    -- (A) Classical rank-uniform LYM fails on `L34` (`111/110 > 1`):
    (L34.IsAntichain antichain34 ∧
      QRat.lt QRat.one (QRat.sumList antichain34 wClassical34)) ∧
    -- (B) Every normalization of `|μ|` fails optimal tight LYM on a finite geometric lattice:
    (∀ mode : MobiusNormalization,
      (¬ SatisfiesOptimalTightLYM L10 (domainOf mode L10) (mobiusWeightOf mode L10)) ∨
      (¬ SatisfiesOptimalTightLYM L46 (domainOf mode L46) (mobiusWeightOf mode L46)) ∨
      (¬ SatisfiesOptimalTightLYM L922 (domainOf mode L922) (mobiusWeightOf mode L922))) := by
  refine ⟨⟨classical_lym_fails_on_L34.2.2.2.2.1, classical_lym_fails_on_L34.2.2.2.2.2.2.2⟩, ?_⟩
  intro mode
  cases mode with
  | globalLower =>
    refine Or.inl ?_
    intro hsat
    have hrk1 : 1 ≤ L10.rk L10.top := by have := lower_mobius_suboptimal_on_L10.2.1; omega
    rcases L10.global_mobius_constant_improvable hrk1 with ⟨hpos, C, hClt, hCbound⟩
    apply hsat.2.1
    refine ⟨C, hClt, fun A hA _ => ?_⟩
    have hcongr : QRat.eqv (QRat.sumList A (mobiusWeightOf .globalLower L10))
        (QRat.sumList A (fun x => QRat.mkNat (L10.absMobius L10.bot x) L10.totalAbsMobiusBot hpos)) := by
      apply QRat.sumList_congr_eqv
      intro x _
      unfold mobiusWeightOf
      simp [hpos, QRat.eqv]
    exact QRat.le_of_eqv_left hcongr (hCbound A hpos hA)
  | properGlobalLower =>
    refine Or.inl ?_
    intro hsat
    have hrk3 : 3 ≤ L10.rk L10.top := by have := lower_mobius_suboptimal_on_L10.2.1; omega
    rcases L10.proper_global_mobius_constant_improvable hrk3 with ⟨hpos, C, hClt, hCbound⟩
    apply hsat.2.1
    refine ⟨C, hClt, fun A hA hAD => ?_⟩
    have hcongr : QRat.eqv (QRat.sumList A (mobiusWeightOf .properGlobalLower L10))
        (QRat.sumList A (fun x => QRat.mkNat (L10.absMobius L10.bot x) L10.totalProperAbsMobiusBot hpos)) := by
      apply QRat.sumList_congr_eqv
      intro x _
      unfold mobiusWeightOf
      simp [hpos, QRat.eqv]
    exact QRat.le_of_eqv_left hcongr (hCbound A hpos hA hAD)
  | rankTwoSided =>
    refine Or.inr (Or.inl ?_)
    intro hsat
    have hf46 := two_sided_mobius_lym_fails_on_L46
    have hle := hsat.1 antichain46 hf46.2.2.1 (fun x _ => L46.mem_elems x)
    have hgt : QRat.lt QRat.one (QRat.sumList antichain46 wTwoSided46) := hf46.2.2.2.2.2.2
    -- Note `mobiusWeightOf .rankTwoSided L46 = wTwoSided46` definitionally!
    change QRat.le (QRat.sumList antichain46 wTwoSided46) QRat.one at hle
    unfold QRat.le at hle
    unfold QRat.lt at hgt
    omega
  | rankUpper =>
    refine Or.inr (Or.inr ?_)
    intro hsat
    have hf922 := upper_mobius_lym_fails_on_L922
    have hle := hsat.1 antichain922 hf922.2.2.2.2.1 (fun x _ => L922.mem_elems x)
    have hgt : QRat.lt QRat.one (QRat.sumList antichain922 wUpper922) := hf922.2.2.2.2.2.2
    change QRat.le (QRat.sumList antichain922 wUpper922) QRat.one at hle
    unfold QRat.le at hle
    unfold QRat.lt at hgt
    omega
  | rankLower =>
    refine Or.inl ?_
    intro hsat
    have hf10 := lower_mobius_suboptimal_on_L10
    apply hsat.2.2
    refine ⟨wUnif10, QRat.mkNat 1 4 (by decide), hf10.2.2.1, ?_, ?_⟩
    · intro x hx
      have heqv := hf10.2.2.2.2.1 x hx
      exact QRat.le_of_eqv_left (QRat.eqv_refl _) (by
        unfold QRat.eqv at heqv; unfold QRat.le; omega)
    · rcases hf10.2.2.2.2.2.2.1 with ⟨x₀, hx₀, heqv₀, _, _⟩
      refine ⟨x₀, hx₀, ?_⟩
      change QRat.lt (wLow10 x₀) (QRat.mkNat 1 4 (by decide))
      exact Classical.byContradiction fun hnot => by
        have hd : (0 : Int) < ((wLow10 x₀).den : Int) := Int.ofNat_lt.mpr (wLow10 x₀).den_pos
        unfold QRat.eqv at heqv₀
        unfold QRat.lt at hnot
        dsimp only [QRat.mkNat] at heqv₀ hnot
        omega

end Conjecture00000008533
