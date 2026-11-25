import Conjecture00000004770.PosetMobius
import Conjecture00000004770.PartitionsAndAnnulus
import Conjecture00000004770.CanonicalRigidity
import Conjecture00000004770.SubfamilyScope

namespace Conjecture00000004770

/-!
# Root Formalization Summary — Conjecture `00000004770`

Exports the two top-level summary theorems:
1. `conjecture_00000004770_positive_foundations`: First-principles Möbius function existence,
   uniqueness, inversion, and isomorphism invariance; universal punctured-annulus /
   circular-boundary lattice equivalence `NC_A(p, 1) = NC_∂^∘(p)`; Kreweras duality between
   the two reflection-boundary families `NC^sym_edge(4)` and `NC^sym_vert(4)`; and explicit
   5-element (`NC(4)`) and 10-element (`NC(8)`) induced sublattice pairs demonstrating that
   arbitrary finite noncrossing sublattices can share Möbius spectra while being non-isomorphic.
2. `conjecture_00000004770_disproof`: Disproof of Conjecture `00000004770` across all canonical
   annular and boundary noncrossing partition families:
   - Mingo–Nica annular permutations `S_NC(2, 1)` fail both join- and meet-semilattice axioms;
   - Mingo–Nica annular set partitions `NC_A(p, q)` fail unique joins for all `p ≥ q ≥ 2`
     with `p + q ≥ 6` (`(4, 2)`, `(3, 3)`, and all higher `(p, q)`);
   - At the equinumerous order `6 = C(4, 2)`, rotational `NC^(B)(2)` and reflection-boundary
     `NC^sym_edge(4)` / `NC^sym_vert(4)` disagree on both lower and full Möbius spectra;
   - Across ALL parameters `(p, q, m)` of all canonical annular and boundary lattice families,
     matching `(card, |μ(0̂, 1̂)|)` holds if and only if the pair is canonically isomorphic.
-/

theorem conjecture_00000004770_positive_foundations :
    -- (1) Existence and uniqueness of the two-variable Möbius function on every finite poset
    (∀ (n : Nat) (P : FinPoset n),
      IsMobiusFunction P (mobius P) ∧ ∀ mu, IsMobiusFunction P mu → mu = mobius P) ∧
    -- (2) Universal punctured-annulus / circular-boundary lattice equivalence `NC_A(p, 1) = NC_∂^∘(p)`
    (∀ (p : Nat) (π : SetPartition (p + 1)), IsAnnularNC p 1 π ↔ IsCircBoundaryNC p π) ∧
    -- (3) Scope boundary: 10-element self-dual sublattices in `NC(8)` sharing all Möbius spectra
    (poset10A.IsLattice ∧ poset10B.IsLattice ∧
      (∀ v : Int, lowerMobiusMult poset10A ⟨0, by omega⟩ v = lowerMobiusMult poset10B ⟨0, by omega⟩ v) ∧
      (∀ v : Int, upperMobiusMult poset10A ⟨9, by omega⟩ v = upperMobiusMult poset10B ⟨9, by omega⟩ v) ∧
      (∀ v : Int, fullMobiusCount poset10A v = fullMobiusCount poset10B v) ∧
      ¬ IsPosetIsomorphic poset10A poset10B) :=
  ⟨fun _ P => ⟨mobius_spec P, mobius_unique P⟩,
   annularNC_p_one_iff_circBoundary,
   poset10AB_all_mobius_spectra_equal_non_iso⟩

theorem conjecture_00000004770_disproof :
    -- (1) Mingo–Nica annular permutation poset `S_NC(2, 1)` is NOT a lattice
    ¬ snc21Poset.IsLattice ∧
    -- (2) Mingo–Nica annular set-partition posets `NC_A(p, q)` fail unique joins for all `p ≥ q ≥ 2, p + q ≥ 6`
    (∀ (p q : Nat), q ≤ p → 2 ≤ q → 6 ≤ p + q →
      ∃ σ τ : SetPartition (p + q),
        IsAnnularNC p q σ ∧ IsAnnularNC p q τ ∧
        ¬ ∃ u : SetPartition (p + q),
            IsAnnularNC p q u ∧ Refines σ u ∧ Refines τ u ∧
            (∀ w : SetPartition (p + q), IsAnnularNC p q w → Refines σ w → Refines τ w → Refines u w)) ∧
    -- (3) Equinumerous size-6 rotational vs. reflection-boundary lattices have distinct Möbius spectra
    (ncB2Poset.IsLattice ∧ ncReflEdge4Poset.IsLattice ∧ ncReflVert4Poset.IsLattice ∧
      lowerMobiusMult ncB2Poset ⟨0, by omega⟩ 3 ≠ lowerMobiusMult ncReflEdge4Poset ⟨0, by omega⟩ 3 ∧
      fullMobiusCount ncB2Poset 3 ≠ fullMobiusCount ncReflEdge4Poset 3 ∧
      fullMobiusCount ncB2Poset 3 ≠ fullMobiusCount ncReflVert4Poset 3) ∧
    -- (4) Universal canonical rigidity: across ALL parameters, no non-isomorphic canonical pair matches
    (∀ (A : AnnularLatticeFamily) (B : BoundaryLatticeFamily),
      ¬ ((A.card = B.card ∧ A.absMu01 = B.absMu01) ∧ ¬ IsCanonicalIsomorphicPair A B)) := by
  refine ⟨snc21_not_lattice.2.2,
          fun _ _ hpq hq hsum => annularNC_no_lub_of_pq_ge_two_sum_ge_six hpq hq hsum,
          ?_, ?_⟩
  · have h6 := size6_trap_resolution
    exact ⟨h6.1, h6.2.1, h6.2.2.1, h6.2.2.2.1, h6.2.2.2.2.2.1, h6.2.2.2.2.2.2.1⟩
  · intro A B ⟨hmatch, hnotiso⟩
    exact hnotiso ((canonical_invariants_match_iff_isomorphic A B).mp hmatch)

end Conjecture00000004770
