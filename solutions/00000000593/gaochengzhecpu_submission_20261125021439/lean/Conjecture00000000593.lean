/-
Copyright (c) 2026. All rights reserved.
 Master module for Conjecture 00000000593 (The Last Math Competition).

 Summary of Formally Verified Results:
 1. `det_mul` (`Determinant.lean`) & `matrix_molien_unconditional` /
    `matrix_group_molien_theorem` (`MatrixMolien.lean`):
    Full Laplace determinant multiplicativity `det (A * B) = det A * det B` over arbitrary
    commutative rings, the polynomial matrix geometric-series identity
    `(I_n - t A)(∑_{s=0}^{e-1} t^s A^s) = (1 - t^e) I_n`, formal power-series inversion
    `invUnitPoly`, and the **unconditional Matrix Molien Theorem** proving directly from
    `∀ A ∈ G, A^e = I_n` (with zero external rationality/degree hypotheses) that the Molien
    series is rational with strict numerator degree `< n * e`, denominator dividing `(1 - t^e)^n`
    and dividing `uniformStrictChain e n` (`∏_{i=0}^{n-1} (1 - t^{2^i e})`), and exact modular
    periodic (Newton quasi-polynomial) structure on residue classes modulo `e`.
 2. `hilbert_serre_strict_chain` & `strictDivChain_upgrade` (`ChainDivisibility.lean`):
    Constructive graded Hilbert-Serre exact-sequence induction (covering arbitrary/modular
    characteristic via Emmy Noether's orbit polynomials) upgraded to an explicit strictly
    increasing divisibility chain `d₁ ∣ d₂ ∣ ... ∣ d_r` (`0 < d₁ < ... < d_r`).
 3. `modular_periodic_iff` & `eventual_modular_periodic_iff` (`ModularPeriodic.lean`):
    Exact three-way equivalence between denominator divisibility into `(1 - t^D)^n`, vanishing of
    `Δ_D^n a`, and discrete Newton binomial quasi-polynomials on residue classes modulo `D`.
 4. Sharpness & Boundary Classification (`Sharpness.lean`):
    - `chain_length_ge_vars` & `not_dvd_single_factor`: minimum chain length `r ≥ n`.
    - `klein_not_equal_any_chain`: "dividing" cannot be strengthened to "equal to" (`SL₂(5)`).
    - `modular_F4_witness`: in modular characteristic `p ∣ |G|`, `exp(G)` fails while `|G|` succeeds.
    - `paritySeq_not_rational_in_index`: refutes hyper-literal index-rationality `a_m ∈ ℚ(m)`.
    - `sym3_nonvacuity_witness`, `bertin_modular_witness`, & `groupNegId2_molien_verified`:
      positive non-vacuity witnesses across matrix, non-modular, and modular invariant rings.
-/
import Conjecture00000000593.PolySeries
import Conjecture00000000593.ChainDivisibility
import Conjecture00000000593.ModularPeriodic
import Conjecture00000000593.Determinant
import Conjecture00000000593.MatrixMolien
import Conjecture00000000593.Sharpness

namespace Conjecture00000000593

/-- **Unconditional Master Theorem for Conjecture 00000000593 (Matrix-Group Molien Series):**
For every dimension `n ≥ 1`, exponent `e ≥ 1` (e.g., `e = |G|` or `e = exp(G)`), and finite
family/group of `n × n` matrices `G : List (Mat Int n)` satisfying `∀ A ∈ G, A^e = I_n`:
the Molien series `M = molienScaledSeries G` (`∑_{A ∈ G} det(I_n - t A)^{-1}`) unconditionally
satisfies:
1. `(1 - t^e)^n · M(t)` is an integer polynomial of strict degree `< n * e`,
2. `M(t)` has rational denominator dividing the explicit length-`n` strict divisibility chain
   `ds = uniformStrictChain e n` (`e ∣ 2e ∣ ... ∣ 2^{n-1} e`, `0 < d₁ < ... < d_n`), and
3. `M` satisfies `(Δ_e^n M)_m = 0` for all `m ≥ 0` and exact Newton binomial quasi-polynomiality
   of degree `< n` on every residue class modulo `e`.
(See also `matrix_group_molien_theorem` for the unscaled dimension sequence `a_m = M_m / |G|`
and `hilbert_serre_strict_chain` for modular invariant theory `char(k) = p ∣ |G|`.) -/
theorem conjecture_00000000593_master {n e : Nat} (hn : 1 ≤ n) (he : 1 ≤ e)
    (G : List (Mat Int n))
    (hpow : ∀ A ∈ G, matPow intCRing A e = matId intCRing n) :
    let M := molienScaledSeries G
    IsPolyBelow (n * e) (mulPolySeries (chainProd (List.replicate n e)) M) ∧
    (∃ ds : List Nat,
      ds.length = n ∧
      IsDivChain ds ∧
      IsStrictIncPos ds ∧
      HasDenominatorDividing (chainProd ds) M) ∧
    (∀ m : Nat, iterModDiff e n M m = 0) ∧
    (∀ c : Nat, c < e → ∀ q : Nat,
      M (q * e + c) = newtonEval n (fun q' => M (q' * e + c)) q) :=
  matrix_molien_unconditional hn he G hpow

end Conjecture00000000593
