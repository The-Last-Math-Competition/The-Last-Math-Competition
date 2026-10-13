# TLMC 00000003869: crossing signs in Pfaffian expansions

**Verdict: proved**, termwise at every finite order, under the standard canonical perfect-matching convention for a Pfaffian. This is a classical combinatorial identity, supplied here with a self-contained proof and unbounded Lean verification. Prepared for Galaxy-0; AI-assisted. No pull request has been opened by this package.

## Main result

For a perfect matching M on 2n ordered endpoints, list each edge (a,b) with a<b and sort edges by a. Its flattened list is an actual permutation. Then

    inversions(flatten M) = crossings(M) + 2 * nestings(M).

Consequently its permutation sign is (-1)^crossings. Every canonical matching occurs exactly once in the finite expansion. The instrumented crossing algorithm returns both the count and exactly n(n-1)/2 pair tests.

## Files

- `main.tex`, `main.pdf`: complete proof, conventions, finite-order Fredholm application, complexity, and formalization scope.
- `source.md`: exact current bilingual conjecture and upstream source SHA.
- `lean/`: self-contained Lean 4.31.0 project using only Std.
- `verification/`: build, axiom, eligibility, independent finite verification, and PDF inspection evidence.
- `build_pdf.sh`: standard pdflatex build; optional existing TeX format directory for minimal environments.

## Reproduce

    cd lean
    lake build
    lake env lean Axioms.lean

The toolchain is pinned in `lean-toolchain`; no Mathlib download is needed. Independent supplemental tests can be run with `python3 verification/independent.py`. They are not premises of the Lean proof.

## Semantic correspondence

`PerfectMatching n as` is the actual canonical presentation: pair endpoints increase, first endpoints strictly increase across the list, and the flattened endpoint list is a permutation of `List.range (2*n)`. This enforces that every endpoint occurs exactly once. Conversely any ordinary partition into pairs has exactly this presentation after orienting and sorting; the proof of this representational observation is given in the report.

- `mem_matchings`: complete enumeration iff this perfect-matching predicate.
- `matchings_nodup`: no duplicate expansion term.
- `matching_endpoint_permutation`, `matching_endpoints_distinct`: actual permutation and pairwise distinct endpoints.
- `inversion_crossing_identity`: unbounded inversion = crossing + twice nesting.
- `sign_eq_neg_one_pow`: the parity sign really is the integer power of -1.
- `formal_pfaffian_expansion`: equality of formal signed monomial lists. The Pfaffian uses the standard permutation-sign definition, not a crossing-defined surrogate.
- `evaluated_pfaffian_expansion`: arbitrary evaluation and finite sum in any type with addition and zero. Real and complex kernel entries are therefore covered; the additional integer version is only a specialization.
- `crossingCountWithCost_correct`: the instrumented algorithm computes the mathematical count and test count.
- `crossingTests_exact`, `crossingTests_quadratic`: exact and upper-bound pair-test counts at all sizes.

The formal signed monomial retains its edge list. An evaluation may take `(epsilon,M)` to `epsilon * product A[a,b]` in any commutative ring, so no matrix-entry restriction is hidden in the proof.

## Scope and conventions

The matching sign is a combinatorial coefficient, not the numerical sign of a kernel-entry product. The report uses Pf(J+K); Pf(J-K) incorporates -K in its entries and contributes the familiar additional (-1)^n. The external factor 1/n! and integrals are distinct from the matching sign.

The result applies at every finite order of the Fredholm series, formally or wherever that series is defined. It does not assert convergence for arbitrary kernels. It does not claim that enumerating all matchings is polynomial time. Computing the crossing count for one matching uses n(n-1)/2 tests, each with at most three comparisons, hence O(n^2) word operations or O(n^2 log(n+1)) bit operations on the bounded endpoint labels.

## Verification and eligibility

The source SHA is 880f529917afd80295d5bf2217e3c3993eebd1fe. Exact full-ID all-state PR search was empty on 2026-10-13; the Pfaffian keyword search returned only unrelated PRs 483 and 484. The pre-submission review checked current metadata (`proven=false`, `disproven=false`) and absence of a current solution folder. Eligibility must be checked again before publication.

No custom axioms, admitted proofs, or native decision shortcuts are used. The theorem axiom footprints contain only `propext`, `Classical.choice`, and `Quot.sound` as applicable.
