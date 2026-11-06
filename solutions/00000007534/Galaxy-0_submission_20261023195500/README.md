# Conjecture 00000007534: modular coefficients obstruct the claimed projector

Take the connected real finite etale scheme X = Spec C. Its geometric base change is two disjoint complex points. The absolute Galois group C2 swaps their constant F2 coefficients, so geometric degree-zero etale cohomology is the permutation module F2². Its fixed subspace is the nonzero proper diagonal. The coefficient group algebra F2[C2] has only idempotents 0 and 1; their images are zero and the whole module, not the diagonal. Thus the unqualified group-ring idempotent clause is false.

This familiar modular obstruction is not a new phenomenon and is not a counterexample to characteristic-zero averaging. The printed statement does not restrict coefficients or require geometric connectedness. No claim is made against a reformulation using Q_l coefficients or geometrically connected varieties. The degree-zero geometric cohomology representation must not be confused with group cohomology H0(G,M), which is already the invariant subspace.

## Files and reproduction

With an existing Lean 4.31.0 toolchain and Python 3 on PATH, run:

    bash verify.sh

This copies the five source/project/check files into a fresh temporary directory, runs strict compilation, a clean Lake build, every-named-theorem axiom audit, independent leanchecker replay, and supplementary Python checks. There are no external package dependencies and no downloads. Existing compiled objects are not used as project inputs. The temporary build is removed on exit.

Individual commands are:

    lean -DwarningAsError=true Counterexample.lean
    lake build
    lake env lean -DwarningAsError=true Audit.lean
    lake env leanchecker Counterexample
    python3 check_finite_model.py

For a normal installed TeX distribution, rebuild the PDF with:

    pdflatex -output-format=pdf -interaction=nonstopmode -halt-on-error solution.tex
    pdflatex -output-format=pdf -interaction=nonstopmode -halt-on-error solution.tex

The two-page PDF was rendered and visually reviewed. The cloud image's preinstalled TeX sources/fonts required explicit search paths and an existing local format; no new packages were installed. This environment-specific workaround does not add mathematical or Lean dependencies.

## Theorem and semantic map

- `f2_*`: arithmetic laws for Boolean XOR/AND as the field of two elements.
- `group_*`: cyclic order-two group, linear permutation action.
- `convolution_*`, `regular_action`, `ring_action_comp`: the coefficient group algebra and its faithful action, not an arbitrary operation assigned to a ring.
- `invariants_diagonal`, `all_idempotents`: exhaustive, universally quantified finite classifications.
- `evaluate`, `fromFunction`, their inverse laws and `evaluate_action`: pairs are exactly functions on the two vertices, and the group action is permutation pullback.
- `dminus`, `dplus`, `cycles`, `boundary`: the degree-zero cochain complex of the discrete two-vertex simplicial complex. Every cochain is closed; the only boundary is zero.
- `H0`: actual quotient by the relation of differing by a boundary, with `coordinates`/`classOf` inverse isomorphisms. The Galois and group-ring actions are induced on this quotient, with action laws proved.
- `no_cohomology_idempotent_with_invariant_image`: the main obstruction, phrased as absence of any group-ring idempotent with image equal to the fixed subspace.
- `no_cohomology_idempotent_projection`: the equivalent retraction formulation.
- `norm_element_image`, `norm_element_square_zero`: the norm element maps onto invariants but is nilpotent, not idempotent.
- `ordinary_is_projection`, `ordinary_not_equivariant`: a vector-space projection exists but is not equivariant. We do not claim all projections are impossible.

## Verification and limitations

All 55 named theorems passed axiom audit. Of these, 54 have no axioms; `evaluate_from` uses only the standard foundational axiom `Quot.sound` through function extensionality. The main obstruction theorems use no axioms. There are no admitted proofs, custom axioms, native proof evaluation, or kernel bypasses. Finite universal claims are checked by Lean kernel reduction, not merely `#eval` or empirical enumeration. The Python program is independent supplementary arithmetic evidence, not the proof.

The scheme, real/complex fields, general etale site, and degree-zero etale-cohomology identification are established in the mathematical document and cited Stacks results, not constructed in Lean. The formal development checks the complete resulting finite cochain quotient and action. It is not presented as a general Lean formalization of etale cohomology.

Official statement: https://github.com/The-Last-Math-Competition/The-Last-Math-Competition/blob/main/conjectures/00000007534.md

References, accessed 23 October 2026:
- https://stacks.math.columbia.edu/tag/04JI (finite etale schemes and Galois sets)
- https://stacks.math.columbia.edu/tag/03QQ (cohomology of a point and constant coefficients)

Source and eligibility were checked against upstream main `b355e42906e6eaf52bc7e9d005e0ef02d8aa7400`. The coordinator performs fresh metadata, solutions-directory and all-state PR checks immediately before publication. Verification, PR submission, merge, and official accepted scoring are separate statuses.
