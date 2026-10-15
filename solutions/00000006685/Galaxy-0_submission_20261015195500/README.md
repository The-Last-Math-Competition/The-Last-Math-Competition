# Counterexample 00000006685: nondegenerate 3D power cells

The paper gives five rational weighted sites whose genuine power-cell facet adjacency is K5. It proves nondegeneracy and uses the classical Euler obstruction. The Lean project verifies actual finite geometry, a field-general no-common-power-sphere theorem, and the K5 rotation-system obstruction.

## Scope

This is a complete mathematical counterexample, with exact formal certificates. It is **not** a claim that real topology and the general plane-embedding/rotation-system correspondence have been formalized in Std. The paper explicitly proves and identifies the semantic bridges. Reviewers requiring every general topological bridge in Lean should treat that extra foundational formalization as outstanding, not as a hidden axiom in this project.

- `PowerCells.lean`: exact power distances, strict bisectors, three noncollinear points on every facet, every site visible, distinct weights, every four sites affinely independent.
- `NoSphere.lean`: no common power sphere over any characteristic-zero field, including R; symbolic affine distance-difference identity.
- `FacialBound.lean`: generic closed-walk partition bound, derived from absence of one- and two-cycles.
- `K5Rotation.lean`: actual local rotation orders, edge reversal, facial permutation, genuine closed-walk face decompositions, no spherical Euler face count.
- `Conjecture6685.lean`: bundle of finite counterexample certificates.
- `paper.tex` / `paper.pdf`: complete argument and formalization boundaries.
- `verify.py`: optional independent exact-rational audit; not part of Lean's trusted base.

## Reproduce

Lean version: 4.31.0. Only the bundled Std library is required.

    ./verify.sh
    # Or pass the directory of your Lean toolchain binaries:
    # ./verify.sh /path/to/lean/bin
    python3 verify.py
    pdflatex paper.tex
    pdflatex paper.tex

The verification script also saves build, independent kernel-replay, axiom-audit, and exact-arithmetic logs. For a single independent Lean kernel check after a build:

    lake env leanchecker Conjecture6685

No `sorry`, `native_decide`, user-added axioms, or external solver certificates are used. The finite enumeration uses kernel decision procedures.

## Eligibility snapshot

Official conjecture source was retrieved on 2026-10-15, matches the local bilingual corpus, and is saved in `original-source.md`. The metadata snapshot marks both proven and disproven false. The complete fetched 1020-PR all-state listing had no 6685 match. This snapshot is not a guarantee against later submissions; recheck before publication. No external submission has been made.
