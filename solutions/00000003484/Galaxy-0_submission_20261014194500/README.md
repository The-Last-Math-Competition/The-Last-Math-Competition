# Disproof of 00000003484

The connected 3-sun is chordal and has four maximal cliques and a four-bag clique tree, but has no interval representation. Thus no genus satisfies both the claimed subtraction formula and the zero-genus characterization. No value or invented definition is assigned to the unspecified genus.

## Reproduce

Install the official Lean 4.31.0 toolchain (pinned in `lean-toolchain`), make `lean`, `lake`, and optionally `leanchecker` available on PATH, and run:

    bash VERIFY.sh
    python3 verification/independent.py
    pdflatex -interaction=nonstopmode -halt-on-error report.tex
    pdflatex -interaction=nonstopmode -halt-on-error report.tex
    sha256sum -c SHA256SUMS

The project imports only Std and has no external package dependency. A normal configured TeX installation supplies the standard AMS packages and Computer Modern font maps. The verification folder includes exact successful build and audit logs. SHA256SUMS checks the frozen delivered files; rerunning PDF builds may change PDF timestamps and thus the PDF checksum.

## Contents and semantics

- `Main.lean`: complete mathematical construction; `C3484.full_counterexample` combines the required graph hypotheses, genuine clique tree, independent counts, interval obstruction, and incompatible natural/integer genus clauses.
- `Axioms.lean`: axiom audit of every authored theorem.
- `report.tex` / `report.pdf`: complete written proof, semantic correspondence, explicitly stated formalization boundaries, and source.
- `verification/`: independent source-only build, kernel replay, all-theorem audit, finite Python cross-check, and independent mathematical/PDF review. These are internal checks, not organizer endorsement.
- `eligibility/`: exact bilingual source, pinned metadata and directory evidence, all-state search and reviewed-hit evidence. A timestamped empty search is not a guarantee of first-solver status. Recheck before publication.

## Explicit boundaries

Lean proves the contradiction for natural and integer genus values; ordinary cancellation over other standard number systems is explained on paper. It proves nonexistence of closed-interval representations over arbitrary total transitive endpoint relations, which includes real order. The elementary normalization of arbitrary finite interval representations to closed bounded ones is written in the paper. The problem's undefined genus and recursion are not supplied with invented definitions: already two necessary clauses are incompatible. All 38 authored theorem axiom footprints use only standard foundational axioms as applicable; no custom axioms or incomplete proofs are used.

AI-assisted submission by Galaxy-0.
