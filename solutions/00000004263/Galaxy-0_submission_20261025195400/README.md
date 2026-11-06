# Conjecture 00000004263: a one-dimensional F-matrix solution

The usual fusion category of finite-dimensional complex vector spaces has one simple object. In its fusion bases the actual tensor associator has F matrix `[1]`, and both pentagon paths agree. This disproves the printed lower bound of three. No claim is made about the separate Brauer-recursion conjunct or a nontriviality restriction absent from the source.

## Mathematical and formal scope

Read `solution.pdf` / `solution.tex` for the complete mathematical argument, including semisimplicity, finite Hom spaces, naturality, the tensor pentagon, and rigidity using dual bases. EGNO Examples 2.3.3, 2.10.12 and 4.1.2 are the primary reference.

`Main.lean` proves actual tensor-coordinate reassociation and inverse maps, the distinct pentagon paths for arbitrary index and coefficient types, the triangle, coefficientwise linearity, complete singleton basis lists, encoding/decoding, integer basis spanning and independence, the matrix entry/inverse/pentagon, and the unit-simple snake equations. Its 26 named theorems are listed in `theorems.txt` and audited by `Audit.lean`.

This is not a general formalization of complex vector spaces, tensor-product universal properties, abelian or fusion categories, or rigidity for every object. Those identifications are explicit mathematical proofs in the report. Integer checks are an integral certificate for the coefficient formulas, not a claim that integer modules form a fusion category. The generic coefficient-map and coordinate-bijection theorems are independent of the scalar type.

## Reproduce

Use the official Lean 4.31.0 toolchain (commit 68218e876d2a38b1985b8590fff244a83c321783); no external Lean dependencies are needed. Put its `bin` directory on PATH and run:

    bash VERIFY.sh

For a source-only clean build, copy `Main.lean`, `Audit.lean`, `lakefile.toml`, `lean-toolchain`, and `VERIFY.sh` to a new directory and run the same command. `lake-manifest.json` records an empty dependency list. `leanchecker Main` performs independent kernel replay after compilation.

Compile the report using a standard TeX Live installation:

    pdflatex -interaction=nonstopmode -halt-on-error solution.tex
    pdflatex -interaction=nonstopmode -halt-on-error solution.tex

The leading `pdfmapfile` lines load standard Computer Modern/AMS font maps explicitly. All fonts in the supplied two-page PDF are embedded; all pages were rendered and visually inspected.

## Evidence and status

Author and independent clean builds, warning-strict source checks, all-theorem axiom audits and kernel replay passed. Only standard `propext` and `Quot.sound` occur. No `sorry`, extra axioms, `native_decide`, or kernel bypass is used. The core generic pentagon and inverse identities have no axioms.

The local eligibility check read current unsolved metadata, found no solution directory, and searched all 1198 historical PR entries plus live short/padded ID searches. Publication must recheck these facts. AI assisted both preparation and independent review; this is not human review, organizer acceptance, or scoring. See the preserved original statement in `source.md`.
