# TLMC 00000000506: a singleton first Betti support

Verdict: false under the standard graded-Betti interpretation. For the actual monomial ideal I=(X,Y) in F₂[X,Y], the minimal
graded resolution is 0 → R(-2) → R(-1)² → I → 0. The first Betti support is {2},
which has an isolated point. A singleton is connected; connectedness itself is
not the claim being refuted. The quotient-ring indexing convention instead
gives first support {1}, also verified as a minimal-generator support.

This is a complete proof package prepared for review; no organizer acceptance
is claimed. No mathematical novelty beyond the elementary standard Koszul
example is claimed.

## Contents

- `solution.pdf` and `solution.tex`: five-page mathematical argument, source
  interpretation, formal coverage, references, and reproduction instructions.
- `source.md`: the exact bilingual conjecture.
- `*.lean`, `lakefile.toml`, `lean-toolchain`: self-contained Lean 4.31.0 project,
  depending only on core and Std.
- `VERIFY.sh`: a fresh source-only build, strict checks, transitive audit of all
  authored theorems, official kernel replay, and supplemental Python checks.
- `reproduce.py`: independent finite polynomial tests. These are diagnostic,
  not a substitute for the universal Lean proof.
- `verification/`: the completed build, axiom, kernel, computation, and PDF logs.
- `ELIGIBILITY.md`: dated read-only repository eligibility record.
- `SHA256SUMS`: frozen-package file integrity manifest.

## Formal coverage

The proof constructs finitely supported bivariate polynomials with genuine
monomial-distribution multiplication, proves their ring laws, identifies the
two-element coefficient field, and proves the free module and scalar maps.
It computes every syzygy, not just one displayed relation. It verifies the
minimality of the original X,Y presentation using a unique basis in I/mI,
the differential's minimality, the standard grading and its multiplicativity,
and the exact identification of XK+YK with the finite-sum ideal-module product
mK. The actual quotient K/mK is constructed with its equivalence relation,
its field-linear residue bijection, and its one-vector basis.

`TLMC506.conjecture506_counterexample` packages the monomial ideal, the
verified exact minimal resolution, integer-indexed support {2}, and the
failure of the no-isolated-points condition. The topological result works in
every ambient topology, and a separate result works for every irreflexive
adjacency relation. The full syzygy module's Hilbert function is explicitly
distinguished from the Betti row.

No general Tor or Taylor-resolution library is assumed or required: the proof
uses the standard minimal-generator definition of first Betti support for the
verified minimal presentation.

## Reproduce

With Lean 4.31.0 available on PATH, run:

    ./VERIFY.sh

Alternatively set `LEAN_BIN_DIR` to an existing toolchain's bin directory.
The script copies only source/configuration into a fresh temporary directory;
no authored olean, cache, generated binary, or hidden local dependency is
shipped or reused. It runs `lake build Main Audit`, strict individual source
checks, `lake env lean Audit.lean`, and `lake env leanchecker Main`.

The finished audit checked 287 theorem declarations, including generated
supporting theorems. Their transitive axiom sets are subsets of the standard
Lean axioms propext, Classical.choice, and Quot.sound. The final theorem uses
exactly those three. No added axioms, unfinished proofs, native proof escapes,
or kernel bypasses occur.

`python3 reproduce.py` checks all 4,096 pairs of polynomials of total degree at
most two, finds exactly the eight expected kernel pairs, and performs 20,480
associativity/distributivity test cases. The universal conclusion does not
depend on these finite tests.

To rebuild the report with a normal TeX Live installation and Poppler, run
`./build_pdf.sh`. The script also supports the configured local TeX formats
used for preparation. It creates all five page PNGs for visual inspection.

## Verification and provenance

All authored mathematical sources were rebuilt from a clean source-only copy.
The complete all-theorem audit and official fresh kernel replay passed.
Every rendered PDF page was visually reviewed; no clipping, overlap, missing
glyphs, or malformed mathematical notation was found. The logs contain two
minor underfull-line notices, not overfull boxes or missing fonts.

Prepared with OpenAI assistance on 21 October 2026. An additional AI semantic
review is included when present; it is not independent human review or
organizer acceptance. Repository status remains a dated snapshot and must be
checked again before any future publication.
