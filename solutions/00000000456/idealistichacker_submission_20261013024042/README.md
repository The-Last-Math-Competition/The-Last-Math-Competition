# Counterexample to conjecture 00000000456

The stated factorial ratio is not the cardinality of standard rational parking
functions. We use the height-first convention `(m,n)=(3,2)`, meaning paths from
`(0,0)` to `(2,3)`, with three labelled north steps and two east steps. The actual
count is four, whereas the displayed ratio is `4!/2! = 12`.

The self-contained Lean 4.33.1 project checks actual north/east words, every
vertex's diagonal inequality, endpoint step counts, exhaustive column and label
records, path/column correspondence, label distinctness and increasing order,
and exactly four distinct parking functions. Natural-coefficient polynomials
are represented by finite coefficient lists with ordinary Horner evaluation.
The final theorem is a closed negation of the necessary simultaneous q=1
specializations to the actual cardinality and the displayed factorial ratio.
It is not a theorem about a hard-coded Boolean standing in for parking functions.

The width-first convention instead gives count four against 24 for `(2,3)`;
either convention contradicts a universally asserted factorial formula. Only
the declared height-first witness is advertised as kernel-checked in this package.
The other convention is explanatory, not a second theorem claimed without proof.

## Reproduction

From this directory run:

```text
python -B -X utf8 reproduce.py --repo <conjecture-checkout> --lake <Lean-4.33.1-lake>
```

The project has no external packages: `Std` is bundled with the pinned Lean
release. The reproducer checks the exact source blob, inventory, toolchain and
empty dependency manifest, independently enumerates paths and label permutations,
cleans only the project's own generated cache, rebuilds and prints every theorem's
type and axiom closure. No network dependency install is needed.

Compile `main.tex` using Tectonic 0.15.0 with `SOURCE_DATE_EPOCH=0`; `main.pdf` is
the actual compiled artifact. Complete validation also rebuilds and compares its
raw bytes. Compiler binaries and bundled Std are trusted; no compiler or full
standard-library audit is claimed.

## Scope And Disclosure

This refutes a necessary counting clause of the full enumerative assertion.
The isolated factorial ratio as a bare number has a positive q-integer product;
we do not deny that numerical fact or unrelated rational-parking-function
positivity results. Such a product cannot enumerate these actual objects at q=1.

Source and all original organizer metadata remain unmodified. AI assistance
includes the release coordinator, Hume's finite core proof contribution and
Hooke's reproducer; the final frozen-content reviewer must be a different agent.
No affiliation, human expert endorsement, first-solution credit, score or upstream
acceptance is claimed. Local review and compilation are not publication permission:
current source, complete duplicate checks, authorized WIP and release gates remain
the coordinator's responsibility.
