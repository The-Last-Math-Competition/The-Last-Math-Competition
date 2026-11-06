# TLMC 00000003322: two edge-ideal counterexamples

Prepared for review. The package disproves the explicit regularity/matching-number equivalence under both standard normalizations. It makes no claim about the source's undefined Cohen–Macaulay-tree generalization.

- Literal ideal regularity: K2 is a bipartite forest with matching number 1, but reg I(K2)=2.
- Quotient-ring regularity: K3 has matching number 1 and reg(F2[x,y,z]/I(K3))=1, but is not bipartite.

The computations are over F2. The report gives elementary full proofs, not numerical searches. The Lean project constructs actual finite-support polynomial rings, actual edge ideals, the quotient module and its action, exact minimal graded resolutions, reduction modulo the homogeneous maximal ideal, and homogeneous cycles modulo boundaries. Both convention-specific false equivalences are combined in TLMC3322.complete_counterexamples.

## Files

- `paper.tex`, `paper.pdf`: complete mathematical report and formalization scope.
- `source.md`, `source-live.json`: exact bilingual source and live source blob.
- `eligibility.json`, `pr-padded.json`, `pr-unpadded.json`, `solution-folder.json`: before-work eligibility evidence. The complete historical snapshots were inspected locally and their hashes are recorded; the snapshots themselves are not dependencies.
- Sixteen mathematical `.lean` modules, enumerated in `theorem-manifest.json`.
- `Audit.lean`: types and axiom dependencies of all 323 top-level theorems.
- `OriginAudit.lean`: origin-module audit of all 554 theorem declarations, including generated and local declarations, among 758 authored constants.
- `verify.py`: source/gate/audit integrity checks and independent finite sanity tests.
- `make_audit.py`: regenerates the top-level manifest and printable audit from the mathematical source modules.
- `verification/`: clean build, both axiom audits, and per-module fresh kernel-replay evidence.

No admitted proofs, custom axioms, native-evaluator proof tactic, or kernel bypass are used. The only audited logical foundations are propext, Classical.choice, and Quot.sound. Choice selects finite monomial representations; representation independence of multiplication is proved. The audit metaprogram inspects proofs and does not supply proofs.

## Reproduce without installation or network access

Prerequisites already installed: Lean 4.31.0 with `lean`, `lake`, and `leanchecker`; Python 3; and a working pdfLaTeX installation with the standard AMS and Latin Modern packages/fonts. Mathematical modules use bundled Std; the origin-based audit additionally uses bundled Lean.

Run:

```sh
./VERIFY.sh
```

The script copies source only into a fresh temporary directory, builds the complete project, recompiles every mathematical module with warnings as errors, runs both axiom audits, independently kernel-replays every mathematical module, and rebuilds the PDF twice without shell escape. It performs no installation, authentication, downloads, or external mutation.

Optional environment settings:

```sh
LEAN_BIN_DIR=/path/to/existing/lean/bin ./VERIFY.sh
BUILD_PDF=0 ./VERIFY.sh
TLMC_TEXFORMATS=/path/to/existing/format/directory ./build_pdf.sh
```

`TLMC_TEXFORMATS` is only for an environment whose existing pdfLaTeX format is not in the default search path. It is not needed on a normal configured TeX installation. `build_pdf.sh` uses standard TeX search defaults as a fallback and does not depend on any sibling workspace. It explicitly selects PDF output and existing font maps. The report's PDF timestamp is fixed for reproducibility.

The development environment used pre-existing Lean binaries and a pre-existing pdfLaTeX format selected through those optional environment variables. That environment setup is separate from the clean, no-install reproduction procedure above.

## Verification scope

Polynomials have arbitrary finite support and no degree cutoff. Grading uses natural-number internal degrees and integer values of d-i; all shifts are nonnegative, so negative internal graded pieces vanish. This is a concrete minimal-resolution calculation, not a claim to implement a general integer-graded-module or Tor library.

The Python graph checks are exhaustive for K2 and K3. Its triangle test exhausts 4096 polynomial triples of total degree at most 1 and 256 pairs. These are explicitly only independent sanity checks. The unrestricted exactness, injectivity, grading and regularity proofs are Lean theorems.
