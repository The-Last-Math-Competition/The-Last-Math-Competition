# Disproof of TLMC 00000004091

Galaxy-0, AI-assisted submission, 14 October 2026.

## Result

For one particle, the usual unordered configuration space is homeomorphic to the graph's topological realization. The finite simple connected graphs K2 and C4 both have chromatic number 2, but their rational first Betti numbers are 0 and 1. Thus chromatic number does not determine this Betti number, even by an arbitrary function. The conjecture's polynomial clause is false already at n = 1. Its subdivision-invariance clause is true and is not disputed.

The counterexample idea previously appeared in orionsheep's [PR 292](https://github.com/The-Last-Math-Competition/The-Last-Math-Competition/pull/292), using P4 and C4. That submission was closed without merging because its Lean result formalized only disconnected arithmetic facts. We credit the earlier mathematical observation. See `PRIOR_SUBMISSION.md` for the complete review issue and the present repair.

## Formalization and explicit boundary

`lean/Conjecture4091/Basic.lean` imports only Std and uses Lean 4.31.0. It defines finite simple graphs by oriented endpoints, genuine proper colorings and chromatic minimality, the rational incidence boundary, its cycle kernel, and a dimension certificate with spanning and unique coefficients. It proves the K2 kernel has an empty basis and the C4 kernel has the all-one basis. The conclusion `TLMC4091.conjecture_00000004091_false` refutes the universal property `ChromaticDeterminesFirstBetti` using these actual graph invariants.

The mathematical report explicitly constructs each graph realization, identifies these coordinate spaces and the boundary with cellular chains, invokes cellular-to-singular homology comparison over Q, and proves Conf_1(|G|) is homeomorphic to |G|. Those topology bridges are paper mathematics, not Lean theorems or added axioms. This package must not be described as a complete Lean formalization of singular/configuration-space topology. The competition's reviewers decide whether the disclosed formalization boundary meets their requirements.

No Betti numbers or chromatic numbers are assigned as unexplained labels. No `sorry`, `admit`, `native_decide`, custom axiom, or unsafe declaration is used. Authored theorems depend only on standard logical axioms `propext`, `Classical.choice`, and `Quot.sound`, as applicable.

## Files

- `solution.tex`, `solution.pdf`: complete mathematical report and compiled PDF
- `lean/`: final source-only Lean project, including independent Audit.lean
- `empirical.py`: exact rational matrix ranks, exhaustive coloring, and enumeration of all 1,099 labeled simple graphs of orders 1 through 5
- `review/independent.py`: independently implemented exact witness checks
- `PRIOR_SUBMISSION.md`: prior submission and semantic repair
- `VERIFICATION.md`: commands, outcomes, formalization boundary, and visual QA
- `evidence/`: fresh clean-build, kernel, axiom, computation, PDF, and live-eligibility evidence
- `verify.sh`, `build_pdf.sh`: reproduction helpers
- `SHA256SUMS`: SHA-256 checksums of all other packaged files

## Reproduce

Install or select Lean 4.31.0 so `lean`, `lake`, and `leanchecker` are on PATH. Python 3 needs only its standard library. No Mathlib or external Lean packages are required.

```sh
bash verify.sh /tmp/tlmc4091-clean
```

The output directory must not contain an existing `lean/` tree. The script copies only the final Lean sources, creates a fresh build, runs strict elaboration, compiles the independent audit, separately kernel-replays all three modules, scans for unsafe/admitted declarations, and executes both Python checks. The result and logs remain in the requested output directory; the submission stays source-only.

Manual core commands are:

```sh
cd lean
lake build
lake env lean -DwarningAsError=true Conjecture4091/Basic.lean
lake env lean -DwarningAsError=true -o .lake/build/lib/lean/Audit.olean Audit.lean
lake env leanchecker Conjecture4091.Basic
lake env leanchecker Conjecture4091
lake env leanchecker Audit
```

A regular LaTeX installation with pdfLaTeX, Latin Modern, AMS packages, geometry, microtype, xurl, and hyperref can rebuild the PDF:

```sh
bash build_pdf.sh /tmp/tlmc4091-pdf
```

On a minimal image with TeX sources/fonts but no format-search index, a second argument may name a directory containing a compatible `pdflatex.fmt`. The helper then exposes the existing Debian TeX paths. The PDF uses explicit Latin Modern and AMS symbol font maps. PDF binary hashes may vary between rebuilds because of creation metadata; inspect the reproduced output rather than expecting its hash to match.

To check the frozen submitted bytes:

```sh
sha256sum -c SHA256SUMS
```

## Eligibility snapshot

At 2026-10-14 19:46 UTC, upstream main was `cce2d90cb298de9595798eb674d2c80712100532`. Conjecture source blob was `73f51cfa010d743d7f2363be23ee139f9c819802`; metadata marked neither proven nor disproven and the solutions path returned 404. All-state full-ID and Betti/subdivision searches found the closed, unmerged PR 292; it is acknowledged above. Short-ID and configuration/chromatic searches returned no matches, demonstrating why a single search was insufficient. The complete responses and direct prior-PR fetch are preserved in the evidence JSON. This is a historical check, not a guarantee against later or unpublished submissions.

Only this personal submission directory is proposed. No conjecture, root README, metadata, leaderboard, other solution, or repository state has been changed by preparing this package.
