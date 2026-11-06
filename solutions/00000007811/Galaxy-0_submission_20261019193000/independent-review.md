# Independent review: TLMC 00000007811

Review date: 2026-10-19 UTC. Review completed on the corrected `solution.tex` and `solution.pdf` identified below. This is a pre-submission independent review, not a review or acceptance by the competition maintainers. No publication, push, or pull-request action was performed.

## Verdict

**Pass, with the explicitly stated semantic scope.** The printed claim that the natural map from the Chow tautological ring `R*(M_g)` to the Chow ring `A*(M_g)` has a nonzero kernel for every `g >= 8` is false under the standard meaning of these objects. The inclusion has zero kernel, including at genus 8 and in degree 4. The report gives a complete mathematical argument for this disproof. The Lean project proves the universal generated-subring inclusion result and its genus-indexed consequence, without axioms or proof holes.

This verdict does **not** certify a Lean construction of moduli spaces, Chow rings, or tautological characteristic classes. These are not implemented, and the report says so. The formal proof establishes the general fact that applies by the externally documented definition. It also neither establishes nor refutes the separate alternating-relations/cohomology clause, and it does not disprove Faber's Gorenstein conjecture. Refuting the asserted nonzero kernel suffices to refute the printed conjunction.

Two bibliographic defects found during review were corrected before this verdict: the original report gave the wrong title for Vakil's linked paper, and its MIT Pixton URL returned HTTP 404. Both final references are verified below. No remaining mathematical or rendering defect was found.

## Original statement and independent provenance check

I read both the English and Chinese statement in full. Both explicitly assert a nontrivial kernel of `R*(M_g) -> A*(M_g)` for `g >= 8`, with the first nontrivial relation in degree `g - 4`.

I separately fetched `conjectures/00000007811.md` from `The-Last-Math-Competition/The-Last-Math-Competition` with the GitHub file connector. The returned original matched `source-conjecture.md` **byte for byte**, checked in Python rather than inferred from appearance.

- Source: <https://github.com/The-Last-Math-Competition/The-Last-Math-Competition/blob/main/conjectures/00000007811.md>
- Returned Git blob SHA: `2d3cb16d8dd358abc2db1b129e41a30333194687`
- SHA-256 of the exact source: `7e89cddb8e693c30090c2fbd6c2868d95961d4e8bc586f7366381eaa4d1057ea`
- The connector response, including original content and blob identity, is preserved in `verification/independent/original-fetch.json`.

The working report is named `solution.tex`; no separate file named `fullsolution.tex` exists in this submission.

## Semantic review

### Why the interpretation is justified

The source supplies a short definition by tautological generators and names the target as the Chow ring. In this setting the standard Chow tautological ring is the subring of actual Chow classes, not a free ring of formal symbols. This is not a definition invented to force injectivity:

1. Ravi Vakil, *The moduli space of curves and Gromov-Witten theory*, §3.1, printed page 13, explicitly defines the tautological ring inside the Chow ring using kappa classes. I read the supplied downloaded text around §3.1 and independently opened the primary PDF. I also rendered and visually inspected its page 13. The immediately preceding discussion distinguishes working in Chow from working in cohomology; the following displayed identity explains that lambda classes are determined by kappa classes.
   Primary source: <https://math.stanford.edu/~vakil/files/cimefeb19.pdf>.
2. Aaron Pixton, *The tautological ring of the moduli space of curves*, Princeton dissertation, June 2013, §2.2, printed page 7, defines tautological rings as subrings of rational Chow rings and explains the smooth-locus generators. Its abstract and introduction are consistent with that definition. I opened the final cited URL, downloaded the author's Michigan copy, extracted text, and rendered and visually inspected PDF page 15 (printed page 7).
   Primary source: <https://websites.umich.edu/~pixton/papers/tautological.pdf>.
   The independently downloaded equivalent author-hosted URL was <https://public.websites.umich.edu/~pixton/papers/tautological.pdf>.

Thus the map induced by taking the same tautological classes in Chow is the inclusion. The conjecture specifies no alternate source, quotient, or map that would override this standard interpretation. A polynomial/strata presentation can have a nonzero evaluation kernel, but its source is not the tautological subring after relations. A cycle-class map has a cohomology target, not the printed Chow target. A cohomological tautological ring also does not by that definition furnish the claimed reverse map into Chow. Replacing the printed map with one of these would change the problem.

The disproof therefore supports the literal standard Chow-theoretic reading. It does not resolve an unspecified intended repair of the problem. The word “alternating” is insufficiently explained in the other clause, but that is not needed for this contradiction.

### Mathematical completeness

- Subring elements are ambient elements together with membership. Equality of their ambient images implies equality in the subring.
- The subring zero is the ambient zero with its membership proof. Therefore the inverse image of ambient zero contains exactly that element.
- At genus 8 the asserted universal lower bound applies, while the inclusion has zero kernel. This supplies the required contradiction.
- Restricting the domain to any degree cannot create a nonzero kernel element. In particular no such witness exists in degree `8 - 4 = 4`.
- No computation of the dimension of the Chow ring, existence of an unusual algebraic cycle, or unproved geometric theorem is used. The definition of the subring is the entire external semantic bridge.

## Lean source audit and coverage

I read all of `lean/Main.lean`, `lean/Audit.lean`, the Lake configuration, toolchain declaration, README, and the complete LaTeX report.

- `Main.lean:7-23`: `Operations` contains ambient operations. `Generated` is their inductive closure on **ambient elements**, including zero, one, chosen generators, sums, products, and negatives. This is not a formal expression algebra.
- `Main.lean:25-32`: `GeneratedSubring` is the membership subtype; `inclusion` is value projection; `subringZero` is the actual ambient zero with its construction proof.
- `Main.lean:35-47`: injectivity is proved with `Subtype.ext`, then the exact zero-kernel equivalence is proved. Injectivity is not a hypothesis.
- `Main.lean:49-55`: nontriviality means a genuinely nonzero subtype element whose image is zero. Its negation follows from the preceding equivalence.
- `Main.lean:59-67`: the genus claim is a universal statement for every natural number at least eight, for arbitrary genus-indexed ambient carriers and generators. Its negation is proved by specializing at eight. The numerical check `by decide` is kernel-checked ordinary reduction, not `native_decide`.
- `Main.lean:70-74`: an arbitrary degree predicate is allowed; a nonzero kernel witness under any such predicate is impossible. This is stronger than the particular needed degree exclusion, but is not a construction of a graded Chow ring.

Absence of ring laws does not weaken the applicable injectivity result: it proves a stronger elementary subtype fact. For a rational subalgebra one may include the rational constants among the generator predicate. No axiom about the actual geometry, or already-proved injectivity, is inserted. The fact that the construction is named `GeneratedSubring` should not be mistaken for a bundled Lean ring structure; only the carrier and operations needed for this theorem are modeled, exactly as disclosed in the report.

Manual source inspection and a text search found no `sorry`, `admit`, declared custom axiom, `unsafe`, `implemented_by`, `native_decide`, or kernel-bypass setting in the proof. Each of the five audited theorems reports no axiom dependencies. Proof irrelevance here is part of Lean's underlying type theory; “no axioms” refers to the actual `#print axioms` result, not an assertion that no foundational logic is trusted.

## Executed clean build, audit, and kernel replay

I created a new directory containing **only** `Main.lean`, `Audit.lean`, `lakefile.toml`, and `lean-toolchain`. It had no copied `.lake` directory, object files, or manifest. The fresh build generated its own manifest. The compiler's installed standard library was used; this review does not claim to rebuild Lean itself.

Executed from `verification/independent/source-only`:

```sh
export PATH=/workspace/scratch/76cdbd0d1d68/tlmc20261008/toolchain/bin:$PATH
which lean lake leanchecker
lean --version
find . -type f -print
lake build
lake env lean -DwarningAsError=true Main.lean
lake env lean -DwarningAsError=true Audit.lean
lake env leanchecker Main
lake env leanchecker Audit
```

**All commands succeeded.** Lean identified itself as 4.31.0, release commit `68218e876d2a38b1985b8590fff244a83c321783`. Lake built both targets. Both direct elaborations passed with warnings promoted to errors. The five axiom results were empty. Both kernel replays exited successfully; silence is their successful output, not a missing run. The shell used `set -eu`, and command tracing and output are saved in `verification/independent/clean-build-audit-kernel.log`.

After the reference fixes, `cmp` confirmed that the final `Main.lean` and `Audit.lean` remained byte-identical to those clean-built sources.

## PDF reconstruction and every-page visual review

I checked the supplied PDF metadata, extracted its full text, and rendered **both** final pages afresh with:

```sh
pdfinfo solution.pdf
pdffonts solution.pdf
pdftotext -layout solution.pdf verification/independent/solution-extracted.txt
pdftoppm -r 110 -png solution.pdf verification/independent/page
```

I opened and visually inspected `verification/independent/page-1.png` and `page-2.png`, including after the bibliographic corrections.

- Page 1: title, abstract, problem statement, corrected sources, zero-kernel proposition and proof, and genus-8 contradiction are complete and legible. Kappa, lambda, genus subscripts, the inclusion, zero symbols, and degree four render correctly. The hyperlink boxes do not obscure the text.
- Page 2: presentation/cycle-class distinctions, formalization scope, all five listed theorem claims, and reproduction commands are complete and legible. No clipped code or missing math glyphs were found.
- Both pages have consistent margins, numbering, and readable typesetting. No overlapping or cut-off content was found. All listed fonts are embedded.

I also copied **only the final LaTeX source** to `verification/independent/pdf-source-only` and compiled it twice with:

```sh
pdflatex -no-shell-escape -interaction=nonstopmode -halt-on-error solution.tex
pdflatex -no-shell-escape -interaction=nonstopmode -halt-on-error solution.tex
```

The first attempt with the default environment failed because this restricted installation could not locate `pdflatex.fmt` or write its default home-directory cache. This was an environment issue, preserved in `pdf-source-only/initial-missing-format.log`. I reran using the existing installed-font search paths and cached format described in the provided build environment:

```sh
export TEXINPUTS=/usr/share/texlive/texmf-dist/tex//:/usr/share/texmf/tex//:
export TFMFONTS=/usr/share/texlive/texmf-dist/fonts/tfm//:/usr/share/texmf/fonts/tfm//:
export T1FONTS=/usr/share/texlive/texmf-dist/fonts/type1//:/usr/share/texmf/fonts/type1//:
export ENCFONTS=/usr/share/texlive/texmf-dist/fonts/enc//:/usr/share/texmf/fonts/enc//:
export TEXFONTMAPS=/usr/share/texlive/texmf-dist/fonts/map//:/usr/share/texmf/fonts/map//:
export TEXFORMATS=/workspace/scratch/76cdbd0d1d68/tlmc20261008/reports:
export TEXMFVAR=/tmp/tlmc-tex-var
```

Both compilations then succeeded. Extracted text of this clean reconstruction matched the final submitted PDF **exactly** using `cmp`. The PDF binaries are not asserted identical, because rebuild metadata can differ. A warning about the default `pdftex.map` remains, but the source loads the needed Latin Modern and AMS maps explicitly; font embedding and visual inspection passed. The first-run hyperlink rerun warning cleared on the second run. No overfull boxes or missing characters were found.

For the primary-source verification I also executed:

```sh
curl -fL --retry 0 'https://public.websites.umich.edu/~pixton/papers/tautological.pdf' -o verification/independent/pixton-tautological.pdf
pdftotext -layout verification/independent/pixton-tautological.pdf verification/independent/pixton-tautological.txt
pdftoppm -f 15 -l 15 -r 110 -png verification/independent/pixton-tautological.pdf verification/independent/pixton-source-page
pdftoppm -f 13 -l 13 -r 110 -png ../tlmc20261019-selection/vakil-tautological.pdf verification/independent/vakil-source-page
```

Pixton's source PDF causes Poppler warnings about an unknown `Black` operator. Text extraction and the relevant page rendering still succeed, and I verified that page visually. Those warnings concern the external reference PDF, not `solution.pdf`. I inspected the relevant primary-source sections, not all 133 pages of Pixton's dissertation or all 54 pages of Vakil's paper; neither full-document review is needed for the cited definitions. Downloaded reference PDFs are local review material and need not be included in a submission package.

## Final reviewed SHA-256 identities

```text
7e89cddb8e693c30090c2fbd6c2868d95961d4e8bc586f7366381eaa4d1057ea  source-conjecture.md
83800f3ffb05f31c4ef8efaaa2c5cc6416de157aba99d6d74d471a1f107f9949  solution.tex
58ae76ac5245469cc169c9df76ef0f8ee784bdcf1085063f9e45e0d9e8cc8086  solution.pdf
009456ebdb82770fc1d761965dedfc3c4e6871a7b707925f5800ae57159d0c47  lean/Main.lean
be674375b8b07955beac881708070b90a3f8dadd89bebf670095a84b62cb74ab  lean/Audit.lean
70cd95c8b5259f7374afb1e9694e306f86b0d6a4bed8f5a42d115f5df06e5a50  lean/lakefile.toml
efac0b94923b2d8b6840cd35be9177ad0fc5ab2332f4f4311c98712cee92fdee  lean/lean-toolchain
ba2d7926604adfa6e3101d50bee381c84afa695bcaa7a78a1c0011d353388a5d  lean/lake-manifest.json
4ceeb5367ce0bfbac1bd47a01948854c0400281140c0583d6fe9f4c8fc9ab92b  README.md
c66894f55d2aa1280240e87b979f225bdd14ff8f5647e26985ee943e4eac8932  build-pdf.sh
d3f86c2b79979703babfd9eea61fc5006ed11bc4a3bdae0108fc72b8bffaa9e6  verification/independent/page-1.png
0554278becb607dcc093c5723fa2fbce01f329ae60690ca9d6a88814b664706e  verification/independent/page-2.png
e2cf7c1a195bd964c263beb011173e6425697ff3a07ee444331bf3b2084ac67a  verification/independent/clean-build-audit-kernel.log
b0cee73cf1b721d8a6e26597a1c735940de55a73bbfac38348c2e825d8b45af6  ../tlmc20261019-selection/vakil-tautological.pdf
a089fc8dbe9e569bb9ad4dd0e7417960d0048e6a2fbf6498ce0cb240965f87fe  verification/independent/pixton-tautological.pdf
```

## Remaining limitations

The kernel, installed standard library, compiler/toolchain provenance, and conventional mathematical definitions are part of the trust boundary. The review did not rebuild the toolchain, formalize algebraic geometry, decide the undefined alternating-cohomology clause, or assess a conjecture with a different map. No external numerical auxiliary program is needed for the mathematical result. The review also does not assert repository eligibility, priority, or eventual maintainer acceptance; those are separate checks.

Within these disclosed boundaries, the final report, actual formal theorem, and printed conjecture's kernel clause match. No unresolved blocking defect remains.
