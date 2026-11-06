# Independent verification of TLMC 00000003322

Review date: 21 October 2026 UTC.

## Verdict and exact scope

The mathematical disproof, the complete Lean development, the auxiliary code, and all four pages of the final report pass independent review. The reviewed inputs are identified by `REVIEWED-INPUTS.sha256`. This is a verification record, not an assertion of official competition acceptance.

The bilingual conjecture was independently retrieved from the public repository and matches Git blob `c13f3ca1b54b390533587ff148a83be0d1800bf8`. It explicitly asserts that regularity equals the matching number if and only if the graph is a bipartite forest. Both established normalizations are addressed, without inserting a new hypothesis or changing the quantifiers. No separate claim is made about the source's undefined Cohen–Macaulay-tree generalization.

## Mathematical and semantic review

For ideal regularity, the single edge K2 is a bipartite forest and has matching number one. Its actual edge ideal (xy) in F2[x,y] is graded-isomorphic to R(-2), through the injective coefficient-shift map a ↦ xya. Its regularity is therefore two, disproving one direction of the equivalence.

For quotient regularity, K3 has matching number one and is not bipartite. Over S=F2[x,y,z], its actual edge ideal is J=(xy,xz,yz). The displayed sequence

0 → S(-3)^2 → S(-2)^3 → S → S/J → 0

is exact and minimal. The first map has columns (z,y,0) and (z,0,x). For a kernel vector (a,b,c), coefficient restrictions and cancellation give c=xc′, b=yb′, and a=z(b′+c′), proving that these two columns generate the entire kernel. Their map is injective. The quotient is constructed with well-defined module operations, a surjective projection, and kernel exactly the edge ideal.

The proof does not merely calculate a supplied degree table. The actual polynomial rings, least-ideal edge generators, module maps, exactness, shifts, and minimality are proved. Coordinate reduction has kernel exactly the homogeneous maximal ideal times the free module. The induced residue differentials descend from the polynomial maps and vanish. Explicit cycles outside the boundary images are proved equivalent to the Betti support. The quotient support is exactly (0,0), (1,2), (2,3), giving regularity one and disproving the other direction.

The finite-support polynomial definitions have no fixed degree cutoff. Internal degrees are natural numbers; all exponents and shifts are nonnegative, so negative graded pieces vanish. Regularity uses the integer difference d−i. The report accurately describes this concrete construction rather than claiming a general Tor or integer-graded-module library.

## Executed verification

- Copied source only into an independent directory, without `.olean` files or build caches.
- Built and strictly checked all 16 mathematical modules under Lean 4.31.0, with warnings treated as errors; both final audit modules also passed strict checks.
- Checked all 323 top-level theorem types and axiom lists.
- Independently audited every theorem declaration by originating module: 554 theorem declarations among 758 authored constants, including generated and local declarations. Only `propext`, `Classical.choice`, and `Quot.sound` occur. No authored axiom or proof bypass was found.
- Independently kernel-replayed every mathematical module with `leanchecker`.
- Executed the exact final package's `VERIFY.sh` successfully, including Python integrity/finite checks and the PDF rebuild. Regenerating the printable audit and theorem manifest reproduced identical files.
- Independently checked the triangle's finite-degree matrix kernels through coefficient degree eight as supplementary diagnostics, not as a substitute for the unrestricted Lean proof.
- Rechecked all 34 reviewed source/report/evidence input hashes after the final assembly. No mathematical source or report changed.

The included logs are the actual successful executions. The final portable run is in `logs/final-portable-verifier.log`; its detailed build, top-level audit, origin audit, kernel replay and PDF logs are included. The separate independent audit source and generation script are included for inspection. Standard installed Lean, Python and TeX tools were used; no installation, authentication, external mutation or publication was performed by this review.

## PDF review and reproducibility

The LaTeX source was independently rebuilt twice, without shell escape, using the documented option for an existing pdfLaTeX format. The result was byte-identical to the submitted PDF. Every rendered page was visually inspected: page 1 covers source scope and conventions; page 2 contains the two resolutions and exactness argument; page 3 completes the regularity calculation and accurately maps the formal coverage; page 4 contains reproduction details and verified references. Equations, fonts, symbols, links, margins and page transitions are readable, with no missing glyphs, clipping, overlap or unfinished content.

- `paper.tex` SHA-256: `74b8015e4d8e2a8ee51652aa7f89658e825d71b111e82e30d3a894db9b281a9c`
- `paper.pdf` SHA-256: `17cd2d527d549db5cea85f88710360ee549471f9a7a9416e9dceb260109d3393`
- PDF: four pages, 324,378 bytes.

Eligibility evidence was independently checked against the supplied complete snapshots, but a fresh publication-time eligibility gate remains a separate responsibility. This record authorizes no publication and makes no claim about submissions arriving after those snapshots.

## Sources

- [Exact conjecture at the reviewed repository commit](https://github.com/The-Last-Math-Competition/The-Last-Math-Competition/blob/b355e42906e6eaf52bc7e9d005e0ef02d8aa7400/conjectures/00000003322.md).
- [Banerjee, Kara and Ha, Regularity of Edge Ideals and Their Powers](https://arxiv.org/pdf/1712.00887), Sections 2.2–2.3, for the minimal-resolution characterization and ideal convention.
- [Biyikoglu and Civan, Prime graphs, matchings and the Castelnuovo–Mumford regularity](https://doi.org/10.1216/JCA-2019-11-1-1), introduction, for the quotient convention.
