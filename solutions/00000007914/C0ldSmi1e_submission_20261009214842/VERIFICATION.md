# Local verification of 00000007914

The final Lean source has SHA-256 `0bf9a035b94cb234d993036532fa30ec755dfbf52e6eeb125e1f8eb4557867d8`. An independent reviewer read the full bilingual original, Lean source, and report. The supplied `SEMANTIC_REVIEW.md` records its exact scope and hashes; final layout changes were separately checked without changing mathematical assertions.

A separate fresh project used only the final authored source/configuration and neutral stock dependency caches. No author-produced proof build artifacts were copied. The exact delivered `lean/verify.py` passed its full run: 42 commands, clean project build, strict replay of both Lean files, all twelve complete theorem types and all twelve standard-only axiom reports. The five proof/configuration hashes and nine pinned stock dependency revisions were checked before and after; tracked stock sources were clean. The complete command outputs are consolidated in `verification/independent-commands.log`; individual proof/type/axiom outputs and machine-readable records are also included.

The axioms are only `propext`, `Classical.choice`, and `Quot.sound`. No admitted proof, custom axiom, unsafe proof shortcut, or native decision shortcut appears in the authored sources. A scoped lexical scan supplements exact source hashes and kernel checks; it is not a general Lean parser. Stock Mathlib/dependency caches are reused, not rebuilt entirely from source.

The final LaTeX source compiled successfully in the desktop editor and exported successfully with no warnings. All three PDF pages were rendered and visually inspected. The PDF/source hashes and final layout observations are in `verification/pdf-review.json`. The report and Lean include finite-liminf nonnegativity, addressing the Chinese wording explicitly.

There is no separate numerical computation to reproduce: the order, logarithmic limit, asymptotic transfer, measure and limiting interfaces are proved in Lean. Mathematical applicability, kernel verification, document checks and repository eligibility are distinct checks. These records do not assert maintainer acceptance or passing GitHub CI.

The same verifier was subsequently run on the assembled personal submission directory and again passed all 42 commands, including a new project build. Its exact command/status record is `verification/installed-package-result.json`; the proof/configuration hashes are unchanged.
