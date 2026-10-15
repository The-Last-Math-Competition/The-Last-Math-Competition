# Independent review of conjecture 00000005366

Verdict: PASS within the explicitly stated ordinary (restricted) star-height scope. This is not an interpretation-independent refutation of the source.

## Source and semantic scope

Read both versions in `tlmc20261015-selection/source5366.md`. Neither supplies a definition of star height choosing between ordinary and generalized conventions. Neither excludes Z² or the standard inverse-closed four-letter generating alphabet. The independent construction uses a < A < b < B, not an assumed language axiom. Under generalized height the same language is star-free, so the qualification is essential.

Ordinary convention is supported by Place and Zeitoun, Generic Results for Concatenation Hierarchies, introduction pp.1–2: https://www.labri.fr/perso/tplace/Files/TOCS18.pdf . The paper defines ordinary regex using union, concatenation and iteration, then introduces complement separately for generalized height. Pin, Open problems about regular languages, 35 years later, section 3.2 p.9, supplies the exact recursive restricted-height syntax and semantics: https://www.irif.fr/~jep/PDF/Brzozowski.pdf . These match the Lean syntax and interpretation.

## Formal audit

Reviewed every authored definition and proof in Main.lean. Eval is the actual displacement sum in Z². Geodesic quantifies over every word of equal evaluation. Canonical adds lexicographic minimality among equal-length words. The final theorem proves that actual canonical language lacks an ordinary height-zero expression; it does not assume a surrogate language or the desired contradiction.

Copied source to an independent directory; source SHA-256 c1600b00ba9fbbfc1c262b2cd3861c7a0cc72338e9bfa970ae0fe87e9e75b79f matches author's file at audit time. Lean 4.31.0 strict clean compilation passed. All 26 authored top-level declarations were audited using AllDeclarations.lean; theorem dependencies are contained in propext and Quot.sound. No sorry, custom axiom, unsafe, native_decide, extern or implemented_by occurs. Independent LEAN_PATH=. leanchecker Main passed (exit 0). Logs: compile.log, axioms.log, all-declarations.log, kernel.log.

## Written mathematical bridge

For (x,y), word length is at least |x|+|y|; equality excludes cancellation on either axis. The lexicographically first shortest word is H(x)V(y). Hence the canonical language equals (a* union A*)(b* union B*), establishing regularity and the upper bound one. For adjacent endpoints in the vertical direction, equal-time padded paths differ by at most one. For adjacent horizontal endpoints, horizontal prefixes differ by at most one and the vertical start time differs by at most one, giving distance at most two. Zero/sign crossings obey the same bound. Thus the language is a synchronous automatic structure.

Lean proves the lower bound directly. The explicit normal-form equality, regularity, fellow-traveller criterion, and upper bound one are written mathematics, not formalized results. Current report.tex accurately discloses this division. Its generalized-height limitation is correct: each c* is the complement of U(Sigma minus {c})U with U the complement of the empty language; union and concatenation suffice for the whole language.

No conclusions about the unspecified DAG conversion, state count, or depth clauses should be attributed to this formal development. A failure of the ordinary-height conjunct is enough only for that interpretation.

## Paper review

Current report.tex mathematical content PASS. Requested correction to Rees bibliography: actual PDF title is 'When Artin groups are sufficiently large ...', 22 September 2012, definitions on PDF pp.3–4. Final PDF visual inspection pending author completion.

Final PDF inspection completed: copied final report.pdf independently, rendered all three pages with pdftoppm, and visually inspected each page at 1600-pixel scale. PASS: equations, full theorem statement including negation, semantic qualification, and references are readable and within margins; no clipping or overlap. Rees reference title correction confirmed. The PDF appropriately foregrounds the ordinary-height scope in its title and abstract. Final combined verdict remains PASS under the stated ordinary scope, with the automaticity bridge supplied in prose rather than Lean.
