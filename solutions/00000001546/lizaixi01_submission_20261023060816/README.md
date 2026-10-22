# Conjecture 00000001546: necessary growth clauses conflict

Both source languages assert upper growth n*exp(O(sqrt(log n))) AND that no polynomial upper bound exists. For every real C and x>=1, square nonnegativity gives C*sqrt(log x)<=log x+C^2/4, hence x*exp(C*sqrt(log x))<=exp(C^2/4)*x^2. The claimed upper growth is therefore O(n^2).

Lean treats the O inside the exponential directly: h=O(sqrt(log n)) implies n*exp(h(n))=O(n^2), with eventual equality transfer. It also proves the envelope Big-O transitivity route and one-sided nonnegative/natural-count variants. Final theorems quantify every candidate function and refute the printed necessary conjunction. No actual geometric count is assigned. No sharp halving-line result, interpretation of the imprecise geometry, or denial of the compatible lower bound is claimed.

Polynomial upper bound means O(n^d) for some fixed natural exponent; d=2 is an explicit witness. The actual real log, sqrt, exp, eventual equality and Mathlib Asymptotics.IsBigO are used. All 11 theorems have transitive axiom audits.

Included: complete original bilingual SOURCE.md; report.tex/report.pdf; pinned Lean 4.33.0 / Mathlib project; new build, axiom audit and full official fresh-kernel replay; source-bound evidence, final eligibility/review and SHA256 manifest. OpenAI Codex assisted, with separate supervising AI review. Organizer acceptance is pending.
