# Disproof of Conjecture 00000007803

Actual iid samples uniform on [-sqrt(3),sqrt(3)] are isotropic and log-concave, but their maxima are uniformly bounded. The exact normalization in the source, including any fixed multiple of its log-log correction, tends almost surely to zero and cannot converge to any positive-scale Gumbel law.

## Scope

Refutes the first distributional assertion under the stated sequence hypotheses, even with iid samples. The source does not exclude dimension one or bounded support. No alternative extreme-value normalization or definition of the additional L_K/thin-shell constants is selected. A degenerate point mass is not a nondegenerate Gumbel law.

## Formalization

Lean proves the actual conditional Lebesgue measure and its density representation, standard log-concavity, integrability and isotropic moments. It constructs the real infinite product measure, actual cylinders, marginal laws and Mathlib independence, then proves measurability and bounds for the actual running maximum. Both exact centering formulas tend to zero; original and corrected normalized maxima tend almost surely to zero. Actual event CDFs equal Mathlib pushforward CDFs and are eventually one at x=1, whereas every standard Gumbel CDF formula is continuous and strictly below one there. The formal theorem refutes the standard necessary CDF condition; the paper explains that necessity and does not claim to formalize the full weak-convergence equivalence or construct a separate Gumbel measure. All formulas consistently use sample count N=n+1.

## Reproduction

Inside lean/: `lake exe cache get`, `lake build`, and
`lake env lean -DwarningAsError=true Main.lean`.
Lean 4.19.0 and Mathlib c44e0c8ee63ca166450922a373c7409c5d26b00b are pinned.
Compile `main.tex` with Tectonic. Any supplementary root-level Python
programs are run with Python 3; none is a computation oracle for Lean.
The exact bilingual source, provenance, actual fresh-build logs, axiom
audit, artifact hashes and all-page PDF review are included. The author
agent supplied a self-review; the parent reviewed the entire frozen proof
and final artifacts separately. No external independent review is claimed.
