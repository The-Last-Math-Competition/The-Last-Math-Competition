# Disproof of Conjecture 00000001715

For every irrational alpha and every positive frequency k, the actual coefficient c_k = (1 - exp(2 pi i k alpha))^(-1) is well defined and has modulus at least 1/2. It therefore cannot tend to zero; alpha = sqrt(2) gives an explicit counterexample to the source's stated decay assertion.

## Scope

Refutes only the explicit necessary assertion that the displayed coefficients c_k form a decaying sequence, present in both source languages, and thus the conjecture as written. It does not assert that the entire LLT is false under other formulations, analyze the correction's low-frequency criterion, or exclude decay of products with Fourier coefficients of a smooth function. No unboundedness claim is made.

## Formalization

Lean uses actual Complex.exp, standard Irrational, complex norm, and Filter.Tendsto. It proves denominator nonvanishing for all positive integer frequencies, the uniform modulus lower bound 1/2 for every irrational parameter, failure of convergence to zero, and an explicit irrational sqrt(2) witness. The universally quantified DecayAssertion is negated by disprove_decay_assertion. All mathematics of the paper's displayed theorem is formalized; the source-reading argument is explicitly separated. Only propext, Classical.choice, Quot.sound occur in the audited theorem axioms.

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
