# Counterexample to 00000007171

For t>=1, the real symmetric2x2 matrix diag(t,1-t) has trace1, largest eigenvalue t and spectral radius t. Hence the whole fixed-trace symmetric class has no finite bound or maximizing matrix for these quantities. Every ordered trace-one pair is also strictly majorized by another actual spectrum in this class.

The source's phrase 'maximal spectrum' is underspecified; the report states these standard interpretations precisely. Positivity and norm restrictions are absent from the source. The positive-semidefinite concentration theorem is not refuted.

See `report.pdf`/`report.tex` for the complete argument and `lean/Main.lean` for the actual spectrum, supremum/attainment, whole-class no-maximizer theorem and majorization statement. Run `lake build` from `lean/` with Lean4.19.0 and the pinned Mathlib dependencies.
