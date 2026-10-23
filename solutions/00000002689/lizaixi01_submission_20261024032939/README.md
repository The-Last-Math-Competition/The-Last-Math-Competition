# Counterexample to 00000002689

For the actual degree-two polynomial `f(z)=z²` over `Q`, the point `2` has strictly increasing iterates `2^(2^k)`, hence an infinite forward orbit and is not preperiodic. Its native logarithmic Weil height at iterate `k` is `2^k log 2`. The ordinary arithmetic mean of the first `n` orbit heights is therefore `(2^n-1) log 2/n` and tends to infinity. The corresponding means of the native multiplicative heights also tend to infinity.

The canonical height is constructed from the actual degree-normalized height limit and equals `log 2` at this point. It is not assigned as a constant. The formal proof uses Mathlib's heights defined from all absolute values and the proved rational-height formulas, the actual polynomial degree and evaluation, all iterates, finiteness of the forward orbit, genuine finite sums and real convergence.

The explicit interpretation is the ordinary, unnormalized orbit arithmetic mean. This refutes the source's finite mean-convergence clause under both standard naive-height conventions. It does not assign undefined Fourier coefficients or an orbit-frequency measure, and does not claim to refute a degree-normalized averaging statement or canonical-height and equidistribution theorems under their hypotheses.

The personal submission includes the original bilingual source, LaTeX and rendered PDF, a full pinned Lean project, exhaustive namespace axiom checks, exact build/fresh-kernel receipts and a SHA256 manifest.
