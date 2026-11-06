# Parent adversarial review: 00000009634

Verdict: PASS

Parent read the exact bilingual source, the complete frozen Main.lean and
its amended general state-emission constructor, the full author proof and
self-review, exact auxiliary program, actual author logs and final fresh
build evidence, and all four final rendered pages. This is an internal
parent review of an agent-developed proof, not external independence.

The source's first equality is actually false: full ordinary Hankel rank
need not equal the minimum number of nonnegative hidden states. The model
is a real stationary four-symbol Markov process with the explicit matrix
P=(I+C4)/2 and uniform pi. P has genuine nonnegative normalized rows and
columns, pi P=pi, and every word probability is the actual normalized
matrix-product probability. Both left and right cylinder consistency hold
for ALL words and the empty word has probability one. The support language
is proved exactly equal to the paths in the explicit four-vertex labelled
graph; its self-loops ensure extension to bi-infinite paths. This supplies
the usual finite labelled presentation, in fact a shift of finite type.

The HMM class permits arbitrary nonnegative normalized symbol-transition
matrices and arbitrary initial distribution. Parent identified and repaired
a timing-convention gap in the explanatory bridge: the new generic
fromStateEmission constructor uses E_i(a)Q_ij, emitting before transition,
and verifies all normalization conditions for arbitrary mu,Q,E. It therefore
covers ordinary current-state HMMs without requiring stationarity of a
competitor. The concrete witness uses Q_ij E_j(a), observing after a
transition, which is harmless because its actual pi is stationary.
The final paper explicitly distinguishes these two conventions.

The full Hankel is literally Matrix Word Word Real for ALL finite words,
including empty ones. Every future vector satisfies f3=f0-f1+f2, including
the empty-word vector. The whole infinite matrix factors through three
actual real columns, and a genuine span inclusion proves its actual
Mathlib Matrix.cRank is at most three. The actual singleton-word 3x3 minor
has determinant1/512 and rank three; the submatrix-rank inequality proves
the matching lower bound. Neither transition rank nor a finite experiment
is substituted for the infinite column-space dimension. Subtraction in the
linear factorization is correctly allowed, and never treated as probability.

For EVERY n-state competing model realizing all words, its actual
length-two probability matrix admits a nonnegative n-column factorization
using reach and future vectors. Four positive diagonal entries each select
a positive product. If two selected hidden indices collide, positivity
forces both crossed products positive, contradicting an actual crossed zero
and the nonnegative term-to-sum bounds. This is an explicit injection from
four symbols to hidden states, so n>=4, including the n=0 boundary.
The concrete HMM4 witnesses attainment. IsLeast proves the actual minimum
hidden-state count equals four, and the final theorem directly denies any
realization with cRank.toNat=3 states. No competing model is assumed to use
the same transition matrix, support graph or deterministic observation.

Parent's independent Fraction program checks genuine matrix-product
probabilities and normalization through length6, support paths, an85x85
factorization sample, minor1/512 and all crossed zeros. This is supplemental
only. The final submission's full Lean project was built in a new directory;
complete lake build, strict Main and auxiliary verification all exited zero.
Official dependency revisions and tracked-source cleanliness were checked.
All printed principal axioms are the three standard foundational axioms.
No placeholders, custom axioms or numerical rank oracle are used.

The exact final TeX passed native compilation and zero-warning Tectonic.
Parent inspected all four final pages, including the repaired theorem-name
line and less-dense references: complete readable proof, matrices and
reproduction, with no clipping or overlap. Scope is the first equality
conjunct only; learning complexity and geometric isolation are not claimed
as independently settled.


Reviewed artifact hashes:

- Main.lean: `ca81d6a6e852a777b38f7d9cb02385da754c5c0c03d35824288446cb6b7e7eea`
- main.tex: `d30877c2edbe9fac4535fc8a02d64678cb0754dbdbed3eb10b25801a92360fef`
- main.pdf: `3bce0df78fcf4afab78bf8978d460d9d4c8f614e61e3ce29e90fe11da5f03f7b`
- SOURCE.md: `697fd9d5216832ed98a11643b269798352f2158e20e6522e131e864eef154a51`
