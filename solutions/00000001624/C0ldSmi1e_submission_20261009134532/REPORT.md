# A literal disproof of conjecture 00000001624

The requested spectrum does not exist under the standard meaning of a real Cantor set
and an internal spectral gap. Every closed, positive-Lebesgue-measure subset of the real
line with empty interior has a bounded complementary gap. This obstruction applies to
all potential models and all spectral-measure conditions.

## Exact source

> **English.** Conjecture: There exists a quasiperiodic potential whose spectrum is a positive-measure Cantor set with no gaps while the spectral measure is singular (an explicit construction of gapless singular spectra).
>
> **中文。** 猜想：存在拟周期势使谱为正测度 Cantor 且无隙,同时特征测度奇异(无隙奇异谱的显式构造)。

The exact source bytes and both rule files are retained in `source/`. The original file's
SHA-256 is `53acb6877d3ac08f6469e5f63d03a4de0e22fe4a402699415ee499682705a77a`.

## Definitions and scope

For a real set S, a bounded internal gap is an interval (a,b), where a<b, both endpoints
belong to S, and (a,b) is disjoint from S. For a closed set, this is the usual bounded
connected component of its complement. The proof below and the Lean theorem
`IsGap.component` establish the component assertion explicitly. Unbounded exterior
components do not count as internal gaps, and an arbitrary proper subinterval of a gap
does not count as an entire gap.

A real Cantor set is nonempty, compact, perfect, and nowhere dense. Mathlib's `Perfect`
means closed with every point an accumulation point. For a closed set, nowhere density
is equivalent to empty interior. The formal definition `IsRealCantor` uses these standard
properties and imposes no zero-measure condition. In particular, the contradiction does
not come from erroneously defining every Cantor set to have measure zero.

Positive measure means positive Lebesgue measure. “No gaps” means no bounded internal
gap anywhere in the spectrum. For closed real sets, `hasNoGaps_iff_ordConnected` also
proves equivalence with containing every real point between any two of the set's points.

This global condition differs from the absence of a gap at one selected energy. For
example, [0,1] ∪ [2,3] contains a neighborhood of energy 1/2 and nevertheless has the gap
(1,2). That distinction is verified in `Verification.lean`. Neither source language
supplies a reference energy or a different restricted meaning of “gapless.” This disproof
addresses the literal standard real spectral-gap statement; it does not decide a revised
claim using an energy-specific meaning or a different nonstandard definition.

## General geometric obstruction

**Theorem.** Let S be a closed subset of ℝ with empty interior and positive Lebesgue
measure. There are finite real numbers a<b such that a,b∈S and (a,b)∩S=∅. Moreover,
(a,b) is a full connected component of ℝ\S.

**Proof.** A set with at most one point has Lebesgue measure zero. Therefore S contains
two distinct points; write them as x<y. The open interval (x,y) cannot be contained in S,
since a nonempty open interval contained in S would be contained in its interior. Choose
c∈(x,y)\S.

Put L=S∩(-∞,c] and R=S∩[c,∞). L contains x and is bounded above by c; R contains y and
is bounded below by c. Both are closed. Consequently

    a = sup L ∈ L,              b = inf R ∈ R.

In particular a,b∈S, a≤c≤b. Since c∉S, neither endpoint is c, so a<c<b. Let t∈(a,b).
If t∈S and t≤c, then t∈L, implying t≤a, a contradiction. If t∈S and c≤t, then t∈R,
implying b≤t, another contradiction. Every real t satisfies one of these alternatives.
Thus (a,b) is disjoint from S.

For completeness, let C be the connected component of ℝ\S containing c. The interval
(a,b) is connected, lies in ℝ\S, and contains c, so (a,b)⊆C. Conversely, a connected
subset of the real line contains the interval between any two of its points. If C
contained t≤a, then it would contain a between t and c, contradicting a∈S. If C
contained t≥b, it would similarly contain b, contradicting b∈S. Hence C⊆(a,b), so
C=(a,b). This proves the theorem. ∎

The argument uses neither compactness nor perfection; it applies to all closed sets
with empty interior and at least two points. Positive measure is used only to ensure the
last property.

## Application to the conjecture

Suppose a potential satisfying the source existed, and let S denote its real spectrum.
The Cantor requirement makes S closed with empty interior; the positive-measure
requirement supplies positive Lebesgue measure. The theorem produces an internal gap of
S, contradicting “with no gaps” / “且无隙.” Thus no such potential exists, and in
particular no explicit construction with the requested properties can exist.

This is a universal obstruction. It does not select a particular quasiperiodic model,
frequency, coupling, regularity class, boundary condition, or spectral type. The Lean
theorem `no_source_potential` quantifies over an arbitrary type of potentials, an arbitrary
map assigning a real spectrum to each potential, and arbitrary predicates for
quasiperiodicity and singular spectral measure. A conjunction already contradicted by
its geometric properties cannot become satisfiable when these further conditions are
imposed. Consequently no formal definition of those unused analytic conditions is needed
for the logical reduction. The precise source-to-theorem mapping is in
`SOURCE-MAPPING.md`.

中文说明：这里“无隙”按通常的整体谱意义理解，即实谱的补集中没有有界开区间分支。
正测度 Cantor 实集是闭集且内部为空。它至少有两个不同点；在这两点之间取一个不属于
谱的点，再分别取其左侧谱集的上确界和右侧谱集的下确界，就得到两个属于谱的不同端点，
中间的整个开区间不含谱点。该区间正是补集的一个有界连通分支，所以与“且无隙”矛盾。
这个论证适用于所有实谱，不依赖于拟周期势的具体模型，也不依赖于附加测度条件。
仅在某个指定能量处没有谱隙，是另一种较弱要求，本结论并未声称证伪那种改写。

## Formal verification and limits

`Conjecture1624.lean` contains three definitions and ten theorems, culminating in
`no_source_spectrum` and the universal `no_source_potential`. `Verification.lean` contains
separate, kernel-checked challenge cases for positive gapless intervals, the zero-measure
singleton, an exact gap and its connected component, a proper omitted subinterval that is
not a maximal gap, the reference-energy distinction, the role of closedness, and
unrestricted auxiliary predicates. These are boundary checks of the definitions and
logical coverage, not replacements for the general proof.

`Audit.lean` enumerates every declaration owned by both proof modules, including any
generated declarations; independently reports standard `collectAxioms` results for each;
and traverses their full dependency graph. It examines types, theorem and definition
bodies, opaque bodies, inductive families and constructors, and recursor rule bodies.
The allowed axioms are exactly `propext`, `Classical.choice`, and `Quot.sound`. The audit
rejects any additional axiom or unsafe or partial dependency. The ten main theorem axiom
reports are also printed explicitly.

The final replay rebuilds the owned project from a removed local build directory and
checks both proof files and the audit with warnings treated as errors. It removes the old
generated audit report before invocation and requires a newly created regular report; an
isolated negative replay verifies rejection of a successful no-op audit despite an old PASS
record. The source checksum contract and the entire normalized dependency manifest are
also checked exactly. The pinned standard
library is reused; it is identified by exact source revisions and imported-artifact
fingerprints, rather than represented as freshly rebuilt from source. There is no network
mathematical search, no imported problem solution, no custom axiom, no admitted proof,
no native decision procedure, and no unsafe proof dependency. Honest development snapshots
and failed diagnostics are retained separately under `attempts/` and `records/`; those
snapshots are not build roots.

The Lean verification establishes the mathematical proposition as formalized. The bridge
from the bilingual source to standard meanings is a semantic judgment made explicitly
above and in `SOURCE-MAPPING.md`; successful compilation alone would not establish it.
The source omits model-specific operator definitions, but those choices cannot affect the
set-level contradiction for any real spectrum. Publication eligibility, repository
submission procedures, and external review are separate from this mathematical authoring
record and are not certified by this report.
