# Author-agent adversarial self-review: 00000009634

Verdict: PASS

# Conjecture 9634: four hidden states, full Hankel rank three

Status: AUTHOR REVIEW PASS. Parent adversarial review, final paper and fresh publication build remain required. This is author self-review, not independent external review.

## Target and scope

The exact bilingual source `round5/source/00000009634.md` asserts, as its first conjunct, that the minimal hidden-state count of a sofic shift's output process equals the rank of its Hankel matrix. The counterexample below is an actual stationary four-symbol Markov process. Its positive-probability language is presented by a concrete finite labelled graph, so it is a sofic process (in fact supported on a shift of finite type). Its full, infinite, all-word Hankel matrix has rank three, while every nonnegative hidden Markov realization needs at least four states and a four-state realization is exhibited. Thus the first conjunct fails. No claim about the algorithmic or geometric-isolation clauses is needed.

## Concrete process

Let the alphabet and hidden state set both be {0,1,2,3}. Put

    P = (1/2) [[1,1,0,0],
               [0,1,1,0],
               [0,0,1,1],
               [1,0,0,1]],      pi=(1/4,1/4,1/4,1/4).

P is nonnegative, every row and column sums to one, and pi P=pi. Observe the hidden state itself. In transition-emission notation take

    (T_a)_(i,j)=P_(i,j) 1_(j=a),
    p(w)=pi T_(w_1) ... T_(w_l) 1,    p(empty)=1.

This is also a conventional state-emission HMM with deterministic emissions E_j(a)=1_(j=a). Observing after a transition gives the same stationary process as observing the current state. The Lean file explicitly proves the emission normalization and T_a(i,j)=P_(i,j) E_j(a), not merely that the matrices happen to be nonnegative.

For arbitrary words the proof derives

    p(a w)=(1/4) f_a(w),
    f_i(empty)=1,   f_i(a w)=P_(i,a) f_a(w),
    p(u v)=r(u) dot f(v),    r(u)=pi T_u.

It proves p(w)>=0, p(empty)=1, and both stationary consistency equations

    sum_a p(a w)=p(w),     sum_a p(w a)=p(w)

for every word, not just for a bounded sample. These are the actual stationary cylinder probabilities of this finite Markov chain.

## Sofic support, with a real finite graph

The four vertices are the symbols; an edge i->j exists exactly when P_(i,j)>0, equivalently j=i or j=i+1 modulo four. Label vertex i by i. Every vertex has a self-loop, so finite paths extend indefinitely in either direction. The Lean theorem `positive_probability_iff_path` proves for every finite word w that p(w)>0 iff w is a path in this exact graph (List.Chain'). `support_finite_labelled_presentation` gives the explicit finite vertex-labelled graph presentation of the whole positive-probability language. This is the ordinary finite-presentation meaning of sofic, not a replacement predicate with the desired property built in.

## Entire Hankel matrix has rank three

Use the full matrix H_(u,v)=p(u v) with both indices ranging over **all** finite words, including the empty word. The Lean definition is literally `Matrix Word Word Real`; its rank is Mathlib's `Matrix.cRank`, the cardinal dimension of its genuine column span.

The rows of P satisfy P_(3,a)=P_(0,a)-P_(1,a)+P_(2,a) for every a. The future vectors therefore satisfy for every word v

    f_3(v)=f_0(v)-f_1(v)+f_2(v).

This holds for the empty word too, since 1=1-1+1. Consequently

    H_(u,v) = (r_0(u)+r_3(u)) f_0(v)
            + (r_1(u)-r_3(u)) f_1(v)
            + (r_2(u)+r_3(u)) f_2(v).

This gives a factorization of the **whole infinite matrix** through three actual real columns. The proof shows that every column of H belongs to the span of these three columns, then uses the real column-space cardinal dimension to obtain cRank(H)<=3. Negative coefficients are allowed in this ordinary linear factorization, exactly as ordinary matrix rank requires.

For rows [0],[1],[2] and columns [0],[1],[2], the actual Hankel submatrix is

    (1/8) [[1,1,0], [0,1,1], [0,0,1]],

whose determinant is 1/512. It is invertible, hence has rank three. Mathlib's `cRank_submatrix_le` then gives cRank(H)>=3. Thus the standard full infinite Hankel rank is exactly three. The proof never substitutes the rank of P or of one finite sample for the full Hankel rank.

## Every HMM realization needs four states

The Lean `HMM n` structure uses arbitrary nonnegative initial weights summing to one and arbitrary nonnegative symbol-transition matrices S_a whose summed outgoing rows equal one. Its probability for **every** finite word is the actual matrix-product probability. The generic constructor `fromStateEmission` explicitly includes every usual current-state-emission HMM with arbitrary initial distribution mu, row-stochastic transition Q, and normalized state-emission table E, by setting S_a(i,j)=E_i(a) Q_(i,j), i.e. emit first and then transition. This formula makes mu S_w 1 the ordinary initial-state emission probability; the last transition cancels because Q 1=1. It is not confused with Q_(i,j) E_j(a), which emits after transitioning and agrees for the concrete stationary witness but need not agree for arbitrary nonstationary mu. Our transition-emitting class even permits more general kernels, making the lower bound stronger. No stationarity assumption is imposed on a competing realization, so a nonstationary hidden initialization cannot evade the argument.

For any such n-state model M reproducing all p(w), its length-one versus length-one Hankel block factorizes nonnegatively:

    H_([i],[j])=sum_(s=1)^n A_(i,s) B_(s,j),
    A_(i,s)=(initial S_i)_s >=0,
    B_(s,j)=(S_j 1)_s >=0.

The exact observed block is P/4. Its four diagonal entries are positive; for each distinct i,j at least one of H_([i],[j]) and H_([j],[i]) is zero. For each i choose a hidden index s_i making its positive diagonal term A_(i,s_i) B_(s_i,i)>0. Such an index exists because the finite sum is positive. If s_i=s_j for i!=j, the positive factors force both crossed terms A_(i,s_i) B_(s_i,j) and A_(j,s_j) B_(s_j,i) to be positive. Nonnegativity bounds each such term above by its corresponding Hankel entry, contradicting the crossed zero. Thus i->s_i is an injection from four symbols into n hidden states, so n>=4.

The displayed four-state model gives the matching upper bound. Lean proves `IsLeast {n | exists M:HMM n, M realizes p} 4`. Combined with cRank(H)=3, it also directly proves there is no realization with precisely `cRank(H).toNat` hidden states.

The key distinction is ordinary real rank versus the nonnegative factorization required by hidden-state probabilities. The rank-three linear factorization above is allowed a subtraction; it does not manufacture a valid three-state probability model.

## Lean theorem mapping

- `HMM`, `wordMatrix`, `future`, `reach`, `probability`: actual nonnegative finite-state models and all-word matrix-product probabilities.
- `fromStateEmission`: generic normalized E_i(a) Q_(i,j) constructor for every conventional state-emission model and every initial distribution, independent of the stationary concrete witness's Q_(i,j) E_j(a) formula.
- `hankel`: the full word-concatenation matrix, not a finite truncation.
- `hankel_factor`: arbitrary-model forward/backward factorization.
- `future_nonneg`, `wordMatrix_nonneg`, `reach_nonneg`, `probability_nonneg`: general positivity bridges.
- `P`, `P_nonneg`, `P_row_sum`, `P_col_sum`, `model`: explicit four-state Markov model.
- `model_future_cons`, `model_probability_cons`, `model_probability_nil`: exact all-word recurrences and empty-word normalization.
- `future_relation`, `whole_hankel_factorization`, `whole_hankel_rank_upper`: all-word three-column linear factorization and real column-span dimension bound.
- `minor_eq`, `minor_det`, `minor_rank`, `minor_cRank`, `whole_hankel_rank`: actual nonzero Hankel minor and full infinite cRank=3.
- `diagonal_positive`, `crossing_zero`, `nonnegative_factor_lower`: exact fooling-set obstruction against **arbitrary** nonnegative n-column factors.
- `Realizes`, `any_HMM_needs_four_states`, `minimal_hidden_state_count`: actual realization equality on every word and sharp minimal state count four.
- `emission`, `emission_nonneg`, `emission_sum`, `transition_emission`: conventional deterministic state-observation bridge.
- `initial_stationary`, `stationary_left_consistency`, `stationary_right_consistency`: actual stationary Markov initial distribution and both all-word cylinder consistency identities.
- `allowedEdge`, `allowedEdge_self`, `allowedEdge_iff`, `future_positive_iff_path`, `positive_probability_iff_path`: explicit four-vertex graph and exact full language support.
- `HasFiniteLabelledPresentation`, `support_finite_labelled_presentation`: genuine finite labelled-graph presentation witness.
- `counterexample`: full rank three, minimal state count four, and finite graph presentation together.
- `no_realization_with_hankel_rank_states`: direct negation of a realization with the claimed Hankel-rank number of hidden states.

## Author adversarial review

1. **Whole Hankel rank, not transition rank? PASS.** Matrix indices are all List(Fin 4), including []; factorization is proved for every pair of words. Upper bound is on Mathlib's actual cRank, and the nonzero finite minor gives only the lower bound.
2. **Actual nonnegative probabilities? PASS.** HMM fields require initial/nonnegative transition normalization. Probabilities are matrix-product probabilities, not arbitrary formal series guessed to have the desired rank. General positivity and both stationary consistency equations are proved.
3. **Sofic condition? PASS.** Every positive-probability word is proved equivalent to a path in the explicit finite graph. Every vertex has a self-loop, eliminating transient nonextendable paths. The graph presentation uses actual finite vertices, adjacency and labels.
4. **Original HMM convention? PASS.** The lower bound is for arbitrary normalized nonnegative transition-emitting models. The generic `fromStateEmission` constructor proves the E_i(a) Q_(i,j) conversion, including arbitrary ordinary initial distributions. The four-state upper witness instead uses P_(i,j) E_j(a), with its formal deterministic-emission factorization and stationary initial distribution pi P=pi. The before/after-transition timing choices are explicitly distinguished; stationarity is used only for the concrete witness, not assumed of an arbitrary competing realization.
5. **General competing realizations? PASS.** `Realizes M` requires equality on all finite words. The argument only needs the necessary length-two consequences and allows arbitrary n and nonstationary hidden initialization. It does not assume the candidate realization has the same graph, labels, transition matrix or deterministic emissions.
6. **Nonnegative-rank proof? PASS.** The four positive diagonal terms select actual hidden indices; collisions are ruled out by crossed zeros and nonnegative term-to-sum bounds. No numerical rank heuristic, assumed nonnegative-rank oracle or unproved support counting is used.
7. **Upper bound n=4? PASS.** The concrete process itself supplies a genuine four-state normalized model; thus the conclusion is exact minimality four, not merely a lower bound.
8. **Empty word and zero states? PASS.** Empty-word normalization is explicit and the future linear relation holds there too. HMM n permits n=0 syntactically, but normalized initial weights rule it out; the injection lower bound handles it without an exception.
9. **No false stronger claim? PASS.** The first equality clause is refuted. No result about exact learning complexity, statistical identifiability from finite noisy samples, or geometric isolation is claimed.
10. **Computation and proof trust? PASS.** Needed claims have kernel-checked Lean proofs. Python verifies exact Fraction identities on a finite sample only and is labelled auxiliary. Strict warnings-as-errors and all printed axiom lists pass without sorry/admit/native_decide/custom axioms.

## Verification evidence

Toolchain: leanprover/lean4:v4.19.0.
Mathlib revision: c44e0c8ee63ca166450922a373c7409c5d26b00b.

Actual strict command from `round5/drafts/00000009634/lean`:

    PY -X utf8 ../../../../round7/run_safe.py ../../../../tools/lean-4.19.0-windows/bin/lake.exe env lean -DwarningAsError=true Main.lean

Result after the parent's requested generic state-emission bridge: exit 0, 10.766 seconds. Seven actual axiom lists are recorded in `round14/quantum/9634-strict.log`, each containing only propext, Classical.choice and Quot.sound.

`round14/quantum/9634-status.json` records exact commands and hashes. Full `lake build` is recorded separately in `round14/quantum/9634-lake-build.log` and its result in the status JSON.

Auxiliary `verify.py` was copied from the parent's independent exact check and actually executed with exit 0. It checks stationarity, all word probabilities and normalization through length 6, exact support/graph equivalence on those words, an 85-by-85 all-short-word Hankel factorization sample, the determinant 1/512 and all fooling-set crossed zeros. Its actual output is in `round14/quantum/9634-verify.log`. These checks are supplemental and not used as Lean axioms or norm/rank oracles.

Main.lean SHA256:
ca81d6a6e852a777b38f7d9cb02385da754c5c0c03d35824288446cb6b7e7eea

verify.py SHA256:
2e60c378409a5d4751c112d45a9133df2a986ff5640c2e47d899f99afe360b29

## Primary reference for terminology and background

Yoshito Ohta, *On the Realization of Hidden Markov Models and Tensor Decomposition*, arXiv:2008.11487 (2020), Sections 1-2. The actual primary PDF was opened and read: https://arxiv.org/pdf/2008.11487 . It describes stationary finite-alphabet HMM realizations and the additional nonnegativity constraint distinguishing general linear/quasi-realizations from actual hidden Markov realizations. The explicit four-state counterexample and every required proof above are self-contained. No result of the paper is assumed by Lean.

The older Vidyasagar author-hosted PDF URL redirected to an unrelated university page, so it is not used as a verified full-text reference here.

## Handoff

Only this agent's `round14/quantum` files and the owned draft Lean project/verify.py have been edited. No TeX/PDF, PR, global snapshot or publishing allowlist has been written. Parent must do final paper/PDF, source provenance, semantic adversarial review and fresh sealed build. After this frozen handoff, follow the user's continued-work instruction by screening the next candidate; do not modify these finalized Lean sources unless a parent review finds a concrete issue.


Reviewed artifact hashes:

- Main.lean: `ca81d6a6e852a777b38f7d9cb02385da754c5c0c03d35824288446cb6b7e7eea`
- main.tex: `d30877c2edbe9fac4535fc8a02d64678cb0754dbdbed3eb10b25801a92360fef`
- main.pdf: `3bce0df78fcf4afab78bf8978d460d9d4c8f614e61e3ce29e90fe11da5f03f7b`
- SOURCE.md: `697fd9d5216832ed98a11643b269798352f2158e20e6522e131e864eef154a51`
