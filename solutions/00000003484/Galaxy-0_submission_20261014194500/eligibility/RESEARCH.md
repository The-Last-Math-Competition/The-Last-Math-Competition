# Eligibility and exact-source research: 00000003484

## Result

As checked on 2026-10-14 between 19:23:49 UTC and 19:24:42 UTC, the live repository records this conjecture as neither proved nor disproved, has no solution directory for it, and the requested all-state pull-request searches reveal no relevant duplicate. This is a time-stamped research result, not organizer acceptance or a guarantee of first-solver credit. Recheck before any publication.

Repository: https://github.com/The-Last-Math-Competition/The-Last-Math-Competition

Pinned main commit: cce2d90cb298de9595798eb674d2c80712100532
Commit date: 2026-10-14T04:42:36Z
Exact source Git blob: 6e8283ae36deff4684090880c4d608259201b28e
Exact source SHA-256: ee45b512bb8537d3d36add20f97d48f642e44331f76cd02ba30451c75d18daab
Exact source size: 692 bytes
Metadata Git blob: ea8c9f6be73eecad1aa3b9e3b802a03a06072a86

Pinned source: https://github.com/The-Last-Math-Competition/The-Last-Math-Competition/blob/cce2d90cb298de9595798eb674d2c80712100532/conjectures/00000003484.md

## Exact source wording

# 00000003484

**English.** Definition: The clique tree is the tree structure of maximal cliques of chordal graphs, with clique bags the nodes. Conjecture: The bag count equals the maximal-clique count minus the Helly covering genus; the genus is zero if and only if the graph is an interval graph, with the bag count given explicitly by the recursion of clique-tree embedding counts. (clique tree bag count formula)

**中文。** 定义：团树为弦图极大团的树结构，团袋为团树节点。猜想：团树的袋数恰为极大团数减去 Helly 覆盖亏格；亏格为零当且仅当图为区间图且袋数由团树嵌入选数的递推显式给出。（团树袋数公式）

## Metadata and solution directory

Metadata header:
id,well_definedness_level,importance,novelty,proof_difficulty,disproof_difficulty,proven,disproven,first_submission_time,completed_by_ai,first_solver

Exact row:
00000003484,,,,,,false,false,,false,

The Contents API request for solutions/00000003484 returns HTTP 404. Independently, the complete, non-truncated solutions tree at SHA 735647fb89aa45afc9a8490098b4add305d82792 contains 876 entries and no entry for 00000003484.

## Pull-request searches and duplicate review

All searches cover all PR states, not just open PRs. Raw GitHub issue-search responses additionally record total_count and incomplete_results=false for all four required searches:
- 00000003484: 0.
- 3484: 0.
- "Helly covering genus": 0.
- "clique tree": 3, all reviewed below.

Additional all-state connector searches:
- Helly: only PR 732.
- clique-tree: PRs 964, 983, 1007, 732.
- clique tree bag: only PR 732.
- 覆盖亏格: 0.
- 团树: 0.

All four unique returned PRs were read and their full changed-file listings inspected. None changes a 3484 solution, and none is a duplicate of the bag-count / zero-genus characterization:
- https://github.com/The-Last-Math-Competition/The-Last-Math-Competition/pull/964 — closed/merged, conjecture 3470, K2 perfect-elimination-ordering count versus clique-tree embedding count. Eight changed files, all under solutions/00000003470/.
- https://github.com/The-Last-Math-Competition/The-Last-Math-Competition/pull/983 — closed/merged, conjecture 4227, filled-triangle spanning 2-tree versus chromatic-polynomial evaluation. Nineteen changed files, all under solutions/00000004227/.
- https://github.com/The-Last-Math-Competition/The-Last-Math-Competition/pull/732 — closed/merged, conjecture 1680, random-geometric-graph treewidth. Fifteen changed files, all under solutions/00000001680/.
- https://github.com/The-Last-Math-Competition/The-Last-Math-Competition/pull/1007 — closed/merged, conjecture 3996, satisfiable Ramsey diagonal CNFs. Sixteen changed files, all under solutions/00000003996/.

These are search results, not an exhaustive semantic reading of every file ever submitted in the repository. None of the API search responses reports incomplete results, and no result count approaches its 100-item page limit.

## Semantic assessment

1. The source defines clique-tree nodes to be the maximal-clique bags. Under the ordinary clique-tree definition there is one node for each maximal clique, hence bag count B equals maximal-clique count M identically.
2. The asserted formula B = M - g then forces g = 0, with ordinary integer/real subtraction. If formalized with natural-number truncated subtraction, one should explicitly use M > 0 to infer g = 0 from M = M - g; a nonempty finite counterexample provides this.
3. The next claim requires zero genus to imply that the graph is an interval graph. Thus a chordal non-interval graph contradicts the conjunction independently of any numerical definition of g.
4. "Helly covering genus" is not defined anywhere in the source paragraph. Do not silently invent a standard invariant or compute a numerical value for it. The robust refutation is that no value assigned to it can make both asserted properties true on the counterexample.
5. No recursion, embedding equivalence convention, base cases, or meaning of "embedding counts" is supplied. A refutation of the earlier conjuncts does not need to repair or evaluate that unspecified recursion.
6. The Chinese grammar puts "且袋数由…递推显式给出" after the interval-graph phrase inside a potentially joint right-hand side of "当且仅当"; the English instead uses a trailing "with" clause. Both readings still include the necessary implication g = 0 -> graph is interval, so the proposed contradiction survives this scope ambiguity.
7. Replacing a clique tree by a tree decomposition with repeated/nonmaximal bags, or taking a quotient of its maximal cliques, changes the explicit definition. The proof should state that it uses the source's own maximal-clique-node definition.
8. The source does not explicitly state finite, simple, or connected graph conventions. A finite connected simple chordal non-interval example avoids those scope concerns.

## Evidence files

- conjecture-00000003484.md: byte-exact bilingual source; Git blob identity independently recomputed after writing.
- source-provenance.json: pinned source, check timestamp, identities, metadata row.
- metadata-00000003484.csv: relevant header and row.
- repository.json and branch-main.json: live repository and main-branch records.
- root-tree.json and solutions-tree.json: pinned complete directory evidence.
- solution-directory-check.json: direct missing-directory response.
- pr-searches.json: all nine connector query responses with check timestamps.
- pr-searches-raw.json: four raw GitHub API search responses with counts and completeness flags.
- reviewed-prs.json: metadata and changed-file contents for all four unique PR hits.

No external write or publication was performed.

