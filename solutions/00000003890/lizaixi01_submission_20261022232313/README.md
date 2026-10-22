# Conjecture 00000003890: infinitely many F-jumps of one fixed ideal

The nonzero proper ideal (X) in F2[X] has a jump at every positive integer. This refutes the first clause, which claims that the full jumping set of any fixed ideal is finite. No claim is made here about the second clause concerning unions of jumping sets in (0,1), or about finiteness inside a bounded interval.

The Lean proof constructs actual polynomial ideals and Frobenius powers via Ideal.map. It proves against every candidate ideal J that the least Frobenius root of (X^N) is (X^floor(N/q)). It defines generalized test ideals by the ideal supremum of these roots, proves that the root stages are increasing, and identifies the supremum with the literal union. The definitions match [Badilla-Cespedes and Leon-Cardenal, Definition 4.1](https://arxiv.org/html/2305.00571v3), with e+1 corresponding to their positive Frobenius exponents.

At each integer k, the test ideal is (X^k). Explicit parameters approaching k+1 from the left have X^k in their test ideal, while X^k is absent at k+1. Parameter monotonicity then proves inequality for every earlier nonnegative parameter. An injection of the positive integers proves that the real jump set is infinite. No numerical test-ideal formula is assumed.

## Reproduce

With elan installed, enter `lean/` and run:

```sh
lake exe cache get
bash verify.sh
```

The project pins Lean 4.33.0, Mathlib db584cd6d46c92f209a44c0f1c829460d327499d and all transitive dependencies. The script builds Main, audits fifteen key declarations' transitive axiom dependencies, and invokes the official `leanchecker --fresh Main`. Public dependency artifacts may be cached; the submitted Main is newly built and independently replayed.

To reproduce the PDF, compile report.tex twice with pdflatex. The supplied two-page report was rendered and every page visually checked. Source-bound command logs, verification receipts and SHA256 checksums accompany the package.

SOURCE.md records the bilingual original at the fixed upstream commit. No previous exact-ID PR was found before submission. This is a classical example, not new mathematics. OpenAI Codex assisted the proof and report, and a separate supervising Codex agent reviewed the complete formal chain. This is AI review, not human certification. Organizer acceptance is pending.
