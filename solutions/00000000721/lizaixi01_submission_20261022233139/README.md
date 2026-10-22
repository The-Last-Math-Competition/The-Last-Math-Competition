# Conjecture 00000000721: negative factorial powers

With the minus sign printed in the question, every convergent displayed series at p=2 has only finitely many nonzero digits. All its values in the actual algebraic closure of Q2 therefore lie in the image of Q, a countable set. In particular they contain no subfamily of continuum cardinality, irrespective of algebraic independence. This disproves the stated conjunction.

The Lean proof uses `PadicAlgCl 2` with its extended p-adic norm. A nonzero digit is 1, and the term with exponent `-(n+1)!` has norm at least 1. Convergence forces the terms to tend to zero and hence the digits eventually to vanish. The proof treats both ordinary forward partial sums and `HasSum`, proves that they give exactly the same value set here, and explicitly reindexes the source's n>=1. It never assigns a sum to a divergent series through a default `tsum` value.

The final theorem excludes any subset of cardinality `2 ^ aleph0`. The construction is in `PadicAlgCl`, not a replacement real norm or the completion of the algebraic closure. A different problem with positive factorial powers is not addressed.

## Reproduce

With elan installed, enter `lean/` and run:

```sh
lake exe cache get
bash verify.sh
```

The project pins Lean 4.33.0, Mathlib db584cd6d46c92f209a44c0f1c829460d327499d and all transitive dependencies. The script builds Main, audits fourteen key declarations' transitive axiom dependencies, and invokes the official `leanchecker --fresh Main`. Public dependency artifacts may be cached; the submitted Main is newly built and independently replayed.

To reproduce the PDF, compile report.tex twice with pdflatex. The supplied two-page report was rendered and every page visually checked. Source-bound command logs, verification receipts and SHA256 checksums accompany the package.

SOURCE.md records the bilingual original at the fixed upstream commit. No previous exact-ID PR was found before submission. OpenAI Codex assisted the proof and report, and a separate supervising Codex agent reviewed the complete formal chain. This is AI review, not human certification. Organizer acceptance is pending.
