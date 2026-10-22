# Conjecture 00000002571: rank-one counterexamples to the printed bound

The exact inequality D(f) <= 16 (log rank M_f)^2 has no rank floor or additive constant. For AND with its real 0/1 matrix, and XOR with its real sign matrix, the matrix rank is 1 but communication is necessary. Thus the right-hand side is zero and the bound fails.

This addresses only the literal unregularized rank-one boundary. It does not refute the usual asymptotic log-rank conjecture, a formulation with max(2,rank), or a formulation with an additive constant. The separate assertion concerning the optimal exponent is not addressed.

The Lean proof implements actual binary deterministic protocol trees. Each internal node sends one bit determined by the speaker's local input; a terminal node allows Bob to output any function of his own input. The minimum cost is defined from the set of correct protocols using Nat.find. Zero-depth protocols are proved local to Bob, while both functions are proved not local to either party. Explicit one-bit protocols show D=1 in this Bob-output convention. If both parties must output, the same positive lower bound holds; no exact one-bit claim for that stricter convention is made.

Both matrix ranks use Mathlib's Matrix.rank over R. Outer products give the upper bound and a nonzero 1-by-1 minor the lower bound. Numerical cost and rank are proved rather than built into the definitions.

For standard background on deterministic communication and the 0/1 real-rank convention, see [Ben-Sasson, Lovett and Zewi, section 1.1](https://arxiv.org/abs/1111.5884). SOURCE.md records the bilingual original at the fixed upstream commit.

## Reproduce

With elan installed, enter `lean/` and run:

```sh
lake exe cache get
bash verify.sh
```

The project pins Lean 4.33.0, Mathlib db584cd6d46c92f209a44c0f1c829460d327499d and all transitive dependencies. The script builds Main, audits seventeen key declarations and invokes the official `leanchecker --fresh Main`. Public dependency artifacts may be cached; the submitted Main is newly built and independently replayed.

Compile report.tex twice with pdflatex to reproduce the PDF. Both supplied PDF pages were rendered and visually checked. Source-bound receipts, exact command logs and SHA256 checksums accompany the package. OpenAI Codex assisted; a separate supervising Codex agent reviewed the complete formal chain. This is AI review, not human certification. Organizer acceptance is pending.
