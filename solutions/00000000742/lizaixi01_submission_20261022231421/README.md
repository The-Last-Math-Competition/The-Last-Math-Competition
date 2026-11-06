# Conjecture 00000000742: two minimality counts

For p=2 the proposed number p^(p-1) is 2. The actual adding-one map on Z2 is 1-Lipschitz and every forward orbit is dense in the 2-adic topology. Its only nonempty closed minimal invariant subset is the entire space, so its number of minimal components is 1.

The source also says "a count of minimal maps". To cover that reading, the proof constructs three distinct 1-Lipschitz minimal maps, x -> x+1, x -> x+3 and x -> x+5. Odd integers are units in Z2; multiplication by a unit and translation preserve density of the nonnegative integers. The maps are distinct by their values at zero. Thus the collection of actual minimal maps cannot have cardinality 2. These maps are mutually conjugate; no claim about counting nonconjugate systems is made, and the source does not specify a conjugacy quotient.

The Lean proof uses the actual PadicInt 2, its metric, topology, natural-number density, iterates, closure and function equality. It does not replace Z2 by a finite quotient.

## Reproduce

Install elan, enter `lean/`, and run:

```sh
lake exe cache get
bash verify.sh
```

The manifest pins Lean 4.33.0, Mathlib db584cd6d46c92f209a44c0f1c829460d327499d and every dependency. The script compiles Main, audits eleven main declarations' transitive axiom dependencies, and performs official `leanchecker --fresh Main` replay. The optional public dependency cache is reused; Main itself is newly built in a separate project. No auxiliary numerical computation is needed.

Compile report.tex twice with pdflatex to reproduce the supplied two-page PDF. Both pages were rendered and visually inspected; exact source-bound logs and hashes accompany the package.

## Definitions and attribution

The standard meaning of a minimal subsystem is used: nonempty closed invariant subset, with every forward orbit dense in that subset. Fan and Liao, *On minimal decomposition of p-adic polynomial dynamical systems*, https://arxiv.org/abs/1010.5583, distinguish clopen minimal components from periodic orbits, and describe an everywhere minimal system as having one component. Their degree-at-least-two theorem is not invoked for the affine maps here. Our unique minimal closed subset is the entire clopen space, so it also covers their narrower component convention.

SOURCE.md preserves the original bilingual conjecture and its upstream commit. No earlier submission was found in the pre-submission check. OpenAI Codex assisted the proof and report, and a separate supervising Codex agent reviewed both interpretations and the formal chain. This is AI review, not human certification. The examples are classical. Organizer acceptance is pending.
