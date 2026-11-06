# Conjecture 00000001002: complete arcs have a larger uniform lower bound

For every finite field K of size q, an actual complete arc of PG(2,q) with k points satisfies k² > 2q. Its normalized minimum size is therefore at least sqrt(2), which rules out the stated liminf=1 over all prime powers, as well as the stronger sqrt(q)+o(sqrt(q)) assertion.

The proof uses the actual Mathlib projective space of K³. Arc means that every dimension-two subspace contains at most two selected projective points; complete means that no outside point can be inserted. Existence of a complete arc and a minimum-cardinality complete arc are proved using finite maximum/minimum selection. The minimum is not defined by a numerical guess.

Every outside point lies on a secant through two arc points. Counting the union of those secants gives q²+q+1 <= k + choose(k,2)(q+1), which implies k²>2q. Plane and line counts use projectivization and actual finite-dimensional subspaces. The lower bound is uniform over all finite fields. Separate extended-real and real liminf theorems apply to any sequence of finite fields, including an enumeration of all prime-power sizes tending to infinity. The real-library fallback case is treated explicitly; the geometric contradiction relies on the uniform lower bound and the extended-real result, not on a fallback convention.

[Bartoli et al., introduction](https://arxiv.org/abs/1111.3403) provides standard definitions and records a stronger classical lower bound. The formalization independently proves the elementary bound above, without claiming the stronger extra constant.

## Reproduce

With elan installed, enter `lean/` and run:

```sh
lake exe cache get
bash verify.sh
```

The project pins Lean 4.33.0, Mathlib db584cd6d46c92f209a44c0f1c829460d327499d and all transitive dependencies. Main is newly compiled; sixteen key declarations are audited and the official `leanchecker --fresh Main` replays the proof. No sorry, native_decide or additional axiom.

Compile report.tex twice with pdflatex to reproduce the PDF. Source-bound receipts, exact logs, PDF review and hashes accompany the package. OpenAI Codex assisted, and a separate supervising Codex agent reviewed the complete source. This is AI review, not human certification. Organizer acceptance is pending.
