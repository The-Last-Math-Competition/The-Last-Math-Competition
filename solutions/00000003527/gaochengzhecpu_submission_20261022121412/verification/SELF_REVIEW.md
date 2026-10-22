# Author adversarial self-review: conjecture 00000003527
Verdict: PASS

Developed by a delegated AI agent with a self-review; the coordinating agent
reviews it separately. No external independent review is claimed.

1. **Full domain and quantifiers.** `FixedPointClaim` quantifies every normal
   function on actual Mathlib ordinals, polymorphically in the universe. It
   is not a finite test, a special normal function, or a separately defined
   proxy for ordinals. All starting ordinals are quantified in the iteration
   and least-fixed-point clauses.
2. **Actual fixed points.** `Function.fixedPoints f` is the equality f(a)=a.
   The range theorem identifies the actual Mathlib ordinal derivative with
   this complete set; no subset enumeration substitutes for the source's
   fixed-point sequence.
3. **Actual closure.** The proof uses `IsClosed` for the actual ordinal order
   topology. A normal function is genuinely continuous by Mathlib's
   equivalence theorem. Its fixed set is the equalizer with the identity in
   a Hausdorff topology. Closure is not stipulated as an unproved convention.
4. **Actual unboundedness.** `¬ BddAbove (fixedPoints f)` is the formal main
   clause. The separate `arbitrarily_large_fixed_point` supplies a strictly
   larger fixed point for every ordinal a, using nfp f (succ a).
5. **Enumeration indexing.** Indexing starts at zero, with d(0)=nfp f 0 and
   d(succ a)=nfp f (succ (d(a))). The successor must be inside the starting
   ordinal to avoid repeating d(a). The limit hypothesis `Order.IsSuccLimit`
   excludes zero, and the supremum is over the actual strict initial segment.
6. **The ω-th enumerand.** `enumeration_omega` is exactly d(ω)=sup_n d(n),
   using the actual ordinal ω and actual natural-number embeddings. It is
   the limit stage of the fixed-point enumeration, not the first fixed point.
7. **Original-function iteration.** `iterate_omega` states nfp f a equals
   the supremum of actual iterates f^[n](a). `least_fixed_point` verifies
   a≤nfp f a, the fixed-point equation, and minimality among all fixed b≥a.
   `identity_limits` demonstrates that the two formulas need not agree.
8. **Source ambiguity.** Both languages describe the fixed-point sequence's
   ω-th term. The paper states the standard enumeration reading explicitly,
   and also proves the ordinary-iteration formula. It does not claim the
   false identity d(ω)=sup_n f^[n](0); the identity example explains why.
9. **Human proof checked.** The iterative supremum is fixed by normality
   and cofinality, including the case where the sequence becomes constant.
   Its minimality follows by bounding all iterates. Enumeration surjectivity
   uses the least index crossing a given fixed point, with separate zero,
   successor, and nonzero-limit cases. No unproved new spectral or numerical
   object is introduced.
10. **Library credit and formal scope.** This is classical. The main
    mathematical work on derivative enumeration and next-fixed-point limits
    is already supplied by Mathlib and used substantively. The paper names
    these dependencies. All theorem conclusions are formalized; the paper's
    explanatory derivation is not misrepresented as a new formal proof from
    first principles.
11. **Strict check and axiom audit.** Lean 4.19.0 strict checking passes with
    warnings as errors. Main/closure/range/ω/minimality audits use only
    propext, Classical.choice and Quot.sound. No sorry, admit, native_decide,
    custom axiom, or opaque declaration is used. Parent fresh build and PDF
    inspection are distinct later checks, not claimed as author work.
12. **Provenance.** The source SHA-256 agrees with the parent's fresh source
    record. The parent checked no prior PR or solution exists. Review is an
    author self-review plus separately performed parent review, with no
    external independent review claim.

Reviewed author artifact hashes:

- Main.lean: `c735ed11b3cd690c63a4d372fd23b31eebd092d6a77dcf2a86769fdc3d4e7484`
- main.tex: `e5ce86dbd56eeeabe8425a6dace0f89cd1a6b87654b7189ced86b1755788d956`
- SOURCE.md: `1b36c16e1f37c47498803fa844b3550ed91df0b7920f33a0a7f852d47620c34a`

Author strict output is preserved in `AUTHOR_STRICT_LEAN.log` (exit code 0).
The author has not compiled or inspected a PDF and has not performed a
separate fresh Lake project build; those checks are assigned to the parent.


Reviewed artifact hashes:

- Main.lean: `c735ed11b3cd690c63a4d372fd23b31eebd092d6a77dcf2a86769fdc3d4e7484`
- main.tex: `bf85dc718e01eab64bddf848ddb104c64dda80fe70423094883630f07ee64aef`
- main.pdf: `011edbe8dd7b9185ab3bec0658e47edec992286214357c09fd63c8d92bf88fff`
- SOURCE.md: `1b36c16e1f37c47498803fa844b3550ed91df0b7920f33a0a7f852d47620c34a`
