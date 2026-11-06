# Proof of Conjecture 00000007126: Combinatorial Barycentric Subdivision

## Declared Source Interpretation

The standard combinatorial barycentric subdivision is the **order complex of
the actual nonempty face poset**. We prove that it is flag and that its
d-dimensional face count equals the number of strict face chains with d+1
elements. The counts are invariant under face-poset isomorphisms.

The source does not name a particular invariant. Here the enumerative invariant
is explicitly the **f-vector**, not a complete classifier or a quantity unchanged
by performing subdivision. The entire chain-incidence family describes the
combinatorial complex, which contains more information than its count vector.
We do not claim a geometric barycenter-coordinate/triangulation theorem, nor
that counts alone reconstruct or classify the original polytope.

Both full-polytope and boundary conventions are proved. Actual face subsets,
not a simplicial-vertex-subset surrogate, are ordered by actual inclusion.
Empty faces are excluded; for the boundary the whole face is also removed.
The universal finite-family theorem has no simplicial-polytope hypothesis and
applies to actual faces of bounded convex polytopes under the standard
combinatorial definition. See `statement-alignment.md` and `main.pdf` for the
precise source interpretation and formalization boundary.

`source.md` preserves both original languages at upstream commit
`b355e42906e6eaf52bc7e9d005e0ef02d8aa7400`, Git blob
`6c54d99d7caf701ff7e55c4530c2eb441a049aec`, raw SHA-256
`89cc2b903ced78703633302b34683740d496f5ea055dddab0d91f16f73d71a59`.
No original conjecture or organizer metadata is modified.

## Actual Formal Objects

`lean4/OrderSubdivision.lean` constructs a Mathlib `AbstractSimplicialComplex`
from nonempty finite chains and a genuine `SimpleGraph` of distinct comparable
vertices. It proves the two-face/edge bridge, chain/clique equivalence and
clique-to-face flag property. It supplies actual face/chain equivalences and
the d+1 f-vector interface. It then specializes to finite families of actual
`Set E` faces, including the empty/whole-face filters, and constructs mutually
inverse face transports under an actual order isomorphism.

`Main.lean` imports the complete core. `Check.lean` prints all 21 public theorem
types and axiom footprints. Only `propext`, `Classical.choice`, and `Quot.sound`
are allowed. The code proves a universal combinatorial assertion, not a
hard-coded instance, assumed flagness, or an unproved face-count premise.

The formal universal domain is finite families of actual subsets; it does not
include a separate geometric Polytope type or Lean proofs of geometric face
finiteness, barycenter affine independence, coverage and gluing. The standard
face-poset definition and its specialization to bounded polytopes are explicitly
explained in the report with primary references. Do not advertise stronger
formal geometric results than the compiled theorem types establish.

## Reproduction

Use Python 3.10+, an installed Lean 4.33.1 toolchain and an organizer-source Git
checkout containing the source commit. Mathlib and its nine-package dependency
lock are pinned. The normal online preparation path is:

```text
python reproduce.py --lake <installed-Lean4.33.1-lake> --repo <organizer-source-checkout>
```

For existing exact physical dependencies and compatible caches, the explicitly
offline mode is:

```text
python reproduce.py --lake <installed-Lean4.33.1-lake> --repo <organizer-source-checkout> --skip-update
python -m unittest discover -s tests -q
```

The reproducer verifies the actual source identity, exact declarative lock,
mathematical raw hashes, all theorem inventories, path safety, own Git metadata,
dependency HEAD/origin/raw bytes/index/tree equality before and after execution.
It cleans **only its own project's build outputs**, builds Main, replays its
authored sources with warnings as errors, and checks all compiled types/axioms.
Junctions and symbolic links are rejected. Three fixed inert Git-link blobs
may be ordinary link-text files on Windows only, never executed benchmark code.
No broad filesystem cleanup or dependency-source mutation is performed.

Default full-reproduction budget is 285 seconds within the coordinator's
300-second subprocess limit. Failure or timeout blocks release; an old PASS
is not substituted. `--preflight-only` executes no Lean and is insufficient.
The 61 focused safety tests use synthetic fixtures and mocked build paths;
they are not evidence of actual Lean execution. Full reproduction is separate.

Finite square/full-boundary incidence regressions are exact diagnostics, not
the universal proof. Installed compiler and dependency build caches remain
trusted; no empty-machine, full-dependency-clean, Linux, cross-platform or hosted
CI success is claimed. `review.json` is a separate frozen-package AI review,
not human endorsement or organizer acceptance.

AI-assisted submission by **idealistichacker**; no affiliation, award,
first-solver priority or acceptance is claimed.
