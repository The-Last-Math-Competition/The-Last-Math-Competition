# Author-agent adversarial self-review: 00000009624

Verdict: PASS

# 9624: a radius-one three-symbol shift violates the proposed entropy bound

Status: formal proof complete and frozen for parent review. Recorded strict check exit 0 (12.328 seconds), full Lake build exit 0 (13.875 seconds), and independent exact verification exit 0 (0.203 seconds). No TeX, PDF or PR is created by this agent.

## Exact source and counterexample

The exact bilingual source is `round5/source/00000009624.md`, SHA256 `332437d8b3b7784ae6a55b9b5e9636344b3b3b8b4aaf60424f22f965125f9ab3`. It asserts that surjective sliding-block automorphisms of radius r satisfy h <= r log 2. Neither language restricts the alphabet to two symbols. Refuting that first assertion refutes the whole conjunction; no separate claim about the later equality or spectrum clauses is necessary.

Take the entire bilateral full shift X={0,1,2}^Z, with the product of discrete topologies, and F(x)_k=x_(k+1). This is a homeomorphism, with inverse F^(-1)(x)_k=x_(k-1), and commutes with the underlying shift. Its local window [-1,0,1] uses the rule f(a,b,c)=c. The inverse rule is g(a,b,c)=a. Thus both directions have radius one.

Its minimal radius is exactly one. Indeed the all-zero configuration x and the configuration y with y_1=1 and all other coordinates zero agree at coordinate zero, but F(x)_0=0 and F(y)_0=1. A radius-zero rule could not distinguish them. This is checked in Lean, including the universal implication that any valid radius r is at least one.

## Genuine topological entropy, formally connected to actual configurations

This proof uses Mathlib's actual `Dynamics.coverEntropy` from the pinned `Mathlib/Dynamics/TopologicalEntropy/CoverEntropy.lean`. It is Bowen-Dinaburg topological entropy, defined as the supremum over uniform entourages of the limsup exponential growth of minimal dynamical covering cardinalities. The configuration type is the complete function space `Z -> Fin 3`, with the discrete uniformity on Fin 3 and the standard product uniformity. Compactness of this actual configuration space is also formally checked.

Let U={(x,y):x_0=y_0}. The proof checks that U belongs to that product uniformity. Iteration is proved for every n, x and k: F^n(x)_k=x_(k+n). Consequently the actual dynamical ball B_n(x,U) consists exactly of configurations y whose coordinates 0,...,n-1 agree with x.

Every word w in {0,1,2}^n extends to a genuine bilateral configuration by setting all outside coordinates to zero. Reading the length-n block of the extension recovers w. Hence the actual language is all 3^n words. These extensions are not substituted for the full state space: they are explicit representatives used to prove covering bounds on the full space X.

For any finite dynamical cover s of X, the map from its centers to their read length-n words is surjective. All 3^n words must therefore occur, so |s| >= 3^n. Conversely, the set of zero-extended words covers every configuration, and the extension map is injective, so it has precisely 3^n centers. The genuine Mathlib `coverMincard F univ U n` is therefore exactly 3^n, including n=0.

Mathlib's `expGrowthSup_pow` yields the exact entourage entropy log 3. The supremum over all entourages is at least this one, so the actual topological entropy satisfies h_top(F) >= log 3 > log 2 = 1*log 2. That strict inequality alone disproves the proposed upper bound. The formal conclusion does not require an upper bound on the total topological entropy.

In particular, no arbitrary counting sequence has been renamed entropy; the construction proves actual dynamical covering cardinalities and then uses the library's original entropy definition. No external coding theorem, symbolic-entropy bridge or other unproved mathematical assumption is used.

## Formal conclusions and trust

`shiftHomeomorph` gives the actual continuous invertible map on all configurations. `shift_radius_one`, `unshift_radius_one`, `shift_radius_minimal` give the local rules and minimality. `full_language` realizes every word. `cylinder_coverMincard` and `cylinder_entropy` give the exact dynamical cover count and its true entropy. `counterexample` gives surjectivity, radius one and true topological entropy strictly exceeding log 2. `radius_entropy_law_false` directly negates the universally quantified proposed inequality for shift-commuting homeomorphisms of this concrete full shift.

The final proof is `round5/drafts/00000009624/lean/Main.lean`, SHA256 `8753723a5af1689041cda852cf5b51e5ed3dd237c1224fc01cf8457b6d0df1f1`. All six printed central theorem dependency lists contain only propext, Classical.choice and Quot.sound. No sorry, admit, custom axiom or native_decide occurs. Lean 4.19.0 and Mathlib commit c44e0c8ee63ca166450922a373c7409c5d26b00b are pinned. The Lake default target is Main and warningAsError is enabled.

## Adversarial author audit

1. The configuration domain is all integer-indexed three-symbol sequences, not a finite periodic sample, not just nonnegative sequences, and not only selected word extensions.
2. The topology is the ordinary product topology of the discrete alphabet. The genuine map and inverse are continuous; compactness is not assumed as an opaque hypothesis.
3. The map is an automorphism of the full shift: a homeomorphism commuting with the shift. Surjectivity and the inverse are explicit.
4. The radius convention is a symmetric window indexed -r,...,r. Radius one is the true minimal radius; the witness is not padded from a radius-zero rule.
5. Every claimed word is realized in an actual configuration, and the read/extend identity is proved for all n. The all-word cardinality is therefore the language cardinality of the actual system.
6. The lower cover estimate applies to every finite dynamical cover of the full space. The upper estimate supplies an actual cover of that same full space. Thus `coverMincard` is not assigned its desired value by definition.
7. U is an actual uniform entourage. Its n-step dynamical balls use the true iterate of the actual shift. The equality between those balls and length-n cylinders is proved.
8. The limsup exponential growth and supremum over entourages come from Mathlib's topological entropy definition. No custom proxy or unproved equivalence is substituted.
9. EReal allows the general entropy definition to take infinite values. The lower bound and strict counterexample remain valid regardless; no unjustified coercion of infinite entropy to a real number occurs.
10. The base of logarithm is immaterial to the failure: any common base b>1 scales both sides by the same positive constant. Lean uses natural logarithms consistently.
11. The source permits arbitrary finite alphabets. A binary-only radius bound would be a different statement and is not what the exact bilingual source says.
12. The independent finite verifier is a sanity check, not a theorem-prover oracle. It enumerates all words up to length 8, checks the actual bilateral-extension orbit traces, both inverse identities, both local rules and the radius-zero witness. The Lean proof independently handles every n and the full infinite configuration space.

## Reproduction

From the draft's `lean/`, run the pinned Lake `env lean -DwarningAsError=true Main.lean` and `build`; `round7/run_safe.py` supplies process-local Git trust for the local pinned dependency junctions. `round14/quantum/check9624.py` records complete commands, actual exit codes, times, frozen hashes and all output in `9624-status.json` and `9624-*.log`. Run `verify.py` independently for the exact finite checks.

No shared snapshot, publication allowlist, TeX, PDF, PR, other problem or editor state was changed. The only dependency update was fetching seven missing official pinned Mathlib cache modules needed for the actual topological entropy API.


Reviewed artifact hashes:

- Main.lean: `8753723a5af1689041cda852cf5b51e5ed3dd237c1224fc01cf8457b6d0df1f1`
- main.tex: `9383d2b78eb49bf63f4606c6d1ac9c2b6172885f0e85a543213b5f3fb1733639`
- main.pdf: `1af5a282b29ebe8e15dd4d2ded0dd210a0ac4657e28f29fe55ea95837e606fae`
- SOURCE.md: `332437d8b3b7784ae6a55b9b5e9636344b3b3b8b4aaf60424f22f965125f9ab3`
