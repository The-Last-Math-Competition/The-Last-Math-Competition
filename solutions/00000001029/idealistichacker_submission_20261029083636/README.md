# Conjecture 00000001029: An Executable Labelled Exhaustive Catalogue

Solver: idealistichacker. Mathematics and implementation are AI-assisted.
The mathematical verdict is **proved** in the finite explicit labelled-list
sense stated below. This is not a nonemptiness or efficiency theorem, a
structural classification, or a unique-isomorphism-representative catalogue.

## Exact Source And Scope

`source.md` preserves both original languages from organizer commit
`b355e42906e6eaf52bc7e9d005e0ef02d8aa7400`, Git blob
`001aa6f79c0aaaa70d0907eb42b9fb5169beb631`, raw official UTF-8 SHA-256
`db3ca796bb8d3bd640ca4ae51be82bb4a2beba95e7554c3691a2b1e307d7779a`.
For organizer-checkout comparison, only CRLF-to-LF normalization is allowed;
do not trim text, normalize other whitespace, or silently change the source.

Both languages request a finite explicit list of S(2,k,n)_q for each n and
k dividing n. Here q has its standard finite-field meaning: a prime power
p^m with p prime and m > 0. The construction proves a stronger all-n,k result,
then specializes to k dividing n. The standard guard 2 <= k <= n is included
in BOTH the algorithm and actual mathematical design predicate.

The output is an actual duplicate-free Lean `List` of labelled block-family
codes, with exact membership proved. Labelling fixes field labels and vector
coordinates. No quotient by GL, semilinear, or general incidence isomorphisms
is taken. The code list can be empty; no unknown efficient classification or
existence of a design for every admissible parameter is asserted.

## Executable Input And Actual Output Meaning

`Steiner1029.QOnly.catalogue q n k` takes only natural numbers q,n,k. It does
not take a field, basis, oracle, externally selected model, or a supplied
solution family. It is a total finite algorithm: failure to find any valid
field table returns `none`; a successful result contains its chosen field
table and a finite `codes` List. Every prime-power q is proved to give `some`
result. For any successful field result, invalid 2 <= k <= n gives an empty
code list, including n=k=0. Empty list and failed field search are distinct.

A block decodes to a genuine `Submodule K (Fin n -> K)`. An actual design D
has every block of actual `Module.finrank K` equal to k, and EVERY actual
2-dimensional submodule U is contained in exactly one block W of D. These
are statements about real submodules and their order, not only Boolean tests,
bases, arbitrary vector subsets, or assumed filter conclusions.

For every actual field K of cardinality q, a fixed proof-side field
isomorphism from the selected table field to K acts in each coordinate.
Actual subspace containment, finrank, and unique containment are preserved
both ways. Every actual design over K is obtained from exactly one output
member after that fixed transport. Uniqueness is labelled and relative to
this fixed transport, not uniqueness up to an isomorphism class.

There is no extra finiteness premise on an arbitrary set of blocks. The
ambient submodule type injects into the finite carrier-code type, so every
`Set (Submodule K (Fin n -> K))` is proved finite. `FamilySets` proves the
set-to-Finset membership bridge and the exact output theorem for arbitrary
set-valued design families. The main final theorem is
`Steiner1029.SetFamilies.source_conjecture_sets`.

## Finite Enumeration And Formal Bridges

1. Enumerate all zero/one labels and all addition/multiplication tables on
   `Fin q` using primitive finite tuple/function enumeration in a fixed order.
   Bounded tests check sufficient minimal field axioms. Choose the first valid
   table. `Field.ofMinimalAxioms` reconstructs an ACTUAL computable Field on
   the fresh `TableElem` wrapper. Negatives and inverses use bounded `Fin.find`
   searches; inverse of zero is defined explicitly. There is no input field.
2. For prime-power q, an existing finite field can be relabelled onto `Fin q`.
   Its operations occur in the enumerated tables and pass every test, proving
   the first-table search succeeds. `GaloisField` and classical relabelling
   occur only in existence proofs, not on the executable catalogue path.
3. Enumerate the powerset of the actual finite vector space. Test zero,
   addition, and all scalar closure by finite decisions. Passing carriers
   decode to actual submodules; every actual submodule has a unique code.
   Equality, inclusion, and cardinality agree with the actual objects.
4. The actual theorem `Module.card_eq_pow_finrank` gives carrier.card =
   q^(actual finrank). Since a field has q >= 2, natural exponentiation is
   injective. A cardinality filter therefore enumerates EXACTLY the
   k-dimensional subspaces, without executing a noncomputable finrank.
5. Enumerate all families of k-dimensional codes. Retain one exactly when each
   2-dimensional code is included in exactly one block code. Soundness,
   completeness, encode/decode inverse laws and labelled uniqueness are
   proved against the actual incidence predicate. List conversion preserves
   membership and is proved `Nodup`.
6. The same-cardinality finite-field ring equivalence, pointwise semilinear
   coordinate equivalence and actual submodule order isomorphism transfer the
   statement to EVERY field model of order q. FamilySets removes any
   finite-family hypothesis for arbitrary sets of blocks.

The 11 mathematical modules, in dependency order, are FieldTables,
TableFields, CarrierCodes, Catalogues, ExplicitLists, QCatalogue,
FieldExistence, PrimePowerCatalogues, Transport, Main, and FamilySets.
`Demo.lean` is a separate diagnostic. `Check.lean` imports FamilySets and
checks the sorted inventory of all 122 public mathematical theorems with
their actual axiom footprints; `submission.json` lists the identical names.
The separate `CheckDefinitions.lean` entry audits 50 definitions, structures
and instances without adding commands to the exact theorem-only Check file.
Both audit entries and the strict small Demo run in the complete reproducer.
Only standard `propext`, `Classical.choice`, and `Quot.sound` are permitted.
Classical encoding, field-isomorphism selection, and transport facts used in
proofs do not replace the specified running enumeration by classical choice.

## Reproduction Contract And Current Validation Boundary

Pinned Lean: `leanprover/lean4:v4.33.1`. Pinned Mathlib:
`0df444a360eaa60ab8c11dca51a86af692955474`. The Lake lock records all nine
physical Git dependencies with exact revisions, not just the Mathlib name.
Every flat source module is explicitly registered as a library root, together
with Check, CheckDefinitions and Demo; warnings are errors. CheckDefinitions
and its exact manifest inventory are included in this package.

Run the reproducer from this submission directory:

```text
python reproduce.py --lake <pinned-installed-lake> --repo <organizer-checkout>
python reproduce.py --lake <pinned-installed-lake> --repo <organizer-checkout> --skip-update
```

`--lake` must identify the installed Lean 4.33.1 Lake executable. `--repo`
identifies the organizer source checkout for the exact-source comparison.
Default dependency preparation may access the pinned public sources.
`--skip-update` is an explicit OFFLINE exact-dependency mode,
not permission to skip verification or accept a merely matching version string.

The offline audit resolves all NINE physical checkout paths and
checks each source/origin URL, exact HEAD against the lock revision, full Git
tree and index, every tracked raw byte, and physical path boundaries before
AND after reproduction. It performs a clean OWN-PROJECT build with
no reused author-module outputs, audit all 122 actual theorem types/axioms,
run the strict small Lean Demo and the bounded independent diagnostics/tests,
and records actual exits and source/dependency stability. All real symlinks,
junctions and reparse points are rejected. On Windows only, three fixed Git
link entries are accepted as exact inert ordinary link-text files: two
Mathlib benchmark helpers and one batteries document. Their immutable blob
IDs are in `WINDOWS_LINKTEXT`; none is executed and unknown link entries
remain blocked. Reading installed dependency caches remains a trust input;
an own-project clean build is not a full-dependency-clean rebuild or an
empty-machine, Linux, hosted-CI, or OS-sandbox validation.

The author ran the complete offline reproduction on October 29, 2026,
09:38:29--09:42:23 UTC. It exited 0 in 234.125 seconds under the default
285-second internal budget, with nine dependency audits before and after,
an empty-own-build reconstruction of all 11 mathematical modules, all 122
theorem and 50 definition/instance type/axiom audits, the strict Lean Demo,
and all 55 Python tests passing without skips. This author run preceded only
this README validation-status update; final frozen-package independent review
must execute the complete reproducer again rather than inherit that result.

The preserved mathematical-core freeze is
`8cbf2af2ca5490ffbf06536d51ffc43d9fd261c5ce96d3410ca3a99d101a30d4`.
It is a research-core identifier, NOT the final submission content hash.
Independent AI core review recorded PASS for the 11 modules, 122 actual
types/axioms and strict small Demo. Earlier failed/blocked attempts are kept.
This core result does not approve this assembled package, reproducer, tests,
dependency relocation, final PDF, publication, or a later changed source.
`main.tex` and the actual compiled `main.pdf` are included; author build/visual
checks do not substitute for final independent frozen-package/PDF review.

## Diagnostics, Cost And Disclosures

The successful strict small Lean Demo observed q=2,n=2,k=2 returning one
family with the whole-space block; q=2,n=k=0 returning an empty code list;
and q=0 or 1 returning no field model. It is a diagnostic, not the generic
proof. An older combined Lean Demo containing n=3 timed out at the original
180-second bound; that failed attempt is retained. No n=3 Lean catalogue
computation is claimed. Separate bounded Python diagnostics did execute
GF(2) n=3 examples, and are not Lean-evaluation or all-parameter evidence.
The independent Python diagnostic interface is restricted to 0 <= n <= 3;
this executable diagnostic bound is not a restriction on the generic theorem.

The enumeration is finite but may be extraordinarily expensive. No practical
runtime or memory guarantee, nonempty catalogue for every valid parameter,
canonical field-isomorphism choice, or structural/isomorphism classification
is claimed. Exact finite tests cannot replace the general formal bridges.

AI agents assisted mathematics, code, documentation and independent core
review for idealistichacker. A separate AI reviewer is not a human reviewer;
shared toolchain/cache correlation remains a disclosed limitation. At the
author checkpoint, final frozen-package review and coordinator validation
were still pending. Their later outcomes require actual hash-bound review
and execution records; this README is not a substitute for either.
No human endorsement, affiliation, upstream acceptance, publication, score,
ranking, first-solve credit, or award is claimed.
