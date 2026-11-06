# Statement Alignment and Evidence Boundaries

The unchanged bilingual conjecture is preserved byte-for-byte in `source.md`.
Official commit: `b355e42906e6eaf52bc7e9d005e0ef02d8aa7400`.
Git blob: `001aa6f79c0aaaa70d0907eb42b9fb5169beb631`.
Raw SHA256: `db3ca796bb8d3bd640ca4ae51be82bb4a2beba95e7554c3691a2b1e307d7779a`.
Only current organizer-checkout CRLF-to-LF comparison is normalized; the frozen
Git blob is neither rewritten nor replaced with an easier conjecture.

## Meaning Actually Established

The source requests a finite explicit list of S(2,k,n)_q for each n and k
dividing n. Standard finite-field q means a prime power greater than one.
Standard subspace-design parameters have 2 <= k <= n. These conventions are
stated openly and occur in both the actual target and the running algorithm.
Invalid k,n produce an empty list, including n=k=0; they do not produce
vacuous nonstandard designs. The field search is total for all natural q,
returning failure when no valid table is found.

An explicit list here means a specified terminating finite enumeration with
proved exact membership. It does not mean a closed classification formula,
an efficient enumeration, a nonempty list, or one representative per
isomorphism class. The source gives no such stronger requirement. The result
is labelled exhaustiveness; it is not a solution to the usual difficult
existence/classification questions for proper q-Steiner systems.

## Source to Mathematical Object to Lean

| Requirement | Actual object or quantifier | Lean evidence |
| --- | --- | --- |
| Only q,n,k as executable inputs | Search finite operation tables on Fin q, then enumerate finite vector carriers and block families | `QOnly.catalogue`, `firstFieldTable`, `fieldTables`, `Explicit.catalogueList` |
| Genuine finite field | Computable operations on a fresh label wrapper, all Field laws proved from finite tests | `TableElem`, `TableValid`, `fieldOfTable`, `tableElem_card` |
| Every standard q | For every prime power q a finite field exists, its table occurs in the search, so the first-valid search succeeds | `firstFieldTable_exists_of_isPrimePow`, `QOnly.catalogue_exists_prime_power` |
| No noncomputable oracle in the running entry | GaloisField is used only for existence; arbitrary model isomorphisms are proof-side semantics | `FieldExistence`, `QOnly.modelEquiv`; actual strict q-only small Demo |
| Blocks are linear subspaces | Closed finite carriers decode to actual Submodule K (Fin n -> K) and encode back | `toSubmodule`, `ofSubmodule`, `toSubmodule_ofSubmodule`, `ofSubmodule_toSubmodule` |
| Dimension is real finrank | Cardinality equals q^finrank; q>=2 makes powers injective | `card_eq_pow_finrank`, `card_eq_pow_iff_finrank`, `mem_dimCarriers_iff_finrank` |
| Every 2-subspace lies in exactly one block | Actual submodule inclusion and uniqueness, equivalent to the finite incidence filter | `Catalog.actualDesign`, `Catalog.incidence_encode_iff`, `Catalog.catalogue_sound`, `Catalog.catalogue_complete` |
| Finite explicit List, not classical selection of a list | Enumerate actual tuples and sublists, filter and deduplicate; membership agrees with the finite-set catalogue | `Explicit.subsetCodes`, `Explicit.catalogueList`, `Explicit.mem_catalogueList`, `Explicit.catalogueList_nodup` |
| Every actual design occurs once as a labelled code | Soundness, completeness and inverse encode/decode identities | `QOnly.actualDesign_iff_existsUnique_output` |
| Not tied to a specially supplied field | For any field K with card K=q, a fixed ring isomorphism transports actual coordinates, subspaces and families in both directions | `Transport.subspaceIso`, `Transport.subspace_finrank`, `Transport.actualDesign_transport_iff`, `QOnly.actualDesign_iff_output_over_model` |
| Arbitrary sets of blocks, no extra finiteness assumption | Every set of ambient subspaces is finite, with an injective set-to-finite-family encoding | `SetFamilies.every_family_finite`, `SetFamilies.finiteFamily_injective`, `SetFamilies.actualSetDesign_iff_output` |
| For each n and k dividing n | A stronger all-n,k catalogue result is specialized without assuming a design exists | `QOnly.source_conjecture`, `SetFamilies.source_conjecture_sets` |

The final theorem quantifies arbitrary set-valued actual design families over
every finite field model of order q. It characterizes exactly one member of
the SAME q-only output, relative to the fixed semantic field transport.
Neither the target model, its isomorphism, nor a desired design is an input
to the executable catalogue.

## Verification Scope

`Check.lean` explicitly requests actual types and transitive axiom footprints
for all 122 advertised mathematical theorems. `CheckDefinitions.lean`
separately requests types and axioms for 50 definitions, structures and instances,
including the finite decisions and actual field constructor. The only permitted
axioms are propext, Classical.choice and Quot.sound. Exact reviewed source hashes
are a gate in the reproducer; declaration scanning is not advertised as a
general Lean parser or a malicious-code sandbox.

The reproduction interface requires an own-project clean build from exact
physical dependency checkouts, all theorem/definition audits, the strict
small Lean Demo, and bounded independent-representation Python checks/tests.
The installed compiler and existing official dependency build caches remain
trust inputs. No full-dependency-clean, empty-machine bootstrap, Linux,
hosted-CI or operating-system-sandbox execution is claimed.

The strict Lean diagnostic computes q=2 field search, the whole-space design
at (q,n,k)=(2,2,2), invalid (2,0,0), and q=0,1 failures. The earlier mixed
diagnostic including n=3 exceeded 180 seconds and lacked retained partial
stdout; that failure is not converted into successful n=3 Lean execution.
Separate bounded Python computations at dimensions up to3 are not general
proofs and do not establish efficient execution of the Lean catalogue.

Independent research-core review is not independent final-package review.
The original two 60-second independent timeouts remain recorded; after
aligning the full fixed Lake runtime-path environment, the independent
reviewer compiled all11 modules and the strict Demo, checked all122 actual
types/axioms, and stayed within the original cumulative300-second compiler
budget. No particular environment key was isolated as the sole cause.

This file records mathematical alignment and required verification scope.
Actual whole-package, PDF and final-review outcomes must come from their
real execution records, not these requirements. No acceptance, first-solve
credit, human endorsement, affiliation, score, ranking or award is claimed.
