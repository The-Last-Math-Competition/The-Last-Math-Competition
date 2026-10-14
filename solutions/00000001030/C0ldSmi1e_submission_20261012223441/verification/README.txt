FROZEN-SOURCE VERIFICATION

The mathematical source inventory is frozen-sources.json. Its paths are
relative to ../lean. expected-pins contains the exact toolchain and dependency
manifest used as independent inputs. Review the main proof separately from
the audit machinery: the latter deliberately tests rejection of invalid
fixtures, including admitted proofs and custom axioms. Those fixtures are not
part of the submitted mathematical project or any theorem dependency.

The portable ordinary build is described in ../README.txt. The stricter
verification driver used for this submission runs on macOS and requires a
previously populated, pinned generic Mathlib checkout and the Lean 4.19.0 bin
directory. STOCK below is that Mathlib checkout itself; its transitive packages
and compiled artifacts must be present under .lake. LEAN_BIN contains lean and
lake. OUT must be a new output directory. From the submission directory:

  python3 verification/verify.py verify lean \
    verification/frozen-sources.json STOCK LEAN_BIN OUT \
    verification/expected-pins
  python3 verification/check_audit_graph.py OUT/declaration-audit.json
  python3 verification/test_hardening.py NEW_HARDENING_OUTPUT

Replace the uppercase arguments with actual paths; choose previously nonexistent
output directories. The driver preserves failures and their receipts instead
of overwriting them. It performs:

* Exact source/configuration and expected-pin checks; a source-token audit.
* Private clone-on-write dependency copies, checking every tracked package
  source against its pinned Git blob, and recording cache/runtime identities.
* A fresh owned-source Lake build with --no-cache --wfail, followed by a direct
  -DwarningAsError=true replay of every owned Lean source, including both
  auxiliary audit modules and a strict lakefile compilation.
* An imported-environment declaration dependency audit. It follows type, body,
  recursor and inductive dependencies, compares axiom collections, requires
  named capstones, and checks all safe owned declarations against the three
  standard axioms with no unsafe proof dependencies.
* Actual import resolution and source/cache identity checks, rejecting shadows,
  unexpected owned compiled modules, and changed or untracked package artifacts.
* A valid control and five invalid Lean controls: direct and transitive custom
  axioms, an admitted proof, native_decide, and an unsafe declaration. Separate
  hardening controls test mutation, shadowing, missing provenance and pins.
* Source, dependency-index, runtime, and pin stability checks after verification.

The graph checker independently reconstructs closure/trust summaries from the
exported graph. This is not a second extraction of the Lean environment or a
second kernel implementation. Lean source compilation supplies kernel checking;
the audit records kernel_check_performed=false to avoid overstating its role.

Evidence layout

engineering-summary.json and the local review reports summarize the run.
The original unoptimized auditor completed successfully and supplies the
authoritative evidence. Its generic summary deliberately retains
PASS_PENDING_RUNTIME_HELPER_CLASSIFICATION. engineering-verdict.json and
runtime-helper-classification.txt resolve that condition: all 45 compiler
runtime helpers are excluded from all 244 safe owned declaration closures.
The original inspection took about 21 minutes; allow time for reproduction.
engineering-evidence.tar.gz preserves the full JSON/log evidence, command
receipts, source/cache inventories, generated audit source and controls. It
omits bulky dependency checkouts and compiled binaries. Supplemental performance
corroboration includes the separately reviewed faster inspector and its test
sources/receipts. Both full runs produced byte-identical audit graphs; the
authoritative original graph is stored once. To inspect it, extract
into an empty directory, then run check_audit_graph.py on the extracted
engineering/declaration-audit.json. The archive's file inventory binds each
stored member by SHA-256. Original absolute working paths in receipts identify
the actual run; they are not paths required to rebuild this submission.

Limits

The generic dependency compiled artifacts were reused after identity checks;
all Mathlib sources were not rebuilt. The supplied Lean runtime was not
bootstrapped. PATH wrappers deter unexpected command-line network access but
are not operating-system network isolation. Mathematical definitions, report
scope, and auxiliary/configuration/metaprogramming side effects require source
review in addition to compilation. Generated unsafe runtime helpers, if any,
must be classified separately and cannot occur in safe proof dependencies.

The included evidence reports actual local checks. It does not claim maintainer
acceptance, theorem novelty, or independent human review.
