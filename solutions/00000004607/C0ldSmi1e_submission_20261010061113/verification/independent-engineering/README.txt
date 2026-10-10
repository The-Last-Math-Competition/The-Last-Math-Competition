Independent engineering verification: conjecture 00000004607

The frozen Lean sources passed a fresh offline Lake build, followed by strict
warning-as-error direct Lean compilation of every authored source and an
independent transitive declaration/axiom audit. Mathematical interpretation,
report semantics and PDF production are separate reviews.

Frozen proof identity
  Author MANIFEST.json:
  41469ccd4692e117267c9b13f49578928c00dd3471ec148a7dee43103729eb02
  Disproof.lean:
  d205fbd455ce337943421b4f73ed623feecb7da08ca1027ee359998d1366a146
  Original report.tex:
  ab294d6267a8b356b300a2292b26f5b9924c01014219a78d249fd87ed09ccd5a

Actual results
  Four local declarations were selected by originating module, independently
  of their namespace. All four are kernel-safe. Their complete exported graph
  has 5,253 reachable declarations. Every safe root has no unsafe dependency
  and only the allowed axioms propext, Classical.choice and Quot.sound. There
  are no compiler-generated unsafe roots in the submitted mathematical modules.
  AxiomAudit contributes no declarations and independently prints the three
  capstone axiom sets. The full declaration types and graph are retained.

  The nine dependency packages match their pinned Git revisions and have clean
  tracked source trees. All tracked source files were hash-compared with the
  private copies. All 2,413 external imported modules were bound either to
  byte-identical stock .olean files and source hashes, or to supplied runtime
  .olean identities. Runtime executable/library hashes are retained separately.

Trust controls
  Fresh operational fixtures demonstrate acceptance of an ordinary safe
  definition and rejection of an unused axiom in an unrelated namespace,
  transitive axioms through an opaque value, sorryAx, native_decide's
  Lean.ofReduceBool/Lean.trustCompiler, and an explicitly unsafe declaration.
  The sorry fixture also fails direct strict compilation. These controls do
  not use mathematics or proof/control content from another conjecture.

Preparation and operational records
  preparation/run-0001 preserved an actual infrastructure failure: applying
  all-root unsafe rejection to a safe definition also rejected its generated
  runtime helpers. The corrected positive control enforces trust on safe roots
  while still exporting generated helpers; the explicit unsafe control uses
  all-root rejection. preparation/run-0002 passes.

  run-0001 passed the complete proof checks, but its read-only Git status
  commands did not disable optional index refresh. A later stock/private-clone
  index comparison found differences; this is not a before/after stock check
  and does not establish a stock mutation, since Lake can refresh private
  clone metadata. No stock metadata was restored. run-0002 records the single
  failed attempt to add an operating-system sandbox; the host rejected nested
  sandbox-exec with “Operation not permitted” before Lean ran. It was not
  escalated or retried.

  run-0003 is the final replay. It sets GIT_OPTIONAL_LOCKS=0, reads stock Git
  state using only read-only commands, uses fresh private dependency copies,
  and checks original stock index hashes before and after. Network downloader
  commands and unexpected Git operations are denied during the Lake build;
  Lake cache downloading is disabled. The exact full commands, environments,
  output, errors, exits, source hashes and all earlier records are retained.

Reproduce
  Keep verify.py and templates/ClosureAudit.lean.txt together. Supply a stock
  Mathlib v4.19.0 tree with its pinned packages and cached imports, a Lean 4.19.0
  bin directory, and a fresh output directory. The current copy command uses
  macOS copy-on-write cp -cR; on another operating system replace that copy
  command with a recursive copy preserving a distinct writable destination.

  python3 verify.py verify SUBMISSION MANIFEST STOCK_MATHLIB LEAN_BIN NEW_OUTPUT

  MANIFEST may be the supplied FROZEN.json, the author's original MANIFEST.json
  with a files array, or a final-package SHA256SUMS.json path-to-hash map.
  Explicitly passing a manifest selects and verifies those exact bytes. The
  driver verifies every manifest entry and checks them again at completion.
  All current .lean files outside .lake, .git and evidence are discovered;
  excluded historical attempts must remain non-executable archival records.
  No authored .olean or .lake cache is copied. Lake rebuilds the project from
  source and direct strict compiles repeat every authored module. For a new
  project any unsafe runtime roots cause a pending result until their
  compiler-generated provenance is reviewed explicitly.

  python3 verify.py prepare STOCK_MATHLIB LEAN_BIN NEW_OUTPUT

  The preparation mode compiles only the inspector and the generic trust
  fixtures. It does not open or validate a submission.

Scope and limitations
  The generic inspector was reused from the authorized earlier engineering
  template; the operational driver was adapted and fresh controls were written.
  This is not a from-source rebuild of all Mathlib, its dependencies or Lean.
  Cached imports are tied to the supplied stock cache and source identity.
  The trusted Lean runtime was not bootstrapped independently. Author sources
  were first accessed only after the parent's explicit frozen-source trigger;
  nothing was written to the author package. No publication, external message,
  network operation, or PDF operation is part of this engineering task.
