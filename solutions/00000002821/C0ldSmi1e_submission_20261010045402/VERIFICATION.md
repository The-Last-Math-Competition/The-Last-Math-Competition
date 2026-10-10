# Independent engineering verification

The four mathematical Lean modules are copied byte for byte from the author freeze. The report.tex contains only two root-reviewed formatting fixes after the author freeze: emergency line stretch and break opportunities in a long library identifier. Its finalized SHA-256 is `38fe41578abcac30ace6dda4e363a9c88c419399e475388635e4bf116998a767`. The lakefile.toml is extended to build the independent Verification library; the manifest inputRev label is aligned with the already pinned exact Mathlib revision, without changing a dependency revision. The original verify.sh is preserved and executed.

Run with Python 3.9+ and Lean/Lake 4.19.0:

```sh
python3 verify.py --lean-bin /absolute/path/to/lean-4.19.0/bin --stock-mathlib /absolute/path/to/mathlib --work-dir /absolute/path/to/new-verification-run
```

The work directory must not exist and must be outside this package. The stock Mathlib checkout and its .lake/packages caches must match the pinned lake-manifest.json. On macOS the verifier clones the stock directory using copy-on-write; the caller's stock tree is never a compilation target. No authored compiled artifacts are reused. The verifier checks every tracked dependency file against its pinned Git blob before and after compilation. Stock compiled dependency caches are reused and individually fingerprinted; this is not a full rebuild of Mathlib or Lean. Mathlib.Analysis.SpecialFunctions.Log.ENNRealLog is rebuilt when missing.

The verifier performs a full Lake build, executes verify.sh, recompiles every authored mathematical and verification module with warnings as errors, and audits all declaration roots by originating module. Closure traversal includes types, bodies including opaque bodies, recursor rules, and inductive families and constructors. All 47 kernel mathematical declarations are safe, including generated proof auxiliaries. Six compiler-generated unsafe runtime declarations for support/speed are separately listed and excluded from mathematical roots; none is reachable from a mathematical root. All 53 declarations, including these six runtime entries, are inventoried exactly. The source guard prohibits authored unsafe declarations. Only propext, Classical.choice and Quot.sound are permitted as axioms. Infrastructure runtime declarations are separately inventoried and are not mathematical evidence. Exact declaration names and kinds are frozen in verification-manifest.json.

Negative controls exercise admission, custom axioms, native decision, unsafe declarations and proof use, a changed frozen file, and an unlisted module. Raw stdout, stderr and command receipts are timestamped; all failures are retained.

verification-manifest.json is a public reproducibility specification, not an authenticated signature. The final verification result records its SHA-256. The root-reviewed final report is frozen and is not revised by this engineering check. The report/PDF semantic review is handled separately.

## Bootstrap history

The first bootstrap lacked the verification library root import and failed the Lake job computation after all mathematical modules compiled. The second bootstrap applied the strict audit to compiler-generated runtime declarations as well as mathematical declarations; it rejected the runtime entries and confirmed all 47 mathematical declarations had clean closures. These failed attempts are preserved. The exact 53-entry compiled inventory was reviewed and frozen from this bootstrap, with the six runtime names explicitly enumerated; the final verifier independently rebuilds and requires that exact inventory.
