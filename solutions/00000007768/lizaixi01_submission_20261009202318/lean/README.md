# Pinned local package for 00000007768

`Main.lean` assembles the actual polynomial counterexample. It imports the three
included local modules and pinned Mathlib. The package toolchain is Lean 4.33.0;
the dependency revisions are in `dependency-pins.json`. Its mathematical and
bilingual correspondence is in `SourceCorrespondence.md`.

For an ordinary Lake checkout, place the exact pinned dependency package tree at
`.lake/packages` and run `lake build` with this `lakefile.toml`. No git/network
update is authorized by the package. The author instead uses an explicit private
compiled-library path and the supplied existing executable:

```powershell
./replay.ps1 -DependencyRoot <pinned-packages> -ToolchainRoot <lean-4.33.0-root> -CompiledLibrary <private-lib/lean>
```

`replay.ps1` compiles all four author modules sequentially with the actual relevant
Mathlib options, captures commands, source hashes and diagnostics, and exits on
failure. `Main` prints the final theorem axioms. A successful author run is still
preparation for an independent source review, mechanical gate and fresh replay.

`build_private.py` records exact original-source dependency compiles. Its private
library uses hardlinks to immutable existing compiled public files to support
Lean's top-level namespace lookup; it compiles only missing or privately generated
modules and explicitly refuses to overwrite any hardlink. All new outputs and
logs stay here. The first invocation lacked the source Lake options; the one
diagnostic retry with `autoImplicit=false,maxSynthPendingDepth=3` succeeded, and
the rebuild of private outputs is captured separately. Do not treat cached
outputs as fresh manager verification.

`proof.tex` was compiled with Tectonic 0.17.0 using only the pre-existing cache
copied into this directory. `proof.pdf` has two rendered, visually checked A4
pages. Source/Lean/PDF semantics must be reviewed together. The final strict result
and semantic-file manifest describe which obligations actually compiled; any
open obligation remains a blocker rather than a verified original solution.
