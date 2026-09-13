/-
  Development diagnostics scratch file (not part of the `tlmc8234` library).

  This file was used to probe which core-Lean features are available
  (`List.finRange`, `Fin.cases`, decidability of the swap-graph adjacency, ...)
  while developing `Main.lean`.  It is kept for the record and is deliberately
  minimal; the finished formalisation is in `../Main.lean`.  `lake build` builds
  only the `Main` library, so this file is not compiled by the project build.
-/

import Std

namespace Diag

/-- `List.finRange` is available in core Lean / `Std` (used by `Main.lean`). -/
example : (List.finRange 3).length = 3 := by decide

end Diag
