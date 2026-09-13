/-
  Development scratch file (not part of the `tlmc8234` library).

  This file was used only while developing `Main.lean`.  It is kept for the
  record and is deliberately minimal: the finished formalisation is in
  `../Main.lean` and its audit is in `../Check.lean`.  `lake build` builds only
  the `Main` library, so this file is not compiled by the project build.
-/

import Std

namespace Scratch

/-- A placeholder example so the file is not empty. -/
example : (2 : Nat) + 2 = 4 := by decide

end Scratch
