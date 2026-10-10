# Face-coloring counts do not determine matching parity

The actual planar trees K2 and K1,3 each have one face, hence the same face-coloring counts/classes, but have perfect-matching counts 1 and 0. Their parities differ. The report handles the usual distinct-face adjacency convention and the alternative convention that bridge self-adjacency forbids all face colorings; either gives equal input counts.

Lean verifies actual graph adjacency and perfect matchings, bijections enumerating actual oriented-edge darts, actual reversal/local rotations/face rules, one face orbit for each graph, equivalent coloring sets and counts, and unequal matching parity. No nonplanar/Petersen claim is required.

Reproduce using Lean 4.19.0: lake update then lake build inside lean. Public Mathlib pin: c44e0c8ee63ca166450922a373c7409c5d26b00b. Final theorem audits are printed. No sorry/admit/native_decide/custom axioms/unsafe. Ignored local junctions are conveniences only.
