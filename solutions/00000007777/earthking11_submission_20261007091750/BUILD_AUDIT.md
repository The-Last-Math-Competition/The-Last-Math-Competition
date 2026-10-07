# Build and axiom audit

- Lean: `leanprover/lean4:v4.33.1`.
- Mathlib revision: `0df444a360eaa60ab8c11dca51a86af692955474`.
- `lake build`: succeeded for the final `Main.lean` (2329 jobs).
- `#print axioms TLMC7777.counterexample`: `propext`, `Classical.choice`, and `Quot.sound` only.
- No `sorry`, `admit`, `native_decide`, or custom axiom is used.
- No auxiliary computation is required; the orbit growth is proved for all subsequent iterates.
