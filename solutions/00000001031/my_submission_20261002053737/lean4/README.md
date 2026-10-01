# Lean 4 machine check (core Lean, no Mathlib)

Proves, by pure computation (`rfl`, zero `sorry`, zero axioms):

- `D = {1,2,4}` is a (7,3,1) difference set: each nonzero residue of `Z_7`
  arises as an ordered difference exactly once (`diffs_cover_*`).
- The multiplier group `{t : tD = D}` is exactly `[1,2,4]`, order 3
  (`multGroup_value`, `multGroup_order`).
- The conjectured norm subgroup `N(F_8/F_2) = F_2^*` has order `q-1 = 1` and
  index `q^2+q+1 = 7` (`normSub_order`, `normSub_index`).
- `multGroup ≠ normSub` — conjecture 00000001031 is FALSE
  (`conjecture_claim_bool`, `multGroup_ne_normSub`), and the "no other
  multipliers" clause fails too (`other_multipliers_exist`).

## Build

```
lake build && lake env lean Check.lean
```

Every `#print axioms` line must report "does not depend on any axioms".
