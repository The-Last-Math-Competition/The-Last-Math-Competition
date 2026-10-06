# Disproof of conjecture `00000003836`

**Verdict: false.** Under the standard signature convention that repeatedly
deletes adjacent `+ -` pairs, the two-letter word itself is a counterexample.

- For `w = [+,-]`, the adjacent pair cancels, so the output is empty and has
  `0` plus signs.
- Its cyclic rotation is `rot(w) = [-,+]`.  There is no adjacent `+ -` pair,
  so the reduced output is `[-,+]` and has `1` plus sign.

Thus cyclic rotation changes the plus count from `0` to `1`.  The first clause
of the conjecture is false, so the conjunction is false independently of how
the string parameter in the second clause is interpreted.  With the opposite
sign convention the same two rotations exchange roles.

## Formal verification

`lean4/Main.lean` implements the classical cancellation with a stack, defines
one-step cyclic rotation, evaluates both outputs, and proves the universal
rotation-invariance statement false.

```sh
tectonic --outdir build main.tex
cd lean4
lake build
lake env lean Check.lean
```

The project uses only core Lean/Std and has no proof placeholders.
