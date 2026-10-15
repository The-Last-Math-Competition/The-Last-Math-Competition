# Verification record

Verified on October 15, 2026, using Lean 4.24.0 and TeX Live 2025.

The following commands all completed with exit code 0:

```console
cd lean4
lake build
lake env lean Conjecture7973.lean
lake exe verify
cd ..
python verify.py
```

`lake build` completed with six jobs. The main theorems
`minimum_weight_two`, `not_minimum_weight_three`, `counterexample`, and
`refutes_every_claim_covering_this_code` depend only on `propext` and
`Quot.sound`. The field-law and complete weight-enumerator theorems depend
only on `propext`. No proof holes, native decision shortcuts, or custom
axioms occur in the source. The Lake manifest has no external packages.

The independent Python check enumerated nine distinct codewords with
weight counts `{0: 1, 2: 6, 3: 2}`. It is supplementary; Lean establishes
the lower bound for every member of the code, as well as the witness.

The final report was compiled twice with shell escape disabled. Both pages
were rendered to images and inspected. The final LaTeX log has no warnings,
overfull boxes, or underfull boxes.

An independent second agent reviewed the mathematical identification,
all hypotheses, the finite-code quantifiers, and the formalization scope,
and repeated the Lean checks successfully. The complete Weierstrass
semigroup at infinity is also specified in the report.

Selection used upstream `cce2d90c`: both solved flags were false, and no
upstream solution directory existed. An all-state GitHub PR search for
`00000007973` returned no previous submission. Only this personal submission
directory is part of the contribution.
