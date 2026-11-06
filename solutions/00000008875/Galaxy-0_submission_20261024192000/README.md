# Disproof of conjecture 00000008875

The short number game Q = {0 | {0 | 1}} has value 1/4. At positive temperatures its numerical thermograph is the vertical line at 1/4, not a half-integer. Q is not equivalent to any nimber *n, so the named exception does not apply.

## Files

- `solution.tex`, `solution.pdf`: mathematical proof, source interpretation and exact formalization scope.
- `Main.lean`: self-contained finite-game, dyadic-value, thermograph-number-base-case and nimber-exclusion proofs.
- `lean-toolchain`, `lakefile.toml`: pinned Lean 4.31.0 project, no external packages.
- `reproduce.sh`: local validation commands. It does not install software or download dependencies.

## Reproduce

With Lean 4.31.0 and Lake already installed and on PATH, run:

```sh
bash reproduce.sh
```

This runs `lake build`, `lake env lean --error=warning Main.lean`, and `lake env leanchecker Main`. Start from a fresh copy of the submitted sources for a clean build.

With a normal installed TeX Live environment, regenerate the document with:

```sh
pdflatex -interaction=nonstopmode -halt-on-error solution.tex
pdflatex -interaction=nonstopmode -halt-on-error solution.tex
```

Both commands were actually run successfully. The supplied PDF has two pages and was rendered and visually checked. The execution image needed explicit paths for existing TeX files/fonts and its already present format; this did not change the source or install dependencies. The independent validation log records Lean checks.

## Coverage and limitations

`disproof_even_with_nimber_exception` refutes the universal half-integrality consequence even after excluding all game values equivalent to nimbers. `quarter_not_equivalent_nimber` is quantified over every natural n and uses the actual recursive Conway game order. `quarter_numeric_wall` evaluates Q itself; it does not assign a separate desired wall constant.

The thermography formalization is deliberately restricted to its standard numerical base case and positive rational temperatures. The concrete simplest-dyadic calculation is kernel checked. General soundness of the evaluator on all possible games and thermography of arbitrary non-number games are not claimed. These are not needed for the exhibited numerical counterexample. The PDF explains the precise link to the standard definition and cites Berlekamp's original numerical-thermograph discussion.

No `sorry`, `native_decide`, custom axioms, or kernel-bypass mechanisms occur. `decide +kernel` uses Lean kernel reduction. Final proof dependencies are only `propext`, `Classical.choice`, and `Quot.sound`.

## Provenance

Source conjecture checked against upstream commit `b355e42906e6eaf52bc7e9d005e0ef02d8aa7400` on 2026-10-24. This submission was prepared with AI assistance; mathematical/source/coverage review and actual tool validation were performed by AI agents. No human review is claimed. Submission does not imply acceptance or scoring. Files are contributed under the upstream repository's GPL-3.0 license; no root license is changed.
