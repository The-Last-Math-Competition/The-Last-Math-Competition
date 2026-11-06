# Verification scope

This AI-assisted submission refutes the half-integrality conjunct of conjecture 00000008875. It does not claim separate results about mast uniqueness or a probability distribution on random games.

The finite game is `quarter = {0 | {0 | 1}}`. The Lean development uses recursive Conway comparison, the finite birthday/simplicity construction for number values, and the conventional positive-temperature numerical thermograph base case. The final theorem `TLMC8875.disproof_even_with_nimber_exception` negates half-integrality even after excluding games equivalent to any recursively defined nimber. The nimber exclusion is quantified over every natural number, not a finite empirical check.

The numerical thermograph base case is sufficient for a counterexample to the universal claim. No complete implementation of general cooling theory, negative-temperature thermography, or thermography of all non-numerical games is claimed.

Source reviewed: upstream commit b355e42906e6eaf52bc7e9d005e0ef02d8aa7400. Primary mathematical reference: E. R. Berlekamp, *The Economist's View of Combinatorial Games*, 1996, section 2.5, page 388 and Figure 18, https://math.berkeley.edu/~berlek/papers/econview.pdf .

Independent clean-directory validation used Lean 4.31.0: `lake build`, `lake env lean -DwarningAsError=true Main.lean`, and `lake env leanchecker Main`, all with exit status zero. The final theorem's reported axioms are only `propext`, `Classical.choice`, and `Quot.sound`. The source contains no `sorry`, `native_decide`, or custom axiom declarations. These local results are not an upstream acceptance or CI result.

Reviewed Main.lean SHA-256: 48285b8ef6c2014de67b0ec541efdb56da031ebc5a1e34a89d64c6847c4a5e11.

The submission is provided under the repository's GNU GPL version 3 license. It was prepared and checked with AI assistance; no human review is asserted.
