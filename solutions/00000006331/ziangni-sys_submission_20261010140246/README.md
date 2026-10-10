# Disproof of 00000006331: infinitely many constructed Hadamard orders

The actual Sylvester matrices H_0=(1), H_(n+1)=[[H_n,H_n],[H_n,-H_n]] are Hadamard matrices of order2^n for every n. Their attainable orders are unbounded, contradicting the finite construction-spectrum clause under its attainable-order meaning.

The report explicitly states this interpretation. It does not identify the construction spectrum with the set of missing orders, classify Paley constructions, or settle the Hadamard conjecture.

## Reproduce

With Lean4.19.0 run `lake build` in `lean/`. Public Mathlib is pinned to c44e0c8ee63ca166450922a373c7409c5d26b00b; the manifest pins its public transitive dependencies. Local cache junctions are ignored and not required for reproduction.

## Formal scope

`Index` and `sylvester` construct the actual finite integer matrices recursively. `card_index` gives order2^n; `entries_sign` proves every entry is1 or-1; `row_inner` proves every row inner product is exactly2^n on the diagonal and0 off it. `sylvester_is_hadamard` reindexes onto Fin(2^n) to prove the ordinary finite-matrix Hadamard definition. `arbitrarily_large_constructed_orders` and `construction_spectrum_infinite` prove unboundedness and infinitude of the actual attainable-order set.

The complete proof is symbolic and requires no auxiliary program or certificate. The full build prints six final axiom audits, all limited to propext, Classical.choice, and Quot.sound. There are no proof placeholders, custom axioms, or native_decide calls.
