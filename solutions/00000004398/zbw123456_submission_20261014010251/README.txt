Conjecture 00000004398: review candidate, not an accepted competition solution.

Scope
Uses precisely the printed single-density-determines-all-statistics definition,
interpreting density as homomorphism density. Actual finite simple graphs,
all vertex maps, edge-preserving maps, and cross-multiplied density equality
are defined. The enumeration is proved to contain every map, and the two
finite enumerations used are certified duplicate-free. This is not a Lean
formalization of graphon integrals or asymptotic quasirandom graph sequences.

Reproduction
Install Lean 4.19.0 through elan. In lean/, run lake build, then
lake env lean -DwarningAsError=true GraphDensity.lean.
No third-party Lean dependencies.

With pdflatex available, sh verify.sh also compiles the report twice.
No proof placeholders, native_decide, or custom axiom declarations are used.
Only standard Lean foundations occur in the axiom audit.

Publication
Prepared locally for review. No PR or Issue was created. Official metadata
and historical/open PR evidence are recorded in the separate batch audit.
