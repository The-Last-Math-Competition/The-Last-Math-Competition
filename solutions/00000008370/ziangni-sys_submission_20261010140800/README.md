# Reproduction and scope

A connected real metric segment of nonintegral length1/2 has canonical measure (delta_0+delta_r)/2 and actual continuous Arakelov Green kernel g(x,y)=1/8−abs(x−y)/2. Its nonzero diagonal value1/8 is rational, disproving the universal transcendence clause.

Main.lean defines the whole kernel, proves its actual piecewise derivatives, derives endpoint fluxes, and proves the exact graph Laplacian action on arbitrary test functions (including endpoint sources). The canonical endpoint integral is zero for every y in the interval. The PDF explains the continuous metrized graph bridge and uniqueness, citing the primary Baker–Faber definitions. There is no assumed Green certificate or finite-matrix surrogate.

From lean/, run `lake update` if dependencies are absent and `lake build`. Public pins: Lean4.19.0 and Mathlib c44e0c8ee63ca166450922a373c7409c5d26b00b. The build prints final axiom audits. Generated .lake files and local cache junctions are ignored. Compile proof.tex with Tectonic or another LaTeX engine. No auxiliary numerical computation is used.
