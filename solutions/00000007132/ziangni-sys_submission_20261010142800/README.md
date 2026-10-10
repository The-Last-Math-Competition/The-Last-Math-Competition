# Reproduction and scope

The actual Minkowski sum of two coordinate segments is the square. Its associated two-axis arrangement has four connected quadrant regions; the square has eight nonempty proper faces. Lean constructs five distinct proper exposed faces, already more than four.

Main.lean proves the actual segment-sum equality, exposed faces as maximizers of real linear functionals, distinctness/properness, connectedness of quadrants, and the intermediate-value obstruction to any connected set crossing an axis. The PDF explains the exact face counts and the correct vertex/region theorem, which is not contradicted.

From lean/, run `lake update` if dependencies are absent, then `lake build`. Public pins: Lean4.19.0 and Mathlib c44e0c8ee63ca166450922a373c7409c5d26b00b. Build output prints standard-axiom audits. Local generated .lake artifacts and dependency junctions are ignored. Compile proof.tex with Tectonic or another LaTeX engine. No auxiliary numerical computation is used.
