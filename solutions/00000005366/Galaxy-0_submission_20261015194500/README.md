# Conjecture 00000005366: ordinary star-height counterexample

This is a disproof of the ordinary (restricted) star-height-zero clause using the standard four-letter canonical geodesic language of Z². It is not a disproof under the generalized convention allowing complement. The original source does not explicitly resolve that terminology; the report discusses this limitation prominently.

Lean 4.31.0, Std only:

    lake build Main Audit
    lake env lean -DwarningAsError=true Main.lean
    lake env lean Audit.lean
    lake env leanchecker Main

All nine authored theorems are audited. Dependencies are only standard propext and Quot.sound; the finite generator commutation check has no axioms.

Main.lean proves actual group-word evaluation and lexicographic geodesic membership for all a^n, independently defines full ordinary regex semantics, and proves that no height-zero expression denotes the canonical language. The report mathematically checks the regular normal-form automatic structure and identifies the exact formalization boundary. The Lean theorem does not include an automatic-structure formalization or need an unproved assumption about one.

Build report.pdf with two ordinary pdflatex invocations, or run build_pdf.sh with an existing format directory on minimal TeX installations. No network or additional Lean packages are needed.

No external publication or submission was performed by this task.
