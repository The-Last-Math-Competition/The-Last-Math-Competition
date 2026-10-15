# Verification evidence

Lean 4.31.0, Std only. Main.lean compiled with warnings treated as errors (strict.log is empty on success). All nine authored theorem axiom checks are in axioms.log. Only standard propext and Quot.sound occur. Kernel replay through lake env leanchecker Main exited zero; the checker is silent on success (kernel.log is empty, exit status recorded separately).

The three-page report.pdf was rendered with pdftoppm and all pages visually inspected on 2026-10-15: no clipping or overlap. The TeX report has no overfull boxes. Two harmless underfull bibliography boxes do not impair legibility.

An independent review, if included, is an internal verification report and not an organizer endorsement. Run ../VERIFY.sh from a clean source-only project to reproduce the Lean checks.

Independent reviewer checked all 26 authored top-level declarations in AllDeclarations.lean and reviewed a separately copied report.pdf. Both PDF hashes match:
0fc0bba316de7c99516bf1cf9fd0e2144021971afbafea51b0c7e2d940ba3def
Main.lean independently reviewed hash:
c1600b00ba9fbbfc1c262b2cd3861c7a0cc72338e9bfa970ae0fe87e9e75b79f
