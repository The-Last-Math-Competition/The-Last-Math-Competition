# TLMC 00000007978: PIR capacity needs the message count

The posted unrestricted formula depending only on server count is false. One server and three independent messages have standard PIR capacity 1/3, not 1/2. The formula is correct for two messages; this submission does not dispute that restricted case.

## Reproduce

Use an existing Lean 4.31.0 toolchain, with `lean`, `lake`, and `leanchecker` on PATH. No third-party Lean packages are required.

1. `lake build` builds every listed module.
2. `bash verify.sh` compiles all modules in a fresh temporary directory using `--trust=0 -DwarningAsError=true`, replays each with `leanchecker -v`, and prints the axioms of every named theorem. Set `LEAN_BIN=/path/to/lean-4.31.0/bin` if needed.
3. In an ordinary TeX Live installation, run `pdflatex -interaction=nonstopmode -halt-on-error solution.tex` twice. `build_pdf.sh` also supports the author's cloud image, whose installed TeX tree lacks search indexes; no package installation or network call is made.

`verification.log` records the author's fresh strict compile, kernel replay and axiom audit; `lake-build.log` records the real Lake build. Independent reviewer records are included separately. Kernel replay means replay by Lean's kernel, not verification with a second independent kernel implementation.

## Formal coverage

The Lean development defines actual database triples, random-query/answer/decoder schemes, base-B packing and unpacking, and private download-all achievability. It proves an arbitrary-alphabet zero-error converse. The approximate model counts actual failures of three decoders and allows query-dependent response lengths. The expected-cost theorem yields a uniform rate bound of 4/9 for L>=4 when the sum of the three error probabilities is <=1/6. Thus it excludes a whole neighborhood of the claimed 1/2 capacity, not merely its exact attainment. The coupling module reorders equal-query-distribution random tapes and preserves all integer-valued costs.

The full mathematical proof and the standard-model entropy/Fano extension are in solution.pdf. General arbitrary-measure probability theory, real supremum/limit definitions and the general multi-server Sun–Jafar theorem are not claimed to be Lean-formalized. No custom axioms, sorry, native_decide or computational observations substituted for proofs are used.

## Provenance

This is an AI-assisted counterexample to the posted formulation, not a new discovery of PIR capacity. The primary established capacity theorem is Hua Sun and Syed Ali Jafar, IEEE Transactions on Information Theory 63(7), 4075–4088, July 2017, DOI 10.1109/TIT.2017.2689028. Source/model sections were actually read. The upstream source, eligibility, current duplicate checks and final submission status are separate from proof verification and remain subject to organizers' review.
