# Independent AI review of TLMC 4374

Reviewed 2026-10-26 UTC. Status: PASS for the literal printed degree claim, independently verified mathematics, Lean, complete report, and both PDF pages.

## Source semantics

Independently retrieved the bilingual original at upstream commit b355e42906e6eaf52bc7e9d005e0ef02d8aa7400 through the GitHub connector. Both languages assert odd homotopy occurrence degrees themselves are multiples of p^2-1, uniformly for odd primes. The English final clause also calls them periods, but does not replace the explicit absolute-degree clause with a shifted-degree formula.

The formal necessary clause is a valid weakening: it permits a different occurrence degree for each prime and omits minimality of the next occurrence. Taking p=3 gives an even multiple of eight, incompatible with any odd degree. This is independent of actual K-theory. Arbitrarily quantifying the nonzero-homotopy predicate is sound here because the arithmetic impossibility holds for every such predicate; no invented geometric example or theorem assumption is used. The cutoff is arbitrary. The report correctly separates a repaired shifted-period statement (which this proof does not refute).

## Actual independent verification

Copied only source files into this fresh review directory, not the author's compiled artifacts. With the pre-existing official Lean 4.31.0 toolchain on PATH:

- lake build: PASS, 3 jobs.
- lake env lean -DwarningAsError=true -t0 OddDegree.lean: PASS.
- lake env lean -DwarningAsError=true -t0 Audit.lean: PASS, all 8 named theorems audited.
- lake env leanchecker OddDegree: PASS.

Theorems three_odd and period_three use no axioms. The others use only propext and Quot.sound. No custom axiom, sorry, native_decide, admit, unsafe declaration, or trust bypass occurs in the proof.

Reviewed source SHA256: 5f13eb34337b99a4569dfe3d08dbba174d89cfca290b6734a84a8651ad7925c8.

## Document review

Read the complete LaTeX source. Its conclusion, formula, proof, formal mapping, scope limitation, and AI disclosure agree with the Lean result. Initial author's aggregate verification failed in PDF generation because the default TeX format cache was read-only; this was reported, not treated as a successful aggregate run. The author is fixing the cache/format path using existing resources. No mathematical correction requested.

This is independent AI review, not human review or organizer acceptance. Publication eligibility is handled separately by the coordinating agent.

## Final document and aggregate verification

At 20:05 UTC, independently reran the corrected verify.sh in the fresh review source directory with the existing format/font paths and separate writable TeX caches. The full source-only build, strict trust-zero, eight-theorem audit, leanchecker replay, and two-pass PDF rebuild passed. The script explicitly forces PDF output and verifies a nonempty PDF exists. Complete log: full-verify.log.

Visually inspected BOTH final PDF pages from the author's rebuilt PDF. All text and formulas are legible, with no clipped lines, overlaps, missing glyphs, or overfull source-link line. Read the final README and found the verification limits and prior TeX failures accurately disclosed. Final PDF SHA256: e867e32d4b7abcb69a622de6c4c7cafe0f7c10b5ea4dcdb4a94a9edb8d3eddb0. Lean source hash remains unchanged.

No further correction required. This approval covers the literal absolute-degree contradiction only, not actual K-group computation, shifted-period claims, human acceptance, or submission eligibility.
