# Independent local semantic review: Conjecture 00000007914

**Verdict:** No blocking mathematical or semantic flaw found. The complete report and Lean source faithfully disprove the literal conjecture by showing that its finite-rank asymptotic is impossible for a nonnegative real spectrum.

This is an independent local mathematical and source-to-formal review. It is not a maintainer review or acceptance decision. The complete bilingual original, complete report source, and complete Lean source were read. Compilation/replay records and PDF visual verification are separate checks; this review does not present those checks as its own execution.

## Reviewed versions

SHA-256 hashes bind this verdict to these exact file contents:

| File | SHA-256 |
|---|---|
| `conjecture.md` | `d5dec2d2a5bda01db6cca1c8eb55b1bc1bad0b3c415f470e651c0c1ef54e90b2` |
| `proof.tex` | `00ae00057c1b96171868abef6675723111edf3b8496ba9fa306d8520484c332b` |
| `lean/CovolumeSpectrum.lean` | `0bf9a035b94cb234d993036532fa30ec755dfbf52e6eeb125e1f8eb4557867d8` |
| `lean/lake-manifest.json` | `8d8e5829ddacd806e26f35f980d0c15b8c6dfc477a2e5d611869b2293afa9deb` |
| `lean/lakefile.toml` | `1150c806b1420243820a8dccba1ca717dbd64600168c9b2c00097a05250e7131` |
| `lean/lean-toolchain` | `55e97be96000b5e9e290c9e74482e5e317861499a5540353ce845471bded8cea` |

## Findings

1. **Finite rank is represented faithfully.** `HasRank` requires membership in the spectrum and exactly the specified number of distinct strict predecessors. It does not merely select some smaller elements. The one-based source indexing is preserved. Additional elements of transfinite rank are permitted; no enumeration of the entire well-order is assumed.

2. **The exact formula is analyzed.** The source uses the literal reciprocal-logarithmic expression with real exponent −2/3. It tends to zero for every fixed real leading constant. The ratio-limit bridge handles every nonzero constant, and the report separately explains Mathlib's broader zero-constant convention. Values at indices zero and one do not affect the asymptotic.

3. **The contradiction is valid even when zero belongs to the spectrum.** Exact ranks give 0≤v₁<v₂≤vₖ for k≥2, so the sequence has a fixed positive lower bound. Asymptotic equivalence to the displayed scale forces convergence to zero. No geometric lower-bound theorem or inference of monotonicity from asymptotic equivalence is used.

4. **The volume and limiting bridges are appropriate.** Finite measure values are nonnegative, and the measure interface excludes infinite values before real conversion. Closure and ordinary limits preserve nonnegativity. The explicit extended-real liminf theorem also covers finite sequential lower limits without a hidden boundedness premise, addressing the Chinese wording. These are necessary properties of the original objects, rather than assumptions of an unrelated replacement model.

5. **The logical scope is correct.** Refuting the numerical sub-conjunction refutes the whole original conjunction. The arbitrary remaining proposition permits the triangle-group and trichotomy clauses without making any separate classification claim. The report consistently preserves this distinction.

The report's definitions, argument, theorem references, treatment of the leading constant, and volume/liminf interfaces agree with the Lean source. No unresolved proof gap, unsupported computation, or required arithmetic classification was found. This verdict does not extend to later changes with different hashes.

## Final layout review

The coordinating reviewer checked the final report SHA-256 `24d750a995775137b94f665865b7492cc216802f946f9d8a32fa7d94a9073198` against the independently reviewed report above. The only changes remove unused packages, adjust line breaking, display the dependency hash and two theorem names separately, and start the verification section on a new page. All mathematical assertions and proofs are unchanged. The final source compiled in the desktop editor and exported without warnings. All three final PDF pages were visually inspected, with no clipping, overlap, or missing content. PDF SHA-256: `95334c6e5d095588c952374441fabd0828002ec534c1a4361c08f011350b4714`.
