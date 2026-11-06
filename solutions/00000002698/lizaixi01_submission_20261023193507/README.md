# 00000002698: a tropical fixed point without a classical periodic lift

For the actual polynomial X+1 over Q5, all classical iterates are x+n, so no point has positive period. Coefficientwise min-plus tropicalization is constructed from the actual polynomial coefficients and the extended additive valuation v5(0)=infinity, using Polynomial, Finsupp.mapRange and Tropical (WithTop Int). It evaluates to min(w,0), which fixes -1. This value is attained by 1/5.

Every positive composed polynomial X+n has tropicalization min(w,v5(n)); v5(n)>=0, so -1 remains fixed while the original iterate has no classical periodic points. The generic characteristic-zero proof also rules out classical periodic points over characteristic-zero extensions. The polynomial derivatives are actually 1, the translation has inverse x-1, and unequal valuations prove no cancellation along this negative branch.

This refutes the explicit periodic-set correspondence under the standard coefficientwise tropicalization and classical-point interpretation. The source has no degree-at-least-two assumption. Berkovich points are different and are not covered. The source's unspecified ramification layer and log(p) height are not assigned definitions or claimed resolved.

SOURCE.md preserves the complete bilingual source. report.tex and report.pdf explain the proof and convention, citing Aroca, Krull-Tropical Hypersurfaces, arXiv:0903.5375v2, printed pp. 2-3 and 5. lean/ contains the pinned full proof and audit of every named declaration. evidence/ binds source, commands, logs, fresh replay and separate semantic/PDF review. No earlier same-ID submission was found in the initial all-state search. AI-led selective production; organizer acceptance and a controlled efficiency improvement are not asserted.
