# Problem 00000000145: the unrestricted-alpha LIL claim fails

Use the actual positive parameter alpha=1 and f(t)=sin(2*pi*t). The actual smooth, one-periodic observable has interval mean0, variance1/2 and a nonzero point deviation. Every genuine prime sample has Int.fract(alpha*p)=0; the true centered finite prime sum is identically0. The exact Real.sqrt(x*log(log x)/log x) scale is strictly positive for x>=exp2. Genuine cofinal positive and negative Omega fluctuations are both impossible.

Scope is the printed version without any irrationality, Diophantine or almost-everywhere premise on alpha. No corrected restricted-alpha LIL is refuted. No PNT or probabilistic LIL is proved or assumed.

Prior public PR1055's missing-irrationality direction is attributed in report.tex and the PR description. Its reviewer rejected the missing actual prime-sum/scale/fluctuation formalization, not merely a numerical error. Those exact bridges, plus the genuine mean, variance and regularity, are now formalized. SOURCE.md preserves the full original bilingual text.

From lean/, run `lake build +Main`, `lake env lean -DwarningAsError=true Check.lean`, and `lake env leanchecker --fresh Main`. Every named local definition/theorem is audited. Complete source-bound receipts, fresh kernel logs, PDF visual review, eligibility evidence, pinned versions and the LaTeX/PDF report are included. AI-led work with separate AI supervision; organizer acceptance pending. No sorry/native_decide/extra axiom.
