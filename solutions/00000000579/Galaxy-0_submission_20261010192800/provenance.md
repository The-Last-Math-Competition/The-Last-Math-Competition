# Source and eligibility evidence

Checked 2026-10-10 at approximately 19:22-19:30 UTC against The-Last-Math-Competition/The-Last-Math-Competition.

- Original EN/CN statement: https://github.com/The-Last-Math-Competition/The-Last-Math-Competition/blob/main/conjectures/00000000579.md
- Original statement blob SHA: d94417e9d42ce715bd1e060005006629332458ad
- `conjecture-source.md` reproduces the exact source text; current contents matched the local snapshot byte for substantive byte (with a possible trailing newline difference).
- Current metadata blob SHA: 9189d96240d7117f4ef1d96c2c84502aa7a3ca50
- Exact metadata row: `00000000579,,,,,,false,false,,false,`
- All-state PR searches for `"00000000579"`, `"00579"`, `"dual-difference"`, `"difference" "matroid"`, and `"对偶差"` returned no submissions.
- Broad all-state search `579` returned only unrelated PR #579 on conjecture 00000001022, which is not a duplicate.
- Reference defining the mathematical object: Elias, Proudfoot, Wakefield, The Kazhdan-Lusztig polynomial of a matroid, Theorem 2.2, https://arxiv.org/html/1412.7408v3#S2.Thm2 . The theorem's rank-zero condition, strict degree bound, and flat recurrence are used as the definition; the Lean code proves the witness consequences and nonvacuity directly.

# Actual execution

Lean executable: Lean 4.31.0, commit 68218e876d2a38b1985b8590fff244a83c321783, Release, x86_64-unknown-linux-gnu. Lake 5.0.0-src+68218e8. The already-available toolchain was used; nothing was installed.

Clean `lake build` completed successfully with four jobs, compiling Submission.Basic and Submission. Its log is build.log. Direct Lean checking also returned exit 0. The independent verifier ran successfully; verification.log records its exact output. PDF compilation used two successful pdflatex passes with existing TeX sources/fonts and the previously built pdflatex format. No external state was changed by the verification process.

PDF quality assurance: all three final pages were rendered with pdftoppm and visually inspected. Final two-pass build has no overfull boxes or warnings.
