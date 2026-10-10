## Rules

### Rules for Problem Solvers

1. Each problem solver may submit, for any conjecture, all materials constituting a complete proof or disproof, in the form of a pull request placed in the folder with the corresponding number (e.g., `./solutions/00000000001/[my_GitHub_ID]_submission_20260912041426`). Each submission must include the LaTeX source code, a PDF document, and a Lean 4 project, together with any additional source code and materials (e.g., Python scripts, Matlab, Mathematica, Fortran, Julia, or C programs). Please strictly follow the path naming convention.

2. Before opening a pull request, each problem solver should make sure that the conjecture has not already been solved; otherwise, please refrain from submitting the pull request. If a previous submission for that conjecture is wrong, the description of your new pull request must give a complete account of the error in the previous submission, together with the correct solution in the present one.

3. Each problem solver may only submit personal submissions under the corresponding problem folder; for any other matter, please open a new issue. Please do not include modifications to the conjecture descriptions, the README, the leaderboard, the metadata, or any other files in the pull request.

### Rules for Reviewers

1. As a reviewer, you must review the entire LaTeX report in full, make sure the Lean project compiles and runs completely and contains no `sorry` or anything else that would make the proof or disproof of the conjecture incomplete, and make sure the Lean project and the LaTeX report match the definition and requirements of the conjecture. You must also make sure that all auxiliary code compiles, runs, and produces the expected results — fully covering the parts that require computation — including Python scripts, Matlab, Mathematica, Fortran, Julia, and C programs.

2. Once a reviewer considers the proof or disproof of the conjecture complete and valid, please create a `review` folder under the corresponding solutions folder `./solutions/[number_ID]` and add a complete solution review — either as a Markdown document, or in the form of a LaTeX source file plus a PDF document. If needed, include in the solution review any additional Lean 4 projects, source code in other languages, and configuration files it requires, so as to constitute a complete review. Finally, merge the pull request into the main branch, and fully update the leaderboard, the metadata, and the leaderboard sections of both the Chinese and the English READMEs.

3. Once a reviewer considers the proof or disproof invalid, incomplete, or not conforming to the definition of the conjecture, the pull request should be closed, together with a complete explanation.

### Rules for Maintainers

1. As a maintainer, your responsibility is to periodically add 10,000 new conjectures and to produce those 10,000 conjectures yourselves, ensuring that the problems are of the highest possible quality — original, and with the potential for breakthroughs and disruption — mathematical conjectures that push forward the frontier of mathematical research or inspire an entirely new field of mathematics. Save them as `[number_ID].md` files in the `./conjectures` folder, where `number_ID` is an 11-digit number giving the conjecture's ID.

2. Before each submission, make sure that both the Chinese and the English versions exist, and that every conjecture has a complete and clear definition with all the necessary conditions.
