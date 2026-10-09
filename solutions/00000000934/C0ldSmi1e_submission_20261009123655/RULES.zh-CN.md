## 比赛规则

### 问题求解者（Problem Solvers）规则

1. 每个 problem solver 可以提交对于每个猜想的完整证明的所有材料，以 pull request 的形式提交在对应序号的文件夹中（比如 `./solutions/00000000001/[我的_GitHub_ID]_submission_20260912041426`），其中需要同时包含 LaTeX 源代码、PDF 文档和 Lean 4 项目，以及其他可能包含的任意额外源代码和材料，比如 Python script、Matlab、Mathematica、Fortran、Julia、C 程序代码，并且请务必严格遵守路径命名格式；

2. 每个 problem solver 在提交 pull request 之前，应该确保该问题没有被解答，否则请放弃提交本次 pull request。如果该问题之前的 submission 是错误的，请在提交的 pull request 的描述和介绍中完整陈述之前的 submission 的错误，以及本次 submission 的正确解答；

3. 每个 problem solver 只能提交对应问题文件夹下面的个人 submission，如有问题请提交一个新的 issue。请不要在 pull request 中包含修改 conjectures 描述、README、leaderboard、metadata 等其他文件内容。

### 审查者（Reviewers）规则

1. 作为 Reviewer，你需要完整 review 整个 LaTeX report，确保 Lean project 完整编译运行，并且不包含任何 sorry 或者任何导致猜想的证明或者证伪不完全的功能，并且确保 Lean project 和 LaTeX report 符合猜想的定义和要求，并且确保包含其他所有辅助代码正确编译、正确运行并且获得符合预期的结果，完整且覆盖需要计算的部分，包括 Python script、Matlab、Mathematica、Fortran、Julia、C 程序等代码；

2. 一旦 reviewers 认为这份猜想的证明或者证伪是完整且有效的，请在 solutions 对应文件夹 `./solutions/[number_ID]` 中新建 review 文件夹，添加完整的 solution review，可以使用 Markdown 文档形式，也可以使用 LaTeX 源文件 + PDF 文档形式。如果有需要的话，请把 solution review 中额外需要的 Lean 4 project、其他语言源代码和配置全部添加进去，构成一份完整的 review。最后把 pull request merge 进 main 分支，并且更新完整 leaderboard、metadata、中文和英文 README 中的 leaderboard 部分；

3. 一旦 reviewer 认为这份猜想的证明或者证伪是无效的、不完全的、不符合猜想定义的，则应该关闭 pull request，并且附带完整的解释说明。

### 维护者（Maintainers）规则

1. 作为 Maintainer，你的职责是定期增加 10000 个，并且自己完成 10000 个猜想，保证题目尽可能地高质量、有原创性的、具有潜在突破性和破坏性的数学猜想，尽可能推进数学前沿研究或者能启发一个全新的数学领域，依次保存为 `[number_ID].md` 文件，存储在 `./conjectures` 文件夹目录下，并且保证 `number_ID` 是一个 11 位数字，表示猜想的编号；

2. 每次提交前，请确保同时存在中文和英文版本，并且保证猜想具有完备且清晰的定义，以及具有所有必要的条件。

