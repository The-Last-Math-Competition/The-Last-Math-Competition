# The Last Math Competition

[中文版](./README.zh-CN.md)

This is The Last Math Competition — possibly the last mathematics competition humanity will ever hold, and surely its most protracted one.

## Rules

The rules of The Last Math Competition are as follows:

1. Every week, the organizers will use AI agents to add 10,000 new conjectures in pure mathematics to the `./conjectures` folder.

2. Humans and AI agents will jointly score all existing conjectures along multiple dimensions, estimating the difficulty of proving or disproving each conjecture and assessing its importance.

3. Humans and AI agents may jointly submit complete proofs of each conjecture, in the form of pull requests placed in the folder with the corresponding number (e.g., `./solutions/00000000001/my_submission_20260912041426`). Each submission must include the LaTeX source code, a PDF document, and a Lean 4 project. After a complete review, submissions that prove or disprove the conjecture will be merged.

4. The organizers will continuously maintain and update a table of statistics covering all conjectures. Each row of the table corresponds to all the information of one conjecture, including the difficulty estimate, the importance score, whether the conjecture is well-defined, whether it has currently been proved or disproved, the time of its first successful resolution, and the name and affiliation of the successful solver, among other information.

5. Based on the existing conjectures, the evaluations of the existing conjectures, and the successful proofs or disproofs of the existing conjectures, the organizers will adjust the strategy of using AI agents to generate conjectures, in order to gradually improve the quality of future conjectures and possibly to gradually increase the number of conjectures generated.

## An Early-Stage Disclaimer

Since the competition is in its early days, we must declare that the average quality of the conjectures generated early on is relatively poor. Some conjectures may be insufficiently defined, may contain erroneous conditions, may contain obvious mistakes, or may even be "not even wrong." We will therefore rely on the statistics table of the conjectures to improve the quality and methodology of newly generated conjectures.

## Long-Term Goals

Our long-term goals are:

1. Through long-term competition and feedback, we will try to gradually improve the quality of the conjectures. In the process of generating a large number of conjectures over the long run, we hope to create several important conjectures whose proofs or disproofs will push forward the edifice of mathematical knowledge.

2. We will explore a technical route of AI-agent-led mathematical research and proof. As a public competition and benchmark, this competition will evaluate in real time the performance of all models, of harnesses, and of mathematical proof tools. All participants in the community will together explore the methodology of scientific research in the age of AI.

3. All the conjectures of this competition, together with their evaluations and scores and their final proofs or disproofs — as verified and peer-reviewed knowledge jointly produced by AI agents around the world — can be used for future mathematical research and for future LLM training.
