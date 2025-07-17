# Learning Lean

[LEAN](https://lean-lang.org) is a programming langugae for formal math.

One of its major applications is theorem proving through formally verified code, which makes it a prominent tool for research in the field of mathematics.
For example, the author of [this paper](https://arxiv.org/abs/2310.05328) found a subtle error in the original derivation while formalizing it in Lean 4 (the code is accessible [in this repository](https://github.com/teorth/symmetric_project)), which allowed it to be corrected in a subsequent version of the manuscript.
Additionally, LEAN has proven to be an extremely valuable tool to develop automated theorem proving systems, such as [AlphaProof](https://deepmind.google/discover/blog/ai-solves-imo-problems-at-silver-medal-level/) or [DeepSeek prover](https://arxiv.org/abs/2504.21801).

In this repository, I document my Lean 4-learning journey as I work my way through various material sources.
1. I find the [functional programming in Lean page](https://lean-lang.org/functional_programming_in_lean/) is a great way to start learning, as it introduces the basics of LEAN4 as a programing language.
2. I enjoyed going through the [mathematics in lean](https://leanprover-community.github.io/mathematics_in_lean/) tutorial, as it offers an introduction to the methods for theorem proving and their syntax. 
3. I also found the [natural number game](https://adam.math.hhu.de/#/g/leanprover-community/nng4) frames learning Lean as a game, which is kind of addictive!

# Style guides for Lean

I have empirically found that:
- Terms of Props, like theorems and lemmas go in `snake_case`.
- Types, Props, structures and classes go in `UpperCamelCase`.
- Data-returning definitions, such as functions or constants whose return is in `Type` should be in `lowerCamelCase`.
- Functions should be named as if they where what they return, i. e., use `snake_case` if it returns a Prop, or `UpperCamelCase` if a Type.
- When something named in `UpperCamelCase` is part of something in `snake_case`, drop it to `lowerCamelCase`.
- Short acronyms stay as a block of upper/lower case depending on the first letter, e. g., `LE` or `IO`. Longer acronyms ($\geq 4$ letters) combine upper and lower case.
- All these rules apply to structure fields.