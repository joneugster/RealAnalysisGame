import GameServer
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring

World "RealAnalysisStory"
Level 5
Title "The use tactic"

Introduction "
# Proving existence

Sometimes in mathematics, you need to prove that something exists. For example, you might need to prove \"there exists a real number $d$ such that $(x+y)^4 = x^4 + 4x^3y + dx^2y^2 + 4xy^3 + y^4$.\"

This is called an *existence statement*. In Lean, existence is written using `∃` (\"there exists\"). So this goal would look like:
`∃ d : ℝ, (x + y)^4 = x^4 + 4*x^3*y + d*x^2*y^2 + 4*x*y^3 + y^4`

To prove an existence statement, you need to provide a specific value that works. This is where the `use` tactic comes in.

If you think you know what value of `d` would work, you can write `use 6` (or whatever number you think is right). Lean will then substitute that value and ask you to prove that the resulting equation is true.

In this case, from the binomial theorem, we know that $(x+y)^4 = x^4 + 4x^3y + 6x^2y^2 + 4xy^3 + y^4$.

Try using `use 6` followed by `ring_nf`!
"

/-- The `use` tactic provides a specific value to prove an existence statement. -/
TacticDoc use

/-- There exists a real number that makes this binomial expansion work. -/
Statement (x y : ℝ) : ∃ d : ℝ, (x + y)^4 = x^4 + 4*x^3*y + d*x^2*y^2 + 4*x*y^3 + y^4 := by
  Hint "Use `use 6` to provide the missing coefficient, then `ring_nf` to verify the algebra."
  use 6
  ring_nf

NewTactic use

Conclusion "
Perfect! You've learned the `use` tactic for existence proofs.

Notice what happened:
1. `use 6` told Lean that $d = 6$ is our proposed value
2. The goal changed to proving $(x + y)^4 = x^4 + 4x^3y + 6x^2y^2 + 4xy^3 + y^4$
3. `ring_nf` verified that this algebraic identity is correct

The `use` tactic is fundamental in real analysis. You'll use it to:
- Find specific values of $\\varepsilon$ and $\\delta$ in limit proofs
- Construct witnesses for existence theorems
- Provide counterexamples

Your growing toolkit:
- `exact`, `rfl`, `rw` for basic equality reasoning
- `ring_nf` for algebraic manipulation
- `use` for existence proofs
"
