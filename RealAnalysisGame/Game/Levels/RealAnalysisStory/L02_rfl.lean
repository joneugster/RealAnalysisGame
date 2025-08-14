import GameServer
import Mathlib.Data.Real.Basic

World "RealAnalysisStory"
Level 2
Title "The rfl tactic"

Introduction "
# When things are identical to themselves

Sometimes in mathematics, we need to prove that something equals itself. For example, we might need to prove that $x^2 + 2y = x^2 + 2y$.

This isn't quite the same as our previous exercise. There, we had a hypothesis `h` that told us `x = 5`, and we used `exact h` to prove the goal `x = 5`.

But now we don't have any hypothesis that says `x^2 + 2y = x^2 + 2y`. We're just being asked to prove that some expression equals itself. We can't say `exact something` because there's no `something`.

Instead, we will use what mathematicians call the *reflexive property* of equality: everything is equal to itself. In Lean, if you get to a situation where you're trying to prove an equality, and the two things on both sides are *identical*, then the syntax is to give the command `rfl` (short for \"reflexivity\").

Try it out!
"

/-- The `rfl` tactic proves goals of the form `A = A` where both sides are *identical*. -/
TacticDoc rfl

/-- Every mathematical expression equals itself. -/
Statement (x y : ℝ) : x^2 + 2*y = x^2 + 2*y := by
  Hint "Use `rfl` since we're proving that something equals itself."
  rfl

NewTactic rfl

Conclusion "
Excellent! You've learned the `rfl` tactic.

The key difference:
- Use `exact hypothesis_name` when you have a hypothesis that matches your goal exactly
- Use `rfl` when you need to prove that something equals itself

These are two of the most fundamental tactics in Lean. As we progress through real analysis, you'll see that many complex proofs ultimately come down to showing that two expressions are identical.
"
