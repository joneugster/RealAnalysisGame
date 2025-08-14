import GameServer
import Mathlib.Data.Real.Basic

World "RealAnalysisStory"
Level 3
Title "The rw tactic"

Introduction "
# Rewriting with equalities

Now let's learn about rewriting. Suppose you have a hypothesis called `Bob : x = 2`, and your goal is to prove that `x + y = 2 + y`.

Can you use `rfl`? No, because the two sides of the goal (`x + y` and `2 + y`) are not *identically* the same.

Can you use `exact Bob`? No, because `Bob` says `x = 2`, which is not *exactly* what the goal is asking for.

But you can use the hypothesis `Bob` to *rewrite* the goal. Since `Bob` tells us that `x = 2`, we can replace `x` with `2` in our goal.

In Lean, if you have a hypothesis which is an equality, and you want to replace the *left hand side* of that equality with the *right hand side* in your goal, you use the `rewrite` tactic. The syntax is:

`rewrite [hypothesis_name]`

Unfortunately, those square brackets are part of the Lean syntax, and there's nothing you or I can do about them right now. Just remember: `rewrite [Bob]` means \"use the equality in `Bob` to rewrite the goal.\"

After you rewrite, you're not done. But you should know how to finish from there.

Try it out!
"

/-- The `rewrite` tactic replaces the left-hand side of an equality with the right-hand side in the goal. The syntax is `rewrite [hypothesis_name1, hypothesis_name2, etc]`.  -/
TacticDoc rewrite

/-- If we know that $x = 2$, then we can prove that $x + y = 2 + y$. -/
Statement (x y : ℝ) (Bob : x = 2) : x + y = 2 + y := by
  Hint (hidden := true) "Type `rewrite [Bob]` to replace `x` with `2` in the goal. Then what?"
  rewrite [Bob]
  rfl

NewTactic rewrite

Conclusion "
Great! You've learned the `rewrite` tactic.

Notice what happened: after you typed `rewrite [Bob]`, the goal changed from `x + y = 2 + y` to `2 + y = 2 + y`. Then you needed to type `rfl` to finish the proof, since both sides were now identical.

So far you've learned:
- `exact hypothesis_name` when a hypothesis exactly matches your goal
- `rfl` when you need to prove something equals itself
- `rewrite [hypothesis_name]` when you want to use an equality to rewrite your goal

The `rewrite` tactic is incredibly powerful and you'll use it constantly in real analysis!
"
