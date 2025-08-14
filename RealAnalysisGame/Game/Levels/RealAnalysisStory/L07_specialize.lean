import GameServer
import Mathlib.Data.Real.Basic

World "RealAnalysisStory"
Level 7
Title "The specialize tactic"

Introduction "
# Using universal statements

Now let's learn the flip side of `intro`. You have already learned that:
- if you have `∃` in the goal, you write `use` to provide a specific value. And
- if you have `∀` in the goal, you write `intro` to introduce an arbitrary variable

But what if you have `∀` in a *hypothesis* and you want to use it for a particular value?

Suppose you have:
- A positive real number `t`, that is a real number `t`, together with a hypothesis, say, `t_pos` that `t > 0`
- A function `f : ℝ → ℝ`
- A hypothesis `hf : ∀ x > 0, f (x) = x^2`, meaning \"for all x positive, f (x) equals x²\". (Note that you *have* to put a space after `f` before `(x)` or else Lean will be very angry with you! In fact, Lean will often drop unnecessary parentheses, so you'll see `f x` instead of `f (x)` -- and again, definitely *not* `f(x)`.)
- And you want to prove the goal `f (t) = t^2`.

Can you use `exact hf`? No! The hypothesis `hf` says \"for all positive x, f (x) = x²\" but the goal asks specifically about `f (t) = t²`. They're not *exactly* the same.

This is where `specialize` comes in. You can write `specialize hf t` to specialize the statement `hf` to the particular value `t`. This transforms `hf` from \"∀ x > 0, f (x) = x²\" into \"t > 0 → f (t) = t²\". Just like we had to `intro` multiple times (once for the dummy variable name, and again to name the hypothesis), we can specialize multiple times; so you can now write `specialize hf t_pos`. Or you can kill two birds with one swoop via: `specialize hf t t_pos`.

I'm sure you can solve the goal from there yourself!
"

/-- The `specialize` tactic applies a universal statement in a hypothesis to a specific value. -/
TacticDoc specialize

/-- If a function of `x` always equals `x²`, then it equals `t²` when evaluated at `t`. -/
Statement (t : ℝ) (f : ℝ → ℝ) (hf : ∀ x, f (x) = x^2) : f (t) = t^2 := by
  Hint (hidden := true) "Write `specialize hf t` to apply the universal statement to the specific value t; then you should be able to finish it yourself."
  specialize hf t
  exact hf

NewTactic specialize

Conclusion "
Great! You've learned the `specialize` tactic.

Notice what happened:
1. Initially, `hf : ∀ x, f (x) = x^2` was a universal statement
2. `specialize hf t` transformed it into `hf : f (t) = t^2`
3. Now `exact hf` worked because the hypothesis exactly matched the goal

The pattern is:
- `intro` when you have `∀` in the goal (\"introduce an arbitrary term...\")
- `specialize` when you have `∀` in a hypothesis (\"apply the hypothesis to specific value...\")

This is fundamental in real analysis when working with:
- Function properties that hold \"for all x\"
- Limit definitions involving \"for all ε > 0\"
- Continuity statements

Last lesson in Level 1 coming up.
"
