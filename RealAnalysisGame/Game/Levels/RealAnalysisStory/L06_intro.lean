import GameServer
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring

World "RealAnalysisStory"
Level 6
Title "The intro tactic"

Introduction "
# Universal statements

In mathematics, we often need to prove statements that are true \"for all\" values of some variable. For example, we might want to prove: \"for all $\\varepsilon > 0$, we have $(\\varepsilon + 1)^2 = (\\varepsilon + 1)^2$.\"
(Of course the condition that `ε` be positive is mathematically superfluous, and is only here for pedagogical purposes.)

If you're thinking that `rfl` will do the trick, that's a good idea, but it won't work, because the goal isn't (yet) an equality. So we need to do something else first.

In Lean, as in mathematics, \"for all\" is written using `∀`; this is called the *universal quantifier*, and is gotten by typing \\forall, that is, backslash, then `forall`, then a space. In Lean, this goal looks like so:

`∀ ε > 0, (ε + 1)^2 = (ε + 1)^2`.

(Note that to write an epsilon in Lean, you just type \\\\e, that is, backslash, then `e`, then space.)

To prove a \"for all\" statement, you need to show that it's true for an arbitrary element. In English, you would say: give me an arbitrary `ε`, and give me the fact that it's positive (we can give that fact a name, like `hε`, since it's a hypothesis about `ε`, or perhaps an even more descriptive name like `ε_pos`, since the hypothesis is the positivity of `ε`). Note that `ε` here is a dummy variable, and we could choose to name it something else on the fly. In English, we might say: give me some `ε`, but I want to call it `Alice`; then give me the fact that `Alice` is positive, and my goal will be to prove that `(Alice + 1)^2 = (Alice + 1)^2`. If we were more polite, we might replace \"give me\" above with \"introduce\", like:
introduce an `ε`, and introduce the fact, call it `hε`, that `ε` is positive.

In Lean, the syntax for this is the command `intro`, followed by whatever name you want to give a dummy variable or a hypothesis.

So: when you see a goal that starts with `∀`, you can write `intro` to \"introduce\" the variable. For example:
- `intro ε` introduces the variable ε. But look at the goal state now! It changes to: `ε > 0 → (ε + 1)^2 = (ε + 1)^2`. So we're not done introducing things.
- Then `intro hε` introduces the hypothesis that `ε > 0` (and again, you can call the hypothesis whatever you want; try `intro ε_pos` instead).

After using `intro` twice, the goal will become one that you
should know how to solve.

If you want to be really slick, you can combine the two `intro` commands into
one: `intro ε hε`. But don't feel obliged.
"

/-- The `intro` tactic introduces variables and hypotheses from ∀ statements or implications. -/
TacticDoc intro

/-- For all positive real numbers, this algebraic identity holds. -/
Statement : ∀ ε : ℝ, ε > 0 → (ε + 1)^2 = (ε + 1)^2 := by
  Hint (hidden := true) "Use `intro ε` to introduce the variable, then `intro hε` to introduce the hypothesis `ε > 0`. Then how do you solve the goal?"
  intro ε
  intro h
  rfl

NewTactic intro

Conclusion "
Excellent! You've learned the `intro` tactic for universal statements.

Notice what happened:
1. `intro ε` introduced the arbitrary real number ε
2. `intro hε` introduced the hypothesis `hε : ε > 0`
3. The goal became `(ε + 1)^2 = (ε + 1)^2`
4. `rfl` solved the goal, by the reflexive property of the equals sign.

The `intro` tactic is absolutely crucial in real analysis. You'll use it constantly to:
- Handle \"for all ε > 0\" statements in limit definitions
- Introduce arbitrary points in domain/range proofs
- Work with function definitions

This pattern of `intro` followed by algebraic manipulation is everywhere in analysis!
"
