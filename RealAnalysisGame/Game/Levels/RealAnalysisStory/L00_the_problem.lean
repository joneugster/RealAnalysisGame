import GameServer
import Mathlib.Data.Real.Basic

World "RealAnalysisStory"
Level 1
Title "Introduction to Lean"

Introduction "
# Theorem Prover Software

In this course, we will be using a \"proof assistant\" called Lean. This is software that checks that our proofs prove *exactly* what we
claim they prove. It has other really cool pedagogical features that we'll get to later.
It will take a little while to get used to the syntax, so until we're comfortable, we'll intersperse exercises teaching Lean with exercises teaching Real Analysis. Pretty soon all the exercises will just be about Real Analysis.


For this first exercise, we have a hypothesis that we called `h` (but we could've called it anything, like `x_eq_5`, or `Alice`) that says a real number `x` equals 5. Our goal is to prove that `x` equals 5.
This shouldn't be very hard, but if you don't know
the command, you'll be out of luck. Our goal is to
prove *exactly* the same statement as one of the hypotheses.
To solve that goal, the syntax is to write `exact`, then a space, and then the name of the hypothesis which exactly matches the goal.
"
/-- The `exact` tactic solves a goal when one of the hypotheses is *exactly* the same as the goal. The syntax is `exact hypothesis_name` -/
TacticDoc exact

/-- If we know that $x = 5$, then we can prove that $x = 5$. -/
Statement (x : ℝ) (h : x = 5) : x = 5 := by
  Hint "Use `exact h` since the hypothesis `h` is exactly what we want to prove."
  exact h

NewTactic exact

Conclusion "
Perfect! You've completed your first Lean proof involving real numbers.

Remember: the `exact` tactic is used when you have exactly what you need to prove the goal. Look at the top right: your list of tactics now includes `exact`, and if you forget how it works or what it does, just click on it for a reminder.
"
