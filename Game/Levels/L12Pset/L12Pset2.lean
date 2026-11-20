import Game.Levels.L12Pset.L12Pset1

World "L12Pset"
Level 2
Title "Problem 2"

Introduction "
# Problem 2:

More fun with Cauchy sequences. Show that `1/n` is Cauchy but is neither `Monotone` nor `Antitone`! (Because of how division by zero works in Lean...)

"

/-- Prove this
-/
Statement (a : ℕ → ℝ) (ha : ∀ n, a n = 1 / n) : IsCauchy a ∧ ¬ Monotone a ∧ ¬ Antitone a := by
  split_ands
  apply IsCauchy_of_SeqConv
  use 0
  apply OneOverNLimZero a ha
  intro h
  specialize h (by bound : 1 ≤ 2)
  rewrite [ha, ha] at h
  norm_num at h
  intro h
  specialize h (by bound : 0 ≤ 1)
  rewrite [ha, ha] at h
  norm_num at h

Conclusion ""
