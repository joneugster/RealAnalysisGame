import Game.Levels.L6Pset.L6Pset2

World "L6Pset"
Level 3
Title "Problem 3"

Introduction "# Problem 3

You are given that a sequence `a : ℕ → ℝ` converges to 5.
Prove that it is eventually positive.
"

/-- Prove the statement. -/
Statement (a : ℕ → ℝ) (ha : SeqLim a 5)
  : ∃ N, ∀ n ≥ N, 0 < a n := by
  have f0 : (0 : ℝ) < 5 := by norm_num
  specialize ha 5 f0
  choose N hN using ha
  use N
  intro n hn
  specialize hN n hn
  rewrite [abs_lt] at hN
  linarith [hN.1]

Conclusion "Done."
