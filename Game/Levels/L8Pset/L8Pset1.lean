import Game.Levels.L8Lecture
import Game.Levels.L7PsetIntro

World "L8Pset"
Level 1
Title "Problem 1"

Introduction "# Problem 1

"

/-- For all `n : ℕ`, `2 * n + 9 ≤ 2 ^ (n + 4)`. -/
TheoremDoc Pset8Ex1 as "Pset8Ex1" in "Temporary"

/-- Prove the statement. -/
Statement Pset8Ex1 (n : ℕ) : 2 * n + 9 ≤ 2 ^ (n + 4) := by
  induction' n with n hn
  norm_num
  have f1 : 2 * (n + 1) + 9 = (2 * n + 9) + 2 := by ring_nf
  rewrite [f1]
  have f2 : 2 ^ (n + 1 + 4) = 2 ^ (n + 4) * 2 := by ring_nf
  rewrite [f2]
  have f3 : 2 ≤ 2 * n + 9 := by bound
  linarith [f3, hn]

Conclusion ""
