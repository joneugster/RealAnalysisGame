import Game.Levels.L8Pset.L8Pset2

World "L8Pset"
Level 3
Title "Problem 3"

Introduction "# Problem 3

Prove that `n (n + 1) (2 n + 1)` is always divisible by `6`. (Hint: induction.)
"

/-- Prove the statement. -/
Statement (n : ℕ) : ∃ k, n * (n + 1) * (2 * n + 1) = 6 * k  := by
  induction' n with n hn
  use 0
  norm_num
  choose k hk using hn
  use k + (n + 1) ^ 2
  have expand : (n + 1) * (n + 2) * (2 * (n + 1) + 1)
                = (n + 1) * (n + 2) * (2 * n + 3) := by ring_nf
  rewrite [expand]
  have key : (n + 1) * (n + 2) * (2 * n + 3)
              = n * (n + 1) * (2 * n + 1) + 6 * (n + 1) ^ 2 := by ring_nf
  rewrite [key, hk]
  ring_nf

Conclusion ""
