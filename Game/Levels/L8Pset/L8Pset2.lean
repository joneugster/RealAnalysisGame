import Game.Levels.L8Pset.L8Pset1

World "L8Pset"
Level 2
Title "Problem 2"

Introduction "# Problem 2

We proved in class that `n < 2 ^ n`. It's even true that `n ^ 2 ≤ 2 ^ n`, but only for `n` sufficiently large (how large?).

Look at the problem statement. Note how we've implemented induction starting somewhere other than zero: by shifting the argument by that amount.

Hint: The result from Problem 1 might come in handy...
"

/-- Prove the statement. -/
Statement : ∃ N, ∀ n, (n + N) ^ 2 ≤ 2 ^ (n + N) := by
  use 4
  intro n
  induction' n with n hn
  norm_num
  have f1 : (n + 1 + 4) ^ 2 = (n + 4) ^ 2 + (2 * n + 9) := by ring_nf
  rewrite [f1]
  have f2 : 2 ^ (n + 1 + 4) = 2 ^ (n + 4) * 2 := by ring_nf
  rewrite [f2]
  have f3 : 2 * n + 9 ≤ 2 ^ (n + 4) := by apply Pset8Ex1
  linarith [f3, hn]

Conclusion ""
