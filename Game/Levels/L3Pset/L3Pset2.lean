import Game.Levels.L3Pset.L3Pset1

World "L3Pset"
Level 2
Title "Problem 2"

Introduction "# Problem 2

Prove that the sequence `(n + 1) / n` has a limit, say, `L`, and determine what it is.

We haven't yet learned a good way to use the theorem `OneOverNLimZero`
that we already proved, so just adapt the proof of that, rather than trying to quote it. (It's good practice!)
"

/-- Prove that the sequence `(n + 1) / n` has a limit `L` and determine what it is. -/
Statement (a : ℕ → ℝ) (ha : ∀ n, a n = (n + 1) / n) :
    ∃ L, SeqLim a L := by
  use 1
  intro ε hε
  choose N hN using ArchProp hε
  use N
  intro n hn
  specialize ha n
  rewrite [ha]
  have : 0 < 1 / ε := by bound
  have Npos : (0 : ℝ) < N := by linarith [hN, this]
  have : (N : ℝ) ≤ n := by exact_mod_cast hn
  have : (0 : ℝ) < n := by linarith [this, Npos]
  have : ((n : ℝ) + 1) / n - 1 = 1 / n := by field_simp; ring_nf
  rewrite [this]
  have : |(1 : ℝ) / n| = 1 / n := by bound
  rewrite [this]
  field_simp
  field_simp at hN
  have : ε * N ≤ ε * n := by bound
  linarith [hN, this]


Conclusion "Done."
