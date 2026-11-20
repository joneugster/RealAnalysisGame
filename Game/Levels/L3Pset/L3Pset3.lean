import Game.Levels.L3Pset.L3Pset2

World "L3Pset"
Level 3
Title "Problem 3"

Introduction "# Problem 3

Determine what the limit of the sequence `1 / n ^ 2` is, and prove it.

Hints you may find useful:
- We have yet to learn about dealing with the square-root function.
So see if you can be even lazier in your choice of parameters...
- If you know that `h : 0 < N` holds in the *natural* numbers, then you can prove that that `1 ≤ N` simply by `apply`ing `h`, that is: `have h' : 1 ≤ N := by apply h`. (This would not work for an inequality in the real numbers, since it's in general not true!)
"

/-- Determine what the limit of the sequence `1 / n ^ 2` is, and prove it. -/
Statement (a : ℕ → ℝ) (ha : ∀ n, a n = 1 / n ^ 2) :
    ∃ L, SeqLim a L := by
  use 0
  intro ε hε
  choose N hN using ArchProp hε
  have OneOverε : 0 < 1 / ε := by bound
  have Npos : (0 : ℝ) < N := by linarith [hN, OneOverε]
  field_simp at hN
  use N
  intro n hn
  specialize ha n
  rewrite [ha]
  have f1 : (1 : ℝ) / n ^ 2 - 0 = 1 / n ^ 2 := by ring_nf
  rewrite [f1]
  have f2 : |(1 : ℝ) / n ^ 2| = 1 / n ^ 2 := by bound
  rewrite [f2]
  have hn' : (N : ℝ) ≤ n := by exact_mod_cast hn
  have f3 : (0 : ℝ) < n := by linarith [Npos, hn']
  field_simp
  have Npos' : 0 < N := by exact_mod_cast Npos
  have NgeOne : 1 ≤ N := by apply Npos'
  have NgeOne' : (1 : ℝ) ≤ N := by exact_mod_cast NgeOne
  have f4 : 1 < ε * N * N := by bound
  have f5 : ε * N * N ≤ ε * n * n := by bound
  linarith [f4, f5]

Conclusion "Done."
