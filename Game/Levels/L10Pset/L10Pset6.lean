import Game.Levels.L10Pset.L10Pset5

World "L10Pset"
Level 5
Title "Problem 5"

Introduction "
# Problem 5:

Show that the sequence `a n = n` is unbounded.

"

/-- Prove this
-/
Statement (a : ℕ → ℝ) (ha : ∀ n, a n = n) : ¬ SeqBdd a := by
  intro h
  choose L Lpos hL using h
  let N : ℕ := ⌈L⌉₊ + 1
  have hN : N = ⌈L⌉₊ + 1 := by rfl
  have hN' : (N : ℝ) = ⌈L⌉₊ + 1 := by exact_mod_cast hN
  have hL' : L ≤ ⌈L⌉₊ := by bound
  have hNL : L < N := by linarith [hL', hN']
  specialize hL N
  rewrite [ha] at hL
  have Npos' : 0 ≤ N := by bound
  have Npos : (0 : ℝ) ≤ N := by exact_mod_cast Npos'
  rewrite [(by apply abs_of_nonneg Npos : |(N : ℝ)| = N)] at hL
  linarith [hL, hNL]

Conclusion "Done."
