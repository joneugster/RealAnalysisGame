import Game.Levels.L15Lecture
import Game.Levels.L13PsetIntro

World "L15Pset"
Level 1
Title "Problem 1"

Introduction "
# Problem 1:

Prove that $0.999... = 1.0000$. Better yet, let's do it in binary.
That is, you have two **rational** (Cauchy) sequences, `a n = 1 - 1 / 2^n` and `b n = 1`.
The two sequences are equivalent if `a n - b n` goes to zero, that is, if for all `ε > 0, ∃ N, ∀ n ≥ N, |a n - b n| < ε`.

Hint: In Lecture 8, we proved a theorem (now) called `IdLeTwoPow`...

"

/-- Prove this
-/
Statement (a b : ℕ → ℚ) (ha : ∀ n, a n = 1 - 1 / 2 ^ n) (hb : ∀ n, b n = 1) : ∀ ε > 0, ∃ N, ∀ n ≥ N, |a n - b n| < ε := by
  intro ε hε
  choose N hN using ArchProp (show (0 : ℝ) < ε by exact_mod_cast hε)
  norm_cast at hN
  use N
  intro n hn
  rewrite [ha n, hb n]
  rewrite [show |(1 : ℚ) - 1 / 2 ^ n - 1| = 1 / 2 ^ n by bound]
  have hn' : (N : ℚ) ≤ n := by exact_mod_cast hn
  have hn'' : (n : ℚ) < 2 ^ n := by exact_mod_cast IdLeTwoPow n
  have εinv : 0 < 1 / ε := by bound
  have Npos : (0 : ℚ) < N := by linarith [εinv, hN]
  have npos : (0 : ℚ) < n := by linarith [Npos, hn']
  field_simp at hN
  have hN' : (1 : ℚ) / N < ε := by field_simp; linarith [hN]
  have hn'inv : (1 : ℚ) / n ≤ 1 / N := by field_simp; linarith [hn']
  have hn''inv : (1 : ℚ) / 2 ^ n < 1 / n := by field_simp; linarith [hn'']
  linarith [hn''inv, hn'inv, hN']

Conclusion "Done."
