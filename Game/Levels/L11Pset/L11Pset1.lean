import Game.Levels.L11Lecture
import Game.Levels.L10PsetIntro

World "L11Pset"
Level 1
Title "Problem 1"

Introduction "
# Problem 1:

Prove that the sequence `a n = n` has no convergent subsequence.

"

/-- Prove this
-/
Statement (a : ℕ → ℝ) (ha : ∀ n, a n = n)
      : ¬ ∃ σ, Subseq σ ∧ SeqConv (a ∘ σ) := by
  intro h
  choose σ σ_subseq hσ using h
  choose L hL using hσ
  choose M Mpos hM using Bdd_of_Conv (a ∘ σ) L hL
  let n : ℕ := ⌈M⌉₊ + 1
  have hn : (n : ℝ) = ⌈M⌉₊ + 1 := by exact_mod_cast (by rfl)
  have hn' : M ≤ ⌈M⌉₊ := by bound
  have hn'' : M < n := by bound
  specialize hM n
  change |a (σ n)| ≤ M at hM
  rewrite [ha] at hM
  have f1 : n ≤ σ n := by apply SubseqGe σ_subseq
  have f2 : (0 : ℝ) ≤ σ n := by exact_mod_cast (by bound)
  rewrite [(by apply abs_of_nonneg f2 : |(σ n : ℝ)| = (σ n))] at hM
  have f3 : (n : ℝ) ≤ σ n := by exact_mod_cast f1
  linarith [f3, hM, hn'']

Conclusion "Done."
