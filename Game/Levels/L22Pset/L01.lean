import Game.Levels.L22Lecture
import Game.Levels.L20PsetIntro

open Finset

World "L22Pset"
Level 1
Title "Pointwise of Uniform Convergence"
Introduction "
# Level 1: Pointwise of Uniform Convergence

Prove that if a sequence of functions converges uniformly to a limit function,
then it also converges pointwise.

"

/-- Prove this
-/
Statement (f : ℕ → ℝ → ℝ) (F : ℝ → ℝ) (hfF : UnifConv f F) :
  ∀ x, SeqLim (fun n ↦ f n x) (F x) := by
  intro x
  intro ε hε
  choose N hN using hfF ε hε
  use N
  intro n hn
  apply hN n hn x
