import Game.Levels.L18Pset.L09
open Finset

World "L18Pset"
Level 10
Title "DiffGoesToZero"
Introduction "
# Level 10: `DiffGoesToZero`

Prove `DiffGoesToZero`:

"

DisabledTheorem DiffGoesToZero

/-- Prove `DiffGoesToZero`
-/
Statement  {a : ℕ → ℝ} (aLim : SeqLim a 0) : SeqLim (fun n ↦ ∑ k ∈ range (2 * n + 1), (-1)^k * a k - ∑ k ∈ range (2 * n), (-1)^k * a k) 0 := by
  intro ε hε
  choose N hN using aLim ε hε
  use N
  intro n hn
  change |Series (fun k ↦ (-1) ^ k * a k) (2 * n + 1) - Series (fun k ↦ (-1) ^ k * a k) (2 * n) - 0| < ε
  rewrite [DiffOfSeries _ (by bound)]
  rewrite [sum_Ico_succ (by bound)]
  rewrite [show ∑ k ∈ Ico (2 * n) (2 * n), (-1) ^ k * a k = 0 by bound]
  rewrite [show (-1) ^ (2 * n) * a (2 * n) = a (2 * n) by ring_nf; bound]
  specialize hN (2 * n) (by bound)
  ring_nf at ⊢ hN
  apply hN

Conclusion "
"
