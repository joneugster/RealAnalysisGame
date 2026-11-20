import Game.Levels.L22Pset.L02

open Finset Set

World "L22Pset"
Level 3
Title "Differentiability Exercise"
Introduction "
# Level 3: Differentiability Exercise

Show that `x ↦ x ^ 3` is differentiable.

"

/-- Prove this
-/
Statement : ∃ g : ℝ → ℝ,
  FunDeriv (fun x ↦ x ^ 3) g := by
  use (fun x ↦ 3 * x ^ 2)
  intro x ε hε
  let δ : ℝ := min 1 (ε / (3 * |x| + 1))
  have δ_le1 : δ ≤ 1 := by bound
  have δ_le2 : δ ≤ ε / (3 * |x| + 1) := by bound
  have δpos : 0 < δ := by sorry
  use δ, δpos
  intro h hne hh
  rewrite [show ((x + h) ^ 3 - x ^ 3) / h - 3 * x ^ 2 = (h - 0) * (3 * x + h) by field_simp; ring_nf]
  rewrite [show |(h - 0) * (3 * x + h)| = |h - 0| * |3 * x + h| by apply abs_mul]
  have h1 : |3 * x + h| ≤ 3 * |x| + 1 := by sorry
  sorry

Conclusion "
"
