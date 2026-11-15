import Game.Levels.L22Pset.L01

open Finset Set

World "L22Pset"
Level 2
Title "Continuity Exercise"
Introduction "
# Level 2: Continuity Exercise

Prove that `x ↦ x ^ 3` is continuous.

"

/-- Prove this
-/
Statement : FunCont (fun x ↦ x ^ 3) := by
  intro x ε hε
  let δ : ℝ := min 1 (ε / (3 * |x| ^ 2 + 3 * |x| + 1))
  have δle1 : δ ≤ 1 := by bound
  have δle2 : δ ≤ ε / (3 * |x| ^ 2 + 3 * |x| + 1) := by bound
  have δpos : 0 < δ := by sorry
  use δ, δpos
  intro y hy
  rewrite [show y^3 - x^3 = (y - x) * (x ^ 2 + x * y + y ^ 2) by ring_nf]
  rewrite [show |(y - x) * (x ^ 2 + x * y + y ^ 2)| = |y - x| * |x ^ 2 + x * y + y ^ 2| by apply abs_mul]
  have hy' : |y| ≤ |x| + 1 := by sorry
  have h' : |x ^ 2 + x * y + y ^ 2| ≤ 3 * |x| ^ 2 + 3 * |x| + 1 := by sorry
  sorry


Conclusion "
"
