import Game.Levels.L18Pset.L08
open Finset

World "L18Pset"
Level 9
Title "BddSeriesOdd"
Introduction "
# Level 9: `BddSeriesOdd`

Prove `BddSeriesOdd`:

"

DisabledTheorem BddSeriesOdd

/-- Prove `BddSeriesOdd`
-/
Statement {a : ℕ → ℝ} (ha : Antitone a) (ha' : ∀ n, 0 ≤ a n) (n : ℕ) : 0 ≤ ∑ k ∈ range (2 * n + 1), (-1)^k * a k := by
  rewrite [sum_range_succ]
  rewrite [show  (-1) ^ (2 * n) * a (2 * n) =  a (2 * n) by ring_nf; bound]
  have f : 0 ≤ ∑ x ∈ range (2 * n), (-1) ^ x * a x := by
    induction' n with n hn;
    bound
    rewrite [show 2 * (n + 1) = 2 * n + 2 by ring_nf]
    rewrite [sum_range_succ, sum_range_succ]
    rewrite [show (-1) ^ (2 * n) * a (2 * n) = a (2 * n) by ring_nf; bound]
    rewrite [show (-1) ^ (2 * n + 1) * a (2 * n + 1) = -a (2 * n + 1) by ring_nf; bound]
    have f2 : a (2 * n + 1) ≤ a (2 * n) := by apply ha (by bound)
    linarith [f2, hn]
  linarith [f, ha' (2 * n)]

Conclusion "
"
