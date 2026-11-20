import Game.Levels.L10Lecture

open Finset

World "L10Pset"
Level 1
Title "Problem 1"

Introduction "
# Problem 1:

Assume that the sequence `c` is a shuffling of sequences `a` and `b`,
namely, that `(c 0, c 1, c 2, ...) = (a 0, b 0, a 1, b 1, a 2, b 2,...)`.
Assume that the sequence `c` converges.
Prove that the sequences `a` and `b` converge, and to the same thing. It's enough to prove that `a` converges, as the proof for `b` will be similar.

## New tactic! `grind`

We'll add another powerful tactic that sometimes works where `bound` doesn't; it's called `grind`.

In this exercise, you might find it useful at some point to write:

`have fact : (if Even (2 * n) then a (2 * n / 2) else b ((2 * n - 1) / 2)) = a n := by grind`

On the right of this equality is just `a n`; on the left it says: if `2 * n` is `Even` (which of course it is), then return `a (2 * n / 2)` -- which we want `grind` to simplify to `a n` -- and if not, then return `b ((2n-1)/2)` -- which is irrelevant, since `2n` is not odd.

See if you can solve it from there...
"

/-- The `grind` tactic is like `bound` but works in *some* situations where `bound` fails.  -/
TacticDoc grind

NewTactic grind

/-- Prove this
-/
Statement (a b c : ℕ → ℝ) (hc : ∀ n, c n = if Even n then a (n / 2) else b ((n - 1) / 2))
        (cConv : SeqConv c) : ∃ L, SeqLim a L := by
  choose L hL using cConv
  use L
  intro ε hε
  choose N hN using hL ε hε
  use 2 * N
  intro n hn
  specialize hN (2 * n) (by bound)
  specialize hc (2 * n)
  rewrite [hc] at hN
  have fact : (if Even (2 * n) then a (2 * n / 2) else b ((2 * n - 1) / 2)) = a n := by grind
  rewrite [fact] at hN
  apply hN

Conclusion "Done."
