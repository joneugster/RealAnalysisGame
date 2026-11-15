import Game.Levels.L18Pset.L04
open Nat

World "L18Pset"
Level 5
Title "SeqEvenOdd"
Introduction "
# Level 5: `SeqEvenOdd`

Prove `SeqEvenOdd`:

## New theorem: `even_or_odd`

"

/--
A natural number `n` is either `Even` (that is, `∃ k, n = 2 * k`), or `Odd` (that is, `∃ k, n = 2 * k + 1`)
-/
TheoremDoc Nat.even_or_odd as "even_or_odd" in "Theorems"

NewTheorem Nat.even_or_odd

DisabledTheorem SeqEvenOdd

/-- Prove `SeqEvenOdd`
-/
Statement {a : ℕ → ℝ} {L : ℝ} (ha2n : SeqLim (fun n ↦ a (2 * n)) L)
(ha2np1 : SeqLim (fun n ↦ a (2 * n + 1)) L) : SeqLim a L := by
  intro ε hε
  choose N1 hN1 using ha2n ε hε
  choose N2 hN2 using ha2np1 ε hε
  let N := (2 * (N1 + N2)) + 1
  have Nis : N = (2 * (N1 + N2)) + 1 := by rfl
  use N
  intro n hn
  have nEvenOrOdd := even_or_odd n
  cases' nEvenOrOdd with h
  choose k hk using h
  specialize hN1 k (by bound)
  change |a (2 * k) - L| < ε at hN1
  rewrite [hk]
  rewrite [show k + k = 2 * k by ring_nf]
  apply hN1
  choose k hk using h
  specialize hN2 k (by bound)
  change |a (2 * k + 1) - L| < ε at hN2
  rewrite [hk]
  apply hN2

Conclusion "
"
