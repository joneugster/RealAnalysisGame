import Game.Levels.L18Pset.L02
open Finset

World "L18Pset"
Level 3
Title "AntitoneLimitBound"
Introduction "
# Level 3: `AntitoneLimitBound`

Prove `AntitoneLimitBound`:

"

DisabledTheorem AntitoneLimitBound

/-- Prove `AntitoneLimitBound`
-/
Statement {a : ℕ → ℝ} (ha : Antitone a) {L : ℝ} (aLim : SeqLim a L) : ∀ n,
  L ≤ a n := by
  by_contra h
  push_neg at h
  choose n0 hn0 using h
  choose N hN using aLim (L - a n0) (by bound)
  specialize hN (N + n0) (by bound)
  rewrite [abs_lt] at hN
  have hN' : a n0 < a (N + n0) := by linarith [hN.1]
  have f1 : a (N+n0) ≤ a n0 := by apply ha (by bound)
  linarith [f1, hN']

Conclusion "
"
