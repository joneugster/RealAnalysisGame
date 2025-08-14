import GameServer
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring

World "RealAnalysisStory"
Level 8
Title "The obtain tactic"

Introduction "
# Extracting information from existence statements

Now let's learn the counterpart to `use`. You know that if you have `∃` in the goal, you write `use` to provide a specific value.

But suppose you have a *hypothesis* that says \"there exists a real number `c` such that `f(c) = 2`\". In Lean, this looks like:
`h : ∃ (c : ℝ), f c = 2`

And say you want to prove that \"there exists a real number `c` such that `(f c)^2 = 4`\".

Again, you can't just say `exact h` because these are different statements. But you can use the information from the hypothesis to construct your proof. The name of this command is `obtain`.

The syntax for `obtain` is the weirdest yet: write

`obtain ⟨c, hc⟩ := h`.

The reason for the angle brackets is that `h` is actually a bundle of two things, first a particular value for `c`, and second is the fact, which we're calling `hc`, that `f c = 2`. And don't forget the colon-equals! You're obtaining `c` and `hc` *from* `h`.

The angle brackets `⟨ ⟩` are typed in Lean via `\\<` (backslash, less than sign, space) and `\\>`.

Then you'll have a value for `c`, and the hypothesis `hc : f c = 2`. You should be able to figure out how to solve the goal from here.
"

/-- The `obtain` tactic extracts a witness from an existence statement in a hypothesis. -/
TacticDoc obtain

/-- If there exists a point where f equals 2, then there exists a point where f² equals 4. -/
Statement (f : ℝ → ℝ) (h : ∃ c : ℝ, f c = 2) : ∃ x : ℝ, (f x) ^ 2 = 4 := by
  Hint (hidden := true) "Use `obtain ⟨c, hc⟩ := h`, then you should be able to finish it yourself."
  obtain ⟨c, hc⟩ := h
  use c
  rewrite [hc]
  ring_nf

NewTactic obtain

Conclusion "
Excellent! You've learned the `obtain` tactic for working with existence in hypotheses.

Notice the complete pattern:
1. `obtain ⟨c, hc⟩ := h` unpacked the hypothesis into a specific value `c` and proof `hc : f c = 2`
2. `use c` provided this same value as our witness for the goal
3. `rewrite [hc]` rewrote `f c` as `2` in the goal, changing it to `2^2 = 4`
4. `ring_nf` verified that `2 ^ 2 = 4`

The symmetry is beautiful:
- `use` when you have `∃` in the goal (\"here's my specific example\")
- `obtain` when you have `∃` in a hypothesis (\"let me unpack this existence claim\")

This completes your basic logical toolkit! In real analysis, you'll use `obtain` constantly when working with:
- Limit definitions (\"given ε > 0, there exists δ > 0...\")
- Intermediate Value Theorem (\"there exists c such that f(c) = 0\")
- Existence theorems throughout analysis

You're now ready to tackle real mathematical proofs!
"
