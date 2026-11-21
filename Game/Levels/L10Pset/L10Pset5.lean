import Game.Levels.L10Pset.L10Pset4

World "L10Pset"
Level 4
Title "Problem 4"

Introduction "
# Problem 4:

Exhibit (by starting with `let a : ℕ → ℝ := fun n ↦ ???`)
a sequence so that

- the terms are all strictly positive: `∀ n, 0 < a n`,
- and yet the sequence converges to zero (and not something strictly positive!).

When you define a new sequence using `let`, you might find it
convenient to immediately prove a trivial theorem restating the definition:

`have ha : ∀ n, a n = ??? := by intro n; rfl`

This may become useful should you want to `rewrite` by `ha` (you can't rewrite by `a`, since it's a definition, not a theorem!)...

**Extra challenge:** See if you can do it by using theorems we already proved, not by going into the `ε-N` definition...

"

/-- Prove this
-/
Statement : ∃ a, SeqLim a 0 ∧ ∀ n, 0 < a n := by
  let a : ℕ → ℝ := fun n ↦ 1 / (n + 1)
  have ha : ∀ n, a n = 1 / (n + 1) := by intro n; rfl
  use a
  split_ands
  let σ : ℕ → ℕ := fun n ↦ n + 1
  have hσ : ∀ n, σ n = n + 1 := by intro n; rfl
  have isSub : Subseq σ := by intro i j hij; bound
  let c : ℕ → ℝ := fun n ↦ 1 / n
  have hc : ∀ n, c n = 1 / n := by intro n; rfl
  have limc : SeqLim c 0 := by apply OneOverNLimZero c hc
  have f1 : ∀ n, a n = c (σ n) := by intro n; rewrite [ha, hσ, hc]; push_cast; rfl
  have f2 : a = c ∘ σ := by grind -- TODO
  rewrite [f2]
  apply SubseqConv c 0 limc σ isSub
  intro n
  rewrite [ha]
  bound

Conclusion "Done."
