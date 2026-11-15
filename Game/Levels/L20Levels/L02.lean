import Game.Levels.L20Levels.L01

World "Lecture20"
Level 2
Title "Continuous Functions"
Introduction "
# Level 2: Continuity at a Point

Excellent work with limits! Now we can define one of the most important concepts in analysis: **continuity**.

## The Definition

**Definition (`FunContAt`):** We say that `f` is **continuous at** `c` if:
```
∀ ε > 0, ∃ δ > 0, ∀ x, |x - c| < δ → |f x - f c| < ε
```

This is written `FunContAt f c`.

## Continuity vs. Limits

Notice the subtle but crucial differences from `FunLimAt`:

1. **No `x ≠ c` condition:** We care about *all* x near c, including c itself
2. **The limit is `f c`:** The function value at c must match the limit as x approaches c; we don't need a separate variable name `L` for the limit, since `L` *must* be `f c`.

In other words: **A function is continuous at c if its limit at c exists and equals f(c).**

## Why This Matters

The function `f(x) = (x² - 1)/(x - 1)` from the previous level had a limit at `x = 1`, but it's *not* continuous there (because `f(1) = 0 ≠ 2` in Lean's system).

However, the function `g(x) = x² - 1` is continuous everywhere, including at `x = 2`!

## Your Challenge

Prove that the function `f(x) = x² - 1` is continuous at `x = 2`:

`FunContAt (fun x ↦ x^2 - 1) 2`

**Hint:** Given `ε > 0`, you need to find `δ > 0` such that `|x - 2| < δ` implies
`|f(x) - f(2)| < ε`.

Note that `f(2) = 3` and `f(x) - f(2) = x² - 1 - 3 = x² - 4 = (x - 2)(x + 2)`.

So `|f(x) - f(2)| = |x - 2| · |x + 2|`.

If we restrict `x` to be within distance `1` of `2` (i.e., `1 < x < 3`), then `|x + 2| < 5`.

Therefore, if we choose `δ = min(1, ε/5)`, we can control `|f(x) - f(2)|`!

Try using `use min 1 (ε / 5)` and split into cases based on whether `|x - 2| < 1`.

"

def FunContAt (f : ℝ → ℝ) (c : ℝ) : Prop :=
  ∀ ε > 0, ∃ δ > 0, ∀ x, |x - c| < δ → |f x - f c| < ε

/-- `∀ ε > 0, ∃ δ > 0, ∀ x, |x - c| < δ → |f x - f c| < ε`


The function `f` is continuous at `x = c`.
-/
DefinitionDoc FunContAt as "FunContAt"

NewDefinition FunContAt

Statement :
    FunContAt (fun x ↦ x^2 - 1) 2 := by
  intro ε hε
  use min 1 (ε / 5)
  split_ands
  bound
  intro x hx
  change |x ^ 2 - 1 - (2 ^ 2 - 1)| < ε
  rewrite [show x ^ 2 - 1 - (2 ^ 2 - 1) = (x + 2) * (x - 2) by ring_nf]
  rewrite [show |(x + 2) * (x - 2)| = |(x + 2)| * |(x - 2)| by bound]
  have f1 : min 1 (ε / 5) ≤ 1 := by bound
  have f2 : min 1 (ε / 5) ≤ ε / 5 := by bound
  have hx' : |x - 2| < 1 := by bound
  have hx'' : |x + 2| < 5 := by
    rewrite [abs_lt] at hx' ⊢
    split_ands
    linarith [hx']
    linarith [hx']
  have hx''' : |x - 2| < ε / 5 := by bound
  have f3 : |(x + 2)| * |(x - 2)| ≤ 5 * |(x - 2)| := by bound
  have f4 : 5 * |(x - 2)| < 5 * ε / 5 := by bound
  rewrite [show 5 * ε / 5 = ε by bound] at f4
  linarith [f3, f4]

Conclusion "
## What We've Learned

This example illustrates the key differences between limits and continuity:

- **Continuity requires three things**: the function must be defined at the point, the limit must exist, and they must be equal
- Unlike limits, continuity cares about what happens **at** the point, not just near it
- The `ε`-`δ` definitions look similar, but the absence of `x ≠ c` makes all the difference

### The Art of Choosing `δ`

Notice our choice: `δ = min(1, ε/5)`. This is a classic technique!

- **First component (`δ ≤ 1`)**: Restricts `x` to a neighborhood where we can bound `|x + 2|`
- **Second component (`δ ≤ ε/5`)**: Actually controls the error to be less than `ε`

The key algebraic insight: `|f(x) - f(c)| = |x - 2| · |x + 2|`

We can't just use `δ = ε` because of that extra factor `|x + 2|`. So we:
1. Use `δ ≤ 1` to ensure `|x + 2| < 5`
2. Use `δ ≤ ε/5` so that `|x - 2| · |x + 2| < (ε/5) · 5 = ε`

**Key insight:** When proving continuity, factor the difference and bound each piece separately!

This \"localize then control\" strategy is fundamental to `ε`-`δ` proofs. You'll see it again and again throughout analysis.
"
