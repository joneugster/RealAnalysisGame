import Game.Levels.L12Levels.L01_MonotoneBdd

World "Lecture12"
Level 4
Title "Iterated Gaps"

Introduction "
# Level 4: Iterated Gaps

Now it's time to prove the technical helper lemma that made Level 3 possible. This result captures the precise mechanism by which persistent gaps in a monotone sequence accumulate under iteration.

## The Setup

Recall from Level 3: we had a bounded monotone sequence that we assumed (for contradiction) was not Cauchy. This gave us:
- Some `ε > 0` representing the persistent gap size
- Subsequences `τ` and `σ` where `τ n ≥ n` and `σ n ≥ τ n`
- The gap condition: `ε ≤ |a (σ n) - a (τ n)|` for all `n`

The question was: how do these gaps accumulate when we iterate `σ`?

## The Goal

**Your task:** Prove that `∀ k, k * ε ≤ a (σ^[k] 0) - a 0`

In words: iterating `σ` exactly `k` times from `0` gives us at least `k * ε` total growth from the starting value. This linear accumulation is what drives the contradiction with boundedness.

## Why This is Non-Trivial

You might think: \"If we get `ε` growth each step, then after `k` steps we get `k * ε` growth - isn't that obvious?\" But there are subtle issues:
- We don't get `ε` growth from `σ^[i] 0` to `σ^[i+1] 0` directly
- Instead, we get `ε` growth from `τ(σ^[i] 0)` to `σ(σ^[i] 0)`
- We need to carefully account for the \"gaps\" between these points

The proof requires showing that monotonicity allows us to \"telescope\" these gaps correctly.

## The Strategy

**Induction on k:**
- **Base case:** `k = 0` gives `0 ≤ a 0 - a 0`, which is trivial
- **Inductive step:** Assume we have `k * ε ≤ a (σ^[k] 0) - a 0`. We need to show `(k+1) * ε ≤ a (σ^[k+1] 0) - a 0`

The key insight: apply the gap condition at the point `σ^[k] 0` to get:
`ε ≤ |a (σ (σ^[k] 0)) - a (τ (σ^[k] 0))|`

Then use monotonicity and the `succ_iterate` theorem to connect this to the growth from `σ^[k] 0` to `σ^[k+1] 0`.

"

DisabledTheorem IterateGap

/-- Prove `IterateGap`
-/
Statement {X : Type*} [NormedField X] [LinearOrder X] [IsStrictOrderedRing X] (a : ℕ → X) (ha : Monotone a) (ε : X)
  (εpos : ε > 0)
  (τ : ℕ → ℕ) (hτ : ∀ n, τ n ≥ n)
  (σ : ℕ → ℕ) (hσ : ∀ n, σ n ≥ τ n)
  (hgap : ∀ n, ε ≤ |a (σ n) - a (τ n)|)
  : ∀ (k : ℕ), k * ε ≤ a (σ^[k] 0) - a 0
  := by
  intro k
  induction' k with k hk
  norm_num
  specialize hgap (σ^[k] 0)
  rewrite [(show |a (σ (σ^[k] 0)) - a (τ (σ^[k] 0))| = a (σ (σ^[k] 0)) - a (τ (σ^[k] 0)) by apply abs_of_nonneg (by bound))] at hgap
  rewrite [show σ (σ^[k] 0) = σ^[k + 1] 0 by apply succ_iterate] at hgap
  have f1 : 0 ≤ a (τ (σ^[k] 0)) - a (σ^[k] 0) := by bound
  push_cast
  linarith [f1, hk, hgap]

Conclusion "
## What You've Accomplished

You've proven the technical engine that drives the fundamental theorem about bounded monotone sequences. This lemma reveals exactly how persistent gaps accumulate under iteration - linearly, predictably, and inevitably.

## The Mathematical Machinery

The proof demonstrates how several sophisticated techniques work together:
- **Induction** to handle the iterative structure
- **Monotonicity** to control the relationships between intermediate points
- **The gap condition** applied at each iteration step
- **Telescoping inequalities** to accumulate the growth

This is real analysis in action: taking local properties and scaling them up to global phenomena through careful mathematical reasoning.

## Why Linear Accumulation Matters

The key insight is that gaps don't just accumulate - they accumulate *linearly*. This linear growth `k * ε` is what makes the contradiction with boundedness inevitable.

## Completing the Circle

With this lemma proven, the main theorem is now complete. You've seen how:
1. **Level 1:** Iteration extracts monotonic subsequences from chaotic growth
2. **Level 2:** Contradiction converts persistent gaps into bounded violation
3. **Level 3:** Technical precision makes the gap accumulation rigorous

Each piece was essential, and together they form a complete argument about a fundamental property of ordered systems.

## The Broader Pattern

You've mastered a proof technique that appears throughout analysis: assume pathological behavior exists, extract witnesses using choice principles, iterate to amplify the pathology until it contradicts known constraints. This pattern - *local pathology + iteration + contradiction* - is one of the most powerful tools in real analysis.

The orbit construction from Level 1, the contradiction framework from Level 2, and the inductive gap accumulation from Level 3 will serve you well in advanced mathematics.
"
