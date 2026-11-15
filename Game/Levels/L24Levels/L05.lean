import Game.Levels.L24Levels.L04

open Set

World "Lecture24"
Level 5
Title "Heine-Borel Theorem: Part 2b"
Introduction "
# Level 5: Heine-Borel Theorem: Part 2b

**The Grand Finale**: We'll complete Heine-Borel by proving that any closed, bounded set is compact. The strategy is elegant: show that closed subsets of compact sets are compact, then use Level 4.

**New Lean Technology - Sum Types** 📦

Before diving into the proof, you need to master Lean's **disjoint union** (sum type):

**What is `α ⊕ β`?**: It's the \"either `α` or `β`\" type - every element is either from type `α` or from type `β`, but not both. Think of it as two boxes labeled \"Left\" and \"Right\":

`α ⊕ β = {Sum.inl a : a ∈ α} ∪ {Sum.inr b : b ∈ β}`

**Note**:
- `Sum.inl a` puts element `a : α` into the \"left\" side
- `Sum.inr b` puts element `b : β` into the \"right\" side

**Pattern Matching with `match`**: To make a function on a sum type, use `match`:

`let f : α ⊕ β → γ := fun x ↦
  match x with
  | Sum.inl a => ... -- handle the α case
  | Sum.inr b => ... -- handle the β case`

**Case Analysis with `cases`**: When arguing about where an element of a sum type came from, use `cases`:

`cases x with
| inl a => ... -- when x came from α
| inr b => ... -- when x came from β`

**Extracting Components**: If `s : Finset (α ⊕ β)`, then:
- `s.lefts : Finset α` extracts all the \"left\" elements
- `a ∈ s.lefts ↔ Sum.inl a ∈ s`

**Why Sum Types for This Proof?**

We need to handle TWO kinds of balls simultaneously:
1. **Original balls** (type `ι`) that cover our closed set `S`
2. **Avoidance balls** (type `Sᶜ`) that cover points outside `S`

The sum type `ι ⊕ Sᶜ` lets us create a unified covering system!

**The Strategy**:
1. Start with any covering of closed set `S ⊆ T` where `T` is compact
2. Since `S` is closed, `Sᶜ` is open - so each point in `Sᶜ` has a ball staying in `Sᶜ`
3. Use sum types to combine: original balls + avoidance balls = covering of all `T` (in fact, all of `ℝ`)
4. Apply compactness of `T` to get finite subcover
5. Extract just the \"left\" (original) balls to cover `S`, since avoidance balls don't touch `S`

**Your Mission**: Master sum types and use them to extend any covering of a closed subset to a covering of the whole compact set. This completes the Heine-Borel theorem!
"

open Classical


def Finset.lefts {α β : Type} (s : Finset (α ⊕ β)) : Finset α :=
  s.filterMap Sum.getLeft? (fun x y hx hy => by
    cases x <;> cases y <;> simp [Sum.getLeft?] at hx hy ⊢
    intro h; rwa [h]
  )

/-- `(s : Finset (α ⊕ β)) : Finset α`

The `lefts` of a finite set `s` of elements from the disjoint union `α ⊕ β` is the finite set of all elements from `α` that appear in `s`.
-/
DefinitionDoc Finset.lefts as "Finset.lefts"

NewDefinition Finset.lefts

-- Main theorem: characterizes membership in lefts
theorem mem_lefts {α β : Type}
    (s : Finset (α ⊕ β)) (a : α) :
    a ∈ s.lefts ↔ Sum.inl a ∈ s := by
  simp [Finset.lefts, Finset.mem_filterMap]

/--
A point `a : α` is in the `lefts` of a finite set `s : Finset (α ⊕ β)` if and only if the element `Sum.inl a` is in `s`.
-/
TheoremDoc mem_lefts as "mem_lefts" in "x∈U"

NewTheorem mem_lefts

namespace RealAnalysisGame

/--
Any closed subset of a compact set is compact.
-/
TheoremDoc RealAnalysisGame.IsCompact_of_ClosedSubset as "IsCompact_of_ClosedSubset" in "x∈U"

Statement IsCompact_of_ClosedSubset {S T : Set ℝ} (hST : S ⊆ T) (hT : IsCompact T) (hS : IsClosed S) : IsCompact S := by
    intro ι xs rs rspos hcover
    change IsOpen Sᶜ at hS
    change ∀ x ∈ Sᶜ, ∃ r > 0, Ball x r ⊆ Sᶜ at hS
    choose δs δspos hδs using hS
    let Sbar : Set ℝ := Sᶜ
    let J : Type := Sbar
    let U : Type := ι ⊕ J
    let xs' : U → ℝ := fun i ↦
      match i with
      | Sum.inl j => xs j
      | Sum.inr x => x
    let rs' : U → ℝ := fun i ↦
      match i with
      | Sum.inl j => rs j
      | Sum.inr x => δs x.1 x.2
    let rs'pos : ∀ i : U, rs' i > 0 := by
      intro i
      cases i with
      | inl j => exact rspos j
      | inr x => exact δspos x.1 x.2
    have hcover' : T ⊆ ⋃ (i : U), Ball (xs' i) (rs' i) := by
      intro t ht
      by_cases htS : t ∈ S
      · specialize hcover htS
        rewrite [mem_Union] at hcover
        choose j hj using hcover
        rewrite [mem_Union]
        use Sum.inl j, hj.1, hj.2
      · change t ∈ Sbar at htS
        rewrite [mem_Union]
        have hball : t ∈ Ball (xs' (Sum.inr ⟨t, htS⟩)) (rs' (Sum.inr ⟨t, htS⟩)) := by
          specialize rs'pos (Sum.inr ⟨t, htS⟩)
          split_ands
          change t - _ < t
          linarith [rs'pos]
          change t < t + _
          linarith [rs'pos]
        use Sum.inr ⟨t, htS⟩, hball.1, hball.2
    specialize hT U xs' rs' rs'pos hcover'
    choose V hV using hT
    let V₁ : Finset ι := V.lefts
    use V₁
    intro s hs
    rewrite [mem_Union]
    have hsT : s ∈ T := by bound
    specialize hV hsT
    rewrite [mem_Union] at hV
    choose i ball_i i_in_V s_in_Ball using hV
    rewrite [mem_range] at i_in_V
    choose hi hi' using i_in_V
    rewrite [← hi'] at s_in_Ball
    cases i with
    | inl j =>
        have hj : j ∈ V₁ := by
          rewrite [mem_lefts]
          apply hi
        use j
        rewrite [mem_Union]
        use hj, s_in_Ball.1, s_in_Ball.2
    | inr x =>
        exfalso
        have hxSbar : x.1 ∈ Sbar := x.2
        have hxS : x.1 ∉ S := by
          intro h
          contradiction
        specialize hδs x.1 hxSbar s_in_Ball hs
        apply hδs

  end RealAnalysisGame

Conclusion "
# 🎉 HEINE-BOREL THEOREM: COMPLETE! 🎉

You did it! You've just completed the proof of one of the most important theorems in all of mathematics:

**HEINE-BOREL THEOREM**: `S ⊆ ℝ is compact ⟺ S is closed and bounded`

**What You've Accomplished**:
- ✅ **Level 1**: Compact ⟹ Bounded
- ✅ **Level 2**: Compact ⟹ Closed
- ✅ **Level 3**: Least Upper Bound Property of ℝ
- ✅ **Level 4**: Closed Interval [a,b] is Compact
- ✅ **Level 5**: Closed Subset of Compact is Compact

**The Sum Type Mastery**: Your final proof showcased advanced Lean programming with sum types. You learned to:
- **Construct** disjoint unions `α ⊕ β`
- **Pattern match** with `match` and `cases`
- **Extract components** with `Finset.lefts`
- **Combine different index types** into unified covering systems

This isn't just theorem proving - it's sophisticated type-level programming!

**The Mathematical Journey**: You've traveled from elementary compactness through:
- **Topology** (open/closed sets, covers)
- **Real Analysis** (supremums, completeness of ℝ)
- **Logic** (proof by contradiction, case analysis)
- **Type Theory** (dependent types, sum types)

**Why This Theorem Changes Everything**:

🧮 **For Calculus**: Every continuous function on [a,b] is now guaranteed to be:
   - Uniformly continuous (by Level 23)
   - Integrable (Riemann sums converge)
   - Bounded and achieving max/min

📊 **For Analysis**: You can now easily check compactness just by verifying \"closed and bounded\" - no more wrestling with covers and subcovers!

🔬 **For Topology**: You've connected the abstract (compactness) with the concrete (closed + bounded), making topology applicable to real analysis.

**Historical Impact**: Your theorem unified 19th-century analysis. Before Heine (1872) and Borel (1895), mathematicians had intuitions about why [a,b] was special but couldn't prove it rigorously.

**The Complete Chain**: You can now trace the full logical chain:

`f continuous on [a,b] → [a,b] compact (Heine-Borel)
                     → f uniformly continuous (Level 23)
                     → f integrable (Level 23)`

**Looking Forward**: You've built the foundation for advanced analysis - measure theory, functional analysis, and differential geometry all build on compactness.

You've just proved one of the crown jewels of mathematics! Take a moment to appreciate the elegant interplay of topology, analysis, and logic you've mastered. 🏆

Welcome to the ranks of real analysts!
"
