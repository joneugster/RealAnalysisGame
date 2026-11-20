import Game.Levels.L24Levels.L02

open Set

World "Lecture24"
Level 3
Title "Least Upper Bound Property"
Introduction "
# Level 3: Least Upper Bound Property

**The Big Picture**: We're taking a detour into the deep structure of ℝ itself. To prove that closed bounded sets are compact, we need a fundamental property (that does not hold for ℚ!): **every bounded set has a supremum**.

**New Definitions**:
- **Upper Bound**: `IsUB S (M : ℝ) := ∀ s ∈ S, s ≤ M`
  - `M` sits above every point in `S`
- **Least Upper Bound**: `IsLUB S L := IsUB S L ∧ ∀ M, IsUB S M → L ≤ M`
  - `L` is an upper bound, and no smaller number is an upper bound

**The Proof Strategy - Bisection**:
We'll construct a sequence of nested intervals `[aₙ, bₙ]` that shrink to the supremum. Here's where Lean's **dependent types** shine:

`let ab : ∀ (n : ℕ), {p : ℝ × ℝ //
  (p.1 ∈ S) ∧ IsUB S p.2 ∧ p.1 ≤ p.2 ∧ p.2 - p.1 ≤ (M - s₀) / 2^n}`

This type says: \"For each `n`, give me a pair `(aₙ, bₙ)` such that:
- `aₙ ∈ S` (so the left endpoint is achievable)
- `bₙ` is an upper bound for `S`
- `aₙ ≤ bₙ` (it's a valid interval)
- The interval length shrinks by half each time\"

**The Inductive Construction**:
- **Base case**: Start with the `s₀ ∈ S` guaranteed by nonemptyness of `S`, and given upper bound `M`
- **Inductive step**: Given interval `[aₙ, bₙ]`, look at midpoint `m = (aₙ + bₙ)/2`
  - If `m` is an upper bound for `S`, set `[aₙ₊₁, bₙ₊₁] = [aₙ, m]`
  - If not, find some `s ∈ S` with `s > m`, set `[aₙ₊₁, bₙ₊₁] = [s, bₙ]`

**Dependent Types Magic**: The type system *guarantees* that our construction maintains all necessary properties at each step. We're not just building sequences - we're building sequences *with proofs* that they satisfy our constraints!

**Your Mission**: Implement this bisection algorithm and prove that the limit sequences converge to the least upper bound of `S`.
"


namespace RealAnalysisGame

def IsUB (S : Set ℝ) (M : ℝ) : Prop := ∀ s ∈ S, s ≤ M

/-- `(S : Set ℝ) (M : ℝ) : Prop := ∀ s ∈ S, s ≤ M`

The point `M` is an upper bound of the set `S` if every element `s` in `S` satisfies `s ≤ M`.
-/
DefinitionDoc IsUB as "IsUB"

def IsLUB (S : Set ℝ) (L : ℝ) : Prop := IsUB S L ∧ ∀ M, IsUB S M → L ≤ M

/-- `(S : Set ℝ) (L : ℝ) : Prop := IsUB S L ∧ ∀ M, IsUB S M → L ≤ M`

The point `L` is a least upper bound (supremum) of the set `S` if `L` is an upper bound of `S`, and for any other upper bound `M` of `S`, we have `L ≤ M`.
-/
DefinitionDoc IsLUB as "IsLUB"

NewDefinition IsLUB IsUB

/--
Every nonempty set of real numbers that is bounded above has a least upper bound.
-/
TheoremDoc RealAnalysisGame.HasLUB_of_BddNonempty as "HasLUB_of_BddNonempty" in "x∈U"

Statement HasLUB_of_BddNonempty {S : Set ℝ} (hS : S.Nonempty) {M : ℝ} (hM : IsUB S M) : ∃ L, IsLUB S L := by
  choose s₀ hs₀ using hS
  let ab : ∀ (n : ℕ), {p : ℝ × ℝ //
      (p.1 ∈ S) ∧
      IsUB S p.2 ∧
      p.1 ≤ p.2 ∧
      p.2 - p.1 ≤ (M - s₀) / 2^n} := by
      intro n
      induction' n with n hn
      · use (s₀, M)
        split_ands
        · apply hs₀
        · apply hM
        · bound
        · bound
      · let hp := hn.2
        set p : ℝ × ℝ := hn.1
        let mid : ℝ := (p.1 + p.2) / 2
        by_cases midS : ∃ s ∈ S, mid ≤ s
        · choose s sInS hs using midS
          use (s, p.2)
          split_ands
          · apply sInS
          · apply hp.2.1
          · bound
          · change p.2 - s ≤ (M - s₀) / 2^(n + 1)
            have hp' := hp.2.2.2
            change (p.1 + p.2) / 2 ≤ s at hs
            field_simp at ⊢ hp' hs
            rewrite [show (2 : ℝ) ^ (n + 1) = 2 * 2 ^ n by ring_nf]
            have f : (p.1 + p.2) * 2 ^ n ≤ 2 * s * 2 ^ n := by bound
            linarith [hp', hs, hp.2.2.1, f]
        · use (p.1, mid)
          split_ands
          · apply hp.1
          · push_neg at midS
            intro s hs
            linarith [midS s hs]
          · change p.1 ≤ (p.1 + p.2) / 2
            linarith [hp]
          · change (p.1 + p.2) / 2 - p.1 ≤ (M - s₀) / 2^(n + 1)
            have hp' := hp.2.2.2
            field_simp at ⊢ hp'
            rewrite [show (2 : ℝ) ^ (n + 1) = 2 * 2 ^ n by ring_nf]
            linarith [hp']

  let a : ℕ → ℝ := fun n ↦ (ab n).val.1
  let b : ℕ → ℝ := fun n ↦ (ab n).val.2

  have a_prop : ∀ n, a n ∈ S := by
    intro n
    have h := (ab n).property.1
    apply h

  have b_prop : ∀ n, IsUB S (b n) := by
    intro n
    have h := (ab n).property.2.1
    apply h

  have aMono : Monotone a := by
    apply Monotone_of_succ
    intro n
    have h := (ab n).property.2.2.1
    by_cases midS : ∃ s ∈ S, (a n + b n) / 2 ≤ s
    · choose s sInS hs using midS
      have ha' : a (n + 1) = (ab (n + 1)).val.1 := by rfl
      have ha'' : (ab (n + 1)).val.1 = s := by
        sorry
      have f1 : a n ≤ b n := by bound
      linarith [f1, ha', ha'', hs]
    · have ha' : a (n + 1) = a n := by sorry
      linarith [ha']

  have bAnti : Antitone b := by sorry

  have aBnded : ∀ n, a n ≤ b 0 := by
    intro n
    have hb : (b n) ≤ b 0 := by bound
    specialize b_prop n (a n) (a_prop n)
    linarith [b_prop, hb]

  have bBnded : ∀ n, a 0 ≤ b n := by
    intro n
    have ha : a 0 ≤ (a n) := by bound
    apply b_prop n (a 0) (a_prop 0)

  have aCauchy := IsCauchy_of_MonotoneBdd aMono aBnded
  have bCauchy := IsCauchy_of_AntitoneBdd bAnti bBnded

  choose La hLa using SeqConv_of_IsCauchy aCauchy
  choose Lb hLb using SeqConv_of_IsCauchy bCauchy

  have L_le_b : ∀ n, Lb ≤ b n := by sorry

  have L_le_b' : ∀ ε > 0, ∃ N, ∀ n ≥ N, b n < Lb + ε := by
    by_contra h
    push_neg at h
    choose ε εpos hε using h
    choose N hN using hLb ε εpos
    choose n n_N hn using hε N
    specialize hN n n_N
    rewrite [abs_lt] at hN
    linarith [hN, hn]

  have a_le_L : ∀ n, a n ≤ La := by sorry

  have a_le_L' : ∀ ε > 0, ∃ N, ∀ n ≥ N, La - ε < a n := by
    by_contra h
    push_neg at h
    choose ε εpos hε using h
    choose N hN using hLa ε εpos
    choose n n_N hn using hε N
    specialize hN n n_N
    rewrite [abs_lt] at hN
    linarith [hN, hn]

  have La_eq_Lb : La = Lb := by
    have f1 : SeqLim (fun n ↦ b n - a n) 0 := by sorry
    sorry

  use La

  split_ands

  · intro s hs
    rewrite [La_eq_Lb]
    by_contra h
    push_neg at h
    specialize L_le_b' (s - Lb) (by bound)
    choose N hN using L_le_b'
    specialize hN N (by bound)
    specialize b_prop N s hs
    linarith [hN, b_prop, h]
  · intro M hM
    by_contra h
    push_neg at h
    specialize a_le_L' (La - M) (by bound)
    choose N hN using a_le_L'
    specialize hN N (by bound)
    rewrite [show La - (La - M) = M by ring_nf] at hN
    specialize hM (a N) (a_prop N)
    linarith [hM, hN]


  end RealAnalysisGame

Conclusion "
# You've Just Proved ℝ is Complete!

Congratulations! You've just established one of the most fundamental properties of the real numbers: the **Least Upper Bound Property**. This is
another way to say that `ℝ` is \"complete\" - it has no gaps.

**What Made This Proof Special**:
- **Dependent Types Power**: Your proof showcased Lean's dependent type system at its best. The type `ℕ → {p : ℝ × ℝ // ...}` didn't just give you pairs of reals - it gave you pairs *with built-in proofs* that they satisfy all your constraints, and depend on the `n : ℕ`.
- **Constructive Algorithm**: Your bisection method doesn't just prove a supremum exists - it gives you an algorithm to compute it to arbitrary precision!
- **Induction on Steroids**: You weren't just proving a property for all `n` - you were constructing a sequence where each element depends on satisfying complex constraints involving the previous ones.

**Why This Property is Profound**:
- **`ℚ` Fails Here**: The rationals are missing \"limit points\" like √2. Your proof shows ℝ has no such gaps.
- **Topology Connection**: Completeness (LUB property) is what makes compact sets in ℝ so well-behaved.
- **Analysis Foundation**: Virtually every major theorem in real analysis depends on this completeness property.

**The Nested Interval Magic**: Your proof created intervals `[aₙ, bₙ]` with three beautiful properties:
1. Each `aₙ ∈ S` (reachable from below)
2. Each `bₙ` is an upper bound (unreachable from `S`)
3. `bₙ - aₙ → 0` (they squeeze together)

The limit of this squeeze is exactly the supremum!

**What's Coming**: Armed with the LUB property, you're now ready for the hard part of Heine-Borel. In Level 4, you'll prove that closed intervals `[a,b]` are compact. This will use your LUB property in a sophisticated way to show that any open cover can be reduced to a finite subcover.

**Historical Note**: This property was one of the last pieces needed to make calculus rigorous. Weierstrass, Dedekind, and Cantor all worked on different ways to construct ℝ with this completeness property in the 1870s.

You've just proved one of the crown jewels of real analysis! 👑
"
