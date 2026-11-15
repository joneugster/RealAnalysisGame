import Game.Levels.L7Pset.L7Pset1

World "L7Pset"
Level 2
Title "Problem 2"

Introduction "# Problem 2

Suppose that sequences `a b : ℕ → ℝ` converge to `L` and `M`, resp, with `L < M`. Show that
eventually, `a n < b n`.

"

/-- Prove the statement. -/
Statement (a b : ℕ → ℝ) (L M : ℝ) (ha : SeqLim a L) (hb : SeqLim b M) (hLM : L < M) :
  ∃ N, ∀ n ≥ N, a n < b n := by
  have LneM : M - L ≠ 0 := by bound
  have absML : 0 < |M - L| := by apply abs_pos_of_nonzero LneM
  have MsubL : 0 ≤ M - L := by bound
  have absMLeq : |M - L| = M - L := by apply abs_of_nonneg MsubL
  have absML2 : 0 < |M - L| / 2 := by bound
  specialize ha (|M - L| / 2) absML2
  specialize hb (|M - L| / 2) absML2
  choose N1 hN1 using ha
  choose N2 hN2 using hb
  use N1 + N2
  intro n hn
  have nN1 : N1 ≤ n := by bound
  have nN2 : N2 ≤ n := by bound
  specialize hN1 n nN1
  specialize hN2 n nN2
  rewrite [abs_lt, absMLeq] at hN1
  rewrite [abs_lt, absMLeq] at hN2
  linarith [hN1.2, hN2.1]

Conclusion "Done."
