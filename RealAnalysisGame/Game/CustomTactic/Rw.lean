/-
Copyright (c) 2023 Jon Eugster. All rights reserved.
This file has been copied from the Natural Number Game (NNG4) at
https://github.com/leanprover-community/NNG4
where it has been released under Apache 2.0 license included here as
`LICENSE-NNG4`.
-/

import Mathlib.Lean.Expr.Basic
import Lean.Elab.Tactic.Basic
import Lean.Elab.Tactic.Rewrite

/-!
# Modified `rw`

Modify `rw` to work like `rewrite`.

This is mainly a copy of the implementation of `rewrite` in Lean core.
-/

namespace RealAnalysisGame

open Lean.Meta Lean.Elab.Tactic Lean.Parser.Tactic

/--
Modified `rw` tactic. For this game, `rw` works exactly like `rewrite`.
-/
syntax (name := rewriteSeq) "rw" (config)? rwRuleSeq (location)? : tactic

@[tactic rewriteSeq] def evalRewriteSeq : Tactic := fun stx => do
  let cfg ← elabRewriteConfig stx[1]
  let loc   := expandOptLocation stx[3]
  withRWRulesSeq stx[0] stx[2] fun symm term => do
    withLocation loc
      (rewriteLocalDecl term symm · cfg)
      (rewriteTarget term symm cfg)
      (throwTacticEx `rewrite · "did not find instance of the pattern in the current goal")
