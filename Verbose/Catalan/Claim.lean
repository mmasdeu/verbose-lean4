import Verbose.Tactics.Lets
import Verbose.Catalan.Common

open Lean Verbose.Catalan

macro ("Tenim" <|> "Fet ") name:ident ":" stmt:term "per" colGt prf:tacticSeq: tactic => `(tactic|have $name : $stmt := by $prf)

open Lean Elab Tactic

elab ("Tenim" <|> "Fet ") name:ident ":" stmt:term "de" prf:maybeAppliedCA : tactic => do
  let prfTerm ← maybeAppliedCAToTerm prf
  evalTactic (← `(tactic|have $name : $stmt := by exact $prfTerm))

example : 1 = 1 := by
  Fet  H : 1 = 1 per
   rfl
  exact H

set_option linter.unusedVariables false

setLang ca

example (n : ℕ) : n + n + n = 3*n := by
  Tenim key : n + n = 2*n per
    linarith
  ring

example (n : ℤ) (h : 0 < n) : True := by
  Tenim key : 0 < 2*n per
    linarith only [h]
  Tenim keybis : 0 < 2*n de mul_pos aplicat a [zero_lt_two, h]
  trivial
