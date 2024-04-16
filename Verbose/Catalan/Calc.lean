import Verbose.Tactics.Calc
import Verbose.Catalan.Common

namespace Lean.Elab.Tactic
open Meta Verbose Catalan

declare_syntax_cat CalcFirstStepCA
syntax ppIndent(colGe term (" de " maybeAppliedCA)?) : CalcFirstStepCA
syntax ppIndent(colGe term (" perquè " factsCA)?) : CalcFirstStepCA
syntax ppIndent(colGe term (" per " tacticSeq)?) : CalcFirstStepCA

-- enforce indentation of calc steps so we know when to stop parsing them
declare_syntax_cat CalcStepCA
syntax ppIndent(colGe term " de " maybeAppliedCA) : CalcStepCA
syntax ppIndent(colGe term " perquè " factsCA) : CalcStepCA
syntax ppIndent(colGe term " per " tacticSeq) : CalcStepCA
syntax CalcStepsCA := ppLine withPosition(CalcFirstStepCA) withPosition((ppLine linebreak CalcStepCA)*)

syntax (name := calcTacticCA) "Calc" CalcStepsCA : tactic

elab tk:"sinceCalcTacCA" factsCA:factsCA : tactic => withRef tk <| sinceCalcTac (factsCAToArray factsCA)

def convertFirstCalcStepCA (step : TSyntax `CalcFirstStepCA) : TermElabM (TSyntax ``calcFirstStep) := do
  match step with
  | `(CalcFirstStepCA|$t:term) => `(calcFirstStep|$t:term)
  | `(CalcFirstStepCA|$t:term de $prf:maybeAppliedCA) => do let prfT ← maybeAppliedCAToTerm prf; `(calcFirstStep|$t := by fromCalcTac $prfT)
  | `(CalcFirstStepCA|$t:term perquè%$tk $factsCA:factsCA) => `(calcFirstStep|$t := by sinceCalcTacCA%$tk $factsCA)
  | `(CalcFirstStepCA|$t:term per $prf:tacticSeq) => `(calcFirstStep|$t := by $prf)
  | _ => throwUnsupportedSyntax


def convertCalcStepCA (step : TSyntax `CalcStepCA) : TermElabM (TSyntax ``calcStep) := do
  match step with
  | `(CalcStepCA|$t:term de $prf:maybeAppliedCA) => do let prfT ← maybeAppliedCAToTerm prf; `(calcStep|$t := by fromCalcTac $prfT)
  | `(CalcStepCA|$t:term perquè%$tk $factsCA:factsCA) => `(calcStep|$t := by sinceCalcTacCA%$tk $factsCA)
  | `(CalcStepCA|$t:term per $prf:tacticSeq) => `(calcStep|$t := by $prf)
  | _ => throwUnsupportedSyntax

def convertCalcStepsCA (steps : TSyntax ``CalcStepsCA) : TermElabM (TSyntax ``calcSteps) := do
  match steps with
  | `(CalcStepsCA| $first:CalcFirstStepCA
       $steps:CalcStepCA*) => do
         let first ← convertFirstCalcStepCA first
         let steps ← steps.mapM convertCalcStepCA
         `(calcSteps|$first
           $steps*)
  | _ => throwUnsupportedSyntax


elab_rules : tactic
| `(tactic|Calc%$calcstx $stx) => do
  let steps : TSyntax ``CalcStepsCA := ⟨stx⟩
  let steps ← convertCalcStepsCA steps
  let some calcRange := (← getFileMap).rangeOfStx? calcstx | unreachable!
  let indent := calcRange.start.character
  let mut isFirst := true
  for step in ← Lean.Elab.Term.getCalcSteps steps do
    let some replaceRange := (← getFileMap).rangeOfStx? step | unreachable!
    let `(calcStep| $(_) := $proofTerm) := step | unreachable!
    let json := json% {"replaceRange": $(replaceRange),
                       "isFirst": $(isFirst),
                       "indent": $(indent)}
    Lean.Widget.savePanelWidgetInfo CalcPanel.javascriptHash (pure json) proofTerm
    isFirst := false
  evalCalc (← `(tactic|calc%$calcstx $steps))

implement_endpoint (lang := ca) failProvingFacts (goal : Format) : CoreM String :=
pure s!"No s'ha pogut demostrar el següent amb les hipòtesis donades.\n{goal}"

setLang ca

example (a b : ℕ) : (a + b)^ 2 = 2*a*b + (a^2 + b^2) := by
  Calc (a+b)^2 = a^2 + b^2 + 2*a*b per ring
  _ = 2*a*b + (a^2 + b^2) de add_comm
