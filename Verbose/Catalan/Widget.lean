import Verbose.Tactics.Widget
import Verbose.Catalan.Help

namespace Verbose.Catalan
open Lean Meta Server

open ProofWidgets

implement_endpoint (lang := ca) mkReformulateHypTacStx (hyp : Ident) (new : Term) : MetaM (TSyntax `tactic) :=
`(tactic|Reformulem $hyp com $new)

implement_endpoint (lang := ca) mkShowTacStx (new : Term) : MetaM (TSyntax `tactic) :=
`(tactic|Demostrem que $new)

implement_endpoint (lang := ca) mkConcludeTacStx (args : List Term) : MetaM (TSyntax `tactic) := do
let concl ← listTermToMaybeAppliedCA args
`(tactic|Concloem amb $concl)

implement_endpoint (lang := ca) mkObtainTacStx (args : List Term) (news : List MaybeTypedIdent) :
  MetaM (TSyntax `tactic) := do
let maybeApp ← listTermToMaybeAppliedCA args
let newStuffCA ← listMaybeTypedIdentToNewStuffSuchThatEN news
`(tactic|Per $maybeApp obtenim $newStuffCA)

implement_endpoint (lang := ca) mkUseTacStx (wit : Term) : Option Term → MetaM (TSyntax `tactic)
| some goal => `(tactic|Demostrem que $wit funciona : $goal)
| none => `(tactic|Demostrem que $wit funciona)

implement_endpoint (lang := ca) mkSinceTacStx (factsCA : Array Term) (concl : Term) :
    MetaM (TSyntax `tactic) := do
  let factsCAS ← arrayToFacts factsCA
  `(tactic|Com que $factsCAS concloem que $concl)

@[server_rpc_method]
def suggestionsPanel.rpc := mkPanelRPC makeSuggestions
  "Use shift-click to select sub-expressions."
  "Suggestions"

@[widget_module]
def suggestionsPanel : Component SuggestionsParams :=
  mk_rpc_widget% suggestionsPanel.rpc

syntax (name := withSuggestions) "with_suggestions" tacticSeq : tactic

@[tactic withSuggestions]
def withPanelWidgets : Lean.Elab.Tactic.Tactic
  | stx@`(tactic| with_suggestions $seq) => do
    Lean.Widget.savePanelWidgetInfo suggestionsPanel.javascriptHash (pure .null) stx
    Lean.Elab.Tactic.evalTacticSeq seq
  | _ => Lean.Elab.throwUnsupportedSyntax
