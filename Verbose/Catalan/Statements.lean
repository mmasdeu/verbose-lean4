import Verbose.Tactics.Statements
import Verbose.Catalan.Widget

import ProofWidgets.Demos.Macro

open Lean Meta Elab Command Parser Tactic

open Lean.Parser.Term (bracketedBinder)

implement_endpoint (lang := ca) mkWidgetProof (prf : TSyntax ``tacticSeq) : CoreM (TSyntax `tactic) :=
Lean.TSyntax.mkInfoCanonical <$> `(tactic| with_suggestions $prf)

elab name?:(ident)? ("Exercici"<|>"Exemple"<|>"Lema"<|>"Teorema") str
    "Dades:"? objs:bracketedBinder*
    "Hipòtesis:"? hyps:bracketedBinder*
    "Conclusió:" concl:term
    tkp:"Demostració:" prf?:(tacticSeq)? tkq:"QED" : command => do
  mkExercise name? objs hyps concl prf? tkp tkq
