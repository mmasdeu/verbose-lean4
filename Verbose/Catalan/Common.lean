import Verbose.Tactics.Common

open Lean

namespace Verbose.Catalan

declare_syntax_cat maybeAppliedCA
syntax term : maybeAppliedCA
syntax term "aplicat a " term : maybeAppliedCA
syntax term "aplicat a [" term,* "]" : maybeAppliedCA
syntax term "aplicat a " term " utilitzant " term : maybeAppliedCA
syntax term "aplicat a " term " utilitzant que " term : maybeAppliedCA
syntax term "aplicat a " term " utilitzant [" term,* "]" : maybeAppliedCA

def maybeAppliedCAToTerm : TSyntax `maybeAppliedCA → MetaM Term
| `(maybeAppliedCA| $e:term) => pure e
| `(maybeAppliedCA| $e:term aplicat a $x:term) => `($e $x)
| `(maybeAppliedCA| $e:term aplicat a $x:term utilitzant $y) => `($e $x $y)
| `(maybeAppliedCA| $e:term aplicat a $x:term utilitzant que $y) => `($e $x (strongAssumption% $y))
| `(maybeAppliedCA| $e:term aplicat a $x:term utilitzant [$args:term,*]) => `($e $x $args*)
| `(maybeAppliedCA| $e:term aplicat a [$args:term,*]) => `($e $args*)
| _ => pure default -- This will never happen as long as nobody extends maybeAppliedCA

/-- Build a maybe applied syntax from a list of term.
When the list has at least two elements, the first one is a function
and the second one is its main arguments. When there is a third element, it is Suposemd
to be the type of a prop argument. -/
def listTermToMaybeAppliedCA : List Term → MetaM (TSyntax `maybeAppliedCA)
| [x] => `(maybeAppliedCA|$x:term)
| [x, y] => `(maybeAppliedCA|$x:term aplicat a $y)
| [x, y, z] => `(maybeAppliedCA|$x:term aplicat a $y utilitzant que $z)
| x::y::l => `(maybeAppliedCA|$x:term aplicat a $y:term utilitzant [$(.ofElems l.toArray),*])
| _ => pure ⟨Syntax.missing⟩ -- This should never happen

declare_syntax_cat newStuffCA
syntax (ppSpace colGt maybeTypedIdent)* : newStuffCA
syntax maybeTypedIdent "tal que" ppSpace colGt maybeTypedIdent : newStuffCA
syntax maybeTypedIdent "tal que" ppSpace colGt maybeTypedIdent " , i "
       ppSpace colGt maybeTypedIdent : newStuffCA

def newStuffCAToArray : TSyntax `newStuffCA → Array MaybeTypedIdent
| `(newStuffCA| $news:maybeTypedIdent*) => Array.map toMaybeTypedIdent news
| `(newStuffCA| $x:maybeTypedIdent tal que $news:maybeTypedIdent) =>
    Array.map toMaybeTypedIdent #[x, news]
| `(newStuffCA| $x:maybeTypedIdent tal que $y:maybeTypedIdent , i $z) =>
    Array.map toMaybeTypedIdent #[x, y, z]
| _ => #[]

def listMaybeTypedIdentToNewStuffSuchThatEN : List MaybeTypedIdent → MetaM (TSyntax `newStuffCA)
| [x] => do `(newStuffCA| $(← x.stx):maybeTypedIdent)
| [x, y] => do `(newStuffCA| $(← x.stx):maybeTypedIdent tal que $(← y.stx'))
| [x, y, z] => do `(newStuffCA| $(← x.stx):maybeTypedIdent tal que $(← y.stx) , i $(← z.stx))
| _ => pure default

declare_syntax_cat newFactsCA
syntax colGt namedType : newFactsCA
syntax colGt namedType " , i "  colGt namedType : newFactsCA
syntax colGt namedType ", "  colGt namedType " , i "  colGt namedType : newFactsCA

def newFactsCAToArray : TSyntax `newFactsCA → Array NamedType
| `(newFactsCA| $x:namedType) => #[toNamedType x]
| `(newFactsCA| $x:namedType , i $y:namedType) =>
    #[toNamedType x, toNamedType y]
| `(newFactsCA| $x:namedType, $y:namedType , i $z:namedType) =>
    #[toNamedType x, toNamedType y, toNamedType z]
| _ => #[]

def newFactsCAToTypeTerm : TSyntax `newFactsCA → MetaM Term
| `(newFactsCA| $x:namedType) => do
    namedTypeToTypeTerm x
| `(newFactsCA| $x:namedType , i $y) => do
    let xT ← namedTypeToTypeTerm x
    let yT ← namedTypeToTypeTerm y
    `($xT ∧ $yT)
| `(newFactsCA| $x:namedType, $y:namedType , i $z) => do
    let xT ← namedTypeToTypeTerm x
    let yT ← namedTypeToTypeTerm y
    let zT ← namedTypeToTypeTerm z
    `($xT ∧ $yT ∧ $zT)
| _ => throwError "No s'han pogut convertir les descripcions dels nous fets a un terme."

open Tactic Lean.Elab.Tactic.RCases in
def newFactsCAToRCasesPatt : TSyntax `newFactsCA → RCasesPatt
| `(newFactsCA| $x:namedType) => namedTypeListToRCasesPatt [x]
| `(newFactsCA| $x:namedType , i $y:namedType) => namedTypeListToRCasesPatt [x, y]
| `(newFactsCA|  $x:namedType, $y:namedType , i $z:namedType) => namedTypeListToRCasesPatt [x, y, z]
| _ => default

declare_syntax_cat newObjectCA
syntax maybeTypedIdent "tal que" maybeTypedIdent : newObjectCA
syntax maybeTypedIdent "tal que" maybeTypedIdent colGt " , i " maybeTypedIdent : newObjectCA

def newObjectCAToTerm : TSyntax `newObjectCA → MetaM Term
| `(newObjectCA| $x:maybeTypedIdent tal que $new) => do
    let x' ← maybeTypedIdentToExplicitBinder x
    -- TODO Better error handling
    let newT := (toMaybeTypedIdent new).2.get!
    `(∃ $(.mk x'), $newT)
| `(newObjectCA| $x:maybeTypedIdent tal que $new₁ , i $new₂) => do
    let x' ← maybeTypedIdentToExplicitBinder x
    let new₁T := (toMaybeTypedIdent new₁).2.get!
    let new₂T := (toMaybeTypedIdent new₂).2.get!
    `(∃ $(.mk x'), $new₁T ∧ $new₂T)
| _ => throwError "No s'ha pogut convertir la descripció del nou objecte a un terme."

-- TODO: create helper functions for the values below
open Tactic Lean.Elab.Tactic.RCases in
def newObjectCAToRCasesPatt : TSyntax `newObjectCA → RCasesPatt
| `(newObjectCA| $x:maybeTypedIdent tal que $new) => maybeTypedIdentListToRCasesPatt [x, new]
| `(newObjectCA| $x:maybeTypedIdent tal que $new₁ , i $new₂) => maybeTypedIdentListToRCasesPatt [x, new₁, new₂]
| _ => default

declare_syntax_cat factsCA
syntax term : factsCA
syntax term " , i " term : factsCA
syntax term ", " term " , i " term : factsCA

def factsCAToArray : TSyntax `factsCA → Array Term
| `(factsCA| $x:term) => #[x]
| `(factsCA| $x:term , i $y:term) => #[x, y]
| `(factsCA| $x:term, $y:term , i $z:term) => #[x, y, z]
| _ => #[]

def arrayToFacts : Array Term → CoreM (TSyntax `factsCA)
| #[x] => `(factsCA| $x:term)
| #[x, y] => `(factsCA| $x:term , i $y:term)
| #[x, y, z] => `(factsCA| $x:term, $y:term , i $z:term)
| _ => default

end Verbose.Catalan

/-- Convert an expression to a `maybeAppliedCA` syntax object, in `MetaM`. -/
def Lean.Expr.toMaybeAppliedCA (e : Expr) : MetaM (TSyntax `maybeAppliedCA) := do
  let fn := e.getAppFn
  let fnS ← PrettyPrinter.delab fn
  match e.getAppArgs.toList with
  | [] => `(maybeAppliedCA|$fnS:term)
  | [x] => do
      let xS ← PrettyPrinter.delab x
      `(maybeAppliedCA|$fnS:term aplicat a $xS:term)
  | s => do
      let mut arr : Syntax.TSepArray `term "," := ∅
      for x in s do
        arr := arr.push (← PrettyPrinter.delab x)
      `(maybeAppliedCA|$fnS:term aplicat a [$arr:term,*])

implement_endpoint (lang := ca) nameAlreadyUsed (n : Name) : CoreM String :=
pure s!"El nom {n} ja està agafat"

implement_endpoint (lang := ca) notDefEq (e val : MessageData) : CoreM MessageData :=
pure m!"El terme donat{e}\nno és definicionalment igual a l'esperat{val}"

implement_endpoint (lang := ca) notAppConst : CoreM String :=
pure "No és l'aplicació d'una definició."

implement_endpoint (lang := ca) cannotExpand : CoreM String :=
pure "No es pot expandir."

implement_endpoint (lang := ca) doesntFollow (tgt : MessageData) : CoreM MessageData :=
pure m!"La següent conclusió no es segueix immediatament de com a molt una hipòtesi local: {tgt}"
