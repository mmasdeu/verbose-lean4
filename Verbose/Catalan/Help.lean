import Verbose.Tactics.Help
import Verbose.Tactics.Notations
import Verbose.Catalan.Tactics

open Lean Meta Elab Tactic Term Verbose

namespace Verbose.Catalan

open Lean.Parser.Tactic in
elab "ajuda" h:(colGt ident)? : tactic => do
unless (← verboseConfigurationExt.get).useHelpTactic do
  throwError "La tàctica ajuda no està habilitada."
match h with
| some h => do
    let (s, msg) ← gatherSuggestions (helpAtHyp (← getMainGoal) h.getId)
    if s.isEmpty then
      logInfo (msg.getD "Cap suggeriment")
    else
      Lean.Meta.Tactic.TryThis.addSuggestions (← getRef) s (header := "Ajuda")
| none => do
    let (s, msg) ← gatherSuggestions (helpAtGoal (← getMainGoal))
    if s.isEmpty then
      logInfo (msg.getD "Cap suggeriment")
    else
      Lean.Meta.Tactic.TryThis.addSuggestions (← getRef) s (header := "Ajuda")

def describe (t : Format) : String :=
match toString t with
| "ℝ" => "un nombre real"
| "ℕ" => "un nombre natural"
| "ℤ" => "un enter"
| t => "una expressió amb tipus " ++ t

def describe_pl (t : Format) : String :=
match toString t with
| "ℝ" => "uns quants nombres reals"
| "ℕ" => "uns quants nombres naturals"
| "ℤ" => "uns quants enters"
| t => "unes quantes expressions amb tipus " ++ t

def libre (s : Ident) : String := s!"El nom {s.getId} es podt escollir lliurement entre els disponibles."

def printIdentList (l : List Ident) : String := commaSep <| l.toArray.map (toString ·.getId)

def libres (ls : List Ident) : String :=
s!"Els noms {printIdentList ls} es poden escollir lliurement entre els disponibles."

def describeHypShape (hyp : Name) (headDescr : String) : SuggestionM Unit :=
  pushCom "La hipòtesi {hyp} té forma “{headDescr}”"

def describeHypStart (hyp : Name) (headDescr : String) : SuggestionM Unit :=
  pushCom "La hipòtesi {hyp} comença amb “{headDescr}”"


implement_endpoint (lang := ca) helpExistRelSuggestion (hyp : Name) (headDescr : String)
    (nameS ineqIdent hS : Ident) (ineqS pS : Term) : SuggestionM Unit := do
  describeHypShape hyp headDescr
  pushCom "Es pot utilitzar fent:"
  pushTac `(tactic|Per $hyp.ident:term obtenim $nameS:ident tal que ($ineqIdent : $ineqS) and ($hS : $pS))
  pushComment <| libres [nameS, ineqIdent, hS]

implement_endpoint (lang := ca) helpConjunctionSuggestion (hyp : Name) (h₁I h₂I : Ident) (p₁S p₂S : Term) :
    SuggestionM Unit := do
  let headDescr := "... and ..."
  describeHypShape hyp headDescr
  pushCom "Es pot utilitzar fent:"
  pushTac `(tactic|Per $hyp.ident:term obtenim ($h₁I : $p₁S) ($h₂I : $p₂S))
  pushComment <| libres [h₁I, h₂I]

implement_endpoint (lang := ca) helpDisjunctionSuggestion (hyp : Name) : SuggestionM Unit := do
  pushCom "La hipòtesi {hyp} té la forma « ... o ... »"
  pushCom "Es pot utilitzar fent:"
  pushTac `(tactic|Separem $hyp.ident:term en casos)

implement_endpoint (lang := ca) helpImplicationSuggestion (hyp HN H'N : Name) (closes : Bool)
    (le re : Expr) : SuggestionM Unit := do
  pushCom "La hipòtesi {hyp} és una implicació"
  if closes then do
    pushCom "La conclusió d'aquesta implicació és l'objectiu actual"
    pushCom "Per tant podem utilitzar-la fent:"
    pushTac `(tactic| Per $hyp.ident:term només cal demostrar $(← le.stx))
    flush
    pushCom "Si ja tenim una demostració {HN} de {← le.fmt} aleshores podem fer:"
    pushTac `(tactic|Concloem amb $hyp.ident:term aplicat a $HN.ident)
  else do
    pushCom "La premisa d'aquesta implicació és {← le.fmt}"
    pushCom "Si ja tenim una demostració {HN} de {← le.fmt}"
    pushCom "aleshores podem fer servir la hipòtesi amb:"
    pushTac `(tactic|Per $hyp.ident:term aplicat a $HN.ident:term obtenim $H'N.ident:ident : $(← re.stx):term)
    pushComment <| libre H'N.ident

implement_endpoint (lang := ca) helpEquivalenceSuggestion (hyp hyp'N : Name) (l r : Expr) : SuggestionM Unit := do
  pushCom "La hipòtesi {hyp} és una equivalència"
  pushCom "La podem utilitzar substituint el terme esquerre (que és {← l.fmt}) pel dret ({← r.fmt}) a l'objectiu, fent:"
  pushTac `(tactic|Reescrivim utilitzant $hyp.ident:term)
  flush
  pushCom "La podem utilitzar per substituir el terme dret a l'objectiu, fent:"
  pushTac `(tactic|Reescrivim utilitzant ← $hyp.ident)
  flush
  pushCom "També podem fer aquestes substitucions en una hipòtesi {hyp'N} fent:"
  pushTac `(tactic|Reescrivim utilitzant $hyp.ident:term at $hyp'N.ident:ident)
  flush
  pushCom "o"
  pushTac `(tactic|Reescrivim utilitzant ← $hyp.ident:term at $hyp'N.ident:ident)

implement_endpoint (lang := ca) helpEqualSuggestion (hyp hyp' : Name) (closes : Bool) (l r : Expr) :
    SuggestionM Unit := do
  pushCom "La hipòtesi {hyp} és una igualtat"
  if closes then
    pushComment <| s!"L'objectiu actual en segueix immediatament"
    pushComment   "Es pot utilitzar fent:"
    pushTac `(tactic|Concloem amb $hyp.ident:ident)
  else do
    pushCom "La podem utilitzar substituint el terme esquerre (que és {← l.fmt}) pel dret ({← r.fmt}) a l'objectiu, fent:"
    pushTac `(tactic|Reescrivim utilitzant $hyp.ident:ident)
    flush
    pushCom "La podem utilitzar per substituir el terme dret a l'objectiu, fent:"
    pushTac `(tactic|Reescrivim utilitzant ← $hyp.ident:ident)
    flush
    pushCom "També podem fer aquestes substitucions en una hipòtesi {hyp'} fent:"
    pushTac `(tactic|Reescrivim utilitzant $hyp.ident:ident at $hyp'.ident:ident)
    flush
    pushCom "o"
    pushTac `(tactic|Reescrivim utilitzant ← $hyp.ident:ident at $hyp'.ident:ident)
    flush
    pushCom "També es pot utilitzar en un pas d'un càlcul, o combinar-la linealment amb altres hipòtesis amb:"
    pushTac `(tactic|Combinem [$hyp.ident:term, ?_])
    pushCom "canviant l'interrogant amb un o més termes que demostrin igualtats."

implement_endpoint (lang := ca) helpIneqSuggestion (hyp : Name) (closes : Bool) : SuggestionM Unit := do
  pushCom "La hipòtesi {hyp} és una desigualtat"
  if closes then
    flush
    pushCom "L'objectiu actual en segueix immediatament."
    pushCom "Es pot utilitzar fent:"
    pushTac `(tactic|Concloem amb $hyp.ident:ident)
  else do
    flush
    pushCom "També es pot utilitzar en un pas d'un càlcul, o combinar-la linealment amb altres hipòtesis amb:"
    pushTac `(tactic|Combinem [$hyp.ident:term, ?_])
    pushCom "canviant l'interrogant amb un o més termes que demostrin igualtats o desigualtats."

implement_endpoint (lang := ca) helpMemInterSuggestion (hyp h₁ h₂ : Name) (elemS p₁S p₂S : Term) :
    SuggestionM Unit := do
  pushCom "La hipòtesi {hyp} demostra la pertanyença a una intersecció"
  pushCom "Es pot utilitzar fent:"
  pushTac `(tactic|Per $hyp.ident:term obtenim ($h₁.ident : $elemS ∈ $p₁S) ($h₂.ident : $elemS ∈ $p₂S))
  pushComment <| libres [h₁.ident, h₂.ident]

implement_endpoint (lang := ca) helpMemUnionSuggestion (hyp : Name) :
    SuggestionM Unit := do
  pushCom "La hipòtesi {hyp} demostra la pertanyença a una unió"
  pushCom "Es pot utilitzar fent:"
  pushTac `(tactic|Separem $hyp.ident en casos)

implement_endpoint (lang := ca) helpGenericMemSuggestion (hyp : Name) : SuggestionM Unit := do
  pushCom "La hipòtesi {hyp} és una pertanyença"

implement_endpoint (lang := ca) helpContradictiomSuggestion (hypId : Ident) : SuggestionM Unit := do
  pushComment <| "Aquesta hipòtesi és una contradicció."
  pushCom "Podem deduir-ne el que en vulguem:"
  pushTac `(tactic|(Demostrem una contradicció
                    Concloem amb $hypId:ident))

implement_endpoint (lang := ca) helpSubsetSuggestion (hyp x hx hx' : Name)
    (r : Expr) (l ambientTypePP : Format) : SuggestionM Unit := do
  pushCom "La hipòtesi {hyp} demostra la inclusió de {l} dins de {← r.fmt}."
  pushCom "Es pot utilitzar fent:"
  pushTac `(tactic| Per $hyp.ident:ident aplicat a $x.ident utilitzant $hx.ident obtenim $hx'.ident:ident : $x.ident ∈ $(← r.stx))
  pushCom "on {x} és {describe ambientTypePP} and {hx} demostra que {x} ∈ {l}"
  pushComment <| libre hx'.ident

implement_endpoint (lang := ca) assumptionClosesSuggestion (hypId : Ident) : SuggestionM Unit := do
  pushCom "Aquesta hipòtesi és igual al que cal demostrar"
  pushCom "Es pot utilitzar fent:"
  pushTac `(tactic|Concloem amb $hypId:ident)

implement_endpoint (lang := ca) assumptionUnfoldingSuggestion (hypId : Ident) (expandedHypTypeS : Term) :
    SuggestionM Unit := do
  pushCom "Aquesta hipòtesi comença amb l'aplicació d'una definició."
  pushCom "La podem fer explícita amb:"
  pushTac `(tactic|Reformulem $hypId:ident com $expandedHypTypeS)
  flush

implement_endpoint (lang := ca) helpForAllRelExistsRelSuggestion (hyp var_name' n₀ hn₀ : Name)
    (headDescr hypDescr : String) (t : Format) (hn'S ineqIdent : Ident) (ineqS p'S : Term) :
    SuggestionM Unit := do
  describeHypStart hyp headDescr
  pushCom "Es pot utilitzar fent:"
  pushTac `(tactic|Per $hyp.ident:term aplicat a $n₀.ident utilitzant $hn₀.ident obtenim $var_name'.ident:ident tal que ($ineqIdent : $ineqS) and ($hn'S : $p'S))
  pushCom "a on {n₀} és {describe t} and {hn₀} és una demostració del fet que {hypDescr}."
  pushComment <| libres [var_name'.ident, ineqIdent, hn'S]

implement_endpoint (lang := ca) helpForAllRelExistsSimpleSuggestion (hyp n' hn' n₀ hn₀ : Name)
    (headDescr n₀rel : String) (t : Format) (p'S : Term) : SuggestionM Unit := do
  describeHypStart hyp headDescr
  pushCom "Es pot utilitzar fent:"
  pushTac `(tactic|Per $hyp.ident:term aplicat a $n₀.ident utilitzant $hn₀.ident obtenim $n'.ident:ident tal que ($hn'.ident : $p'S))
  pushCom "a on {n₀} és {describe t} and {hn₀} és una demostració del fet que {n₀rel}"
  pushComment <| libres [n'.ident, hn'.ident]

implement_endpoint (lang := ca) helpForAllRelGenericSuggestion (hyp n₀ hn₀ : Name)
    (headDescr n₀rel : String) (t : Format) (newsI : Ident) (pS : Term) : SuggestionM Unit := do
  describeHypStart hyp headDescr
  pushCom "Es pot utilitzar fent:"
  pushTac `(tactic|Per $hyp.ident:term aplicat a $n₀.ident utilitzant $hn₀.ident obtenim ($newsI : $pS))
  pushCom "a on {n₀} és {describe t} and {hn₀} és una demostració del fet que {n₀rel}"
  pushComment <| libre newsI

implement_endpoint (lang := ca) helpForAllSimpleExistsRelSuggestion (hyp var_name' nn₀ : Name)
    (headDescr : String) (t : Format) (hn'S ineqIdent : Ident) (ineqS p'S : Term) :
    SuggestionM Unit := do
  describeHypStart hyp headDescr
  pushCom "Es pot utilitzar fent:"
  pushTac `(tactic|Per $hyp.ident:term aplicat a $nn₀.ident obtenim $var_name'.ident:ident tal que ($ineqIdent : $ineqS) and ($hn'S : $p'S))
  pushCom "a on {nn₀} és {describe t}"
  pushComment <| libres [var_name'.ident, ineqIdent, hn'S]

implement_endpoint (lang := ca) helpForAllSimpleExistsSimpleSuggestion (hyp var_name' hn' nn₀  : Name)
    (headDescr : String) (t : Format) (p'S : Term) : SuggestionM Unit := do
  describeHypStart hyp headDescr
  pushCom "Es pot utilitzar fent:"
  pushTac `(tactic|Per $hyp.ident:term aplicat a $nn₀.ident obtenim $var_name'.ident:ident tal que ($hn'.ident : $p'S))
  pushCom "a on {nn₀} és {describe t}"
  pushComment <| libres [var_name'.ident, hn'.ident]

implement_endpoint (lang := ca) helpForAllSimpleForAllRelSuggestion (hyp nn₀ var_name'₀ H h : Name)
    (headDescr rel₀ : String) (t : Format) (p'S : Term) : SuggestionM Unit := do
  pushCom "La hipòtesi {hyp} comença amb “{headDescr}"
  pushCom "Es pot utilitzar fent:"
  pushTac `(tactic|Per $hyp.ident:term aplicat a [$nn₀.ident, $var_name'₀.ident, $H.ident] obtenim ($h.ident : $p'S))
  pushCom "a on {nn₀} and {var_name'₀} són {describe_pl t} and {H} és una demostració de {rel₀}"
  pushComment <| libre h.ident

implement_endpoint (lang := ca) helpForAllSimpleGenericSuggestion (hyp nn₀ hn₀ : Name) (headDescr : String)
    (t : Format) (pS : Term) : SuggestionM Unit := do
  describeHypStart hyp headDescr
  pushCom "Es pot utilitzar fent:"
  pushTac `(tactic|Per $hyp.ident:term aplicat a $nn₀.ident obtenim ($hn₀.ident : $pS))
  pushCom "a on {nn₀} és {describe t}"
  pushComment <| libre hn₀.ident
  flush
  pushCom "Si aquesta hipòtesi no s'ha de fer servir més en la seva forma general, també podem especialitzar {hyp} fent"
  pushTac `(tactic|Especialitzem $hyp.ident:ident en $nn₀.ident)

implement_endpoint (lang := ca) helpForAllSimpleGenericApplySuggestion (prf : Expr) (obj : Format) :
    SuggestionM Unit := do
  let prfS ← prf.toMaybeAppliedCA
  pushCom "Com que l'objectiu {obj}, podem fer:"
  pushTac `(tactic|Concloem amb $prfS)

implement_endpoint (lang := ca) helpExistsSimpleSuggestion (hyp n hn : Name) (headDescr : String)
    (pS : Term) : SuggestionM Unit := do
  describeHypShape hyp headDescr
  pushCom "Es pot utilitzar fent:"
  pushTac `(tactic|Per $hyp.ident:term obtenim $n.ident:ident tal que ($hn.ident : $pS))
  pushComment <| libres [n.ident, hn.ident]

implement_endpoint (lang := ca) helpDataSuggestion (hyp : Name) (t : Format) : SuggestionM Unit := do
  pushComment <| s!"L'objecte {hyp}" ++ match t with
    | "ℝ" => " és un nombre real fixat."
    | "ℕ" => " és un nombre natural fixat."
    | "ℤ" => " és un enter fixat."
    | s => s!" : {s} està fixat."

implement_endpoint (lang := ca) helpNothingSuggestion : SuggestionM Unit := do
  pushCom "No sé com ajudar amb aquesta hipòtesi."
  flush

implement_endpoint (lang := ca) helpNothingGoalSuggestion : SuggestionM Unit := do
  pushCom "No sé com ajudar amb aquest objectiu."
  flush

def descrGoalHead (headDescr : String) : SuggestionM Unit :=
 pushCom "L'objectiu comença amb “{headDescr}”"

def descrGoalShape (headDescr : String) : SuggestionM Unit :=
 pushCom "L'objectiu té la forma “{headDescr}”"

def descrDirectProof : SuggestionM Unit :=
 pushCom "Per tant una demostració directa comença amb:"

implement_endpoint (lang := ca) helpUnfoldableGoalSuggestion (expandedGoalTypeS : Term) :
    SuggestionM Unit := do
  pushCom "L'objectiu comença amb l'aplicació d'una definició."
  pushCom "La podem fer explícita amb:"
  pushTac `(tactic|Demostrem que $expandedGoalTypeS)
  flush

implement_endpoint (lang := ca) helpAnnounceGoalSuggestion (actualGoalS : Term) : SuggestionM Unit := do
  pushCom "El següent pas consisteix a enunciar:"
  pushTac `(tactic| Demostrem ara que $actualGoalS)

implement_endpoint (lang := ca) helpFixSuggestion (headDescr : String) (ineqS : TSyntax `fixDecl) :
    SuggestionM Unit := do
  descrGoalHead headDescr
  descrDirectProof
  pushTac `(tactic|Sigui $ineqS)

implement_endpoint (lang := ca) helpExistsRelGoalSuggestion (headDescr : String) (n₀ : Name) (t : Format)
    (fullTgtS : Term) : SuggestionM Unit := do
  descrGoalHead headDescr
  descrDirectProof
  pushTac `(tactic|Demostrem que $n₀.ident funciona : $fullTgtS)
  pushCom "substituïnt {n₀} per {describe t}"

implement_endpoint (lang := ca) helpExistsGoalSuggestion (headDescr : String) (nn₀ : Name) (t : Format)
    (tgt : Term) : SuggestionM Unit := do
  descrGoalHead headDescr
  descrDirectProof
  pushTac `(tactic|Demostrem que $nn₀.ident funciona : $tgt)
  pushCom "substituïnt {nn₀} per {describe t}"

implement_endpoint (lang := ca) helpConjunctionGoalSuggestion (p p' : Term) : SuggestionM Unit := do
  descrGoalShape "... and ..."
  descrDirectProof
  pushTac `(tactic|Demostrem primer que $p)
  pushCom "Quan acabem aquesta primera demostració, caldrà demostrar encara que {← p'.fmt}"
  flush
  pushCom "També podem començar amb"
  pushTac `(tactic|Demostrem primer que $p')
  pushCom "i llavors, després d'acabar amb aquesta primera demostració, caldrà demostrar que {← p.fmt}"

implement_endpoint (lang := ca) helpDisjunctionGoalSuggestion (p p' : Term) : SuggestionM Unit := do
  descrGoalShape "... o ..."
  pushCom "Per tant una demostració directe comença per enunciar quina alternativa ens disposem a demostrar:"
  pushTac `(tactic|Demostrem que $p)
  flush
  pushCom "o bé:"
  pushTac `(tactic|Demostrem que $p')

implement_endpoint (lang := ca) helpImplicationGoalSuggestion (headDescr : String) (Hyp : Name)
    (leStx : Term) : SuggestionM Unit := do
  descrGoalHead headDescr
  descrDirectProof
  pushTac `(tactic| Suposem $Hyp.ident:ident : $leStx)
  pushComment <| libre Hyp.ident

implement_endpoint (lang := ca) helpEquivalenceGoalSuggestion (r l : Format) (rS lS : Term) :
    SuggestionM Unit := do
  pushCom "L'objectiu és una equivalència. Podem enunciar la demostració de la implicació '→' amb:"
  pushTac `(tactic|Demostrem que $lS → $rS)
  pushCom "Un cop demostrada aquesta implicació, caldrà encara demostrar {r} → {l}"
  flush
  pushCom "També podem començar amb"
  pushTac `(tactic|Demostrem que $rS → $lS)
  pushCom "i llavors, després d'acabar aquesta primera demostració, caldrà demostrar que {l} → {r}"

implement_endpoint (lang := ca) helpSetEqSuggestion (l r : Format) (lS rS : Term) : SuggestionM Unit := do
  -- **FIXME** this discussion isn't easy to do utilitzant tactics.
  pushCom "L'objectiu és una igualtat de conjunts"
  pushCom "La podem demostrar amb reescriptura, fent: `Reescrivim utilitzant`"
  pushCom "o començar un càlcul amb"
  pushCom "  calc {l} = sorry := per sorry"
  pushCom "  _ = {r} := per sorry"
  pushCom "També es pot demostrar per doble inclusió."
  pushCom "En aquest cas, la demostració començaria amb:"
  pushTac `(tactic|Demostrem primer que $lS ⊆ $rS)

implement_endpoint (lang := ca) helpEqGoalSuggestion (l r : Format) : SuggestionM Unit := do
  -- **FIXME** this discussion isn't easy to do utilitzant tactics.
  pushCom "L'objectiu és una igualtat"
  pushCom "Es pot demostrar amb reescriptura, fent `Reescrivim utilitzant`"
  pushCom "o començar un càlcul amb"
  pushCom "  calc {l} = sorry := per sorry"
  pushCom "  _ = {r} := per sorry"
  pushCom "Òbviament, podem posar tants passos intermitjos com vulguem."
  pushCom "També podem fer combinacions lineals d'hipòtesis hyp₁ hyp₂... amb"
  pushCom "  Combinem [hyp₁, hyp₂]"

implement_endpoint (lang := ca) helpIneqGoalSuggestion (l r : Format) (rel : String) : SuggestionM Unit := do
  -- **FIXME** this discussion isn't easy to do utilitzant tactics.
  pushCom "L'objectiu és una desigualtat"
  pushCom "Es pot començar un càlcul amb"
  pushCom "  calc {l}{rel}sorry := per sorry "
  pushCom "  _ = {r} := per sorry "
  pushCom "Òbviament, podem posar tants passos intermitjos com vulguem."
  pushCom "L'última línia no cal que sigui una igualtat, també pot ser una desigualtat."
  pushCom "De manera similar, la primera línia podria ser una igualtat. En total, els símbols relacionals"
  pushCom "s'han de poder encadenar per donar lloc a {rel}."
  pushCom "També podem fer combinacions lineals d'hipòtesis hyp₁ hyp₂... amb"
  pushCom "  Combinem [hyp₁, hyp₂]"

implement_endpoint (lang := ca) helpMemInterGoalSuggestion (elem le : Expr) : SuggestionM Unit := do
  pushCom "L'objectiu és demostrar que {← elem.fmt} pertany a la intersecció de {← le.fmt} amb un altre conjunt."
  pushCom "Per tant una demostració directa comença amb:"
  pushTac `(tactic|Demostrem primer que $(← elem.stx) ∈ $(← le.stx))

implement_endpoint (lang := ca) helpMemUnionGoalSuggestion (elem le re : Expr) : SuggestionM Unit := do
  pushCom "L'objectiu és demostrar que {← elem.fmt} pertany a la unió de {← le.fmt} and {← re.fmt}."
  descrDirectProof
  pushTac `(tactic|Demostrem que $(← elem.stx) ∈ $(← le.stx))
  flush
  pushCom "o per:"
  pushTac `(tactic|Demostrem que $(← elem.stx) ∈ $(← re.stx))

implement_endpoint (lang := ca) helpNoIdeaGoalSuggestion : SuggestionM Unit := do
  pushCom "Ni idea."

implement_endpoint (lang := ca) helpSubsetGoalSuggestion (l r : Format) (xN : Name) (lT : Term) :
    SuggestionM Unit := do
  pushCom "L'objectiu és demostrar la inclusió {l} ⊆ {r}"
  descrDirectProof
  pushTac `(tactic| Sigui $xN.ident:ident ∈ $lT)
  pushComment <| libre xN.ident

implement_endpoint (lang := ca) helpFalseGoalSuggestion : SuggestionM Unit := do
  pushCom "L'objectiu és demostrar una contradicció."
  pushCom "Podem aplicar una hipòtesi que sigui una negació"
  pushCom "és a dir, per definició, que tingui la forma P → false."

implement_endpoint (lang := ca) helpContraposeGoalSuggestion : SuggestionM Unit := do
  pushCom "L'objectiu és una implicació."
  pushCom "Podem començar una demostració per contraposició amb:"
  pushTac `(tactic| Contraposem)

implement_endpoint (lang := ca) helpByContradictionSuggestion (hyp : Ident) (assum : Term) : SuggestionM Unit := do
  pushCom "Podem començar una demostració per reducció a l'absurd amb:"
  pushTac `(tactic| Suposem per arribar a contradicció que $hyp:ident : $assum)

implement_endpoint (lang := ca) helpNegationSuggestion (hyp : Ident) (assum : Term) : SuggestionM Unit := do
  pushCom "L'objectiu és una negació."
  pushCom "Podem començar una demostració \"per reducció a l'absurd\" amb:"
  pushTac `(tactic| Suposem $hyp:ident : $assum)

set_option linter.unusedVariables false

configureAnonymousGoalSplittingLemmas Iff.intro Iff.intro' And.intro And.intro' abs_le_of_le_le abs_le_of_le_le'

configureHelpProviders DefaultHypHelp DefaultGoalHelp

setLang ca


/--
info: Ajuda
• Per h aplicat a n₀ utilitzant hn₀ obtenim (hyp : P n₀)
-/
#guard_msgs in
example {P : ℕ → Prop} (h : ∀ n > 0, P n) : P 2 := by
  ajuda h
  apply h
  norm_num

/--
info: Ajuda
• Per h obtenim n tal que (n_pos : n > 0) and (hn : P n)
-/
#guard_msgs in
example {P : ℕ → Prop} (h : ∃ n > 0, P n) : True := by
  ajuda h
  trivial

/--
info: Ajuda
• Per h obtenim ε tal que (ε_pos : ε > 0) and (hε : P ε)
-/
#guard_msgs in
example {P : ℝ → Prop} (h : ∃ ε > 0, P ε) : True := by
  ajuda h
  trivial

/--
info: Ajuda
• Per h aplicat a n₀ obtenim (hn₀ : P n₀ ⇒ Q n₀)
• Especialitzem h en n₀
-/
#guard_msgs in
example (P Q : ℕ → Prop) (h : ∀ n, P n → Q n) (h' : P 2) : Q 2 := by
  ajuda h
  exact h 2 h'

/--
info: Ajuda
• Per h aplicat a n₀ obtenim (hn₀ : P n₀)
• Especialitzem h en n₀
• Concloem amb h aplicat a 2
-/
#guard_msgs in
example (P : ℕ → Prop) (h : ∀ n, P n) : P 2 := by
  ajuda h
  exact h 2

/--
info: Ajuda
• Per h només cal demostrar P 1
• Concloem amb h aplicat a H
-/
#guard_msgs in
example (P Q : ℕ → Prop) (h : P 1 → Q 2) (h' : P 1) : Q 2 := by
  ajuda h
  exact h h'

/--
info: Ajuda
• Per h aplicat a H obtenim H' : Q 2
-/
#guard_msgs in
example (P Q : ℕ → Prop) (h : P 1 → Q 2) : True := by
  ajuda h
  trivial

/--
info: Ajuda
• Per h obtenim (h_1 : P 1) (h' : Q 2)
-/
#guard_msgs in
example (P Q : ℕ → Prop) (h : P 1 ∧ Q 2) : True := by
  ajuda h
  trivial

/--
info: Ajuda
• Reescrivim utilitzant h
• Reescrivim utilitzant ← h
• Reescrivim utilitzant h at hyp
• Reescrivim utilitzant ← h at hyp
-/
#guard_msgs in
example (P Q : ℕ → Prop) (h : (∀ n ≥ 2, P n) ↔  ∀ l, Q l) : True := by
  ajuda h
  trivial

/--
info: Ajuda
• Demostrem primer que True
• Demostrem primer que 1 = 1
-/
#guard_msgs in
example : True ∧ 1 = 1 := by
  ajuda
  exact ⟨trivial, rfl⟩

/--
info: Ajuda
• Separem h en casos
-/
#guard_msgs in
example (P Q : ℕ → Prop) (h : P 1 ∨ Q 2) : True := by
  ajuda h
  trivial

/--
info: Ajuda
• Demostrem que True
• Demostrem que False
-/
#guard_msgs in
example : True ∨ False := by
  ajuda
  left
  trivial

/-- info: No sé com ajudar amb aquesta hipòtesi. -/
#guard_msgs in
example (P : Prop) (h : P) : True := by
  ajuda h
  trivial

/--
info: Ajuda
• (
  Demostrem una contradicció
  Concloem amb h)
-/
#guard_msgs in
example (h : False) : 0 = 1 := by
  ajuda h
  trivial

/--
info: Ajuda
• Per h aplicat a H obtenim H' : P l k
-/
#guard_msgs in
example (P : ℕ → ℕ → Prop) (k l n : ℕ) (h : l - n = 0 → P l k) : True := by
  ajuda h
  trivial

/--
info: Ajuda
• Per h aplicat a k₀ utilitzant hk₀ obtenim n tal que (n_sup : n ≥ 3) and (hn : ∀ (l : ℕ), l - n = 0 ⇒ P l k₀)
-/
#guard_msgs in
example (P : ℕ → ℕ → Prop) (h : ∀ k ≥ 2, ∃ n ≥ 3, ∀ l, l - n = 0 → P l k) : True := by
  ajuda h
  trivial

/--
info: Ajuda
• Per h aplicat a [k₀, n₀, H] obtenim (h_1 : ∀ (l : ℕ), l - n₀ = 0 ⇒ P l k₀)
-/
#guard_msgs in
example (P : ℕ → ℕ → Prop) (h : ∀ k, ∀ n ≥ 3, ∀ l, l - n = 0 → P l k) : True := by
  ajuda h
  trivial

/--
info: Ajuda
• Per h aplicat a k₀ utilitzant hk₀ obtenim n_1 tal que (n_1_sup : n_1 ≥ 3) and (hn_1 : ∀ (l : ℕ), l - n = 0 ⇒ P l k₀)
-/
#guard_msgs in
example (P : ℕ → ℕ → Prop) (n : ℕ) (h : ∀ k ≥ 2, ∃ n ≥ 3, ∀ l, l - n = 0 → P l k) : True := by
  ajuda h
  trivial

/--
info: Ajuda
• Per h obtenim n tal que (n_sup : n ≥ 5) and (hn : P n)
-/
#guard_msgs in
example (P : ℕ → Prop) (h : ∃ n ≥ 5, P n) : True := by
  ajuda h
  trivial

/--
info: Ajuda
• Per h aplicat a k₀ utilitzant hk₀ obtenim n tal que (n_sup : n ≥ 3) and (hn : P n k₀)
-/
#guard_msgs in
example (P : ℕ → ℕ → Prop) (h : ∀ k ≥ 2, ∃ n ≥ 3, P n k) : True := by
  ajuda h
  trivial

/--
info: Ajuda
• Per h obtenim n tal que (hn : P n)
-/
#guard_msgs in
example (P : ℕ → Prop) (h : ∃ n : ℕ, P n) : True := by
  ajuda h
  trivial

/--
info: Ajuda
• Per h aplicat a k₀ obtenim n tal que (hn : P n k₀)
-/
#guard_msgs in
example (P : ℕ → ℕ → Prop) (h : ∀ k, ∃ n : ℕ, P n k) : True := by
  ajuda h
  trivial

/--
info: Ajuda
• Per h aplicat a k₀ utilitzant hk₀ obtenim n tal que (hn : P n k₀)
-/
#guard_msgs in
example (P : ℕ → ℕ → Prop) (h : ∀ k ≥ 2, ∃ n : ℕ, P n k) : True := by
  ajuda h
  trivial

/--
info: Ajuda
• Demostrem que n₀ funciona: P n₀ ⇒ True
-/
#guard_msgs in
example (P : ℕ → Prop): ∃ n : ℕ, P n → True := by
  ajuda
  use 0
  tauto

/--
info: Ajuda
• Suposem hyp : P
-/
#guard_msgs in
example (P Q : Prop) (h : Q) : P → Q := by
  ajuda
  exact fun _ ↦ h

/--
info: Ajuda
• Sigui n ≥ 0
-/
#guard_msgs in
example : ∀ n ≥ 0, True := by
  ajuda
  intros
  trivial

/--
info: Ajuda
• Sigui n : ℕ
-/
#guard_msgs in
example : ∀ n : ℕ, 0 ≤ n := by
  ajuda
  exact Nat.zero_le

/--
info: Ajuda
• Demostrem que n₀ funciona: 0 ≤ n₀
-/
#guard_msgs in
example : ∃ n : ℕ, 0 ≤ n := by
  ajuda
  use 1
  exact Nat.zero_le 1

/--
info: Ajuda
• Demostrem que n₀ funciona: n₀ ≥ 1 ∧ True
-/
#guard_msgs in
example : ∃ n ≥ 1, True := by
  ajuda
  use 1

/-- info: No sé com ajudar amb aquesta hipòtesi. -/
#guard_msgs in
example (h : Odd 3) : True := by
  ajuda h
  trivial

/--
info: Ajuda
• Sigui x ∈ s
---
info: Ajuda
• Per h aplicat a x_1 utilitzant hx obtenim hx' : x_1 ∈ t
-/
#guard_msgs in
example (s t : Set ℕ) (h : s ⊆ t) : s ⊆ t := by
  ajuda
  Sigui x ∈ s
  ajuda h
  exact h x_mem

/--
info: Ajuda
• Per h obtenim (h_1 : x ∈ s) (h' : x ∈ t)
-/
#guard_msgs in
example (s t : Set ℕ) (x : ℕ) (h : x ∈ s ∩ t) : x ∈ s := by
  ajuda h
  Per h obtenim (h_1 : x ∈ s) (h' : x ∈ t)
  exact h_1

/--
info: Ajuda
• Per h obtenim (h_1 : x ∈ s) (h' : x ∈ t)
---
info: Ajuda
• Demostrem primer que x ∈ t
---
info: Ajuda
• Demostrem ara que x ∈ s
-/
#guard_msgs in
example (s t : Set ℕ) (x : ℕ) (h : x ∈ s ∩ t) : x ∈ t ∩ s := by
  ajuda h
  Per h obtenim (h_1 : x ∈ s) (h' : x ∈ t)
  ajuda
  Demostrem primer que x ∈ t
  exact h'
  ajuda
  Demostrem ara que x ∈ s
  exact h_1

/--
info: Ajuda
• Separem h en casos
---
info: Ajuda
• Demostrem que x ∈ t
• Demostrem que x ∈ s
-/
#guard_msgs in
example (s t : Set ℕ) (x : ℕ) (h : x ∈ s ∪ t) : x ∈ t ∪ s := by
  ajuda h
  Separem h en casos
  Suposem hyp : x ∈ s
  ajuda
  Demostrem que x ∈ s
  exact hyp
  Suposem hyp : x ∈ t
  Demostrem que x ∈ t
  exact  hyp

/--
info: Ajuda
• Suposem hyp : False
-/
#guard_msgs in
example : False → True := by
  ajuda
  simp

/-- info: No sé com ajudar amb aquest objectiu. -/
#guard_msgs in
example : True := by
  ajuda
  trivial

configureHelpProviders DefaultHypHelp DefaultGoalHelp helpContraposeGoal

/--
info: Ajuda
• Suposem hyp : False
• Contraposem
-/
#guard_msgs in
example : False → True := by
  ajuda
  Contraposem
  simp

/-- info: No sé com ajudar amb aquest objectiu. -/
#guard_msgs in
example : True := by
  ajuda
  trivial

configureHelpProviders DefaultHypHelp DefaultGoalHelp helpByContradictionGoal helpNegationGoal

/--
info: Ajuda
• Suposem per arribar a contradicció que hyp : ¬True
-/
#guard_msgs in
example : True := by
  ajuda
  trivial

/--
info: Ajuda
• Suposem hyp : 2 + 2 = 5
-/
#guard_msgs in
example : ¬ (2+2 = 5) := by
  ajuda
  trivial

