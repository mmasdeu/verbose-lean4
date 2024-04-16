import Verbose.Tactics.We
import Verbose.Catalan.Common

open Lean Elab Parser Tactic Verbose.Catalan

declare_syntax_cat becomesCA
syntax colGt " que esdevé " term : becomesCA

def extractBecomesCA (e : Lean.TSyntax `becomesCA) : Lean.Term := ⟨e.raw[1]!⟩

elab rw:"Reescrivim" " utilitzant " s:myRwRuleSeq l:(location)? new:(becomesCA)? : tactic => do
  rewriteTac rw s (l.map expandLocation) (new.map extractBecomesCA)

elab rw:"Reescrivim" " utilitzant " s:myRwRuleSeq " a tot arreu" : tactic => do
  rewriteTac rw s (some Location.wildcard) none

elab "Separem" exp:term " en casos " : tactic =>
  discussOr exp

elab "Separem" " en casos segons si " exp:term : tactic =>
  discussEm exp

elab "Concloem" " amb " e:maybeAppliedCA : tactic => do
  concludeTac (← maybeAppliedCAToTerm e)

elab "Combinem" " [" prfs:term,* "]" : tactic => do
  combineTac prfs.getElems

elab "Calculem" loc:(location)? : tactic => do
  computeTac loc

elab "Apliquem" exp:term : tactic => do
  evalApply (← `(tactic|apply $exp))

elab "Apliquem" exp:term " at " h:ident: tactic => do
  let loc ← ident_to_location h
  evalTactic (← `(tactic|apply_fun $exp $loc:location))

elab "Especialitzem" exp:term " en " e:term : tactic => do
  evalTactic (← `(tactic|specialize $exp $e))

macro "Oblidem" args:(ppSpace colGt term:max)+ : tactic => `(tactic|clear $args*)

macro "Reformulem" h:ident " com " new:term : tactic => `(tactic|change $new at $h:ident)

elab "Contraposem" : tactic => contraposeTac true

elab "Contraposem" " simplement" : tactic => contraposeTac false

elab "Simplifiquem " " la negació " l:(location)? new:(becomesCA)? : tactic => do
  pushNegTac (l.map expandLocation) (new.map extractBecomesCA)

implement_endpoint (lang := ca) rwResultWithoutGoal : CoreM String :=
pure "Només es pot especificar el resultat d'una reescriptura quan queda alguna cosa per demostrar."

implement_endpoint (lang := ca) rwResultSeveralLoc : CoreM String :=
pure "Només es pot especificar el resultat d'una reescriptura quan es reescriu en un sol lloc."

implement_endpoint (lang := ca) cannotContrapose : CoreM String :=
pure "No es pot contraposar: l'objectiu no és una implicació."

setLang ca

example (P Q : Prop) (h : P ∨ Q) : True := by
  Separem h en casos
  . intro _hP
    trivial
  . intro _hQ
    trivial


example (P : Prop) : True := by
  Separem en casos segons si P
  . intro _hP
    trivial
  . intro _hnP
    trivial

set_option linter.unusedVariables false in
example (P Q R : Prop) (hRP : R → P) (hR : R) (hQ : Q) : P := by
  success_if_fail_with_msg "application type mismatch
  hRP hQ
argument
  hQ
has type
  Q : Prop
but is expected to have type
  R : Prop"
    Concloem amb hRP aplicat a hQ
  Concloem amb hRP aplicat a hR

example (P : ℕ → Prop) (h : ∀ n, P n) : P 0 := by
  Concloem amb h aplicat a _

example (P : ℕ → Prop) (h : ∀ n, P n) : P 0 := by
  Concloem amb h

example {a b : ℕ}: a + b = b + a := by
  Calculem

example {a b : ℕ} (h : a + b - a = 0) : b = 0 := by
  Calculem at h
  Concloem amb h

variable (k : Nat)

example (h : True) : True := by
  Concloem amb h

example (h : ∀ _n : ℕ, True) : True := by
  Concloem amb h aplicat a 0

example (h : True → True) : True := by
  Apliquem h
  trivial

example (h : ∀ _n _k : ℕ, True) : True := by
  Concloem amb h aplicat a [0, 1]

example (a b : ℕ) (h : a < b) : a ≤ b := by
  Concloem amb h

example (a b c : ℕ) (h : a < b ∧ a < c) : a ≤ b := by
  Concloem amb h

example (a b c : ℕ) (h : a ≤ b) (h' : b ≤ c) : a ≤ c := by
  Combinem [h, h']

example (a b c : ℤ) (h : a = b + c) (h' : b - a = c) : c = 0 := by
  Combinem [h, h']

example (a b c : ℕ) (h : a ≤ b) (h' : b ≤ c ∧ a+b ≤ a+c) : a ≤ c := by
  Combinem [h, h']

example (a b c : ℕ) (h : a = b) (h' : a = c) : b = c := by
  Reescrivim utilitzant ← h
  Concloem amb h'

example (a b c : ℕ) (h : a = b) (h' : a = c) : b = c := by
  Reescrivim utilitzant h at h'
  Concloem amb h'

example (a b : Nat) (h : a = b) (h' : b = 0): a = 0 := by
  Reescrivim utilitzant ← h at h' que esdevé a = 0
  exact h'

example (a b : Nat) (h : a = b) (h' : b = 0): a = 0 := by
  Reescrivim utilitzant ← h at h'
  clear h
  exact h'

example (f : ℕ → ℕ) (n : ℕ) (h : n > 0 → f n = 0) (hn : n > 0): f n = 0 := by
  Reescrivim utilitzant h
  exact hn

example (f : ℕ → ℕ) (h : ∀ n > 0, f n = 0) : f 1 = 0 := by
  Reescrivim utilitzant h
  norm_num

example (a b c : ℕ) (h : a = b) (h' : a = c) : b = c := by
  success_if_fail_with_msg "El terme donat
  a = c
no és definicionalment igual a l'esperat
  b = c"
    Reescrivim utilitzant h at h' que esdevé a = c
  Reescrivim utilitzant h at h' que esdevé b = c
  Concloem amb h'

example (a b c : ℕ) (h : a = b) (h' : a = c) : a = c := by
  Reescrivim utilitzant h a tot arreu
  Concloem amb h'

example (P Q : Prop) (h : P → Q) (h' : P) : Q := by
  Especialitzem h en h'
  Concloem amb h

example (P Q R : Prop) (h : P → Q → R) (hP : P) (hQ : Q) : R := by
  Concloem amb h aplicat a [hP, hQ]

example (f : ℕ → ℕ) (a b : ℕ) (h : a = b) : f a = f b := by
  Apliquem f at h
  Concloem amb h

example (P : ℕ → Prop) (h : ∀ n, P n) : P 0 := by
  Especialitzem h en 0
  Concloem amb h


example (x : ℝ) : (∀ ε > 0, x ≤ ε) → x ≤ 0 := by
  Contraposem
  intro h
  use x/2
  constructor
  Concloem amb h
  Concloem amb h

example (ε : ℝ) (h : ε > 0) : ε ≥ 0 := by Concloem amb h
example (ε : ℝ) (h : ε > 0) : ε/2 > 0 := by Concloem amb h
example (ε : ℝ) (h : ε > 0) : ε ≥ -1 := by Concloem amb h
example (ε : ℝ) (h : ε > 0) : ε/2 ≥ -3 := by Concloem amb h

example (x : ℝ) (h : x = 3) : 2*x = 6 := by Concloem amb h

example (x : ℝ) : (∀ ε > 0, x ≤ ε) → x ≤ 0 := by
  Contraposem simplement
  intro h
  Simplifiquem la negació
  Simplifiquem la negació at h
  use x/2
  constructor
  · Concloem amb h
  · Concloem amb h

example (x : ℝ) : (∀ ε > 0, x ≤ ε) → x ≤ 0 := by
  Contraposem simplement
  intro h
  success_if_fail_with_msg "El terme donat
  0 < x
no és definicionalment igual a l'esperat
  ∃ ε > 0, ε < x"
    Simplifiquem la negació que esdevé 0 < x
  Simplifiquem la negació que esdevé ∃ ε > 0, ε < x
  success_if_fail_with_msg "El terme donat
  ∃ ε > 0, ε < x
no és definicionalment igual a l'esperat
  0 < x"
    Simplifiquem la negació at h que esdevé ∃ ε > 0, ε < x
  Simplifiquem la negació at h que esdevé 0 < x
  use x/2
  constructor
  · Concloem amb h
  · Concloem amb h

set_option linter.unusedVariables false in
example : (∀ n : ℕ, False) → 0 = 1 := by
  Contraposem
  Calculem

example (P Q : Prop) (h : P ∨ Q) : True := by
  Separem h en casos
  all_goals
    intro
    trivial

example (P : Prop) (hP₁ : P → True) (hP₂ : ¬ P → True): True := by
  Separem en casos segons si P
  intro h
  exact hP₁ h
  intro h
  exact hP₂ h

/-
namespace Verbose.Catalan

def f (n : ℕ) := 2*n

example : f 2 = 4 := by
  We unfold f
  refl

example (h : f 2 = 4) : True → True := by
  We unfold f at h
  guard_hyp_strict h : 2*2 = 4
  exact id

example (h : f 2 = 4) : True → True := by
  success_if_fail_with_msg ""
    We unfold f at h que esdevé 2*2 = 5
  We unfold f at h que esdevé 2*2 = 4
  exact id

example (P : ℕ → ℕ → Prop) (h : ∀ n : ℕ, ∃ k, P n k) : True := by
  We rename n to p at h
  We rename k to l at h
  guard_hyp_strict h : ∀ p, ∃ l, P p l
  trivial

example (P : ℕ → ℕ → Prop) (h : ∀ n : ℕ, ∃ k, P n k) : True := by
  We rename n to p at h que esdevé ∀ p, ∃ k, P p k
  success_if_fail_with_msg ""
    We rename k to l at h que esdevé ∀ p, ∃ j, P p j
  We rename k to l at h que esdevé ∀ p, ∃ l, P p l
  trivial

example (P : ℕ → ℕ → Prop) : (∀ n : ℕ, ∃ k, P n k) ∨ True := by
  We rename n to p
  We rename k to l
  guard_target_strict (∀ p, ∃ l, P p l) ∨ True
  right
  trivial
 -/
example (a b c : ℕ) : True := by
  Oblidem a
  Oblidem b c
  trivial

example (h : 1 + 1 = 2) : True := by
  success_if_fail_with_msg "type mismatch
  this
has type
  2 = 3 : Prop
but is expected to have type
  1 + 1 = 2 : Prop"
    Reformulem h com 2 = 3
  Reformulem h com 2 = 2
  trivial
