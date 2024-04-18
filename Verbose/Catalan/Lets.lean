import Verbose.Tactics.Lets
import Mathlib.Tactic.Linarith

namespace Verbose.Catalan

elab "Demostrem" " per inducció" name:ident ":" stmt:term : tactic =>
letsInduct name.getId stmt

open Lean Elab Tactic in

macro "Demostrem" " que " stmt:term :tactic =>
`(tactic| first | show $stmt | apply Or.inl; show $stmt | apply Or.inr; show $stmt)

declare_syntax_cat explicitStmtCA
syntax ": " term : explicitStmtCA

def toStmt (e : Lean.TSyntax `explicitStmtCA) : Lean.Term := ⟨e.raw[1]!⟩

elab "Demostrem" " que " witness:term " funciona" stmt:(explicitStmtCA)?: tactic => do
  useTac witness (stmt.map toStmt)

elab "Demostrem" " primer que " stmt:term : tactic =>
  anonymousSplitLemmaTac stmt

elab "Demostrem" " ara que " stmt:term : tactic =>
  unblockTac stmt

syntax "Ara cal enunciar: Demostrem ara que " term : term

open Lean Parser Term PrettyPrinter Delaborator in
@[delab app.goalBlocker]
def goalBlocker_delab : Delab := whenPPOption Lean.getPPNotation do
  let stx ← SubExpr.withAppArg delab
  `(Ara cal enunciar: Demostrem ara que $stx)

macro "Demostrem" " una contradicció" : tactic => `(tactic|exfalso)

open Lean

implement_endpoint (lang := ca) inductionError : CoreM String :=
pure "L'enunciat ha de començar amb un quantificador universal sobre un nombre natural."

implement_endpoint (lang := ca) notWhatIsNeeded : CoreM String :=
pure "Això no és el que cal demostrar."

implement_endpoint (lang := ca) notWhatIsRequired : CoreM String :=
pure "Això no és el què es demana ara."

setLang ca


example : 1 + 1 = 2 := by
  Demostrem que 2 = 2
  rfl

example : ∃ k : ℕ, 4 = 2*k := by
  Demostrem que 2 funciona
  rfl

example : ∃ k : ℕ, 4 = 2*k := by
  Demostrem que 2 funciona: 4 = 2*2
  rfl

example : True ∧ True := by
  Demostrem primer que True
  trivial
  Demostrem ara que True
  trivial

example (P Q : Prop) (h : P) : P ∨ Q := by
  Demostrem que P
  exact h

example (P Q : Prop) (h : Q) : P ∨ Q := by
  Demostrem que Q
  exact h

example : 0 = 0 ∧ 1 = 1 := by
  Demostrem primer que 0 = 0
  trivial
  Demostrem ara que 1 = 1
  trivial

example : (0 : ℤ) = 0 ∧ 1 = 1 := by
  Demostrem primer que 0 = 0
  trivial
  Demostrem ara que 1 = 1
  trivial

example : 0 = 0 ∧ 1 = 1 := by
  Demostrem primer que 1 = 1
  trivial
  Demostrem ara que 0 = 0
  trivial

example : True ↔ True := by
  Demostrem primer que True → True
  exact id
  Demostrem ara que True → True
  exact id

example (h : False) : 2 = 1 := by
  Demostrem una contradicció
  exact h

example (P : Nat → Prop) (h₀ : P 0) (h : ∀ n, P n → P (n+1)) : P 4 := by
  Demostrem per inducció H : ∀ k, P k
  . exact h₀
  . exact h k hyp_rec
  . exact H 4

/-
example (P : ℕ → Prop) (h₀ : P 0) (h : ∀ n, P n → P (n+1)) : P 3 := by
  success_if_fail_with_msg "L'enunciat ha de començar amb un quantificador universal sobre un nombre natural."
    Demostrem per inducció H : true
  Demostrem per inducció H : ∀ n, P n
  exact h₀
  exact h

example (P : ℕ → Prop) (h₀ : P 0) (h : ∀ n, P n → P (n+1)) : true := by
  Demostrem per inducció H : ∀ k, P k
  exacts [h₀, h, trivial]

example : true := by
  Demostrem per inducció H : ∀ l, l < l + 1
  decide
  intro l
  intros hl
  linarith
  trivial
-/

set_option linter.unusedVariables false in
example : true := by
  success_if_fail_with_msg "L'enunciat ha de començar amb un quantificador universal sobre un nombre natural."
    Demostrem per inducció H : true
  success_if_fail_with_msg "L'enunciat ha de començar amb un quantificador universal sobre un nombre natural."
    Demostrem per inducció H : ∀ n : ℤ, true
  trivial
