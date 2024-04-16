import Verbose.Tactics.By
import Verbose.Catalan.Common

open Lean Verbose.Catalan

namespace Verbose.Catalan


elab "Per " e:maybeAppliedCA " obtenim " colGt news:newStuffCA : tactic => do
obtainTac (← maybeAppliedCAToTerm e) (newStuffCAToArray news)

elab "Per " e:maybeAppliedCA " escollim " colGt news:newStuffCA : tactic => do
chooseTac (← maybeAppliedCAToTerm e) (newStuffCAToArray news)

elab "Per " e:maybeAppliedCA " només cal demostrar " "que "? colGt arg:term : tactic => do
bySufficesTac (← maybeAppliedCAToTerm e) #[arg]

elab "Per " e:maybeAppliedCA " només cal demostrar " "que "? colGt "["args:term,*"]" : tactic => do
bySufficesTac (← maybeAppliedCAToTerm e) args.getElems

lemma le_le_of_abs_le {α : Type*} [LinearOrderedAddCommGroup α] {a b : α} : |a| ≤ b → -b ≤ a ∧ a ≤ b := abs_le.1

lemma le_le_of_max_le {α : Type*} [LinearOrder α] {a b c : α} : max a b ≤ c → a ≤ c ∧ b ≤ c :=
max_le_iff.1

implement_endpoint (lang := ca) cannotGet : CoreM String := pure "No es pot obtenir."

implement_endpoint (lang := ca) theName : CoreM String := pure "El nom"

implement_endpoint (lang := ca) needName : CoreM String :=
pure "Cal donar un nom a l'objecte escollit."

implement_endpoint (lang := ca) wrongNbGoals (actual announced : ℕ) : CoreM String :=
pure s!"Aplicant això s'obtenen {actual} objectius, en comptes de {announced}."

configureAnonymousFactSplittingLemmas le_le_of_abs_le le_le_of_max_le

setLang ca

example (P : Nat → Prop) (h : ∀ n, P n) : P 0 := by
  Per h aplicat a 0 obtenim h₀
  exact h₀

example (P : Nat → Nat → Prop) (h : ∀ n k, P n (k+1)) : P 0 1 := by
  Per h aplicat a [0, 0] obtenim (h₀ : P 0 1)
  exact h₀

example (n : Nat) (h : ∃ k, n = 2*k) : True := by
  Per h obtenim k tal que (H : n = 2*k)
  trivial

example (n : Nat) (h : ∃ k, n = 2*k) : True := by
  Per h obtenim k tal que H
  trivial

example (P Q : Prop) (h : P ∧ Q)  : Q := by
  Per h obtenim (hP : P) (hQ : Q)
  exact hQ

example (x : ℝ) (h : |x| ≤ 3) : True := by
  Per h obtenim (h₁ : -3 ≤ x) (h₂ : x ≤ 3)
  trivial

example (n p q : ℕ) (h : n ≥ max p q) : True := by
  Per h obtenim (h₁ : n ≥ p) (h₂ : n ≥ q)
  trivial

noncomputable example (f : ℕ → ℕ) (h : ∀ y, ∃ x, f x = y) : ℕ → ℕ := by
  Per h escollim g tal que (H : ∀ (y : ℕ), f (g y) = y)
  exact g


example (P Q : Prop) (h : P → Q) (h' : P) : Q := by
  Per h només cal demostrar que P
  exact h'

example (P Q : Prop) (h : P → Q) (h' : P) : Q := by
  Per h només cal demostrar P
  exact h'

example (P Q R : Prop) (h : P → R → Q) (hP : P) (hR : R) : Q := by
  Per h només cal demostrar [P, R]
  exact hP
  exact hR

/-
example (P Q : Prop) (h : ∀ n : ℕ, P → Q) (h' : P) : Q := by
  success_if_fail_with_msg "Apply this leads to 0 goals, not 1."
    Per h aplicat a [0, 1] només cal demostrar P
  Per h aplicat a 0 només cal demostrar P
  exact h'
 -/

example (Q : Prop) (h : ∀ n : ℤ, n > 0 → Q)  : Q := by
  Per h aplicat a 1 només cal demostrar 1 > 0
  norm_num

set_option linter.unusedVariables false in
example (n : Nat) (h : ∃ n : Nat, n = n) : True := by
  success_if_fail_with_msg "El nom n ja està agafat"
    Per h obtenim n tal que H
  trivial
