import Verbose.Tactics.Since
import Verbose.Catalan.Common
import Lean

namespace Verbose.Catalan

open Lean Elab Tactic

elab "Com" " que" factsCA:factsCA " obtenim " news:newObjectCA : tactic => do
  let newsT ← newObjectCAToTerm news
  let news_patt := newObjectCAToRCasesPatt news
  let factsCAT := factsCAToArray factsCA
  sinceObtainTac newsT news_patt factsCAT

elab "Com" " que" factsCA:factsCA " obtenim " news:newFactsCA : tactic => do
  let newsT ← newFactsCAToTypeTerm news
  let news_patt := newFactsCAToRCasesPatt news
  let factsCAT := factsCAToArray factsCA
  sinceObtainTac newsT news_patt factsCAT

elab "Com" " que" factsCA:factsCA " concloem que " concl:term : tactic => do
  let factsCAT := factsCAToArray factsCA
  -- dbg_trace "factsCAT {factsCAT}"
  sinceConcludeTac concl factsCAT

elab "Com" " que" factsCA:factsCA " només cal demostrar " " que " newGoals:factsCA : tactic => do
  let factsCAT := factsCAToArray factsCA
  let newGoalsT := factsCAToArray newGoals
  sinceSufficesTac factsCAT newGoalsT

implement_endpoint (lang := ca) couldNotProve (goal : Format) : CoreM String :=
pure s!"No s'ha pogut demostrar:\n {goal}"

implement_endpoint (lang := ca) failedProofUsing (goal : Format) : CoreM String :=
pure s!"No s'ha pogut demostrar el següent amb les hipòtesis donades.\n{goal}"

setLang ca

example (n : Nat) (h : ∃ k, n = 2*k) : True := by
  Com que ∃ k, n = 2*k obtenim k tal que H : n = 2*k
  trivial

example (n N : Nat) (hn : n ≥ N) (h : ∀ n ≥ N, ∃ k, n = 2*k) : True := by
  Com que ∀ n ≥ N, ∃ k, n = 2*k and n ≥ N obtenim k tal que H : n = 2*k
  trivial

example (P Q : Prop) (h : P ∧ Q)  : Q := by
  Com que P ∧ Q obtenim (hP : P) and (hQ : Q)
  exact hQ

example (n : ℕ) (hn : n > 2) (P : ℕ → Prop) (h : ∀ n ≥ 3, P n) : True := by
  Com que ∀ n ≥ 3, P n and n ≥ 3 obtenim H : P n
  trivial

example (n : ℕ) (hn : n > 2) (P Q : ℕ → Prop) (h : ∀ n ≥ 3, P n ∧ Q n) : True := by
  Com que ∀ n ≥ 3, P n ∧ Q n and n ≥ 3 obtenim H : P n and H' : Q n
  trivial

example (n : ℕ) (hn : n > 2) (P : ℕ → Prop) (h : ∀ n ≥ 3, P n) : P n := by
  Com que ∀ n ≥ 3, P n and n ≥ 3 concloem que P n

example (n : ℕ) (hn : n > 2) (P Q : ℕ → Prop) (h : ∀ n ≥ 3, P n ∧ Q n) : P n := by
  Com que ∀ n ≥ 3, P n ∧ Q n and n ≥ 3 concloem que P n

example (n : ℕ) (hn : n > 2) (P Q : ℕ → Prop) (h : ∀ n ≥ 3, P n ∧ Q n) : True := by
  Com que ∀ n ≥ 3, P n ∧ Q n and n ≥ 3 obtenim H : P n
  trivial

example (n : ℕ) (hn : n > 2) (P Q : ℕ → Prop) (h : ∀ n ≥ 3, P n) (h' : ∀ n ≥ 3, Q n) : True := by
  Com que ∀ n ≥ 3, P n, ∀ n ≥ 3, Q n and n ≥ 3 obtenim H : P n and H' : Q n
  trivial

example (P Q : Prop) (h : P → Q) (h' : P) : Q := by
  Com que P → Q només cal demostrar que P
  exact h'

example (P Q R : Prop) (h : P → R → Q) (hP : P) (hR : R) : Q := by
  Com que P → R → Q només cal demostrar que P and R
  constructor
  exact hP
  exact hR
