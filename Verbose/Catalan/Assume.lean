import Verbose.Catalan.Fix

open Lean Elab Tactic

syntax "Suposem₁ " colGt assumeDecl : tactic
syntax "Suposem " "que"? (colGt assumeDecl)+ : tactic
syntax "Suposem " "per arribar a contradicció que " (colGt assumeDecl) : tactic

elab_rules : tactic
  | `(tactic| Suposem₁ $x:ident) => Assume1 (introduced.bare x x.getId)

elab_rules : tactic
  | `(tactic| Suposem₁ $x:ident : $type) =>
    Assume1 (introduced.typed (mkNullNode #[x, type]) x.getId type)


elab_rules : tactic
  | `(tactic| Suposem₁ ( $decl:assumeDecl )) => do evalTactic (← `(tactic| Suposem₁ $decl:assumeDecl))

macro_rules
  | `(tactic| Suposem $[que]? $decl:assumeDecl) => `(tactic| Suposem₁ $decl)
  | `(tactic| Suposem $[que]? $decl:assumeDecl $decls:assumeDecl*) => `(tactic| Suposem₁ $decl; Suposem $decls:assumeDecl*)

elab_rules : tactic
  | `(tactic| Suposem per arribar a contradicció que $x:ident : $type) => forContradiction x.getId type

setLang ca

example (P Q : Prop) : P → Q → True := by
  Suposem hP (hQ : Q)
  trivial

example (P Q : Prop) : P → Q → True := by
  Suposem que hP (hQ : Q)
  trivial

example (n : Nat) : 0 < n → True := by
  Suposem que hn
  trivial

example : ∀ n > 0, true := by
  success_if_fail_with_msg "No hi ha cap hipòtesi per introduir."
    Suposem n
  intro n
  Suposem H : n > 0
  trivial


example (P Q : Prop) (h : ¬ Q → ¬ P) : P → Q := by
  Suposem hP
  Suposem per arribar a contradicció que hnQ :¬ Q
  exact h hnQ hP


example (P Q : Prop) (h : ¬ Q → ¬ P) : P → Q := by
  Suposem hP
  Suposem per arribar a contradicció que hnQ : ¬ Q
  exact h hnQ hP

example : 0 ≠ 1 := by
  success_if_fail_with_msg
    "L'objectiu és una negació, no cal demostrar-lo per contradicció. Podeu escriure directament: Suposem 0 = 1."
    Suposem per arribar a contradicció que h : 0 = 1
  norm_num

example : 0 ≠ 1 := by
  Suposem h : 0 = 1
  norm_num at h

allowProvingNegationsByContradiction

example : 0 ≠ 1 := by
  Suposem per arribar a contradicció que h : 0 = 1
  norm_num at h
