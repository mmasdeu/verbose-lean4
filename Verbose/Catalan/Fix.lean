import Verbose.Tactics.Fix

open Lean Elab Tactic

syntax "Sigui₁ " colGt fixDecl : tactic
syntax "Sigui " (colGt fixDecl)+ : tactic

elab_rules : tactic
  | `(tactic| Sigui₁ $x:ident) => Fix1 (introduced.bare x x.getId)

elab_rules : tactic
  | `(tactic| Sigui₁ $x:ident : $type) =>
    Fix1 (introduced.typed (mkNullNode #[x, type]) x.getId type)

elab_rules : tactic
  | `(tactic| Sigui₁ $x:ident < $bound) =>
    Fix1 (introduced.related (mkNullNode #[x, bound]) x.getId intro_rel.lt bound)

elab_rules : tactic
  | `(tactic| Sigui₁ $x:ident > $bound) =>
    Fix1 (introduced.related (mkNullNode #[x, bound]) x.getId intro_rel.gt bound)

elab_rules : tactic
  | `(tactic| Sigui₁ $x:ident ≤ $bound) =>
    Fix1 (introduced.related (mkNullNode #[x, bound]) x.getId intro_rel.le bound)

elab_rules : tactic
  | `(tactic| Sigui₁ $x:ident ≥ $bound) =>
    Fix1 (introduced.related (mkNullNode #[x, bound]) x.getId intro_rel.ge bound)


elab_rules : tactic
  | `(tactic| Sigui₁ $x:ident ∈ $set) =>
    Fix1 (introduced.related (mkNullNode #[x, set]) x.getId intro_rel.mem set)

elab_rules : tactic
  | `(tactic| Sigui₁ ( $decl:fixDecl )) => do evalTactic (← `(tactic| Sigui₁ $decl:fixDecl))


macro_rules
  | `(tactic| Sigui $decl:fixDecl) => `(tactic| Sigui₁ $decl)

macro_rules
  | `(tactic| Sigui $decl:fixDecl $decls:fixDecl*) => `(tactic| Sigui₁ $decl; Sigui $decls:fixDecl*)

implement_endpoint (lang := ca) noObjectIntro : CoreM String :=
pure "No hi ha cap objecte per introduir."

implement_endpoint (lang := ca) noHypIntro : CoreM String :=
pure "No hi ha cap hipòtesi per introduir."

implement_endpoint (lang := ca) negationByContra (hyp : Format) : CoreM String :=
pure s!"L'objectiu és una negació, no cal demostrar-lo per contradicció. \
 Es pot assumir directament {hyp} (amb \"Suposem\")"

implement_endpoint (lang := ca) wrongNegation : CoreM String :=
pure "Això no és el que cal assumir prer arribar a contradicció, fins it tot després de simplificar les negacions."

macro_rules
| `(ℕ) => `(Nat)

setLang ca

example : ∀ b : ℕ, ∀ a : Nat, a ≥ 2 → a = a ∧ b = b := by
  Sigui b (a ≥ 2)
  trivial

set_option linter.unusedVariables false in
example : ∀ n > 0, ∀ k : ℕ, ∀ l ∈ (Set.univ : Set ℕ), true := by
  Sigui (n > 0) k (l ∈ (Set.univ : Set ℕ))
  trivial

-- FIXME: The next example shows an elaboration issue
/- example : ∀ n > 0, ∀ k : ℕ, ∀ l ∈ (Set.univ : Set ℕ), true := by
  Sigui (n > 0) k (l ∈ Set.univ)
  trivial

-- while the following funciona
example : ∀ n > 0, ∀ k : ℕ, ∀ l ∈ (Set.univ : Set ℕ), true := by
  intro n n_pos k l (hl : l ∈ Set.univ)
  trivial
  -/

set_option linter.unusedVariables false in
example : ∀ n > 0, ∀ k : ℕ, ∀ l ∈ (Set.univ : Set ℕ), true := by
  Sigui n
  success_if_fail_with_msg "No hi ha cap objecte per introduir."
    Sigui h
  intro hn
  Sigui k (l ∈ (Set.univ : Set ℕ)) -- same elaboration issue here
  trivial

/-
The next examples show que name shadowing detection does not work.

example : ∀ n > 0, ∀ k : ℕ, true := by
  Sigui (n > 0)
  success_if_fail_with_msg ""
    Sigui n
  Sigui k
  trivial


example : ∀ n > 0, ∀ k : ℕ, true := by
  Sigui n > 0
  success_if_fail_with_msg ""
    Sigui n
  Sigui k
  trivial
 -/

example (k l : ℕ) : ∀ n ≤ k + l, true := by
  Sigui n ≤ k + l
  trivial


example (A : Set ℕ) : ∀ n ∈ A, true := by
  Sigui n ∈ A
  trivial
