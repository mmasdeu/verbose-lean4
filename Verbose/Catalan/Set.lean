import Verbose.Tactics.Set
import Mathlib.Tactic

elab "Definim " n:maybeTypedIdent " := " val:term : tactic => do
  let (n, ty) := match n with
  | `(maybeTypedIdent| $N:ident) => (N, none)
  | `(maybeTypedIdent|($N : $TY)) => (N, some TY)
  | _ => (default, none)
  setTac n ty val

setLang ca


example (a b : ℕ) : ℕ := by
  Definim n := max a b
  exact n

example (a b : ℕ) : ℕ := by
  Definim (n : ℕ) := max a b
  exact n

example : ℤ := by
  Definim (n : ℤ) := max 0 1
  exact n
