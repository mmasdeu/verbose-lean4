import Mathlib.Topology.MetricSpace.Basic
import Verbose.Catalan.All

def funcio_continua_a (f : ℝ → ℝ) (x₀ : ℝ) :=
∀ ε > 0, ∃ δ > 0, ∀ x, |x - x₀| ≤ δ → |f x - f x₀| ≤ ε

def succ_convergeix (u : ℕ → ℝ) (l : ℝ) :=
∀ ε > 0, ∃ N, ∀ n ≥ N, |u n - l| ≤ ε

notation3:50 f:80 " és contínua a " x₀ => funcio_continua_a f x₀
notation3:50 u:80 " convergeix a " l => succ_convergeix u l

def creixent (u : ℕ → ℝ) := ∀ n m, n ≤ m → u n ≤ u m

notation3 u " és creixent" => creixent u

def es_suprem (M : ℝ) (u : ℕ → ℝ) :=
(∀ n, u n ≤ M) ∧ ∀ ε > 0, ∃ n₀, u n₀ ≥ M - ε

notation3 M " és un suprem de " u => es_suprem M u

configureUnfoldableDefs funcio_continua_a succ_convergeix creixent es_suprem

section Subset
variable {α : Type*}

/- The Mathlib definition of `Set.Subset` uses a strict-implicit
argument which confuses Verbose Lean. So let us replace it. -/

protected def Verbose.Catalan.Subset (s₁ s₂ : Set α) :=
  ∀ a, a ∈ s₁ → a ∈ s₂

instance (priority := high) Verbose.Catalan.hasSubset : HasSubset (Set α) :=
  ⟨Verbose.Catalan.Subset⟩

end Subset

open Verbose.Catalan

configureAnonymousFactSplittingLemmas le_le_of_abs_le le_le_of_max_le

configureAnonymousGoalSplittingLemmas LogicIntros AbsIntros Set.Subset.antisymm

useDefaultDataProviders

useDefaultSuggestionProviders
