import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Coloring
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Real.Basic

open SimpleGraph

noncomputable section

/-!
# Erdős Problem #750

Let f(m) be some function such that f(m) → ∞ as m → ∞. Does there exist a
graph G of infinite chromatic number such that every subgraph on m vertices
contains an independent set of size at least m/2 - f(m)?

In [Er69b] Erdős conjectures this for f(m) = εm for any fixed ε > 0. This
follows from a result of Erdős, Hajnal, and Szemerédi [EHS82].

In [ErHa67b] Erdős and Hajnal prove this for f(m) ≥ cm for all c > 1/4.

https://www.erdosproblems.com/750

Tags: graph theory, chromatic number
-/

namespace Erdos750

/-- A finset of vertices is independent in G if no two distinct vertices
    in the set are adjacent. -/
def IsIndepSet {V : Type*} (G : SimpleGraph V) (S : Finset V) : Prop :=
  ∀ u ∈ S, ∀ v ∈ S, u ≠ v → ¬G.Adj u v

end Erdos750

/--
Erdős Problem #750 [Er94b][Er95d]:

For every function f : ℕ → ℕ with f(m) → ∞ as m → ∞, there exists a
graph G with infinite chromatic number such that every finite set of m
vertices in G contains an independent set of size at least m/2 - f(m).
-/
theorem erdos_problem_750 :
    ∀ f : ℕ → ℕ, (∀ C : ℕ, ∃ M₀ : ℕ, ∀ m : ℕ, m ≥ M₀ → f m ≥ C) →
    ∃ (V : Type) (G : SimpleGraph V),
      (∀ k : ℕ, ¬G.Colorable k) ∧
      ∀ (S : Finset V), ∃ I : Finset V,
        I ⊆ S ∧ Erdos750.IsIndepSet G I ∧
        (S.card : ℝ) / 2 - (f S.card : ℝ) ≤ (I.card : ℝ) :=
  sorry

end
