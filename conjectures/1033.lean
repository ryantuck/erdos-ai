import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt

open Classical SimpleGraph Finset

noncomputable section

/-!
# Erdős Problem #1033

Let h(n) be such that every graph on n vertices with > n²/4 many edges
contains a triangle whose vertices have degrees summing to at least h(n).
Estimate h(n). In particular, is it true that
  h(n) ≥ (2(√3 - 1) - o(1))n?

Erdős and Laskar [ErLa85] proved 2(√3 - 1)n ≥ h(n) ≥ (1+c)n for some c > 0.
The lower bound was improved to (21/16)n by Fan [Fa88].

Tags: graph theory
-/

/--
**Erdős Problem #1033** [Er93, p.344]:

For every ε > 0, there exists N₀ such that for all n ≥ N₀, every graph on
n vertices with more than n²/4 edges contains a triangle whose vertices have
degrees summing to at least (2(√3 - 1) - ε) · n.
-/
theorem erdos_problem_1033 :
    ∀ ε : ℝ, ε > 0 →
    ∃ N₀ : ℕ, ∀ n : ℕ, n ≥ N₀ →
    ∀ G : SimpleGraph (Fin n),
      G.edgeFinset.card > n ^ 2 / 4 →
      ∃ u v w : Fin n, G.Adj u v ∧ G.Adj v w ∧ G.Adj u w ∧
        (G.degree u + G.degree v + G.degree w : ℝ) ≥
          (2 * (Real.sqrt 3 - 1) - ε) * (n : ℝ) :=
  sorry

end
