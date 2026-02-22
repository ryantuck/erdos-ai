import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Coloring
import Mathlib.Data.Rat.Lemmas
import Mathlib.Data.Nat.Lattice
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Card
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open SimpleGraph

/-!
# Erdős Problem #571

Show that for any rational α ∈ [1,2) there exists a bipartite graph G such that
ex(n; G) ≍ n^α.

Here ex(n; G) is the Turán extremal number: the maximum number of edges in an
n-vertex graph that does not contain G as a subgraph. The notation ≍ means that
the two sides are equal up to constant factors.

A problem of Erdős and Simonovits. A rational α ∈ [1,2) for which this holds
is known as a Turán exponent. Bukh and Conlon proved the analogous statement
for finite families of graphs.
-/

/-- A graph G contains H as a subgraph via an injective graph homomorphism. -/
def ContainsSubgraph {V U : Type*} (G : SimpleGraph V) (H : SimpleGraph U) : Prop :=
  ∃ f : U → V, Function.Injective f ∧ ∀ u v : U, H.Adj u v → G.Adj (f u) (f v)

/-- The Turán extremal number ex(n; H): the maximum number of edges in a
    simple graph on n vertices that does not contain H as a subgraph. -/
noncomputable def extremalNumber {U : Type*} (H : SimpleGraph U) (n : ℕ) : ℕ :=
  sSup {m : ℕ | ∃ G : SimpleGraph (Fin n),
    ¬ContainsSubgraph G H ∧ G.edgeSet.ncard = m}

/--
Erdős Problem #571 (Erdős-Simonovits):

For every rational α ∈ [1, 2), there exists a finite bipartite graph G such that
the Turán extremal number satisfies ex(n; G) ≍ n^α, meaning there exist positive
constants c₁, c₂ > 0 and a threshold N₀ such that for all n ≥ N₀,
  c₁ · n^α ≤ ex(n; G) ≤ c₂ · n^α.
-/
theorem erdos_problem_571 :
    ∀ α : ℚ, 1 ≤ α → α < 2 →
    ∃ (U : Type) (_ : Fintype U) (G : SimpleGraph U),
      G.Colorable 2 ∧
      ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧
      ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n →
        c₁ * (n : ℝ) ^ (α : ℝ) ≤ (extremalNumber G n : ℝ) ∧
        (extremalNumber G n : ℝ) ≤ c₂ * (n : ℝ) ^ (α : ℝ) :=
  sorry
