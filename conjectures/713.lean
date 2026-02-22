import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Coloring
import Mathlib.Data.Nat.Lattice
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Card
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Order.Filter.AtTopBot.Basic

open SimpleGraph Filter

noncomputable section

/-!
# Erdős Problem #713

Is it true that, for every bipartite graph G, there exists some α ∈ [1,2) and
c > 0 such that ex(n; G) ~ cn^α? Must α be rational?

Here ex(n; G) is the Turán extremal number: the maximum number of edges in an
n-vertex graph that does not contain G as a subgraph. The notation ~ means
asymptotic equivalence: ex(n; G) / (cn^α) → 1 as n → ∞.

A problem of Erdős and Simonovits, worth $500. See also Problem #571.
-/

/-- A graph G contains H as a subgraph via an injective graph homomorphism. -/
def ContainsSubgraph713 {V U : Type*} (G : SimpleGraph V) (H : SimpleGraph U) : Prop :=
  ∃ f : U → V, Function.Injective f ∧ ∀ u v : U, H.Adj u v → G.Adj (f u) (f v)

/-- The Turán extremal number ex(n; H): the maximum number of edges in a
    simple graph on n vertices that does not contain H as a subgraph. -/
noncomputable def extremalNumber713 {U : Type*} (H : SimpleGraph U) (n : ℕ) : ℕ :=
  sSup {m : ℕ | ∃ G : SimpleGraph (Fin n),
    ¬ContainsSubgraph713 G H ∧ G.edgeSet.ncard = m}

/--
Erdős Problem #713, Part 1 (Erdős-Simonovits):

For every finite bipartite graph G, there exist α ∈ [1, 2) and c > 0 such that
ex(n; G) ~ cn^α, i.e., ex(n; G) / (cn^α) → 1 as n → ∞.
-/
theorem erdos_problem_713a :
    ∀ (U : Type) [Fintype U] (G : SimpleGraph U),
      G.Colorable 2 →
      ∃ α : ℝ, 1 ≤ α ∧ α < 2 ∧
      ∃ c : ℝ, 0 < c ∧
      Tendsto (fun n : ℕ => (extremalNumber713 G n : ℝ) / (c * (n : ℝ) ^ α))
        atTop (nhds 1) :=
  sorry

/--
Erdős Problem #713, Part 2 (Rationality of the exponent):

If ex(n; G) ~ cn^α for a finite bipartite graph G, then α must be rational.
-/
theorem erdos_problem_713b :
    ∀ (U : Type) [Fintype U] (G : SimpleGraph U),
      G.Colorable 2 →
      ∀ α : ℝ, 1 ≤ α → α < 2 →
      ∀ c : ℝ, 0 < c →
      Tendsto (fun n : ℕ => (extremalNumber713 G n : ℝ) / (c * (n : ℝ) ^ α))
        atTop (nhds 1) →
      ∃ q : ℚ, (q : ℝ) = α :=
  sorry

end
