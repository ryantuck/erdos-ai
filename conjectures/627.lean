import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Data.Nat.Lattice
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Topology.Order.Basic

open SimpleGraph Filter Topology

attribute [local instance] Classical.propDecidable

noncomputable section

/-!
# Erdős Problem #627

Let ω(G) denote the clique number of G and χ(G) the chromatic number. If f(n) is the
maximum value of χ(G)/ω(G), as G ranges over all graphs on n vertices, then does
  lim_{n → ∞} f(n) / (n / (log₂ n)²)
exist?

Erdős [Er67c] proved that f(n) ≍ n / (log₂ n)² and that the limit, if it exists,
must be in [1/4, 4].

Tags: graph theory, chromatic number
-/

/-- The chromatic number of a simple graph on `Fin n`: the minimum number of colors
    such that there exists a proper coloring. -/
noncomputable def chromaticNumber627 {n : ℕ} (G : SimpleGraph (Fin n)) : ℕ :=
  sInf {k : ℕ | ∃ f : Fin n → Fin k, ∀ u v, G.Adj u v → f u ≠ f v}

/-- The clique number of a simple graph on `Fin n`: the maximum size of a clique. -/
noncomputable def cliqueNumber627 {n : ℕ} (G : SimpleGraph (Fin n)) : ℕ :=
  sSup {k : ℕ | ¬G.CliqueFree k}

/-- `f627 n` is the maximum of χ(G)/ω(G) over all simple graphs G on n vertices. -/
noncomputable def f627 (n : ℕ) : ℝ :=
  sSup {r : ℝ | ∃ G : SimpleGraph (Fin n),
    cliqueNumber627 G > 0 ∧
    r = (chromaticNumber627 G : ℝ) / (cliqueNumber627 G : ℝ)}

/--
**Erdős Problem #627** [Er61d][Er67c][Er69b]:

Does the limit lim_{n → ∞} f(n) / (n / (log₂ n)²) exist, where f(n) is the maximum
of χ(G)/ω(G) over all graphs G on n vertices?
-/
theorem erdos_problem_627 :
    ∃ L : ℝ, Tendsto
      (fun n : ℕ => f627 n / ((n : ℝ) / (Real.logb 2 (n : ℝ)) ^ 2))
      atTop (nhds L) :=
  sorry

end
