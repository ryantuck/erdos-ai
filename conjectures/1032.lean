import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Coloring
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Real.Basic

open Classical SimpleGraph

noncomputable section

/-!
# Erdős Problem #1032

We say that a graph is 4-chromatic critical if it has chromatic number 4, and
removing any edge decreases the chromatic number to 3.

Is there, for arbitrarily large n, a 4-chromatic critical graph on n vertices
with minimum degree ≫ n?

Known results:
- Simonovits [Si72] and Toft [To72] independently constructed 4-chromatic
  critical graphs with minimum degree ≫ n^{1/3}.
- Dirac gave an example of a 6-chromatic critical graph with minimum degree > n/2.
- This problem is also open for 5-chromatic critical graphs.

See also [917] and [944].

Tags: graph theory, chromatic number
-/

/--
A simple graph G is k-critical if its chromatic number equals k and for every
edge e, the graph obtained by deleting e has chromatic number strictly less
than k.
-/
def SimpleGraph.IsCritical {V : Type*} (G : SimpleGraph V) (k : ℕ) : Prop :=
  G.chromaticNumber = (k : ℕ∞) ∧
  ∀ e ∈ G.edgeSet, (G.deleteEdges {e}).chromaticNumber < (k : ℕ∞)

/--
**Erdős Problem #1032** [Er93, p.341]:

There exists a constant c > 0 such that for arbitrarily large n, there exists
a 4-chromatic critical graph on n vertices with minimum degree at least c · n.
-/
theorem erdos_problem_1032 :
    ∃ c : ℝ, c > 0 ∧ ∀ N₀ : ℕ, ∃ n : ℕ, n ≥ N₀ ∧
      ∃ G : SimpleGraph (Fin n),
        G.IsCritical 4 ∧ (G.minDegree : ℝ) ≥ c * (n : ℝ) :=
  sorry

end
