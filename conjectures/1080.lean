import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Order.Floor.Semiring

open SimpleGraph Finset

/--
A simple graph contains a 6-cycle (C₆) if there exist six distinct vertices
a, b, c, d, e, f forming a cycle a-b-c-d-e-f-a.
-/
def SimpleGraph.ContainsCycle6 {V : Type*} (G : SimpleGraph V) : Prop :=
  ∃ (a b c d e f : V),
    a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ a ≠ e ∧ a ≠ f ∧
    b ≠ c ∧ b ≠ d ∧ b ≠ e ∧ b ≠ f ∧
    c ≠ d ∧ c ≠ e ∧ c ≠ f ∧
    d ≠ e ∧ d ≠ f ∧
    e ≠ f ∧
    G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d e ∧ G.Adj e f ∧ G.Adj f a

/--
The number of edges in a simple graph on Fin n.
-/
noncomputable def SimpleGraph.numEdges {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] : ℕ :=
  ((Finset.univ ×ˢ Finset.univ).filter
    fun p : Fin n × Fin n => p.1 < p.2 ∧ G.Adj p.1 p.2).card

/--
Erdős Problem #1080 [Er75] [Er79g]:

Let G be a bipartite graph on n vertices such that one part has ⌊n^{2/3}⌋
vertices. Is there a constant c > 0 such that if G has at least cn edges
then G must contain a C₆?

The answer is no, as shown by De Caen and Székely [DeSz92]. They proved that
for bipartite graphs between n and ⌊n^{2/3}⌋ vertices avoiding both C₄ and C₆,
the maximum number of edges is between n^{58/57+o(1)} and n^{10/9}, both of
which grow faster than cn. Lazebnik, Ustimenko, and Woldar [LUW94] improved
the lower bound to n^{16/15+o(1)}.

We formalise the disproof: for every c > 0, there exists a bipartite graph
with one part of size ⌊n^{2/3}⌋ having at least cn edges but no C₆.
-/
theorem erdos_problem_1080 :
    ∀ (c : ℝ), 0 < c →
      ∃ (n : ℕ) (G : SimpleGraph (Fin n)) (_ : DecidableRel G.Adj),
        -- G is bipartite with one part of size ⌊n^{2/3}⌋
        (∃ (f : Fin n → Fin 2),
          (∀ u v, G.Adj u v → f u ≠ f v) ∧
          (Finset.univ.filter (fun v => f v = 0)).card =
            Nat.floor ((n : ℝ) ^ ((2 : ℝ) / 3))) ∧
        -- G has at least cn edges
        (G.numEdges : ℝ) ≥ c * n ∧
        -- G contains no C₆
        ¬G.ContainsCycle6 :=
  sorry
