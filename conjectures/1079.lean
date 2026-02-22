import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Lattice
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Finset.Card

open SimpleGraph Finset

noncomputable section

/-!
# Erdős Problem #1079

Let r ≥ 4. If G is a graph on n vertices with at least ex(n; K_r) edges then must
G contain a vertex with degree d ≫_r n whose neighbourhood contains at least
ex(d; K_{r-1}) edges?

As Erdős [Er75] says 'if true this would be a nice generalisation of Turán's theorem'.

This is true (unless G is itself the Turán graph), proved by Bollobás and
Thomason [BoTh81]. Bondy [Bo83b] showed that if G has > ex(n; K_r) edges then
the corresponding vertex can be chosen to be of maximum degree in G.

https://www.erdosproblems.com/1079

Tags: graph theory, turan number
-/

/-- An injective graph homomorphism from H to G; witnesses that G contains a
    subgraph isomorphic to H. -/
def containsSubgraph1079 {V U : Type*} (G : SimpleGraph V) (H : SimpleGraph U) : Prop :=
  ∃ f : U → V, Function.Injective f ∧ ∀ u v : U, H.Adj u v → G.Adj (f u) (f v)

/-- The Turán number ex(n; H): the maximum number of edges in a simple graph on n
    vertices that contains no copy of H as a subgraph. -/
noncomputable def turanNumber1079 {U : Type*} (H : SimpleGraph U) (n : ℕ) : ℕ :=
  sSup {m : ℕ | ∃ (V : Type) (fv : Fintype V) (F : SimpleGraph V) (dr : DecidableRel F.Adj),
    haveI := fv; haveI := dr;
    Fintype.card V = n ∧ ¬containsSubgraph1079 F H ∧ F.edgeFinset.card = m}

/-- The number of edges of G both of whose endpoints lie in a set S.
    Counts pairs (i, j) in S with i < j and G.Adj i j. -/
noncomputable def neighborhoodEdgeCount1079 {n : ℕ}
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (S : Finset (Fin n)) : ℕ :=
  (Finset.univ.filter (fun p : Fin n × Fin n =>
    p.1 ∈ S ∧ p.2 ∈ S ∧ p.1 < p.2 ∧ G.Adj p.1 p.2)).card

/--
Erdős Problem #1079 [Er75]:

Let r ≥ 4. If G is a graph on n vertices with at least ex(n; K_r) edges then
G must contain a vertex v with degree d ≫_r n whose neighbourhood contains
at least ex(d; K_{r-1}) edges.

Formalized as: for every r ≥ 4, there exists c > 0 and n₀ such that for all
n ≥ n₀ and all graphs G on n vertices with at least ex(n; K_r) edges, there
exists a vertex v with degree d ≥ c · n and at least ex(d; K_{r-1}) edges
among the neighbors of v.

Proved by Bollobás and Thomason [BoTh81].
-/
theorem erdos_problem_1079 (r : ℕ) (hr : r ≥ 4) :
    ∃ c : ℝ, c > 0 ∧
    ∃ n₀ : ℕ, ∀ n : ℕ, n ≥ n₀ →
    ∀ (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      G.edgeFinset.card ≥ turanNumber1079 (⊤ : SimpleGraph (Fin r)) n →
      ∃ v : Fin n,
        (G.degree v : ℝ) ≥ c * (n : ℝ) ∧
        neighborhoodEdgeCount1079 G (G.neighborFinset v) ≥
          turanNumber1079 (⊤ : SimpleGraph (Fin (r - 1))) (G.degree v) :=
  sorry

end
