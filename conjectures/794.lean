import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Basic

noncomputable section

/-!
# Erdős Problem #794

Is it true that every 3-uniform hypergraph on $3n$ vertices with at least $n^3+1$
edges must contain either a subgraph on 4 vertices with 3 edges or a subgraph on
5 vertices with 7 edges?

DISPROVED: Balogh observed that every 3-uniform hypergraph on 5 vertices with 7
edges contains a sub-hypergraph on 4 vertices with 3 edges, so the second
condition is redundant. Harris provided a counterexample to the remaining
statement: the 3-uniform hypergraph on {1,...,9} with 28 edges, formed by taking
27 edges by choosing one element each from {1,2,3}, {4,5,6}, {7,8,9}, and then
adding the edge {1,2,3}.
-/

/-- A 3-uniform hypergraph H contains a (k, m)-subhypergraph if there exist k
    vertices spanning at least m edges of H. -/
def ContainsSubhypergraph {N : ℕ} (H : Finset (Finset (Fin N))) (k m : ℕ) : Prop :=
  ∃ S : Finset (Fin N), S.card = k ∧ (H.filter (· ⊆ S)).card ≥ m

/--
Erdős Problem #794 (DISPROVED by Harris):

It is NOT true that every 3-uniform hypergraph on 3n vertices with at least n³+1
edges must contain either a subgraph on 4 vertices with 3 edges or a subgraph on
5 vertices with 7 edges.

Harris's counterexample: the 3-uniform hypergraph on {1,...,9} (so n=3, n³+1=28)
with 28 edges, formed by taking 27 edges by choosing one element each from
{1,2,3}, {4,5,6}, {7,8,9}, and then adding the edge {1,2,3}.
-/
theorem erdos_problem_794 :
    ¬ ∀ n : ℕ, ∀ H : Finset (Finset (Fin (3 * n))),
      (∀ e ∈ H, e.card = 3) →
      H.card ≥ n ^ 3 + 1 →
      ContainsSubhypergraph H 4 3 ∨ ContainsSubhypergraph H 5 7 :=
  sorry

end
