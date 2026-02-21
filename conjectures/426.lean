import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Subgraph
import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Set.Card
import Mathlib.Data.Real.Basic
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Topology.Algebra.Ring.Real

open SimpleGraph

/--
Two subgraphs of a graph G are isomorphic if there exists a graph isomorphism
between their coerced graphs (viewed as SimpleGraphs on their respective
vertex subtypes).
-/
def SubgraphIsomorphic {V : Type*} {G : SimpleGraph V}
    (H₁ H₂ : G.Subgraph) : Prop :=
  Nonempty (H₁.coe ≃g H₂.coe)

/--
A subgraph H of G is a "unique subgraph" if it is the only subgraph of G
in its isomorphism class: every subgraph H' of G isomorphic to H must equal H.
-/
def IsUniqueSubgraph {V : Type*} {G : SimpleGraph V}
    (H : G.Subgraph) : Prop :=
  ∀ H' : G.Subgraph, SubgraphIsomorphic H H' → H' = H

/--
The number of unique subgraphs of a graph G on Fin n.
-/
noncomputable def numUniqueSubgraphs {n : ℕ} (G : SimpleGraph (Fin n)) : ℕ :=
  Set.ncard {H : G.Subgraph | IsUniqueSubgraph H}

/--
f(n) is the maximum number of unique subgraphs over all graphs on n vertices.
-/
noncomputable def maxUniqueSubgraphs (n : ℕ) : ℕ :=
  sSup {k : ℕ | ∃ G : SimpleGraph (Fin n), numUniqueSubgraphs G = k}

/--
Erdős Problem #426 (Disproved):

We say H is a unique subgraph of G if there is exactly one way to find H as a
subgraph (not necessarily induced) of G. Let f(n) be the maximum number of
distinct unique subgraphs in a graph on n vertices.

A problem of Erdős and Entringer [EnEr72], who constructed a graph with
≫ 2^(C(n,2) - O(n^{3/2+o(1)})) many unique subgraphs. This was improved by
Brouwer [Br75], who constructed a graph with ≫ 2^(C(n,2) - O(n)) / n! many
unique subgraphs.

Note that there are approximately 2^C(n,2) / n! non-isomorphic graphs on n
vertices, so the bound in the problem statement is trivially best possible.

Erdős believed Brouwer's construction was essentially best possible, but
Spencer suggested that ≫ 2^C(n,2) / n! might be achievable. Erdős offered
$100 for such a construction and $25 for a disproof.

Bradač and Christoph [BrCh24] proved the answer is no:
  f(n) = o(2^C(n,2) / n!).
Quantitatively, the o(1) factor can be taken to be O(log log log n / log log n).
-/
theorem erdos_problem_426 :
    Filter.Tendsto
      (fun n : ℕ =>
        (maxUniqueSubgraphs n : ℝ) /
        ((2 : ℝ) ^ (n.choose 2) / (Nat.factorial n : ℝ)))
      Filter.atTop
      (nhds 0) := by
  sorry
