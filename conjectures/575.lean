import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Lattice
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Finset.Card

open SimpleGraph

noncomputable section

/-!
# Erdős Problem #575

If F is a finite set of finite graphs then ex(n; F) is the maximum number of edges
a graph on n vertices can have without containing any subgraphs from F. Note that it
is trivial that ex(n; F) ≤ ex(n; G) for every G ∈ F.

Is it true that, for every F, if there is a bipartite graph in F then there exists
some bipartite G ∈ F such that ex(n; G) ≪_F ex(n; F)?

That is, there exists a constant C (depending on F) such that
  ex(n; G) ≤ C · ex(n; F) for all n ≥ 1.

A problem of Erdős and Simonovits [ErSi82].

See also Problem #180.
-/

/-- An injective graph homomorphism from H to G: G contains a copy of H as a subgraph. -/
def containsSubgraph575 {V U : Type*} (G : SimpleGraph V) (H : SimpleGraph U) : Prop :=
  ∃ f : U → V, Function.Injective f ∧ ∀ u v : U, H.Adj u v → G.Adj (f u) (f v)

/-- The Turán number ex(n; H): the maximum number of edges in a simple graph on n
    vertices that contains no copy of H as a subgraph. -/
noncomputable def turanNumber575 {U : Type*} (H : SimpleGraph U) (n : ℕ) : ℕ :=
  sSup {m : ℕ | ∃ (V : Type) (fv : Fintype V) (F : SimpleGraph V) (dr : DecidableRel F.Adj),
    haveI := fv; haveI := dr;
    Fintype.card V = n ∧ ¬containsSubgraph575 F H ∧ F.edgeFinset.card = m}

/-- The Turán number for a family ex(n; F): the maximum number of edges in a simple
    graph on n vertices that contains no copy of any member of the family F as a
    subgraph. -/
noncomputable def turanNumberFamily575
    {ι : Type*} [Fintype ι]
    {k : ι → ℕ} (H : (i : ι) → SimpleGraph (Fin (k i))) (n : ℕ) : ℕ :=
  sSup {m : ℕ | ∃ (V : Type) (fv : Fintype V) (F : SimpleGraph V) (dr : DecidableRel F.Adj),
    haveI := fv; haveI := dr;
    Fintype.card V = n ∧ (∀ i : ι, ¬containsSubgraph575 F (H i)) ∧ F.edgeFinset.card = m}

/-- A graph is bipartite if there is a 2-colouring of its vertices such that
    every edge connects vertices of different colours. -/
def IsBipartite575 {V : Type*} (G : SimpleGraph V) : Prop :=
  ∃ f : V → Fin 2, ∀ u v : V, G.Adj u v → f u ≠ f v

/--
Erdős Conjecture (Problem #575) [ErSi82]:

If F is a finite set of finite graphs containing at least one bipartite graph, then
there exists a bipartite G ∈ F such that ex(n; G) ≤ C · ex(n; F) for some constant
C depending on F and all n ≥ 1.

This strengthens Problem #180 by requiring the witness graph G to be bipartite
(under the hypothesis that F contains at least one bipartite member).

See also [180].
-/
theorem erdos_problem_575 :
    ∀ (ι : Type) [Fintype ι] [Nonempty ι]
      (k : ι → ℕ) (H : (i : ι) → SimpleGraph (Fin (k i))),
    (∃ i : ι, IsBipartite575 (H i)) →
    ∃ i : ι,
    IsBipartite575 (H i) ∧
    ∃ C : ℝ, 0 < C ∧
    ∀ n : ℕ, 1 ≤ n →
      (turanNumber575 (H i) n : ℝ) ≤ C * (turanNumberFamily575 H n : ℝ) :=
  sorry

end
