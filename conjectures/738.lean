import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Coloring
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Maps

open SimpleGraph

noncomputable section

/-!
# Erdős Problem #738

If $G$ has infinite chromatic number and is triangle-free (contains no $K_3$)
then must $G$ contain every tree as an induced subgraph?

A conjecture of Gyárfás [Er81].

https://www.erdosproblems.com/738
-/

/-- A graph has infinite chromatic number: it cannot be properly colored
    with finitely many colors. -/
def HasInfiniteChromaticNumber {V : Type*} (G : SimpleGraph V) : Prop :=
  ∀ n : ℕ, IsEmpty (G.Coloring (Fin n))

/--
Erdős Problem #738 (Gyárfás conjecture) [Er81]:

If G is a graph with infinite chromatic number and G is triangle-free
(contains no K₃), then G contains every finite tree as an induced subgraph.
-/
theorem erdos_problem_738 {V : Type*} (G : SimpleGraph V)
    (hchrom : HasInfiniteChromaticNumber G)
    (htri : G.CliqueFree 3) :
    ∀ (m : ℕ) (T : SimpleGraph (Fin m)), T.IsTree →
      Nonempty (T ↪g G) :=
  sorry

end
