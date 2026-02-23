import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Basic

/--
An independent set of a simple graph within a vertex subset S:
a subset I ⊆ S such that no two vertices in I are adjacent in G.
-/
def SimpleGraph.IndepSetIn {V : Type*} (G : SimpleGraph V)
    (I S : Finset V) : Prop :=
  I ⊆ S ∧ ∀ ⦃u⦄, u ∈ I → ∀ ⦃v⦄, v ∈ I → u ≠ v → ¬G.Adj u v

/--
Erdős Problem #73:
Let k ≥ 0. If G is a finite graph such that every induced subgraph H on n
vertices contains an independent set of size ≥ (n - k) / 2, then there exists
a set S of O_k(1) vertices whose removal makes G bipartite.

Equivalently: for every k, there exists a constant C (depending only on k)
such that for any finite graph G on n vertices, if every vertex subset S
contains an independent set of size at least (|S| - k) / 2, then G can be
made bipartite by removing at most C vertices.

Proved by Reed [Re99].
-/
theorem erdos_problem_73 :
    ∀ k : ℕ, ∃ C : ℕ,
      ∀ (n : ℕ) (G : SimpleGraph (Fin n)),
        (∀ S : Finset (Fin n), ∃ I : Finset (Fin n), G.IndepSetIn I S ∧
          2 * I.card ≥ S.card - k) →
        ∃ T : Finset (Fin n), T.card ≤ C ∧
          ∃ f : Fin n → Bool, ∀ ⦃u v⦄, u ∉ T → v ∉ T → G.Adj u v → f u ≠ f v :=
  sorry
