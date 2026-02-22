import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Nat.Lattice
import Mathlib.Data.Set.Card

open SimpleGraph

noncomputable section

/-!
# Erdős Problem #767

Let g_k(n) be the maximal number of edges possible on a graph with n vertices
which does not contain a cycle with k chords incident to a vertex on the cycle.
Is it true that g_k(n) = (k+1)n - (k+1)² for n sufficiently large?

Czipszer proved that g_k(n) exists for all k, and in fact g_k(n) ≤ (k+1)n.
Pósa proved that g_1(n) = 2n - 4 for n ≥ 4.
The conjectured equality was proved for n ≥ 3k + 3 by Jiang [Ji04].

Tags: graph theory, turan number
-/

/-- A graph G contains a cycle with at least k chords incident to a single vertex.
    That is, there exists a simple cycle (given by an injective map f : Fin m → V
    tracing consecutive adjacent vertices) and a vertex f(i₀) on the cycle that
    is adjacent to at least k other cycle vertices which are not its two
    cycle-neighbors. -/
def HasCycleWithKChords {V : Type*} (G : SimpleGraph V) (k : ℕ) : Prop :=
  ∃ (m : ℕ) (hm : m ≥ 3) (f : Fin m → V),
    Function.Injective f ∧
    (∀ i : Fin m, G.Adj (f i) (f ⟨(i.val + 1) % m, Nat.mod_lt _ (by omega)⟩)) ∧
    ∃ i₀ : Fin m,
      k ≤ Set.ncard {j : Fin m |
        j ≠ i₀ ∧
        j.val ≠ (i₀.val + 1) % m ∧
        j.val ≠ (i₀.val + m - 1) % m ∧
        G.Adj (f i₀) (f j)}

/-- g_k(n): the maximum number of edges in a simple graph on n vertices that
    does not contain a cycle with k chords incident to a vertex. -/
noncomputable def maxEdgesAvoidingCycleChords (k n : ℕ) : ℕ :=
  sSup {e : ℕ | ∃ G : SimpleGraph (Fin n),
    ¬HasCycleWithKChords G k ∧ G.edgeSet.ncard = e}

/--
**Erdős Problem #767** (PROVED by Jiang [Ji04]):

For all k ≥ 1, g_k(n) = (k+1)n - (k+1)² for all sufficiently large n.
-/
theorem erdos_problem_767 (k : ℕ) (hk : k ≥ 1) :
    ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n →
      maxEdgesAvoidingCycleChords k n = (k + 1) * n - (k + 1) ^ 2 :=
  sorry

end
