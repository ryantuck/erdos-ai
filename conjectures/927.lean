import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Set.Card
import Mathlib.Data.Nat.Log

noncomputable section

/-!
# Erdős Problem #927

Let g(n) be the maximum number of different sizes of cliques (maximal complete
subgraphs) that can occur in a graph on n vertices. Is it true that

  g(n) = n - log₂ n - log*(n) + O(1),

where log*(n) is the iterated logarithm (the number of times the logarithm
must be applied before the result is less than 1)?

DISPROVED by Spencer [Sp71], who proved that g(n) > n - log₂ n - O(1),
showing the log* correction term is unnecessary.

See also [775].
-/

/-- A set of vertices forms a clique (complete subgraph) in G if every pair
    of distinct vertices in the set is adjacent. -/
def isCliqueSet {n : ℕ} (G : SimpleGraph (Fin n)) (S : Finset (Fin n)) : Prop :=
  ∀ u ∈ S, ∀ v ∈ S, u ≠ v → G.Adj u v

/-- A maximal clique: a clique not properly contained in any other clique. -/
def isMaxCliqueSet {n : ℕ} (G : SimpleGraph (Fin n))
    (S : Finset (Fin n)) : Prop :=
  isCliqueSet G S ∧ ∀ T : Finset (Fin n), S ⊂ T → ¬isCliqueSet G T

/-- The set of distinct sizes of maximal cliques in a simple graph. -/
def graphCliqueSizes {n : ℕ} (G : SimpleGraph (Fin n)) : Set ℕ :=
  {m : ℕ | ∃ S : Finset (Fin n), isMaxCliqueSet G S ∧ S.card = m}

/--
Erdős Problem #927 (DISPROVED by Spencer [Sp71]):

For every n, there exists a graph on n vertices with at least n - ⌊log₂ n⌋ - C
distinct maximal clique sizes, for some absolute constant C.

This disproves Erdős's conjecture that g(n) = n - log₂ n - log*(n) + O(1),
since log*(n) → ∞.
-/
theorem erdos_problem_927 :
    ∃ C : ℕ, ∀ n : ℕ, ∃ G : SimpleGraph (Fin n),
      (graphCliqueSizes G).ncard + C ≥ n - Nat.log 2 n :=
  sorry

end
