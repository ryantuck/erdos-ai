import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Real.Basic

open SimpleGraph

/--
An induced cycle of length k in a simple graph G: an injective map f : Fin k → V
such that G.Adj (f i) (f j) holds if and only if i and j are consecutive modulo k.
This captures the notion that f traces out a cycle with no chords.
-/
def HasInducedCycle {V : Type*} (G : SimpleGraph V) (k : ℕ) : Prop :=
  ∃ f : Fin k → V, Function.Injective f ∧
    ∀ i j : Fin k, i ≠ j →
      (G.Adj (f i) (f j) ↔ (i.val + 1) % k = j.val ∨ (j.val + 1) % k = i.val)

/--
A graph is chordal if it contains no induced cycle of length ≥ 4.
Equivalently, every cycle of length ≥ 4 has a chord.
-/
def IsChordal {V : Type*} (G : SimpleGraph V) : Prop :=
  ∀ k : ℕ, 4 ≤ k → ¬HasInducedCycle G k

/--
Erdős Problem #81 (Erdős, Ordman, Zalcstein [EOZ93]):

Let G be a chordal graph on n vertices — that is, G has no induced cycles of
length greater than 3. Can the edges of G be partitioned into n²/6 + O(n)
many cliques?

The example of all edges between a complete graph on n/3 vertices and an empty
graph on 2n/3 vertices shows that n²/6 + O(n) is sometimes necessary.

Formalized as: there exists a constant C > 0 such that for all n and all
chordal graphs G on n vertices, there exists a collection P of cliques
(vertex sets, each pairwise adjacent in G) that partition the edges of G,
with |P| ≤ n²/6 + C·n.
-/
theorem erdos_problem_81 :
    ∃ C : ℝ, 0 < C ∧
    ∀ n : ℕ, ∀ G : SimpleGraph (Fin n),
      IsChordal G →
      ∃ P : Finset (Finset (Fin n)),
        -- Each set in P is a clique in G
        (∀ S ∈ P, G.IsClique (↑S : Set (Fin n))) ∧
        -- Every edge of G is covered by some clique in P
        (∀ u v : Fin n, G.Adj u v → ∃ S ∈ P, u ∈ S ∧ v ∈ S) ∧
        -- No edge belongs to two distinct cliques (partition, not just cover)
        (∀ S₁ ∈ P, ∀ S₂ ∈ P, S₁ ≠ S₂ →
          ∀ u v : Fin n, u ∈ S₁ → v ∈ S₁ → u ∈ S₂ → v ∈ S₂ → ¬G.Adj u v) ∧
        -- The number of cliques is at most n²/6 + C·n
        (P.card : ℝ) ≤ (n : ℝ) ^ 2 / 6 + C * (n : ℝ) :=
  sorry
