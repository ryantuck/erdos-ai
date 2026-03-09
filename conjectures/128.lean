import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Card

/-!
# Erdős Problem #128

A problem of Erdős and Rousseau. Let G be a graph with n vertices such that every
induced subgraph on at least ⌊n/2⌋ vertices has more than n²/50 edges. Must G
contain a triangle?

The constant 50 is best possible, as witnessed by a blow-up of C₅ or the Petersen graph.
-/

/--
The number of edges in the induced subgraph of G on vertex set S.
-/
noncomputable def inducedEdgeCount {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) : ℕ :=
  ((S ×ˢ S).filter fun p : V × V => p.1 ≠ p.2 ∧ G.Adj p.1 p.2).card / 2

/--
Erdős Problem #128 (Erdős–Rousseau) [Er93, ErRo93, Er97b]:
Let G be a graph with n vertices such that every induced subgraph on at least
⌊n/2⌋ vertices has more than n²/50 edges. Then G contains a triangle.
-/
theorem erdos_problem_128 {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (n : ℕ) (hn : Fintype.card V = n)
    (h : ∀ S : Finset V, n / 2 ≤ S.card →
      50 * inducedEdgeCount G S > n ^ 2) :
    ∃ (a b c : V), a ≠ b ∧ b ≠ c ∧ a ≠ c ∧ G.Adj a b ∧ G.Adj b c ∧ G.Adj a c :=
  sorry
