import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Card

open SimpleGraph

/-- A graph G contains a triangle if there exist three mutually adjacent vertices. -/
def HasTriangle {V : Type*} (G : SimpleGraph V) : Prop :=
  ∃ a b c : V, G.Adj a b ∧ G.Adj b c ∧ G.Adj a c

/--
The number of edges in the subgraph of G induced on vertex set S ⊆ V.

We count ordered adjacent pairs (u, v) with u ≠ v both in S, then divide by 2.
Since G.Adj is symmetric, each undirected edge {u, v} contributes exactly two
ordered pairs (u, v) and (v, u), so the division is exact.
-/
noncomputable def inducedEdgeCount {V : Type*} [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) : ℕ :=
  (S.offDiag.filter (fun p : V × V => G.Adj p.1 p.2)).card / 2

/--
Erdős Problem #128 (Erdős-Rousseau [Er93, ErRo93, Er97b]):
Let G be a finite simple graph on n vertices such that every induced subgraph on
at least ⌊n/2⌋ vertices has more than n²/50 edges. Must G contain a triangle?

The constant 50 would be best possible, as witnessed by a blow-up of C₅ or
the Petersen graph (both triangle-free graphs with local edge density ≈ n²/50).

Partial results:
- Erdős, Faudree, Rousseau, and Schelp [EFRS94] proved the result with 50
  replaced by 16. More generally, they showed: for any 0 < α < 1, if every set
  of ≥ αn vertices spans more than α³n²/2 edges, then G contains a triangle.
- Krivelevich [Kr95] proved the result with n/2 replaced by 3n/5 (and 50 by 25).
- Keevash and Sudakov [KeSu06] proved it under the additional assumption that
  G has at most n²/12 or at least n²/5 edges.
- Razborov [Ra22] proved the result with 1/50 replaced by 27/1024.
-/
theorem erdos_problem_128 :
    ∀ (V : Type*) [Fintype V] [DecidableEq V]
      (G : SimpleGraph V) [DecidableRel G.Adj],
      let n := Fintype.card V
      (∀ (S : Finset V), n / 2 ≤ S.card →
        (n : ℝ) ^ 2 / 50 < (inducedEdgeCount G S : ℝ)) →
      HasTriangle G :=
  sorry
