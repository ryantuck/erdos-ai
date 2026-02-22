import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Walks.Basic
import Mathlib.Combinatorics.SimpleGraph.Paths

noncomputable section

/-!
# Erdős Problem #642

Let $f(n)$ be the maximal number of edges in a graph on $n$ vertices such that
all cycles have more vertices than chords. Is it true that $f(n) \ll n$?

A chord is an edge between two vertices of the cycle which are not consecutive
in the cycle. A problem of Hamburger and Szegedy.

Chen, Erdős, and Staton [CES96] proved $f(n) \ll n^{3/2}$. Draganić, Methuku,
Munhá Correia, and Sudakov [DMMS24] improved this to $f(n) \ll n(\log n)^8$.
-/

namespace SimpleGraph.Walk

variable {V : Type*} [Fintype V] [DecidableEq V]
         {G : SimpleGraph V} [DecidableRel G.Adj]

/-- The number of chords of a walk in a graph. A chord is an edge of G
    connecting two vertices that appear in the walk's support but is not
    itself an edge traversed by the walk. -/
def numChords {u v : V} (p : G.Walk u v) : ℕ :=
  (G.edgeFinset.filter (fun e =>
    (∀ w, w ∈ e → w ∈ p.support.toFinset) ∧ e ∉ p.edges.toFinset)).card

end SimpleGraph.Walk

open SimpleGraph

/--
Erdős Problem #642 [CES96][Er97d]:

There exists a constant $C$ such that for all $n$, every graph $G$ on $n$
vertices in which every cycle has strictly more vertices than chords has at
most $C \cdot n$ edges.
-/
theorem erdos_problem_642 :
    ∃ C : ℕ, ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      (∀ (v : Fin n) (p : G.Walk v v), p.IsCycle →
        p.support.toFinset.card > p.numChords) →
      G.edgeFinset.card ≤ C * n :=
  sorry

end
