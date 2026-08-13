import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Order.Floor.Semiring

open SimpleGraph Finset

/--
A simple graph contains a 6-cycle (C₆) if there exist six distinct vertices
a, b, c, d, e, f forming a cycle a-b-c-d-e-f-a.
-/
def SimpleGraph.ContainsCycle6 {V : Type*} (G : SimpleGraph V) : Prop :=
  ∃ (a b c d e f : V),
    a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ a ≠ e ∧ a ≠ f ∧
    b ≠ c ∧ b ≠ d ∧ b ≠ e ∧ b ≠ f ∧
    c ≠ d ∧ c ≠ e ∧ c ≠ f ∧
    d ≠ e ∧ d ≠ f ∧
    e ≠ f ∧
    G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d e ∧ G.Adj e f ∧ G.Adj f a

/--
The number of edges in a simple graph on Fin n.
-/
noncomputable def SimpleGraph.numEdges {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] : ℕ :=
  ((univ ×ˢ univ).filter
    fun p : Fin n × Fin n => p.1 < p.2 ∧ G.Adj p.1 p.2).card

/--
Erdős Problem #1080 [Er75] [Er79g]:

Let G be a bipartite graph on n vertices such that one part has ⌊n^{2/3}⌋
vertices. Is there a constant c > 0 such that if G has at least cn edges
then G must contain a C₆?

The answer is no, as shown by De Caen and Székely [DeSz92]. They proved that
for bipartite graphs between n and ⌊n^{2/3}⌋ vertices avoiding both C₄ and C₆,
the maximum number of edges is between n^{58/57+o(1)} and n^{10/9}, both of
which grow faster than cn. Lazebnik, Ustimenko, and Woldar [LUW94] improved
the lower bound to n^{16/15+o(1)}. De Caen and Székely (and, independently,
Faudree and Simonovits) also proved more generally that f(n,m) ≪ (nm)^{2/3}
for n^{1/2} ≤ m ≤ n, where f(n,m) is the maximum number of edges of a
bipartite graph between n and m vertices containing neither C₄ nor C₆.

Status on erdosproblems.com (page edition 14 October 2025): DISPROVED (LEAN) —
solved in the negative and the proof verified in Lean (formalized statement in
google-deepmind/formal-conjectures, FormalConjectures/ErdosProblems/1080.lean;
per that file, proved in Lean by Alexeev using Aristotle).

We formalise the disproof: for every c > 0, there exists a (nonempty) bipartite
graph with one part of size ⌊n^{2/3}⌋ having at least cn edges but no C₆.
The condition 0 < n is required: without it, n = 0 with the empty graph would
be a degenerate witness for every c (the part has 0 = ⌊0^{2/3}⌋ vertices,
0 ≥ c·0 edges, and vacuously no C₆), making the statement trivially true.

References:
[Er75] Erdős, P., Some recent progress on extremal problems in graph theory.
  Congr. Numer. (1975), 3-14.
[Er79g] Erdős, P., original problem statement (1979).
[DeSz92] de Caen, D. and Székely, L. A., The maximum size of 4- and 6-cycle
  free bipartite graphs on m,n vertices. (1992), 135-142.
[LUW94] Lazebnik, F. and Ustimenko, V. A. and Woldar, A. J., New constructions
  of bipartite graphs on m,n vertices with many edges and without small
  cycles. J. Combin. Theory Ser. B (1994), 111-117.
-/
theorem erdos_problem_1080 :
    ∀ (c : ℝ), 0 < c →
      ∃ (n : ℕ) (G : SimpleGraph (Fin n)) (_ : DecidableRel G.Adj),
        -- n is positive (the n = 0 empty graph would be a degenerate witness)
        0 < n ∧
        -- G is bipartite with one part of size ⌊n^{2/3}⌋
        (∃ (f : Fin n → Fin 2),
          (∀ u v, G.Adj u v → f u ≠ f v) ∧
          (univ.filter (fun v => f v = 0)).card =
            Nat.floor ((n : ℝ) ^ ((2 : ℝ) / 3))) ∧
        -- G has at least cn edges
        (G.numEdges : ℝ) ≥ c * n ∧
        -- G contains no C₆
        ¬G.ContainsCycle6 :=
  sorry

/--
A simple graph contains an 8-cycle (C₈) if there exist eight distinct vertices
a, b, c, d, e, f, g, h forming a cycle a-b-c-d-e-f-g-h-a.
-/
def SimpleGraph.ContainsCycle8 {V : Type*} (G : SimpleGraph V) : Prop :=
  ∃ (a b c d e f g h : V),
    a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ a ≠ e ∧ a ≠ f ∧ a ≠ g ∧ a ≠ h ∧
    b ≠ c ∧ b ≠ d ∧ b ≠ e ∧ b ≠ f ∧ b ≠ g ∧ b ≠ h ∧
    c ≠ d ∧ c ≠ e ∧ c ≠ f ∧ c ≠ g ∧ c ≠ h ∧
    d ≠ e ∧ d ≠ f ∧ d ≠ g ∧ d ≠ h ∧
    e ≠ f ∧ e ≠ g ∧ e ≠ h ∧
    f ≠ g ∧ f ≠ h ∧
    g ≠ h ∧
    G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d e ∧ G.Adj e f ∧ G.Adj f g ∧
      G.Adj g h ∧ G.Adj h a

/--
Variant (confirmed by the source page): Erdős [Er75] says "it is easy to see
that it contains a C₈" — i.e. in the setting of the main problem there IS a
constant c > 0 such that every (nonempty) bipartite graph on n vertices with
one part of size ⌊n^{2/3}⌋ and at least cn edges contains an 8-cycle. The
hypothesis 0 < n is required: for n = 0 the empty graph has ≥ c·0 edges and
no C₈, which would falsify the statement.

NOTE: this variant statement is NOT compile-verified (added during review;
this container cannot run lake build).
-/
theorem erdos_problem_1080.variants.contains_c8 :
    ∃ (c : ℝ), 0 < c ∧
      ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (_ : DecidableRel G.Adj),
        0 < n →
        (∃ (f : Fin n → Fin 2),
          (∀ u v, G.Adj u v → f u ≠ f v) ∧
          (univ.filter (fun v => f v = 0)).card =
            Nat.floor ((n : ℝ) ^ ((2 : ℝ) / 3))) →
        (G.numEdges : ℝ) ≥ c * n →
        G.ContainsCycle8 :=
  sorry
