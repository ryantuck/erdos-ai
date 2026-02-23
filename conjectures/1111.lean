import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.Coloring

noncomputable section
open SimpleGraph Classical

namespace Erdos1111

/-- Two disjoint sets of vertices A, B are anticomplete in G if there are no edges
    between any vertex in A and any vertex in B. -/
def Anticomplete {V : Type*} (G : SimpleGraph V) (A B : Set V) : Prop :=
  Disjoint A B ∧ ∀ a ∈ A, ∀ b ∈ B, ¬G.Adj a b

/--
Erdős Problem #1111 (Open) — El Zahar and Erdős [ElEr85]:

If t, c ≥ 1 then there exists d ≥ 1 such that if G is a finite graph with
χ(G) ≥ d and ω(G) < t, then there exist anticomplete sets A, B ⊆ V(G) with
χ(G[A]) ≥ c and χ(G[B]) ≥ c.

Two disjoint vertex sets A, B are anticomplete if there are no edges between them.
χ denotes the chromatic number and ω the clique number. The condition ω(G) < t
is expressed as G.CliqueFree t (no clique of size t exists).

El Zahar and Erdős show it suffices to consider t ≤ c. Let d(t,c) be the minimal
such d. Known bounds include d(t,2) ≤ C(t,2)+1 (via Wagon [Wa80b]) and
d(3,3) ≤ 8.
-/
theorem erdos_problem_1111 (t c : ℕ) (ht : 1 ≤ t) (hc : 1 ≤ c) :
    ∃ d : ℕ, 1 ≤ d ∧
      ∀ (n : ℕ) (G : SimpleGraph (Fin n)),
        (d : ℕ∞) ≤ G.chromaticNumber →
        G.CliqueFree t →
        ∃ (A B : Set (Fin n)),
          Anticomplete G A B ∧
          (c : ℕ∞) ≤ (G.induce A).chromaticNumber ∧
          (c : ℕ∞) ≤ (G.induce B).chromaticNumber :=
  sorry

end Erdos1111
