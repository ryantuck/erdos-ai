import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Nat.Lattice
import Mathlib.SetTheory.Cardinal.Finite

open SimpleGraph

noncomputable section

/-!
# Erdős Problem #559 (DISPROVED)

Let R̂(G) denote the size Ramsey number, the minimal number of edges m such
that there is a graph H with m edges that is Ramsey for G (every 2-coloring
of the edges of H contains a monochromatic copy of G).

The conjecture: if G has n vertices and maximum degree d then R̂(G) ≪_d n
(i.e., R̂(G) ≤ C_d · n for some constant C_d depending only on d).

This was disproved by Rödl and Szemerédi [RoSz00] for d = 3, who
constructed graphs on n vertices with maximum degree 3 such that
R̂(G) ≫ n (log n)^c for some absolute constant c > 0.
-/

/-- The size Ramsey number R̂(G): the minimum number of edges in a graph H
    that is Ramsey for G.

    A graph H on N vertices is Ramsey for G if every 2-coloring of the edges
    of H (represented as a symmetric function c : Fin N → Fin N → Bool)
    contains a monochromatic copy of G, i.e., an injective map f from the
    vertices of G into Fin N that preserves adjacency in H and maps all
    edges to the same color. -/
noncomputable def sizeRamseyNumber {V : Type*} [Fintype V]
    (G : SimpleGraph V) : ℕ :=
  sInf {m : ℕ | ∃ (N : ℕ) (H : SimpleGraph (Fin N)),
    Nat.card H.edgeSet = m ∧
    ∀ (c : Fin N → Fin N → Bool),
      (∀ i j, c i j = c j i) →
      ∃ (b : Bool) (f : V → Fin N),
        Function.Injective f ∧
        (∀ u v, G.Adj u v → H.Adj (f u) (f v)) ∧
        (∀ u v, G.Adj u v → c (f u) (f v) = b)}

/--
Erdős Problem #559 (DISPROVED):

The original conjecture states: for every d ≥ 1, there exists a constant C
(depending only on d) such that for all n ≥ 1 and all graphs G on n vertices
with maximum degree at most d, the size Ramsey number satisfies R̂(G) ≤ C · n.

This was disproved by Rödl and Szemerédi [RoSz00] for d = 3.
-/
theorem erdos_problem_559 :
    ¬ (∀ d : ℕ, d ≥ 1 →
      ∃ C : ℕ, ∀ n : ℕ, n ≥ 1 →
        ∀ G : SimpleGraph (Fin n),
          (∀ v, Nat.card (G.neighborSet v) ≤ d) →
            sizeRamseyNumber G ≤ C * n) :=
  sorry

end
