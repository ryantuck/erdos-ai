import Mathlib.Combinatorics.SimpleGraph.Coloring
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Nat.Lattice

open SimpleGraph

noncomputable section

/-!
# Erdős Problem #762

The cochromatic number of G, denoted by ζ(G), is the minimum number of colours
needed to colour the vertices of G such that each colour class induces either a
complete graph or empty graph.

Is it true that if G has no K_5 and ζ(G) ≥ 4 then χ(G) ≤ ζ(G) + 2?

A conjecture of Erdős, Gimbel, and Straight [EGS90], who proved that for every
n > 2 there exists some f(n) such that if G contains no clique on n vertices
then χ(G) ≤ ζ(G) + f(n).

This has been disproved by Steiner [St24b], who constructed a graph G with
ω(G) = 4, ζ(G) = 4, and χ(G) = 7.

Tags: graph theory, chromatic number
-/

/-- A cochromatic colouring: each colour class induces either a complete
    subgraph or an independent set. -/
def IsCochromaticColouring762 {V : Type*} (G : SimpleGraph V) (k : ℕ)
    (c : V → Fin k) : Prop :=
  ∀ i : Fin k,
    (∀ u v, c u = i → c v = i → u ≠ v → G.Adj u v) ∨
    (∀ u v, c u = i → c v = i → u ≠ v → ¬G.Adj u v)

/-- The cochromatic number ζ(G): minimum number of colours in a cochromatic
    colouring. -/
noncomputable def cochromaticNumber762 {V : Type*} [Fintype V]
    (G : SimpleGraph V) : ℕ :=
  sInf {k : ℕ | ∃ c : V → Fin k, IsCochromaticColouring762 G k c}

/--
**Erdős Problem #762** (DISPROVED, Steiner [St24b]):

Is it true that if G has no K_5 and ζ(G) ≥ 4 then χ(G) ≤ ζ(G) + 2?

Steiner constructed a counterexample: a graph G with ω(G) = 4, ζ(G) = 4,
and χ(G) = 7 > ζ(G) + 2 = 6.
-/
theorem erdos_problem_762 :
    ∀ (n : ℕ) (G : SimpleGraph (Fin n)),
      G.CliqueFree 5 →
        cochromaticNumber762 G ≥ 4 →
          G.chromaticNumber ≤ cochromaticNumber762 G + 2 :=
  sorry

end
