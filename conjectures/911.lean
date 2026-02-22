import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Nat.Lattice
import Mathlib.SetTheory.Cardinal.Finite

open SimpleGraph

noncomputable section

/-!
# Erdős Problem #911

Let R̂(G) denote the size Ramsey number, the minimal number of edges m such
that there is a graph H with m edges such that in any 2-colouring of the
edges of H there is a monochromatic copy of G.

Is there a function f such that f(x)/x → ∞ as x → ∞ such that, for all
large C, if G is a graph with n vertices and e ≥ Cn edges then
R̂(G) > f(C) · e?

https://www.erdosproblems.com/911

Tags: graph theory, ramsey theory
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
Erdős Problem #911 [Er82e, p.78]:

There exists a function f : ℕ → ℕ with f(x)/x → ∞ as x → ∞ such that,
for all sufficiently large C, if G is any graph with n vertices and at
least C · n edges then R̂(G) > f(C) · |E(G)|.
-/
theorem erdos_problem_911 :
    ∃ f : ℕ → ℕ,
      -- f(x)/x → ∞ as x → ∞
      (∀ M : ℕ, ∃ x₀ : ℕ, ∀ x : ℕ, x ≥ x₀ → f x ≥ M * x) ∧
      -- For all large C, the bound holds
      ∃ C₀ : ℕ, ∀ C : ℕ, C ≥ C₀ →
        ∀ n : ℕ, ∀ G : SimpleGraph (Fin n),
          Nat.card G.edgeSet ≥ C * n →
          sizeRamseyNumber G > f C * Nat.card G.edgeSet :=
  sorry

end
