import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Nat.Lattice

open SimpleGraph

noncomputable section

/-!
# Erdős Problem #758

The cochromatic number of G, denoted ζ(G), is the minimum number of colours
needed to colour the vertices of G such that each colour class induces either
a complete graph or an empty graph (independent set). Let z(n) be the maximum
value of ζ(G) over all graphs G with n vertices.

Determine z(n) for small values of n. In particular is it true that z(12) = 4?

A question of Erdős and Gimbel [ErGi93], who knew that 4 ≤ z(12) ≤ 5 and
5 ≤ z(15) ≤ 6. This was resolved: z(12) = 4, confirmed computationally by
Bhavik Mehta. Gimbel [Gi86] showed that z(n) ≍ n/log n.
-/

/-- A cochromatic coloring of a simple graph G with k colors is a function
    c : V → Fin k such that each color class is either a clique (all pairs
    adjacent) or an independent set (no pairs adjacent). -/
def IsCochromaticColoring {V : Type*} (G : SimpleGraph V) (k : ℕ)
    (c : V → Fin k) : Prop :=
  ∀ i : Fin k,
    (∀ u v : V, c u = i → c v = i → u ≠ v → G.Adj u v) ∨
    (∀ u v : V, c u = i → c v = i → u ≠ v → ¬G.Adj u v)

/-- The cochromatic number ζ(G): the minimum number of colors needed for a
    cochromatic coloring of G. -/
noncomputable def cochromaticNumber {V : Type*} [Fintype V]
    (G : SimpleGraph V) : ℕ :=
  sInf {k : ℕ | ∃ c : V → Fin k, IsCochromaticColoring G k c}

/-- z(n): the maximum cochromatic number over all simple graphs on n
    vertices. -/
noncomputable def maxCochromaticNumber (n : ℕ) : ℕ :=
  sSup {k : ℕ | ∃ G : SimpleGraph (Fin n), cochromaticNumber G = k}

/--
Erdős Problem #758 [ErGi93]:

Is it true that z(12) = 4, where z(n) is the maximum cochromatic number
over all graphs on n vertices?

Resolved: z(12) = 4 (confirmed computationally by Bhavik Mehta).
-/
theorem erdos_problem_758 : maxCochromaticNumber 12 = 4 := sorry

end
