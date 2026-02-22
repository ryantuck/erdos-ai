import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Lattice

noncomputable section

/-!
# Erdős Problem #832

Let r ≥ 3 and k be sufficiently large in terms of r. Is it true that every
r-uniform hypergraph with chromatic number k has at least C((r-1)(k-1)+1, r)
edges, with equality only for the complete graph on (r-1)(k-1)+1 vertices?

When r = 2 it is a classical fact that chromatic number k implies at least
C(k, 2) edges. Erdős asked for k to be large since he knew the conjecture to
be false for r = k = 3 (Steiner triples with 7 vertices and 7 edges).

This was disproved by Alon [Al85] for all r ≥ 4. The case r = 3 remains open.

Tags: graph theory, hypergraphs, chromatic number
-/

/-- An r-uniform hypergraph on a finite vertex set V: a collection of
    r-element subsets of V. -/
structure UniformHypergraph (V : Type*) [DecidableEq V] (r : ℕ) where
  edges : Finset (Finset V)
  uniform : ∀ e ∈ edges, e.card = r

/-- A proper k-coloring of a hypergraph: a vertex coloring such that no edge
    is monochromatic (for every edge, not all vertices receive the same color). -/
def UniformHypergraph.IsProperColoring {V : Type*} [DecidableEq V] {r : ℕ}
    (H : UniformHypergraph V r) (k : ℕ) (f : V → Fin k) : Prop :=
  ∀ e ∈ H.edges, ∀ c : Fin k, ∃ v ∈ e, f v ≠ c

/-- The chromatic number of a uniform hypergraph: the minimum number of colors
    needed for a proper coloring (no monochromatic edge). -/
noncomputable def UniformHypergraph.chromaticNumber {V : Type*} [DecidableEq V]
    [Fintype V] {r : ℕ} (H : UniformHypergraph V r) : ℕ :=
  sInf {k : ℕ | k ≥ 1 ∧ ∃ f : V → Fin k, H.IsProperColoring k f}

/--
**Erdős Problem #832** [Er74d]:

For r ≥ 3 and k sufficiently large (in terms of r), every r-uniform hypergraph
with chromatic number k has at least C((r-1)(k-1)+1, r) edges.

This conjecture was disproved by Alon [Al85] for all r ≥ 4.
The case r = 3 remains open.
-/
theorem erdos_problem_832 (r : ℕ) (hr : r ≥ 3) :
    ∃ k₀ : ℕ, ∀ k : ℕ, k ≥ k₀ →
    ∀ (V : Type) [DecidableEq V] [Fintype V] (H : UniformHypergraph V r),
      H.chromaticNumber = k →
      H.edges.card ≥ Nat.choose ((r - 1) * (k - 1) + 1) r :=
  sorry

end
