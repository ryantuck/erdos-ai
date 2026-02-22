import Mathlib.Combinatorics.SimpleGraph.Coloring
import Mathlib.Data.Nat.Lattice

open SimpleGraph

noncomputable section

/-!
# Erdős Problem #630

The list chromatic number χ_L(G) is the minimal k such that for any assignment
of a list of k colours to each vertex of G (perhaps different lists for different
vertices) a colouring of each vertex by a colour on its list can be chosen such
that adjacent vertices receive distinct colours.

Does every planar bipartite graph G have χ_L(G) ≤ 3?

A problem of Erdős, Rubin, and Taylor [ERT80]. The answer is yes, proved by
Alon and Tarsi [AlTa92].
-/

/-- A proper list coloring of G with respect to a list assignment L : V → Finset ℕ
    is a function f : V → ℕ such that f(v) ∈ L(v) for all v, and f(u) ≠ f(v)
    whenever u and v are adjacent. -/
def IsProperListColoring {V : Type*} (G : SimpleGraph V) (L : V → Finset ℕ)
    (f : V → ℕ) : Prop :=
  (∀ v, f v ∈ L v) ∧ (∀ u v, G.Adj u v → f u ≠ f v)

/-- A graph G is k-choosable (k-list-colorable) if for every list assignment L
    where each vertex receives a list of at least k colors, there exists a
    proper list coloring. -/
def IsChoosable {V : Type*} (G : SimpleGraph V) (k : ℕ) : Prop :=
  ∀ L : V → Finset ℕ, (∀ v, k ≤ (L v).card) →
    ∃ f : V → ℕ, IsProperListColoring G L f

/-- The list chromatic number (choice number) of a graph G: the minimum k
    such that G is k-choosable. -/
noncomputable def listChromaticNumber {V : Type*} (G : SimpleGraph V) : ℕ :=
  sInf {k : ℕ | IsChoosable G k}

/-- A graph is planar if it can be embedded in the plane without edge crossings.
    Mathlib does not yet have a formalization of graph planarity; we define it
    here as an opaque predicate. -/
def SimpleGraph.IsPlanar {V : Type*} [Fintype V] (G : SimpleGraph V) : Prop :=
  sorry

/--
Erdős Problem #630 [ERT80]:

Every planar bipartite graph G is 3-choosable, i.e., χ_L(G) ≤ 3.

Proved by Alon and Tarsi [AlTa92].
-/
theorem erdos_problem_630 {V : Type*} [Fintype V] (G : SimpleGraph V)
    (hplanar : G.IsPlanar) (hbip : G.Colorable 2) :
    IsChoosable G 3 :=
  sorry

end
