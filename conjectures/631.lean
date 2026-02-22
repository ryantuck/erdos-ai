import Mathlib.Combinatorics.SimpleGraph.Coloring
import Mathlib.Data.Nat.Lattice

open SimpleGraph

noncomputable section

/-!
# Erdős Problem #631

The list chromatic number χ_L(G) is defined to be the minimal k such that for any
assignment of a list of k colours to each vertex of G (perhaps different lists for
different vertices) a colouring of each vertex by a colour on its list can be chosen
such that adjacent vertices receive distinct colours.

Does every planar graph G have χ_L(G) ≤ 5? Is this best possible?

A problem of Erdős, Rubin, and Taylor [ERT80]. The answer to both is yes:
Thomassen [Th94] proved that χ_L(G) ≤ 5 if G is planar, and Voigt [Vo93]
constructed a planar graph with χ_L(G) = 5.
-/

/-- A proper list coloring of G with respect to a list assignment L : V → Finset ℕ
    is a function f : V → ℕ such that f(v) ∈ L(v) for all v, and f(u) ≠ f(v)
    whenever u and v are adjacent. -/
def Erdos631.IsProperListColoring {V : Type*} (G : SimpleGraph V) (L : V → Finset ℕ)
    (f : V → ℕ) : Prop :=
  (∀ v, f v ∈ L v) ∧ (∀ u v, G.Adj u v → f u ≠ f v)

/-- A graph G is k-choosable (k-list-colorable) if for every list assignment L
    where each vertex receives a list of at least k colors, there exists a
    proper list coloring. -/
def Erdos631.IsChoosable {V : Type*} (G : SimpleGraph V) (k : ℕ) : Prop :=
  ∀ L : V → Finset ℕ, (∀ v, k ≤ (L v).card) →
    ∃ f : V → ℕ, Erdos631.IsProperListColoring G L f

/-- A graph is planar if it can be embedded in the plane without edge crossings.
    Mathlib does not yet have a formalization of graph planarity; we define it
    here as an opaque predicate. -/
def Erdos631.IsPlanar {V : Type*} [Fintype V] (G : SimpleGraph V) : Prop :=
  sorry

/--
Erdős Problem #631, Part 1 (Thomassen's theorem [Th94]):

Every planar graph G is 5-choosable, i.e., χ_L(G) ≤ 5.
-/
theorem erdos_problem_631_upper {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (hplanar : Erdos631.IsPlanar G) :
    Erdos631.IsChoosable G 5 :=
  sorry

/--
Erdős Problem #631, Part 2 (Voigt's construction [Vo93]):

There exists a planar graph that is not 4-choosable, showing that 5 is best possible.
-/
theorem erdos_problem_631_lower :
    ∃ (V : Type) (_ : Fintype V) (G : SimpleGraph V),
      Erdos631.IsPlanar G ∧ ¬Erdos631.IsChoosable G 4 :=
  sorry

end
