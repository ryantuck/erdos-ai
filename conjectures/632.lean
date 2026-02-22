import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card

open SimpleGraph

noncomputable section

/-!
# Erdős Problem #632

A graph is (a,b)-choosable if for any assignment of a list of a colours to each of
its vertices there is a subset of b colours from each list such that the subsets of
adjacent vertices are disjoint.

If G is (a,b)-choosable then G is (a*m, b*m)-choosable for every integer m ≥ 1.

A problem of Erdős, Rubin, and Taylor [ERT80]. This is false: Dvořák, Hu, and
Sereni [DHS19] construct a graph which is (4,1)-choosable but not (8,2)-choosable.
-/

/-- A graph G is (a,b)-choosable if for every assignment L of a list of at least a
    colors to each vertex, there exists a choice of a subset S(v) ⊆ L(v) of size b
    for each vertex v, such that the chosen subsets of adjacent vertices are disjoint. -/
def Erdos632.IsABChoosable {V : Type*} (G : SimpleGraph V) (a b : ℕ) : Prop :=
  ∀ L : V → Finset ℕ, (∀ v, a ≤ (L v).card) →
    ∃ S : V → Finset ℕ, (∀ v, S v ⊆ L v) ∧ (∀ v, (S v).card = b) ∧
      (∀ u v, G.Adj u v → Disjoint (S u) (S v))

/--
Erdős Problem #632 [ERT80] (disproved by Dvořák, Hu, and Sereni [DHS19]):

If G is (a,b)-choosable then G is (a*m, b*m)-choosable for every positive integer m.
-/
theorem erdos_problem_632 {V : Type*} (G : SimpleGraph V) (a b m : ℕ) (hm : 1 ≤ m)
    (hab : Erdos632.IsABChoosable G a b) :
    Erdos632.IsABChoosable G (a * m) (b * m) :=
  sorry

end
