import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Nat.Lattice
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Basic

open SimpleGraph

noncomputable section

/-!
# Erdős Problem #753

The list chromatic number χ_L(G) is defined to be the minimal k such that for
any assignment of a list of k colours to each vertex of G (perhaps different
lists for different vertices) a colouring of each vertex by a colour on its list
can be chosen such that adjacent vertices receive distinct colours.

Does there exist some constant c > 0 such that
  χ_L(G) + χ_L(Gᶜ) > n^{1/2+c}
for every graph G on n vertices (where Gᶜ is the complement of G)?

A problem of Erdős, Rubin, and Taylor [ERT80].

The answer is no: Alon [Al92] proved that, for every n, there exists a graph G
on n vertices such that χ_L(G) + χ_L(Gᶜ) ≪ (n log n)^{1/2}, where the implied
constant is absolute.

https://www.erdosproblems.com/753

Tags: graph theory, chromatic number
-/

/-- A graph G is k-choosable (k-list-colorable) if for every assignment of lists
    of size at least k to the vertices, there exists a proper coloring where each
    vertex receives a color from its list. -/
def IsChoosable {V : Type*} (G : SimpleGraph V) (k : ℕ) : Prop :=
  ∀ (L : V → Finset ℕ), (∀ v, k ≤ (L v).card) →
    ∃ f : V → ℕ, (∀ v, f v ∈ L v) ∧ (∀ u v, G.Adj u v → f u ≠ f v)

/-- The list chromatic number (choice number) of a graph: the minimum k such
    that G is k-choosable. -/
noncomputable def listChromaticNumber {V : Type*} (G : SimpleGraph V) : ℕ :=
  sInf {k : ℕ | IsChoosable G k}

/--
**Alon's Theorem (Disproof of Erdős Problem #753)** [Al92]:

There exists an absolute constant C > 0 such that for every n ≥ 2, there exists
a graph G on n vertices with
  χ_L(G) + χ_L(Gᶜ) ≤ C · √(n · log n).
-/
theorem erdos_problem_753 :
    ∃ C : ℝ, C > 0 ∧
    ∀ n : ℕ, n ≥ 2 →
      ∃ (G : SimpleGraph (Fin n)),
        (listChromaticNumber G + listChromaticNumber Gᶜ : ℝ) ≤
          C * Real.sqrt (n * Real.log n) :=
  sorry

end
