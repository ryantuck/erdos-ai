import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic

noncomputable section

open SimpleGraph Classical

/-!
# Erdős Problem #803

We call a graph H *D-balanced* (or *D-almost-regular*) if the maximum degree of
H is at most D times the minimum degree of H.

Is it true that for every m ≥ 1, if n is sufficiently large, any graph on n
vertices with ≥ n log n edges contains an O(1)-balanced subgraph with m vertices
and ≫ m log m edges (where the implied constants are absolute)?

A problem of Erdős and Simonovits [ErSi70]. Disproved by Alon [Al08], who
showed that for every D > 1 and large n there is a graph G with n vertices and
≥ n log n edges such that every D-balanced subgraph on m vertices has
≪ m √(log m) + log D edges.

https://www.erdosproblems.com/803
-/

/-- A simple graph on `Fin m` is *D-balanced* if for every pair of vertices
    u, v, the degree of u is at most D times the degree of v. This is
    equivalent to: max degree ≤ D · min degree. -/
def isDBalanced {m : ℕ} (H : SimpleGraph (Fin m)) (D : ℕ) : Prop :=
  ∀ u v : Fin m, H.degree u ≤ D * H.degree v

/--
Erdős Problem #803 [ErSi70] (Disproved by Alon [Al08]):

There exist absolute constants D ≥ 1 and C > 0 such that for every m ≥ 1,
there exists N₀ such that for all n ≥ N₀, every graph on n vertices with
at least n · log(n) edges contains a D-balanced subgraph on m vertices with
at least C · m · log(m) edges.
-/
theorem erdos_problem_803 :
    ∃ D : ℕ, D ≥ 1 ∧ ∃ C : ℝ, C > 0 ∧
    ∀ m : ℕ, m ≥ 1 →
    ∃ N₀ : ℕ, ∀ n : ℕ, n ≥ N₀ →
    ∀ (G : SimpleGraph (Fin n)),
      (G.edgeFinset.card : ℝ) ≥ (n : ℝ) * Real.log (n : ℝ) →
      ∃ (H : SimpleGraph (Fin m)) (f : Fin m → Fin n),
        Function.Injective f ∧
        (∀ u v, H.Adj u v → G.Adj (f u) (f v)) ∧
        isDBalanced H D ∧
        (H.edgeFinset.card : ℝ) ≥ C * (m : ℝ) * Real.log (m : ℝ) :=
  sorry

end
