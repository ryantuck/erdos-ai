import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Real.Archimedean
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Algebra.Order.Floor.Defs

noncomputable section

/-!
# Erdős Problem #900

There is a function f:(1/2,∞) → ℝ such that f(c) → 0 as c → 1/2⁺ and
f(c) → 1 as c → ∞ and every random graph with n vertices and cn edges
has (with high probability) a path of length at least f(c)·n.

This was proved by Ajtai, Komlós, and Szemerédi [AKS81].
-/

/-- A simple graph G contains a path with at least k edges, i.e., a sequence
    of k+1 distinct vertices where consecutive vertices are adjacent. -/
def graphHasLongPath {V : Type*} (G : SimpleGraph V) (k : ℕ) : Prop :=
  ∃ m : ℕ, m ≥ k ∧
    ∃ (path : Fin (m + 1) → V),
      Function.Injective path ∧
      ∀ i : ℕ, ∀ h : i < m,
        G.Adj (path ⟨i, by omega⟩) (path ⟨i + 1, by omega⟩)

/-- The probability that a uniformly random simple graph on Fin n with exactly
    m edges satisfies a given property, in the Erdős–Rényi G(n,m) model.
    This is the fraction |{G ∈ G(n,m) | P G}| / |G(n,m)|. -/
noncomputable def erdosRenyiProbability (n m : ℕ)
    (P : SimpleGraph (Fin n) → Prop) : ℝ := sorry

/--
Erdős Problem #900 (proved by Ajtai, Komlós, and Szemerédi [AKS81]):

There exists f : ℝ → ℝ with f(c) → 0 as c → (1/2)⁺ and f(c) → 1 as c → ∞,
such that for every c > 1/2, a random graph G(n, ⌊cn⌋) with high probability
contains a path of length at least f(c)·n.
-/
theorem erdos_problem_900 :
    ∃ f : ℝ → ℝ,
    (Filter.Tendsto (fun h => f (1/2 + h))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0)) ∧
    (Filter.Tendsto f Filter.atTop (nhds 1)) ∧
    (∀ c : ℝ, c > 1/2 → ∀ ε : ℝ, ε > 0 →
      ∃ N₀ : ℕ, ∀ n : ℕ, n ≥ N₀ →
        erdosRenyiProbability n (⌊c * (n : ℝ)⌋₊)
          (fun G => graphHasLongPath G (⌊f c * (n : ℝ)⌋₊)) ≥ 1 - ε) :=
  sorry

end
