import Mathlib.Combinatorics.SimpleGraph.Paths
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Card
import Mathlib.Analysis.SpecialFunctions.Pow.Real

noncomputable section

open SimpleGraph

/-- The cycle spectrum of a simple graph: the set of all cycle lengths present in G. -/
def cycleSpectrum84 {V : Type*} (G : SimpleGraph V) : Set ℕ :=
  {ℓ : ℕ | ∃ v : V, ∃ p : G.Walk v v, p.IsCycle ∧ p.length = ℓ}

/-- The number of distinct cycle spectra realizable by simple graphs on Fin n. -/
noncomputable def cycleSetCount84 (n : ℕ) : ℕ :=
  Set.ncard {A : Set ℕ | ∃ G : SimpleGraph (Fin n), cycleSpectrum84 G = A}

/--
Erdős Problem #84 (Conjectured by Erdős and Faudree [Er94b][Er95][Er96][Er97d]):

The cycle set of a graph G on n vertices is the set A ⊆ {3,...,n} of all cycle
lengths present in G. Let f(n) count the number of distinct such sets A over all
graphs on n vertices.

Part 1 (proved by Verstraëte [Ve04]): f(n) = o(2^n).
That is, for every ε > 0, for all sufficiently large n, f(n) ≤ ε · 2^n.

Part 2 (open): f(n)/2^{n/2} → ∞.
That is, for every B > 0, for all sufficiently large n, f(n) ≥ B · 2^{n/2}.

Erdős and Faudree showed 2^{n/2} < f(n) ≤ 2^{n-2}.
Verstraëte proved f(n) ≪ 2^{n - n^{1/10}}, improved by Nenadov to
f(n) ≪ 2^{n - n^{1/2 - o(1)}}.
-/
theorem erdos_problem_84_part1 :
    ∀ ε : ℝ, ε > 0 →
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      (cycleSetCount84 n : ℝ) ≤ ε * (2 : ℝ) ^ n :=
  sorry

theorem erdos_problem_84_part2 :
    ∀ B : ℝ, B > 0 →
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      (cycleSetCount84 n : ℝ) ≥ B * (2 : ℝ) ^ ((n : ℝ) / 2) :=
  sorry

end
