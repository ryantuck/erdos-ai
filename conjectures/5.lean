import Mathlib.Data.Nat.Nth
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Topology.Order.Basic

open Filter Nat Real

noncomputable section

/--
The normalized prime gap at index n (0-indexed):
  (p_{n+1} - p_n) / log(n+1)
where p_n = nth Nat.Prime n is the n-th prime (so p_0 = 2, p_1 = 3, …).
We use n+1 in the denominator so that log is evaluated at a positive argument.
-/
def normalizedPrimeGap (n : ℕ) : ℝ :=
  ((nth Nat.Prime (n + 1) : ℝ) - (nth Nat.Prime n : ℝ)) / Real.log ((n : ℝ) + 1)

/--
Erdős Problem #5 [Er55c, Er57, Er61, Er65b, Er85c, Er90, Er97c]:

Let pₙ denote the n-th prime. Let S be the set of limit points of the sequence
  (p_{n+1} - pₙ) / log n.
The conjecture asserts S = [0, ∞], i.e., every value C ∈ [0, ∞] is attained as
a limit along some subsequence.

Formally (for finite C): for every C ≥ 0 there exists a strictly increasing
sequence of indices n₁ < n₂ < ⋯ such that
  (p_{nᵢ+1} - p_{nᵢ}) / log nᵢ → C   as i → ∞.

Known results toward this conjecture:
- ∞ ∈ S (Westzynthius 1931): prime gaps are unbounded relative to log n.
- 0 ∈ S (Goldston–Pintz–Yıldırım 2009): normalized gaps can be arbitrarily small.
- S has positive Lebesgue measure (Erdős 1955; Ricci 1956).
- S contains arbitrarily large finite numbers (Hildebrand–Maier 1988).
- [0, c] ⊆ S for some c > 0 (Pintz 2016).
- At least 12.5% of [0, ∞) belongs to S (Banks–Freiberg–Maynard 2016).
- At least 1/3 of [0, ∞) belongs to S, and S has bounded gaps (Merikoski 2020).
-/
theorem erdos_problem_5 :
    ∀ C : ℝ, 0 ≤ C →
      ∃ f : ℕ → ℕ, StrictMono f ∧
        Tendsto (fun i => normalizedPrimeGap (f i)) atTop (nhds C) :=
  sorry

end
