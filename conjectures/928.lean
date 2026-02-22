import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Card
import Mathlib.Order.Filter.Basic
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open Set Filter

noncomputable section

/-!
# Erdős Problem #928

Let α, β ∈ (0,1) and let P(n) denote the largest prime divisor of n.
Does the density of integers n such that P(n) < n^α and P(n+1) < (n+1)^β exist?

Erdős asked whether the events P(n) < n^α and P(n+1) < (n+1)^β are independent,
in the sense that the density of n satisfying both conditions equals
ρ(1/α)·ρ(1/β), where ρ is the Dickman function.

Dickman [Di30] showed the density of smooth n, with largest prime factor < n^α,
is ρ(1/α) where ρ is the Dickman function.

Teräväinen [Te18] proved the logarithmic density exists and equals ρ(1/α)ρ(1/β).
Wang [Wa21] proved the natural density equals ρ(1/α)ρ(1/β) assuming the
Elliott-Halberstam conjecture for friable integers.

Reference: [Er76d][ErPo78]
https://www.erdosproblems.com/928
-/

/-- The largest prime factor of n, or 0 if n ≤ 1. -/
noncomputable def largestPrimeFactor (n : ℕ) : ℕ :=
  if h : n.primeFactors.Nonempty then n.primeFactors.max' h else 0

/-- The Dickman function ρ : ℝ → ℝ, the unique continuous function satisfying
    ρ(u) = 1 for 0 ≤ u ≤ 1 and u·ρ'(u) = -ρ(u-1) for u > 1. -/
noncomputable def dickmanRho : ℝ → ℝ := sorry

/-- The natural density of a set S ⊆ ℕ exists and equals d. -/
def HasNaturalDensity (S : Set ℕ) (d : ℝ) : Prop :=
  Filter.Tendsto (fun N : ℕ => ((S ∩ {i | 1 ≤ i ∧ i ≤ N}).ncard : ℝ) / N)
    atTop (nhds d)

/-- The set of n ≥ 2 with P(n) < n^α and P(n+1) < (n+1)^β. -/
def smoothConsecutiveSet (α β : ℝ) : Set ℕ :=
  {n : ℕ | n ≥ 2 ∧
    (largestPrimeFactor n : ℝ) < (n : ℝ) ^ α ∧
    (largestPrimeFactor (n + 1) : ℝ) < ((n + 1 : ℕ) : ℝ) ^ β}

/--
Erdős Problem #928 [Er76d][ErPo78]:

For α, β ∈ (0,1), the natural density of integers n with P(n) < n^α and
P(n+1) < (n+1)^β exists and equals ρ(1/α)·ρ(1/β), where ρ is the Dickman
function. This asserts independence of the smooth-number events for
consecutive integers.
-/
theorem erdos_problem_928 (α β : ℝ) (hα₀ : 0 < α) (hα₁ : α < 1)
    (hβ₀ : 0 < β) (hβ₁ : β < 1) :
    HasNaturalDensity (smoothConsecutiveSet α β)
      (dickmanRho (1 / α) * dickmanRho (1 / β)) :=
  sorry

end
