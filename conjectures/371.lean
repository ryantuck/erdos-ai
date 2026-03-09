import Mathlib.Data.Nat.Factors
import Mathlib.Data.Real.Basic
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Data.List.MinMax

open Filter Finset

noncomputable section

/-- The largest prime factor of n, or 0 if n ≤ 1. -/
def largestPrimeFactor (n : ℕ) : ℕ :=
  n.primeFactorsList.foldr max 0

/-- The natural density of a set A ⊆ ℕ equals d:
    |{m < N : m ∈ A}| / N → d as N → ∞. -/
def HasNaturalDensity (A : Set ℕ) (d : ℝ) [DecidablePred (· ∈ A)] : Prop :=
  Filter.Tendsto
    (fun N : ℕ => ((Finset.range N).filter (· ∈ A)).card / (N : ℝ))
    Filter.atTop (nhds d)

/--
Erdős Problem #371 [ErPo78, Er79e, ErGr80, Er85c, Va99]:

Let P(n) denote the largest prime factor of n. Show that the set of n
with P(n) < P(n+1) has density 1/2.

Conjectured by Erdős and Pomerance, who proved that this set and its
complement both have positive upper density. Teräväinen (2018) proved
that the logarithmic density is 1/2. Tao and Teräväinen (2019) proved
the asymptotic density is 1/2 'at almost all scales'.
-/
theorem erdos_problem_371 :
    HasNaturalDensity {n : ℕ | largestPrimeFactor n < largestPrimeFactor (n + 1)} (1 / 2) :=
  sorry

end
