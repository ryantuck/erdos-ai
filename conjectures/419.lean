import Mathlib.NumberTheory.Divisors
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Topology.Basic
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Order.Filter.Basic

open Filter Topology

noncomputable section

/-!
# Erdős Problem #419

If τ(n) counts the number of divisors of n, then what is the set of limit
points of τ((n+1)!) / τ(n!)?

Erdős and Graham noted that any number of the shape 1 + 1/k for k ≥ 1 is a
limit point (and thus so too is 1), but knew of no others.

Sawhney (and independently Erdős–Graham–Ivić–Pomerance [EGIP96]) proved that
these are the only limit points: the set of limit points of the ratio is
exactly {1 + 1/k : k ≥ 1} ∪ {1}.
-/

/-- The ratio τ((n+1)!) / τ(n!) as a real number, where τ counts divisors. -/
noncomputable def erdos419_ratio (n : ℕ) : ℝ :=
  ((Nat.divisors (n + 1).factorial).card : ℝ) / ((Nat.divisors n.factorial).card : ℝ)

/--
Erdős Problem #419 [ErGr80, p.83] — SOLVED:

The set of limit points of τ((n+1)!) / τ(n!) is exactly
{1 + 1/k : k ≥ 1} ∪ {1}, where τ(n) = |divisors of n|.

A value c is a cluster point of this sequence if and only if
c = 1 or c = 1 + 1/k for some positive integer k.
-/
theorem erdos_problem_419 (c : ℝ) :
    MapClusterPt c atTop erdos419_ratio ↔
      c = 1 ∨ ∃ k : ℕ, 0 < k ∧ c = 1 + 1 / (k : ℝ) :=
  sorry

end
