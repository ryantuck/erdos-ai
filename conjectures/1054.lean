import Mathlib.NumberTheory.Divisors
import Mathlib.Data.Finset.Sort
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Topology.Order.Basic
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Order.Interval.Finset.Nat

open Finset Filter

noncomputable section

/-!
# Erdős Problem #1054

Let $f(n)$ be the minimal integer $m$ such that $n$ is the sum of the $k$
smallest divisors of $m$ for some $k \geq 1$.

Is it true that $f(n) = o(n)$? Or is this true only for almost all $n$,
and $\limsup f(n)/n = \infty$?

The strong claim $f(n) = o(n)$ was disproved by Tao. The remaining open
question is whether $f(n) = o(n)$ for almost all $n$.
-/

/-- The sorted list of divisors of n in increasing order. -/
def erdos1054_sortedDivisors (n : ℕ) : List ℕ :=
  (n.divisors.sort (· ≤ ·))

/-- Prefix sums of a list with accumulator. Returns [acc+a₁, acc+a₁+a₂, ...]. -/
def erdos1054_prefixSums : List ℕ → ℕ → List ℕ
  | [], _ => []
  | a :: as, acc => (acc + a) :: erdos1054_prefixSums as (acc + a)

/-- The set of values obtainable as sums of the k smallest divisors of n,
    for some k ≥ 1. -/
def erdos1054_S (n : ℕ) : Finset ℕ :=
  (erdos1054_prefixSums (erdos1054_sortedDivisors n) 0).toFinset

/-- f(n): the minimal m such that n ∈ erdos1054_S m, i.e., n is the sum of
    the k smallest divisors of m for some k ≥ 1. -/
noncomputable def erdos1054_f (n : ℕ) : ℕ :=
  sInf {m : ℕ | n ∈ erdos1054_S m}

/--
Erdős Problem #1054, strong form (DISPROVED by Tao):

f(n) = o(n), i.e., for every ε > 0, eventually f(n) < ε · n.
-/
theorem erdos_problem_1054_strong :
    ∀ ε : ℝ, 0 < ε →
      ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
        (erdos1054_f n : ℝ) < ε * (n : ℝ) :=
  sorry

/--
Erdős Problem #1054 (OPEN):

f(n) = o(n) for almost all n. Formalized as: for any ε > 0, the density of
{n ≤ x : f(n) ≥ ε · n} tends to 0 as x → ∞.
-/
theorem erdos_problem_1054 :
    ∀ ε : ℝ, 0 < ε →
      Tendsto (fun x : ℕ =>
        (((Finset.Icc 1 x).filter (fun n =>
          (erdos1054_f n : ℝ) ≥ ε * (n : ℝ))).card : ℝ) / (x : ℝ))
        atTop (nhds 0) :=
  sorry

end
